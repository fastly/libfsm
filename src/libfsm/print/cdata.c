/*
 * Copyright 2024 Scott Vokes
 *
 * See LICENCE for the full copyright terms.
 */

#include <assert.h>
#include <string.h>
#include <ctype.h>
#include <stdlib.h>
#include <limits.h>
#include <errno.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>

#include <print/esc.h>

#include <adt/set.h>
#include <adt/u64bitset.h>

#include <fsm/fsm.h>
#include <fsm/pred.h>
#include <fsm/walk.h>
#include <fsm/print.h>
#include <fsm/options.h>

#include "libfsm/internal.h"
#include "libfsm/print.h"

#include "ir.h"

/* Print mode that generates C data literals for the DFA, plus a small interepreter.
 * This mostly exists to sidestep very expensive compilation for large data sets
 * using the other C modes. -sv */

/* How large a numeric ID type do the particular tables need? */
enum id_type {
	U8,
	U16,
	U32,
	U64,
};

static const char*
id_type_str(enum id_type t)
{
	switch (t) {
	case U8: return "uint8_t";
	case U16: return "uint16_t";
	case U32: return "uint32_t";
	case U64: return "uint64_t";
	default:
		assert(!"match fail");
		return "";
	}
}

static enum id_type
size_needed(size_t max_value)
{
	if (max_value < (1ULL << 8)) { return U8; }
	if (max_value < (1ULL << 16)) { return U16; }
	if (max_value < (1ULL << 32)) { return U32; }
	return U64;
}

/* Configuration. Figure out whether we really need a uint32_t for edge offsets
 * or can get by with a uint16_t, etc. and make the output more dense. */
struct cdata_config {
	fsm_state_t start;
	size_t state_count;
	size_t non_default_edge_count;
	size_t group_count;
	size_t range_count;
	size_t endid_count;
	size_t eager_output_count;

	/* numeric type for state IDs, based on the higest state # */
	enum id_type t_state_id;

	/* numeric type for indexes into the dst_state table, based on
	 * the number of edge groups */
	enum id_type t_dst_state_offset;

	/* numeric type for endid and eager_output table offsets */
	enum id_type t_endid_offset;
	enum id_type t_eager_output_offset;

	/* numeric type for endid and eager_output table values */
	enum id_type t_endid_value;
	enum id_type t_eager_output_value;
};

/* TODO: move comments over */
#if 0
typedef uint32_t prefix_cdata_state;
#define NO_DEFAULT ((uint32_t)-1)

struct prefix_cdata_dfa {
	prefix_cdata_state start;
	struct prefix_cdata_state {
		/* which labels have non-default edges */
		uint64_t labels[256/4];
		prefix_cdata_state default_dst; /* NO_DEFAULT -> match failure */

		/* popcount sum at end of labels[i], so finding the edge offset for
		 * only needs to popcount labels[label/64] masked */
		uint8_t rank[3];

		bool end;	/* end state? */

		/* TODO: for a complete state, we could encode just the labels that
		 * have a different destination than the preceding labels, since
		 * there is usually a lot of duplication. */
		/* bool complete; */

		/* FIXME: emit uint64_t or uint32_t here, based on edge table size */
		size_t dst_table_offset; /* where the offsets start */

		/* Offsets into endid and eager output tables. The total table
		 * size is known, and this struct exists for each state, so
		 * ideally emit e.g. uint16_t rather than size_t when possible! */
		uint16_t endid_offset;
		uint16_t eager_output_offset;
	} states[MAX_STATE];  // MAX_STATE is known at compile-time

	/* For a state s, the state's edges start at S->dst_table_offset,
	 * for every bit set in s->labels[] there is a destination state.
	 * Self-edges are explicitly encoded here. */
	prefix_cdata_state dst_table[EDGE_COUNT]; /* EDGE_COUNT is known at compile-time */

	/* endids: a table representing the set of endIDs.
	 * This is a flat array of ascending end IDs, with each run terminated
	 * by the first non-ascending value.
	 *
	 * ENDID_COUNT and EAGER_OUTPUT_COUNT are known at compile time. */
	uint_that_fits_whatever_the_max_endid_is_t endid_table[ENDID_COUNT];
	uint_that_fits_whatever_the_max_eager_output_is_t eager_output_table[EAGER_OUTPUT_COUNT];
};
#endif

static bool
generate_struct_definition(FILE *f, const struct cdata_config *config, bool comments, const char *prefix)
{
	fprintf(f,
	    "\ttypedef %s %s_cdata_state;\n"
	    "#define %s_NO_DEFAULT_STATE ((%s_cdata_state)-1)\n",
	    id_type_str(config->t_state_id),
	    prefix, prefix, prefix);

	/* TODO: comments */
	(void)comments;

	fprintf(f,
	    "\tstruct %s_cdata_dfa {\n"
	    "\t\t%s_cdata_state start;\n"
	    "\t\tstruct %s_cdata_state {\n"
	    "\t\t\t%s_cdata_state default_dst; /* or %s_NO_DEFAULT_STATE */\n"
	    "\t\t\t/* which labels have non-default edges */\n"
	    "\t\t\tuint64_t labels[256/4];\n"
	    "\t\t\tuint64_t label_group_starts[256/4];\n"
	    "\t\t\tuint8_t rank_sums[4]; /* sum as of end of label_group_starts[n] */\n"
	    "\n"
	    "\t\t\tbool end;\n",
	    /* "\t\t\tbool complete;\n", */
	    prefix, prefix, prefix, prefix, prefix);

	fprintf(f, "\t\t\t%s dst_table_offset;\n", id_type_str(config->t_state_id));

	if (config->endid_count > 0) {
		fprintf(f, "\t\t\t%s endid_offset;\n", id_type_str(config->t_endid_offset));
	}
	if (config->eager_output_count > 0) {
		fprintf(f, "\t\t\t%s eager_output_offset;\n", id_type_str(config->t_eager_output_offset));
	}

	fprintf(f,
	    "\t\t} states[%zd];\n"
	    "\n"
	    "\t\t%s_cdata_state dst_table[%zd];\n",
	    config->state_count, prefix, config->non_default_edge_count);

	if (config->endid_count > 0) {
		/* TODO: reduce the size of the endid type when possible -- this will
		 * usually be sequentially allocated, so it will typically fit in a
		 * uint8_t or uint16_t. */
		fprintf(f, "\t\t%s endid_table[%zd + 1];\n",
		    id_type_str(config->t_endid_value), config->endid_count);
	}

	if (config->eager_output_count > 0) {
		/* TODO: reduce the size of the eager_ouptut id type when possible */
		fprintf(f, "\t\t%s eager_output_table[%zd + 1];\n",
		    id_type_str(config->t_eager_output_value), config->eager_output_count);
	}

	fprintf(f,
	    "\t};\n");
	return true;
}

struct dst_buf {
	size_t ceil;
	size_t used;
	uint32_t *buf;
};

static bool
append_edge(struct dst_buf *buf, uint32_t e)
{
	assert(buf->used < buf->ceil);
	buf->buf[buf->used++] = e;
	return true;
}

struct range_info {
	uint8_t start;
	uint8_t end;
	uint32_t dst_state;
};

static int
cmp_outgoing(const void *pa, const void *pb)
{
	const struct range_info *a = (const struct range_info *)pa;
	const struct range_info *b = (const struct range_info *)pb;
	return a->start < b->start ? -1 : a->start > b->start ? 1 : 0;
}

static bool
save_groups(size_t group_count, const struct ir_group *groups,
    struct dst_buf *edges, uint64_t *labels, uint64_t *label_group_starts, uint8_t *rank_sums) {
	/* Convert the group ranges to bitsets and an edge->destination state list. */
#define DUMP_GROUP 1
	if (DUMP_GROUP) {
		fprintf(stderr, "\n%s: dump_group [[\n", __func__);
		for (size_t g_i = 0; g_i < group_count; g_i++) {
			fprintf(stderr, "- group %zd:\n", g_i);
			const struct ir_group *g = &groups[g_i];
			for (size_t r_i = 0; r_i < g->n; r_i++) {
				const struct ir_range *r = &g->ranges[r_i];
				assert(r->start <= r->end);
				fprintf(stderr, "  - range[%zd]: '%c'(0x%02x) -- '%c'(0x%02x)\n",
				    r_i,
				    isprint(r->start) ? r->start : '.', r->start,
				    isprint(r->end) ? r->end : '.', r->end);
			}
		}
		fprintf(stderr, "]]\n");
	}

	/* Because this is a DFA there should be at most 256 outgoing. */
	size_t outgoing_used = 0;
	struct range_info outgoing[256];

	/* Groups and ranges aren't necessarily ordered by character, so collect and sort first,
	 * otherwise the ranks can point to the wrong offset in edges[]. */
	for (size_t g_i = 0; g_i < group_count; g_i++) {
		const struct ir_group *g = &groups[g_i];
		for (size_t r_i = 0; r_i < g->n; r_i++) {
			const struct ir_range *r = &g->ranges[r_i];
			assert(r->start <= r->end);
			outgoing[outgoing_used++] = (struct range_info){
				.start = r->start,
				.end = r->end,
				.dst_state = g->to,
			};
			assert(outgoing_used <= 256);
		}
	}

	/* Sort them by .start. They should be unique and non-overlapping. */
	qsort(outgoing, outgoing_used, sizeof(outgoing[0]), cmp_outgoing);
	for (size_t o_i = 1; o_i < outgoing_used; o_i++) {
		assert(outgoing[o_i - 1].start < outgoing[o_i].start);
	}

	for (size_t o_i = 0; o_i < outgoing_used; o_i++) {
		const struct range_info *r = &outgoing[o_i];
		assert(!u64bitset_get(label_group_starts, r->start));
		u64bitset_set(label_group_starts, r->start);
		if (!append_edge(edges, r->dst_state)) {
			return false;
		}

		for (uint8_t c = r->start; c <= r->end; c++) {
			fprintf(stderr, "  -- char '%c' (0x%02x) -> %d\n",
			    isprint(c) ? c : '.', c, r->dst_state);
			assert(!u64bitset_get(labels, r->start));
			u64bitset_set(labels, c);
		}
	}

	/* Precompute label_group_starts[] rank sums so lookup only needs to
	 * compute rank for the label's word, not every word preceding it. */
	rank_sums[0] = 0;
	uint8_t total = 0;
	for (size_t i = 1; i < 4; i++) {
		total += u64bitset_popcount(label_group_starts[i - 1]);
		rank_sums[i] = total;
	}

	return true;
}

struct endid_buf {
	size_t ceil;
	size_t used;
	uint64_t *buf;
};

static bool
append_endid(struct endid_buf *buf, uint64_t id)
{
	if (buf->used == buf->ceil) {
		const size_t nceil = buf->ceil == 0 ? 8 : 2*buf->ceil;
		uint64_t *nendids = realloc(buf->buf, nceil * sizeof(nendids[0]));
		assert(nendids != NULL);
		buf->buf = nendids;
		buf->ceil = nceil;
	}

	assert(buf->used < buf->ceil);
	buf->buf[buf->used++] = id;
	return true;
}

struct eager_output_buf {
	size_t ceil;
	size_t used;
	uint64_t *buf;
};

static bool
append_eager_output(struct eager_output_buf *buf, uint64_t id)
{
	if (buf->used == buf->ceil) {
		const size_t nceil = buf->ceil == 0 ? 8 : 2*buf->ceil;
		uint64_t *neager_outputs = realloc(buf->buf, nceil * sizeof(neager_outputs[0]));
		assert(neager_outputs != NULL);
		buf->buf = neager_outputs;
		buf->ceil = nceil;
	}

	assert(buf->used < buf->ceil);
	buf->buf[buf->used++] = id;
	return true;
}

static bool
generate_data(FILE *f, const struct cdata_config *config,
    const char *prefix, const struct ir *ir)
{
	(void)f;
	(void)config;
	(void)prefix;
	(void)ir;

	struct dst_buf edges = { .ceil = config->non_default_edge_count };

	edges.buf = malloc(config->non_default_edge_count * sizeof(edges.buf[0]));
	assert(edges.buf != NULL);

	struct endid_buf endid_buf = { .ceil = 0 };
	uint64_t endids_prev = (uint64_t)-1;

	struct eager_output_buf eager_output_buf = { .ceil = 0 };
	uint64_t eager_outputs_prev = (uint64_t)-1;

	fprintf(f,
	    "\tstatic struct %s_cdata_dfa %s_dfa_data = {\n"
	    "\t\t.start = %u,\n"
	    "\t\t.states = {\n", prefix, prefix, config->start);
	for (size_t s_i = 0; s_i < ir->n; s_i++) {
		const struct ir_state *s = &ir->states[s_i];
		const bool is_end = s->isend;
		bool is_complete = false;
		const bool has_endids = s->endids.count > 0;
		const bool has_eager_outputs = s->eager_outputs != NULL && s->eager_outputs->count > 0;
		uint64_t labels[256/64] = { 0 };
		uint64_t label_group_starts[256/64] = { 0 };
		uint8_t rank_sums[4] = { 0 };

		const size_t edge_base = edges.used;
		uint32_t default_dst = ((uint32_t)-1);

		/* Offsets into the endid and eager_output tables
		 * for where this state's IDs will appear, if any. */
		size_t endids_base;
		size_t eager_outputs_base;

		if (s->endids.count > 0) {
			/* If the first endid for this state is later than the last endid
			 * appended, append an extra terminator 0 in-between them. Otherwise,
			 * the last state that had endids will be falsely associated with
			 * this state's as well.
			 *
			 * The numeric size used for endid offsets needs to account for this
			 * padding, so add the state count (the worst case). */
			if (s->endids.ids[0] > endids_prev) {
				if (!append_endid(&endid_buf, 0)) { goto alloc_fail; }
			}

			endids_base = endid_buf.used;
			for (size_t i = 0; i < s->endids.count; i++) {
				if (!append_endid(&endid_buf, s->endids.ids[i])) {
					goto alloc_fail;
				}
			}
			endids_prev = s->endids.ids[s->endids.count - 1];
		}

		const size_t eo_count = s->eager_outputs == NULL ? 0 : s->eager_outputs->count;
		if (eo_count > 0) {
			/* Same as with endids_prev, above. */
			if (s->eager_outputs->ids[0] > eager_outputs_prev) {
				if (!append_eager_output(&eager_output_buf, 0)) {
					goto alloc_fail;
				}
			}
			eager_outputs_base = eager_output_buf.used;

			for (size_t i = 0; i < eo_count; i++) {
				if (!append_eager_output(&eager_output_buf, s->eager_outputs->ids[i])) {
					goto alloc_fail;
				}
			}
			eager_outputs_prev = s->eager_outputs->ids[eo_count - 1];
		}

		fprintf(stderr, "-- processing strategy for state %zd...\n", s_i);

		switch (s->strategy) {
		case IR_NONE:
			break;
		case IR_SAME:	/* all default */
			default_dst = s->u.same.to;
			/* doesn't set any edges */
			break;
		case IR_COMPLETE:
			is_complete = true;
			if (!save_groups(s->u.complete.n, s->u.complete.groups, &edges, labels, label_group_starts, rank_sums)) {
				goto alloc_fail;
			}
			break;
		case IR_PARTIAL:
		{
			if (!save_groups(s->u.partial.n, s->u.partial.groups, &edges, labels, label_group_starts, rank_sums)) {
				goto alloc_fail;
			}
			break;
		}
		case IR_DOMINANT:
		{
			/* fprintf(stderr, "-- dominant\n"); */
			default_dst = s->u.dominant.mode;
			if (!save_groups(s->u.dominant.n, s->u.dominant.groups, &edges, labels, label_group_starts, rank_sums)) {
				goto alloc_fail;
			}
			break;
		}
		case IR_ERROR:
			goto not_implemented;
		case IR_TABLE:
			goto not_implemented;
		default:
			goto not_implemented;
		}

		fprintf(f, "\t\t\t[%zd] = {%s\n", s_i, s_i == config->start ? " /* start */" : "");
		fprintf(f, "\t\t\t\t.labels = { 0x%lx, 0x%lx, 0x%lx, 0x%lx },\n",
		    labels[0], labels[1], labels[2], labels[3]);
		fprintf(f, "\t\t\t\t.label_group_starts = { 0x%lx, 0x%lx, 0x%lx, 0x%lx },\n",
		    label_group_starts[0], label_group_starts[1], label_group_starts[2], label_group_starts[3]);

		/* rank_sums[0] is always 0, but allows us to avoid a subtraction in the inner loop,
		 * and the space would be wasted otherwise anyway due to alignment. */
		fprintf(f, "\t\t\t\t.rank_sums = { %u, %u, %u, %u },\n",
		    rank_sums[0], rank_sums[1], rank_sums[2], rank_sums[3]);

		if (default_dst == (uint32_t)-1) {
			fprintf(f, "\t\t\t\t.default_dst = %zu /* NONE */,\n", config->state_count);
		} else {
			fprintf(f, "\t\t\t\t.default_dst = %u,\n", default_dst);
		}


		fprintf(f, "\t\t\t\t.end = %d,\n", is_end);
		fprintf(f, "\t\t\t\t.dst_table_offset = %zd,\n", edge_base);

		/* Only emit these if any state uses endids/eager_outputs, and if this
		 * state doesn't then use the end of the array as NONE. */
		if (config->endid_count > 0) {
			if (has_endids) {
				fprintf(f, "\t\t\t\t.endid_offset = %zd,\n", endids_base);
			} else {
				fprintf(f, "\t\t\t\t.endid_offset = %zd, /* none */\n", config->endid_count);
			}

		}

		if (config->eager_output_count > 0) {
			if (has_eager_outputs) {
				fprintf(f, "\t\t\t\t.eager_output_offset = %zd,\n", eager_outputs_base);
			} else {
				fprintf(f, "\t\t\t\t.eager_output_offset = %zd, /* none */\n", config->eager_output_count);
			}
		}

		fprintf(f, "\t\t\t},\n");
	}
	fprintf(f, "\t},\n");

	fprintf(f,
	    "\t\t.dst_table = {");

	for (size_t i = 0; i < edges.used; i++) {
		if ((i & 31) == 0) { fprintf(f, "\n"); }
		fprintf(f, " %u,", edges.buf[i]);
	}

	/* edges */
	fprintf(f, "\n\t\t},\n");

	if (endid_buf.used > 0) {
		fprintf(f, "\t\t.endid_table = {");
		for (size_t i = 0; i < endid_buf.used; i++) {
			if ((i & 31) == 0) { fprintf(f, "\n"); }
			fprintf(f, " %lu,", endid_buf.buf[i]);
		}
		fprintf(f, "\n 0 /* end */,\n");
		fprintf(f, "\n\t\t},\n");
	}

	if (eager_output_buf.used > 0) {
		fprintf(f, "\t\teager_output_table = {");
		for (size_t i = 0; i < eager_output_buf.used; i++) {
			if ((i & 31) == 0) { fprintf(f, "\n"); }
			fprintf(f, " %lu,", eager_output_buf.buf[i]);
		}
		fprintf(f, "\n 0 /* end */,\n");
		fprintf(f, "\n\t\t},\n");
	}

	fprintf(f, "\t};\n");

	free(edges.buf);
	free(endid_buf.buf);
	free(eager_output_buf.buf);

	return true;

not_implemented:
	assert(!"not implemented");
	return false;

alloc_fail:
	assert(!"alloc fail");
	return false;
}

static bool
generate_interpreter(FILE *f, const struct cdata_config *config, const char *prefix)
{
	(void)config;
	fprintf(f, "\tconst size_t %s_STATE_COUNT = %zd;\n", prefix, config->state_count);
	fprintf(f, "\tconst size_t %s_EDGE_COUNT = %zd;\n", prefix, config->non_default_edge_count);

	if (config->endid_count > 0) {
		fprintf(f, "\tconst size_t %s_ENDID_TABLE_COUNT = %zd;\n", prefix, config->endid_count);
	}

	if (config->eager_output_count > 0) {
		fprintf(f, "\tconst size_t %s_EAGER_OUTPUT_TABLE_COUNT = %zd;\n", prefix, config->eager_output_count);
	}

	fprintf(f, "\tuint32_t cur_state = %s_dfa_data.start;\n", prefix);

	/* Loop over the input characters.
	 * FIXME: io mode */
	fprintf(f,
	    "\tconst char *pos = input;\n"
	    "\twhile (*pos != 0) {\n"
	    "\t\tconst uint8_t c = *pos;\n"
	    "\t\tpos++;\n");

	fprintf(f,
	    "\t\tconst struct %s_cdata_state *s = &%s_dfa_data.states[cur_state];\n", prefix, prefix);

	/* If any states have eager outputs, check if the current state
	 * does, and if so, emit them somehow. */
	if (config->eager_output_count > 0) {
		assert(!"todo");
	}

	/* Function to count the bits set in a uint64_t. */
	const char *popcount = "__builtin_popcountl";

	/* For each character of the input, check if it's in the set of
	 * outgoing labels. If so, find the label group that contains
	 * that label by counting the bits preceding that offset in
	 * label_group_starts[]. Each label group is represented by its
	 * starting character. Call that the Nth label group. Next,
	 * find the Nth state ID in the edge table, starting from the
	 * state's base offset in that table.
	 *
	 * The bit counts for each word of label_group_starts[] are
	 * cached in s->rank_sums, so it only needs to count the bits
	 * within s->label_group_starts[c/64] before the character mod
	 * 64.
	 *
	 * If the character isn't in the label set, then go to the
	 * default destination state. If default_dst is set to an
	 * out-of-bounds value it means there isn't one, so there's no
	 * match. */
	fprintf(f,
	    "\t\tconst size_t w_i = c/64;\n"
	    "\t\tconst size_t word_rem = c & 63;\n"
	    "\t\tconst uint64_t bit = (uint64_t)1 << word_rem;\n"
	    "\t\tif (s->labels[w_i] & bit) { /* if state has label */\n"
	    "\t\t\tconst uint64_t mask = bit - 1;\n"
	    "\t\t\tconst uint64_t masked_word = s->label_group_starts[w_i] & mask;\n"
	    "\t\t\tconst size_t offset = %s(masked_word);\n"
	    "\t\t\tconst size_t rank = s->rank_sums[w_i] + offset;\n"
	    "\t\t\tconst uint32_t next_state = %s_dfa_data.dst_table[s->dst_table_offset + rank];\n"
	    "\t\t\tcur_state = next_state;\n"
	    "\t\t\tcontinue;\n"
	    "\t\t} else if (s->default_dst < %s_STATE_COUNT) {\n"
	    "\t\t\tcur_state = s->default_dst;\n"
	    "\t\t} else {\n"
	    "\t\t\treturn false; /* no match */\n"
	    "\t\t}\n"
	    "\t}\n",
	    popcount, prefix, prefix);

	/* At the end of the input, check if the current state is an end.
	 * If not, there's no match.  */
	fprintf(f,
	    "\tconst struct %s_cdata_state *s = &%s_dfa_data.states[cur_state];\n"
	    "\tif (!s->end) { return false; }\n", prefix, prefix);

	if (config->endid_count > 0) {
		/* If there are endids in the DFA, check if the current state's
		 * endid_offset is in range. (If not, the state has none.)
		 * Those endids appear in as a run of ascending values in
		 * the endid_table, starting from that offset, and are terminated
		 * by the first lower value. endid_table[] has an extra 0 appended
		 * as a terminator for the last set. */
		fprintf(f,
		    "\tif (s->endid_offset < %s_ENDID_TABLE_COUNT) {\n"
		    "\t\t%s *endid = &%s_dfa_data.endid_table[s->endid_offset];\n"
		    "\t\tuint64_t cur, next;\n"
		    "\t\tdo {\n"
		    "\t\t\tcur = *endid;\n"
		    "\t\t\tendid++;\n"
		    "\t\t\tnext = *endid;\n"
		    "\t\t} while (next > cur);\n"
		    "\t}\n",
		    prefix, id_type_str(config->t_endid_value), prefix);
	}

	/* We got a match. */
	fprintf(f, "\treturn true;\n");
	return true;
}

static bool
populate_config_from_ir(struct cdata_config *config, const struct ir *ir)
{
	memset(config, 0x00, sizeof(*config));
	config->start = ir->start;
	config->state_count = ir->n;

	size_t max_endid = 0;
	size_t max_eager_output_id = 0;

	for (size_t s_i = 0; s_i < ir->n; s_i++) {
		const struct ir_state *s = &ir->states[s_i];

		config->endid_count += s->endids.count;
		for (size_t i = 0; i < s->endids.count; i++) {
			if (s->endids.ids[i] > max_endid) {
				max_endid = s->endids.ids[i];
			}
		}

		const size_t eo_count = s->eager_outputs == NULL
		    ? 0
		    : s->eager_outputs->count;
		config->eager_output_count += eo_count;
		for (size_t i = 0; i < eo_count; i++) {
			if (s->eager_outputs->ids[i] > max_eager_output_id) {
				max_eager_output_id = s->eager_outputs->ids[i];
			}
		}

		switch (s->strategy) {
		case IR_NONE:
			/* fprintf(stderr, "-- none\n"); */
			config->non_default_edge_count += 0;
			break;
		case IR_SAME:	/* all default */
			/* fprintf(stderr, "-- same\n"); */
			config->non_default_edge_count += 0;
			break;
		case IR_COMPLETE:
			/* FIXME: smarter edge encoding */
			/* fprintf(stderr, "-- complete\n"); */
			config->non_default_edge_count += 256;
			break;
		case IR_PARTIAL:
		{
			/* fprintf(stderr, "-- partial\n"); */
			size_t state_total = 0;
			for (size_t g_i = 0; g_i < s->u.partial.n; g_i++) {
				const struct ir_group *g = &s->u.partial.groups[g_i];
				config->group_count++;
				config->range_count += g->n;
				for (size_t r_i = 0; r_i < g->n; r_i++) {
					const struct ir_range *r = &g->ranges[r_i];
					assert(r->end >= r->start);
					state_total += r->end - r->start + 1;
				}
			}
			assert(state_total <= 256);
			config->non_default_edge_count += state_total;
			break;
		}
		case IR_DOMINANT:
		{
			/* fprintf(stderr, "-- dominant\n"); */
			/* not counting the mode, which will become the default */
			size_t state_total = 0;
			for (size_t g_i = 0; g_i < s->u.dominant.n; g_i++) {
				const struct ir_group *g = &s->u.dominant.groups[g_i];
				config->group_count++;
				config->range_count += g->n;
				for (size_t r_i = 0; r_i < g->n; r_i++) {
					const struct ir_range *r = &g->ranges[r_i];
					assert(r->end >= r->start);
					state_total += r->end - r->start + 1;
				}
			}
			assert(state_total <= 256);
			config->non_default_edge_count += state_total;
			break;
		}
			break;
		case IR_ERROR:
			goto not_implemented;
		case IR_TABLE:
			goto not_implemented;
		default:
			goto not_implemented;
		}
	}

	config->t_state_id = size_needed(config->state_count);
	config->t_dst_state_offset = size_needed(config->non_default_edge_count);

	/* These two add the state count to handle the worst-case where every state
	 * after the first needs a 0 terminator. See the comment for endids_prev above. */
	config->t_endid_offset = size_needed(config->endid_count + config->state_count);
	config->t_eager_output_offset = size_needed(config->eager_output_count + config->state_count);

	config->t_endid_value = size_needed(max_endid);
	config->t_eager_output_value = size_needed(max_eager_output_id);

	/* TODO: numeric types for endid and eager_output values */
	return true;

not_implemented:
	assert(!"not implemented");
	return false;
}

int
fsm_print_cdata(FILE *f,
	const struct fsm_options *opt,
	const struct fsm_hooks *hooks,
	const struct ir *ir)
{
	assert(f != NULL);
	assert(opt != NULL);
	assert(hooks != NULL);
	assert(ir != NULL);

	(void)hooks;		/* ignored, for now */

	/* First pass, figure out totals and index sizes */
	struct cdata_config config;
	populate_config_from_ir(&config, ir);

	fprintf(stderr, "// config: state_count %zu, start %d, non_default_edge_count %zd, endid_count %zd, eager_output_count %zd, group_cound %zd, range_count %zd\n",
	    config.state_count,
	    config.start,
	    config.non_default_edge_count,
	    config.endid_count,
	    config.eager_output_count,
	    config.group_count, config.range_count);
	/* fprintf(stderr, "// sizes: state_id %u, edge_id %u, endid_id %u, eager_output_id %u (s%u_e%u_E%u_O%u)\n", */
	/*     config.size_state_id, config.size_edge_id, config.size_endid_id, config.size_eager_output_id, */
	/*     config.size_state_id, config.size_edge_id, config.size_endid_id, config.size_eager_output_id); */

	const char *prefix;
	if (opt->prefix != NULL) {
		prefix = opt->prefix;
	} else {
		prefix = "fsm_";
	}

	if (!opt->fragment) {
		/* generate function head */
		assert(!"todo: AMBIG mode, eager outputs");
#if 0
		fprintf(f, "|n");
		fprinft(f, "int\n%smain", prefix);

		switch (opt->io) {
		case FSM_IO_GETC:
			fprintf(f, "int (*fsm_getc)(void *getc_opaque), void *getc_opaque");
			break;

		case FSM_IO_STR:
			fprintf(f, "const char *s");
			break;

		case FSM_IO_PAIR:
			fprintf(f, "const char *b, const char *e");
			break;
		}
#endif
	} else {
		/* caller sets up the function head */
		if (!generate_struct_definition(f, &config, opt->comments, prefix)) { return -1; }
		if (!generate_data(f, &config, prefix, ir)) { return -1; }
		if (!generate_interpreter(f, &config, prefix)) { return -1; }
	}

#if 0
	if (opt->fragment) {
		/* generate struct definitions */
		/* generate size-specialized interpreter, inside guards */

		if (!print_cdata_body(f, ir, opt, hooks)) {
			return -1;
		}
	} else {
		assert(!"todo");
	}
#endif

	return 0;
}
