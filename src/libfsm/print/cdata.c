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

#include <adt/stateset.h>

#include "libfsm/internal.h"
#include "libfsm/print.h"

#include "ir.h"

/* Print mode that generates C data literals for the DFA, plus a small interepreter.
 * This mostly exists to sidestep very expensive compilation for large data sets
 * using the other C modes. When they generate long runs of nested switch/case
 * statements, gcc and clang spend lots of time and RAM on analyzing them, and it
 * can lead to builds taking several hours or even OOM-ing. -sv */

/* Whether to check the table buffers for previous instances of
 * the same sets of dst_states, endids, and eager_outputs. This
 * should always be an improvement, making the generated code
 * smaller and improve locality. */
#define REUSE_ALL_SETS 0

/* If reusing sets, use a simplistic and inefficient (but easily checked)
 * implementation. If EXPENSIVE_CHECKS is set this will still be used, to check
 * the result of the more efficient approaches. */
#define REUSE_NAIVE 1

/* Disabled for now. Linear scan for this is too slow, whereas
 * it's fine for the other two, and reuse makes a much bigger
 * difference for those. */
#define REUSE_DST_TABLE_SETS (REUSE_ALL_SETS || 0)

/* Disabled for now, this can lead to false positives due to
 * unterminated runs. Needs more testing. */
#define REUSE_ENDID_SETS (REUSE_ALL_SETS || 0)
#define REUSE_EAGER_OUTPUT_SETS (REUSE_ALL_SETS || 0)

/* Log size information to stderr. */
#define LOG_SIZES 0

/* Log stats for set reuse to stderr. */
#define LOG_REUSE 0

/* How large a numeric ID type do the particular tables need? */
enum id_type {
	U8,
	U16,
	U32,
	U64,
	UNSIGNED,		/* always use 'unsigned' */
};

static const char*
id_type_str(enum id_type t)
{
	switch (t) {
	case U8: return "uint8_t";
	case U16: return "uint16_t";
	case U32: return "uint32_t";
	case U64: return "uint64_t";
	case UNSIGNED: return "unsigned";
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

#define STATE_OFFSET_NONE ((size_t)-1)

/* Configuration. Figure out whether we really need a uint32_t for edge offsets
 * or can get by with a uint16_t, etc. and make the output more dense. */
struct cdata_config {
	const struct fsm_alloc *alloc;

	fsm_state_t start;
	size_t state_count;

	/* numeric type for state IDs, based on the higest state # */
	enum id_type t_state_id;

	/* numeric type for indexes into the dst_state table, based on
	 * the number of label groups */
	enum id_type t_dst_state_offset;

	/* numeric types for endid and eager_output table offsets */
	enum id_type t_endid_offset;
	enum id_type t_eager_output_offset;

	/* numeric types for endid and eager_output table values */
	enum id_type t_endid_value;
	enum id_type t_eager_output_value;
	enum id_type t_distinct_eager_output_offset;

	/* numeric type for entries in .bitset_words.pairs[] */
	enum id_type t_label_word_id;

	/* buffer for edge destination states */
	struct dst_buf {
		size_t ceil;
		size_t used;
		uint32_t *buf;
	} dst_buf;

	/* buffer for endids */
	struct endid_buf {
		size_t ceil;
		size_t used;
		unsigned *buf;
	} endid_buf;
	size_t max_endid;

	/* buffer for eager output IDs */
	struct eager_output_buf {
		size_t ceil;
		size_t used;
		uint64_t *buf;
	} eager_output_buf;
	size_t max_eager_output_id;

	/* Collection of distinct eager output IDs, in ascending order.
	 * This is used to map sequentially allocated internal IDs to the
	 * caller's eager output IDs, which are just arbitrary integers. */
	fsm_output_id_t *eager_output_ids;
	size_t distinct_eager_output_id_count;

	struct state_info {
		uint64_t labels[256/64];
		uint64_t label_group_starts[256/64];
		uint8_t rank_sums[4];

		/* Offsets into the other data tables, or STATE_OFFSET_NONE,
		 * which will be converted to the table length and treated
		 * as NONE by a runtime range check. */
		size_t default_dst;
		size_t dst;
		size_t endid;
		size_t eager_output;
	} *state_info;

	/* Collected 64-bit word counts for the .labels and
	 * .label_group_starts 256-bitsets. */
	struct bitset_words {
		size_t used;
		size_t ceil;
		struct bitset_word_pair {
			uint64_t word;
			size_t count;
		} *pairs;
	} bitset_words;

#if LOG_REUSE
	struct reuse_stats {
		size_t miss;
		size_t hit;
	} reuse_stats_dst;
	struct reuse_stats reuse_stats_endid;
	struct reuse_stats reuse_stats_eager_output;
#endif
};

static void
generate_struct_definition(FILE *f, const struct cdata_config *config, bool comments, const char *prefix)
{
	const bool has_endids = config->endid_buf.used > 0;
	const bool has_eager_outputs = config->eager_output_buf.used > 0;

	fprintf(f,
	    "\ttypedef %s %s_cdata_state;\n",
	    id_type_str(config->t_state_id), prefix);

	fprintf(f,
	    "\tstruct %s_cdata_dfa {\n"
	    "\t\t%s_cdata_state start;\n"
	    "\t\tstruct %s_cdata_state {\n"
	    "\n", prefix, prefix, prefix);

	if (comments) {
		fprintf(f,
		    "\t\t\t/* To find the destination state for label character C,\n"
		    "\t\t\t * check if the bit C is set in the word id'd by .labels[].\n"
		    "\t\t\t * If so, find the the 1 bit at or preceding C in\n"
		    "\t\t\t * .label_group_starts[], which represents the start of the Nth\n"
		    "\t\t\t * label group, the group label group that contains C. The dst state will\n"
		    "\t\t\t * be in .dst_table[.dst_table_offset + N]. This offset N is called\n"
		    "\t\t\t * the rank, and .rank_sums has precomputed sums for each\n"
		    "\t\t\t * word preceding .label_group_starts[C/64]. If .labels[]\n"
		    "\t\t\t * isn't set for C, the destination is .default_dst, or the\n"
		    "\t\t\t * state count (%zu) for no match. */\n"
		    "\n", config->state_count);
	}
	fprintf(f,
	    "\t\t\t%s_cdata_state default_dst; /* or %zu for NONE */\n"
	    "\t\t\t%s label_word_ids[4]; /* which labels have non-default edges */\n"
	    "\t\t\t%s label_group_start_word_ids[4]; /* start of each label group */\n"
	    "\t\t\tuint8_t rank_sums[4]; /* rank at end of label_group_starts[n] */\n"
	    "\n",
	    prefix, config->state_count,
	    id_type_str(config->t_label_word_id),
	    id_type_str(config->t_label_word_id));

	if (comments) {
		fprintf(f, "\t\t\t/* Offsets into values in other tables */\n");
	}
	fprintf(f, "\t\t\t%s dst_table_offset;\n", id_type_str(config->t_dst_state_offset));

	if (has_eager_outputs) {
		fprintf(f, "\t\t\t%s eager_output_offset;\n", id_type_str(config->t_eager_output_offset));
	}

	fprintf(f,
	    "\t\t} states[%zd];\n"
	    "\n", config->state_count);

	/* .end could be a single uint64_t bitset */
	if (comments) {
		fprintf(f, "\t\t/* State-associated info only checked at end of input */\n");
	}
	fprintf(f,
	    "\t\tstruct %s_state_end_info {\n"
	    "\t\t\tbool end; /* is this an end state? */\n", prefix);
	if (has_endids) {
		fprintf(f, "\t\t\t%s endid_offset; /* or %zu for NONE */\n",
		    id_type_str(config->t_endid_offset), config->endid_buf.used);
	}
	fprintf(f,
	    "\t\t} state_end_info[%zd];\n"
	    "\n", config->state_count);

	if (comments) {
		fprintf(f,
		    "\t\t/* Table of individual words used in label and label_group_start\n"
		    "\t\t *  bitsets, in descending order by frequency. */\n");
	}
	fprintf(f,
	    "\t\tuint64_t label_word_table[%zd];\n", config->bitset_words.used);

	if (comments) {
		fprintf(f,
		    "\t\t/* Destination states for each edge group in each state,\n"
		    "\t\t * starting from .states[state_id].dst_state_offset. */\n");
	}
	fprintf(f,
	    "\t\t%s_cdata_state dst_table[%zd];\n",
	    prefix, config->dst_buf.used == 0 ? 1 : config->dst_buf.used);

	if (has_endids) {
		if (comments) {
			fprintf(f,
			    "\n"
			    "\t\t/* Ascending runs of endids, refered to\n"
			    "\t\t * by .states[state_id].endid_offset,\n"
			    "\t\t * terminated by non-increasing value. */\n");
		}
		fprintf(f, "\t\t%s endid_table[%zd + 1];\n",
		    id_type_str(config->t_endid_value), config->endid_buf.used);
	}

	if (has_eager_outputs) {
		if (comments) {
			fprintf(f,
			    "\n"
			    "\t\t/* Ascending runs of eager_outputs, refered to\n"
			    "\t\t * by .states[state_id].eager_output_offset,\n"
			    "\t\t * terminated by non-increasing value. */\n");
		}
		fprintf(f, "\t\t%s eager_output_table[%zd + 1];\n",
		    id_type_str(config->t_distinct_eager_output_offset), config->eager_output_buf.used);

		if (comments) {
			fprintf(f,
			    "\n"
			    "\t\t/* All distinct eager_output ID that appear in the DFA,\n"
			    "\t\t * in ascending order. Used to convert the dense bitset for\n"
			    "\t\t * eager_outputs reached one or more times with their values. */\n");
		}
		fprintf(f, "\t\t%s eager_output_ids[%zd + 1];\n",
		    id_type_str(config->t_eager_output_value),
		    config->distinct_eager_output_id_count);
	}

	fprintf(f,
	    "\t};\n");
}

static void
lookup_label_ids(const struct cdata_config *config, const uint64_t *labels, unsigned ids[4]) {
	for (size_t w_i = 0; w_i < 4; w_i++) {
		bool found = false;
		const uint64_t w = labels[w_i];
		for (size_t i = 0; i < config->bitset_words.used; i++) {
			if (config->bitset_words.pairs[i].word == w) {
				ids[w_i] = i;
				found = true;
				break;
			}
		}
		assert(found);
	}
}

static int
cmp_eager_output_id(const void *pa, const void *pb)
{
	const fsm_output_id_t a = *(const fsm_output_id_t *)pa;
	const fsm_output_id_t b = *(const fsm_output_id_t *)pb;
	return a < b ? -1 : a > b ? 1 : 0;
}

static bool
collect_distinct_eager_output_ids(struct cdata_config *config,
    const struct ir *ir)
{
	bool res = false;
	fsm_output_id_t *id_array = NULL;

	/* state set, used as an fsm_output_id_t set. Both are unsigned int. */
	struct state_set *ids = NULL;

	if (config->eager_output_buf.used > 0) {
		/* Add value of 0 at offset 0, because it's used as a list terminator. */
		if (!state_set_add(&ids, config->alloc, 0)) {
			goto cleanup;
		}
	}

	for (size_t s_i = 0; s_i < ir->n; s_i++) {
		const struct ir_state *s = &ir->states[s_i];
		struct ir_state_eager_output *eos = s->eager_outputs;
		if (eos == NULL) { continue; }

		for (size_t id_i = 0; id_i < eos->count; id_i++) {
			const fsm_output_id_t id = eos->ids[id_i];
			/* fprintf(stderr, "%s: state %zu, id %u\n", __func__, s_i, id); */
			if (!state_set_add(&ids, config->alloc, (fsm_state_t)id)) {
				goto cleanup;
			}
		}
	}

	config->distinct_eager_output_id_count = 0;
	config->eager_output_ids = NULL;

	const size_t distinct_eager_output_ids = state_set_count(ids);
	if (distinct_eager_output_ids == 0) {
		state_set_free(ids);
		return true;	/* nothing to do */
	}

	id_array = f_malloc(config->alloc, distinct_eager_output_ids * sizeof(id_array[0]));
	if (id_array == NULL) { goto cleanup; }

	struct state_iter iter;
	state_set_reset(ids, &iter);
	fsm_state_t s_id;
	while (state_set_next(&iter, &s_id)) {
		id_array[config->distinct_eager_output_id_count++] = (fsm_output_id_t)s_id;
	}
	assert(config->distinct_eager_output_id_count == distinct_eager_output_ids);
	qsort(id_array, distinct_eager_output_ids, sizeof(id_array[0]), cmp_eager_output_id);

	config->eager_output_ids = id_array;
	/* fprintf(stderr, "/// distinct eager outputs:\n");
	 * for (size_t i = 0; i < config->distinct_eager_output_id_count; i++) {
	 * 	fprintf(stderr, "-- %zu: %zu\n", i, (size_t)id_array[i]);
	 * } */

	state_set_free(ids);
	return true;

cleanup:
	f_free(config->alloc, id_array);
	state_set_free(ids);
	return res;
}

static void
generate_distinct_eager_output_id_table(FILE *f, const struct cdata_config *config)
{
	assert(config->distinct_eager_output_id_count > 0);

	fprintf(f, "\t\t.eager_output_ids = {\n\t\t\t");
	for (size_t i = 0; i < config->distinct_eager_output_id_count; i++) {
		fprintf(f, " %u,", config->eager_output_ids[i]);
		if ((i & 15) == 15) { fprintf(f, "\n\t\t\t"); }
	}
	fprintf(f, "\n\t\t},\n");
}

static void
generate_data(FILE *f, const struct cdata_config *config,
	bool comments, const char *prefix, const struct ir *ir)
{
	fprintf(f,
	    "\tstatic struct %s_cdata_dfa %s_dfa_data = {\n"
	    "\t\t.start = %u,\n"
	    "\t\t.states = {\n", prefix, prefix, config->start);

	for (size_t s_i = 0; s_i < ir->n; s_i++) {
		const struct ir_state *s = &ir->states[s_i];
		const struct state_info *si = &config->state_info[s_i];

		const bool has_eager_outputs = si->eager_output != STATE_OFFSET_NONE;

		fprintf(f, "\t\t\t[%zd] = {%s\n", s_i, s_i == config->start ? " /* start */" : "");

		if (comments) {
			fprintf(f, "\t\t\t\t// ");
			for (size_t i = 0; i < 256; i++) {
				if (si->labels[i/64] & ((uint64_t)1 << (i & 63))) {
					char c = (char)i;
					if (c == '\\') { c = '.'; }
					fprintf(f, "%c", isprint(c) ? c : '.');
				}
			}
			fprintf(f, "\n");
		}
		unsigned label_ids[4];
		lookup_label_ids(config, si->labels, label_ids);
		fprintf(f, "\t\t\t\t.label_word_ids = { %u, %u, %u, %u },\n",
		    label_ids[0], label_ids[1], label_ids[2], label_ids[3]);

		size_t dst_count = 0;
		if (comments) {
			fprintf(f, "\t\t\t\t// ");
			for (size_t i = 0; i < 256; i++) {
				if (si->label_group_starts[i/64] & ((uint64_t)1 << (i & 63))) {
					char c = (char)i;
					if (c == '\\') { c = '.'; }
					fprintf(f, "%c", isprint(c) ? c : '.');
					dst_count++;
				}
			}
			fprintf(f, "\n");
		}
		lookup_label_ids(config, si->label_group_starts, label_ids);
		fprintf(f, "\t\t\t\t.label_group_start_word_ids = { %u, %u, %u, %u },\n",
		    label_ids[0], label_ids[1], label_ids[2], label_ids[3]);

		/* rank_sums[0] is always 0, but allows us to avoid a subtraction in the inner loop,
		 * and the space would be wasted otherwise anyway due to alignment. */
		fprintf(f, "\t\t\t\t.rank_sums = { %u, %u, %u, %u },\n",
		    si->rank_sums[0], si->rank_sums[1], si->rank_sums[2], si->rank_sums[3]);

		const size_t state_NONE = config->state_count;
		const size_t dst_table_NONE = config->dst_buf.used;
		const size_t eager_output_NONE = config->eager_output_buf.used;

		if (si->default_dst == STATE_OFFSET_NONE) {
			fprintf(f, "\t\t\t\t.default_dst = %zu, /* NONE */\n", state_NONE);
		} else {
			if (comments) {
				fprintf(f, "\t\t\t\t//");
				for (size_t i = 0; i < dst_count; i++) {
					fprintf(f, " %u,", config->dst_buf.buf[si->dst + i]);
				}
				fprintf(f, "\n");
			}
			fprintf(f, "\t\t\t\t.default_dst = %zu,\n", si->default_dst);
		}

		if (si->dst == STATE_OFFSET_NONE) { /* no non-default outgoing edges */
			fprintf(f, "\t\t\t\t.dst_table_offset = %zd, /* NONE */\n", dst_table_NONE);
		} else {
			fprintf(f, "\t\t\t\t.dst_table_offset = %zd,\n", si->dst);
		}

		if (config->eager_output_buf.used > 0) {
			if (has_eager_outputs) {
				if (comments) {
					fprintf(f, "\t\t\t\t/* eager_outputs:");
					for (size_t i = 0; i < s->eager_outputs->count; i++) {
						if (i > 0 && (i & 15) == 0) {
							fprintf(f, "\n\t\t\t\t *");
						}
						fprintf(f, " %u", s->eager_outputs->ids[i]);
					}
					fprintf(f, " */\n");
				}
				fprintf(f, "\t\t\t\t.eager_output_offset = %zd,\n", si->eager_output);
			} else {
				fprintf(f, "\t\t\t\t.eager_output_offset = %zd, /* NONE */\n", eager_output_NONE);
			}
		}

		fprintf(f, "\t\t\t},\n");
	}
	fprintf(f, "\t\t},\n");

	fprintf(f, "\t\t.state_end_info = {\n");
	for (size_t s_i = 0; s_i < ir->n; s_i++) {
		const size_t endid_NONE = config->endid_buf.used;
		const struct ir_state *s = &ir->states[s_i];
		const struct state_info *si = &config->state_info[s_i];
		fprintf(f, "\t\t\t[%zu] = {\n", s_i);
		fprintf(f, "\t\t\t\t.end = %d,\n", s->isend);

		/* Only include these if any state uses endids/eager_outputs, and
		 * if this state doesn't then use the end of the array as NONE. */
		if (config->endid_buf.used > 0) {
			if (si->endid != STATE_OFFSET_NONE) {
				if (comments) {
					fprintf(f, "\t\t\t\t/* endids:");
					for (size_t i = 0; i < s->endids.count; i++) {
						if (i > 0 && (i & 15) == 0) {
							fprintf(f, "\n\t\t\t\t *");
						}
						fprintf(f, " %u", s->endids.ids[i]);
					}
					fprintf(f, " */\n");
				}
				fprintf(f, "\t\t\t\t.endid_offset = %zd,\n", si->endid);
			} else {
				fprintf(f, "\t\t\t\t.endid_offset = %zd, /* NONE */\n", endid_NONE);
			}
		}
		fprintf(f, "\t\t\t},\n");
	}
	fprintf(f, "\t\t},\n");

	fprintf(f,
	    "\t\t.label_word_table = {\n\t\t\t");
	for (size_t i = 0; i < config->bitset_words.used; i++) {
		fprintf(f, " 0x%016lx,", config->bitset_words.pairs[i].word);
		if ((i & 3) == 3) {
			fprintf(f, "\n\t\t\t");
		}
	}
	if ((config->bitset_words.used & 3) != 3) {
		fprintf(f, "\n");
	}

	fprintf(f, "\t\t},\n");

	fprintf(f,
	    "\t\t.dst_table = {");

	for (size_t i = 0; i < config->dst_buf.used; i++) {
		if ((i & 15) == 0) { fprintf(f, "\n\t\t\t"); }
		fprintf(f, " %u,", config->dst_buf.buf[i]);
	}
	if (config->dst_buf.used == 0) {
		/* Avoid "error: use of GNU empty initializer extension". */
		fprintf(f, " 0, /* empty */");
	}

	/* edges */
	fprintf(f, "\n\t\t},\n");

	if (config->endid_buf.used > 0) {
		fprintf(f, "\t\t.endid_table = {");
		for (size_t i = 0; i < config->endid_buf.used; i++) {
			if ((i & 15) == 0) { fprintf(f, "\n\t\t\t"); }
			fprintf(f, " %u,", config->endid_buf.buf[i]);
		}
		fprintf(f, "\n\t\t\t 0 /* end */,\n");
		fprintf(f, "\n\t\t},\n");
	}

	if (config->eager_output_buf.used > 0) {
		fprintf(f, "\t\t.eager_output_table = {");

		for (size_t i = 0; i < config->eager_output_buf.used; i++) {
			if ((i & 15) == 0) { fprintf(f, "\n\t\t\t"); }
			/* TODO This uses linear search and does redundant lookups, but
			 * the distinct eager_output IDs should be fairly small.
			 * This could be replaced with an id->offset map later.
			 *
			 * Note: Non-ascending values are used as a list terminator in
			 * both the original and remapped sets -- because 0 was added
			 * at the start of collect_distinct_eager_output_ids, it will
			 * stay as 0, and since the list of distinct IDs is sorted the
			 * mapping will preserve the relative order -- non-ascending
			 * values terminating runs of IDs will still be non-ascending. */
			fsm_output_id_t id = config->eager_output_buf.buf[i];
			unsigned id_offset = (unsigned)-1;
			for (unsigned i = 0; i < config->distinct_eager_output_id_count; i++) {
				if (config->eager_output_ids[i] == id) {
					id_offset = i;
					break;
				}
			}
			assert(id_offset != (unsigned)-1); /* found */
			fprintf(f, " %u,", id_offset);
		}
		fprintf(f, "\n\t\t\t 0 /* end */,\n");
		fprintf(f, "\n\t\t},\n");

		/* Emit a sorted table of all the distinct eager output
		 * values. This, along with a bitset stack-allocated by
		 * the interpreter, will be used to keep track of which
		 * eager outputs should be set if the DFA as a whole matches. */
		generate_distinct_eager_output_id_table(f, config);
	}

	fprintf(f, "\t};\n");
}

static void
generate_eager_output_check(FILE *f, const struct cdata_config *config, const char *prefix)
{
	/* If any states have eager outputs, check if the current state
	 * does, and if so, set their flags. This assumes eager_output_buf is large enough,
	 * and is a strong incentive to use sequentially assigned IDs. */
	if (config->eager_output_buf.used > 0) {
		fprintf(f,
		    "\n"
		    "\t\tif (state->eager_output_offset < %s_EAGER_OUTPUT_TABLE_COUNT) {\n"
		    "\t\t\tif (debug_traces) {\n"
		    "\t\t\t\tfprintf(stderr, \"-- eager_output_offset %%u\\n\", state->eager_output_offset);\n"
		    "\t\t\t}\n"
		    "\t\t\t%s *eo_scan = &%s_dfa_data.eager_output_table[state->eager_output_offset];\n"
		    "\t\t\t%s cur, next;\n"
		    "\t\t\tdo {\n"
		    "\t\t\t\tcur = *eo_scan;\n"
		    "\t\t\t\tif (debug_traces) {\n"
		    "\t\t\t\t\tfprintf(stderr, \"%%s: setting eager_output flag %%u\\n\", __func__, cur);\n"
		    "\t\t\t\t}\n"
		    "\t\t\t\tuncommitted_eager_output_buf[cur/64] |= (uint64_t)1 << (cur & 63);\n"
		    "\t\t\t\teo_scan++;\n"
		    "\t\t\t\tnext = *eo_scan;\n"
		    "\t\t\t} while (next > cur);\n"
		    "\t\t}\n",
		    prefix,
		    id_type_str(config->t_distinct_eager_output_offset),
		    prefix,
		    id_type_str(config->t_distinct_eager_output_offset));
	}
}

static void
generate_interpreter(FILE *f, const struct cdata_config *config, const struct fsm_options *opt, const char *prefix)
{
	const bool has_endids = config->endid_buf.used > 0;
	const bool has_eager_outputs = config->eager_output_buf.used > 0;

	fprintf(f, "\tconst size_t %s_STATE_COUNT = %zd;\n", prefix, config->state_count);

	if (has_endids) {
		fprintf(f, "\tconst size_t %s_ENDID_TABLE_COUNT = %zd;\n", prefix, config->endid_buf.used);
	}

	if (has_eager_outputs) {
		fprintf(f, "\tconst size_t %s_EAGER_OUTPUT_TABLE_COUNT = %zd;\n", prefix, config->eager_output_buf.used);
	}

	/* start state */
	fprintf(f, "\tuint32_t cur_state = %s_dfa_data.start;\n", prefix);
	fprintf(f, "\n");

	/* Stack-allocated bitset buffer for uncommitted eager_outputs: if the Nth bit in this
	 * buffer is set, then after a successful DFA match the ID in dfa.eager_output_ids[N]
	 * should be reported as matching. The bitset is used to collect redundant eager_outputs,
	 * and to avoid reporting them to the caller until the overall DFA match result is known. */
	if (config->distinct_eager_output_id_count > 0) {
		const size_t eager_output_words = config->distinct_eager_output_id_count/64 + 1;
		fprintf(f, "\tuint64_t uncommitted_eager_output_buf[%zu] = {0};\n", eager_output_words);
	}

	/* Setting this to true will log out execution steps. */
	const bool debug_traces = false;
	fprintf(f,
	    "\tconst bool debug_traces = %s;\n", debug_traces ? "true" : "false");

	/* Loop over the input characters */
	switch (opt->io) {
		case FSM_IO_GETC:
			fprintf(f, "\tint raw_c;\n");
			fprintf(f, "\twhile (raw_c = fsm_getc(getc_opaque), raw_c != EOF) {\n");
			fprintf(f, "\t\tconst uint8_t c = (uint8_t)raw_c;\n");
			break;

		case FSM_IO_STR:
			fprintf(f, "\tconst char *p;\n");
			fprintf(f, "\tfor (p = s; *p != '\\0'; p++) {\n");
			fprintf(f, "\t\tconst uint8_t c = (uint8_t)*p;\n");
			break;

		case FSM_IO_PAIR:
			fprintf(f, "\tconst char *p;\n");
			fprintf(f, "\tfor (p = b; p != e; p++) {\n");
			fprintf(f, "\t\tconst uint8_t c = (uint8_t)*p;\n");
			break;
	}

	fprintf(f,
	    "\t\tconst struct %s_cdata_state *state = &%s_dfa_data.states[cur_state];\n", prefix, prefix);

	/* If the state being entered has eager_outputs, set their flags. */
	generate_eager_output_check(f, config, prefix);

	/* Function to count the bits set in a uint64_t.
	 *
	 * TODO It may be faster to use a small lookup table and add
	 * the next N least significant bits, halting on 0:
	 *
	 *     size_t sum = 0;
	 *     while (word != 0) {
	 *         sum += lookup_table_8_bit_popcount[word & 0xff];
	 *         word >>= 8;
	 *     }
	 *
	 * because usually many of the upper bits will be masked out. */
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
	 * cached in state->rank_sums, so it only needs to count the bits
	 * within state->label_group_starts[c/64] before the character mod
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
	    "\t\tconst %s label_word_id = state->label_word_ids[w_i];\n"
	    "\t\tconst uint64_t label_word = %s_dfa_data.label_word_table[label_word_id];\n"
	    "\t\tif (label_word & bit) { /* if state has label */\n"
	    "\t\t\tif (debug_traces) {\n"
	    "\t\t\t\tfprintf(stderr, \"-- label '%%c' (0x%%02x) -> w_i %%zd, bit 0x%%016lx\\n\", isprint(c) ? c : 'c', c, w_i, bit);\n"
	    "\t\t\t}\n"
	    "\t\t\tconst uint64_t lgs_word_id = state->label_group_start_word_ids[w_i];\n"
	    "\t\t\tconst uint64_t lgs_word = %s_dfa_data.label_word_table[lgs_word_id];\n"
	    "\t\t\tconst size_t back = (lgs_word & bit) ? 0 : 1; /* back to start of label group */\n"
	    "\t\t\tconst uint64_t mask = bit - 1;\n"
	    "\t\t\tconst uint64_t masked_word = lgs_word & mask;\n"
	    "\t\t\tconst size_t bit_rank_in_masked_word = %s(masked_word) - back;\n"
	    "\t\t\tconst size_t rank = state->rank_sums[w_i] + bit_rank_in_masked_word;\n"
	    "\t\t\tconst size_t dst_offset = state->dst_table_offset + rank;\n"
	    "\t\t\tcur_state = %s_dfa_data.dst_table[dst_offset];\n"
	    "\t\t\tif (debug_traces) {\n"
	    "\t\t\t\tfprintf(stderr, \"-- has label, rank %%zd -> dst_offset %%zu -> next_state %%u\\n\",\n"
	    "\t\t\t\t\trank, dst_offset, cur_state);\n"
	    "\t\t\t}\n"
	    "\t\t\tcontinue;\n"
	    "\t\t} else if (state->default_dst < %s_STATE_COUNT) {\n"
	    "\t\t\tcur_state = state->default_dst;\n"
	    "\t\t\tif (debug_traces) {\n"
	    "\t\t\t\tfprintf(stderr, \"-- doesn't have label -> default state %%u\\n\", state->default_dst);\n"
	    "\t\t\t}\n"
	    "\t\t} else {\n"
	    "\t\t\tif (debug_traces) {\n"
	    "\t\t\t\tfprintf(stderr, \"-- doesn't have label -> match fail\\n\");\n"
	    "\t\t\t}\n"
	    "\t\t\treturn 0; /* no match */\n"
	    "\t\t}\n"
	    "\t}\n",
	    id_type_str(config->t_label_word_id),
	    prefix, prefix, popcount, prefix, prefix);

	/* At the end of the input, check if the current state is an end.
	 * If not, there's no match.  */
	fprintf(f,
	    "\tconst struct %s_state_end_info *state_end = &%s_dfa_data.state_end_info[cur_state];\n"
	    "\tif (!state_end->end) { return 0; /* no match */ }\n", prefix, prefix);

	/* Set the passed-in reference to the endids, if any. */
	if (has_endids) {
		/* If there are endids in the DFA, check if the current state's
		 * endid_offset is in range. (If not, the state has none.)
		 * Those endids appear in as a run of ascending values in
		 * the endid_table, starting from that offset, and are terminated
		 * by the first lower value. endid_table[] has an extra 0 appended
		 * as a terminator for the last set. */
		fprintf(f,
		    "\tif (state_end->endid_offset < %s_ENDID_TABLE_COUNT) {\n"
		    "\t\t%s *endid_scan = &%s_dfa_data.endid_table[state_end->endid_offset];\n"
		    "\t\tconst %s *endid_base = endid_scan;\n"
		    "\t\tsize_t endid_count = 0;\n"
		    "\t\tuint64_t cur, next;\n"
		    "\t\tdo {\n"
		    "\t\t\tcur = *endid_scan;\n"
		    "\t\t\tendid_scan++;\n"
		    "\t\t\tendid_count++;\n"
		    "\t\t\tnext = *endid_scan;\n"
		    "\t\t} while (next > cur);\n",
		    prefix,
		    id_type_str(config->t_endid_value),
		    prefix,
		    id_type_str(config->t_endid_value));

		switch (opt->ambig) {
		case AMBIG_NONE:
			fprintf(f,
			    "\t\t(void)endid_base;\n");
			break;

		case AMBIG_ERROR:
		case AMBIG_EARLIEST:
			fprintf(f,
			    "\t\t*id = *endid_base;\n"
			    "\t\t(void)endid_count;\n");
			break;

		case AMBIG_MULTIPLE:
			fprintf(f,
			    "\t\t*%s = endid_base;\n"
			    "\t\t*%s = endid_count;\n",
			    /* TODO: rename these to endid_ids and endid_count?
			     * That will be an interface change. */
			    "ids", "count");
			break;

		default:
			assert(!"unreached");
			abort();
		}

		fprintf(f,
		    "\t}\n");
	}

	/* If the end state has eager_outputs, set their flags. */
	if (has_eager_outputs) {
		fprintf(f, "\t{\n");	/* add {} nesting so the tabs match */
		fprintf(f, "\t\tconst struct %s_cdata_state *state = &%s_dfa_data.states[cur_state];\n",
		    prefix, prefix);
		generate_eager_output_check(f, config, prefix);
		fprintf(f, "\t}\n");

		/* commit eager_output matches to the caller's buffer */
		const size_t eager_output_words = config->distinct_eager_output_id_count/64 + 1;
		fprintf(f, "\tfor (size_t w_i = 0; w_i < %zu; w_i++) {\n", eager_output_words);
		fprintf(f, "\t\tconst uint64_t w = uncommitted_eager_output_buf[w_i];\n");
		fprintf(f, "\t\tif (w == 0) { continue; }\n");
		fprintf(f, "\t\tfor (size_t bit = 0; bit < 64; bit++) {\n");
		fprintf(f, "\t\t\tif (w & ((uint64_t)1 << bit)) {\n");
		fprintf(f, "\t\t\t\tconst uint64_t id = %s_dfa_data.eager_output_ids[64*w_i + bit];\n", prefix);
		fprintf(f, "\t\t\t\teager_output_buf[id/64] |= ((uint64_t)1 << (id & 63));\n");
		fprintf(f, "\t\t\t}\n");
		fprintf(f, "\t\t}\n");
		fprintf(f, "\t}\n");
	}

	/* Got a match. */
	fprintf(f, "\treturn 1; /* match */\n");
}

static bool
append_endid(const struct fsm_alloc *alloc, struct endid_buf *buf, uint64_t id)
{
	if (buf->used == buf->ceil) {
		const size_t nceil = buf->ceil == 0 ? 8 : 2*buf->ceil;
		unsigned *nbuf = f_realloc(alloc, buf->buf, nceil * sizeof(nbuf[0]));
		if (nbuf == NULL) {
			return false;
		}
		buf->buf = nbuf;
		buf->ceil = nceil;
	}

	assert(buf->used < buf->ceil);
	buf->buf[buf->used++] = id;
	return true;
}

static bool
save_state_endids(struct cdata_config *config, const struct ir_state_endids *endids, size_t *offset)
{
	if (endids->count == 0) {
		assert(*offset == STATE_OFFSET_NONE);
		return true;
	}

	/* These must be in ascending order. */
	for (size_t i = 1; i < endids->count; i++) {
		assert(endids->ids[i - 1] < endids->ids[i]);
	}

#if REUSE_ENDID_SETS
	/* Intern the run of endids. They are often identical
	 * between states, so the earlier reference could be reused.
	 * This is particulary important since they're all stored as
	 * "unsigned" rather than reducing to the smallest numeric
	 * type that fits all values used. */

#if REUSE_NAIVE || EXPENSIVE_CHECKS
	/* Search for a previous run of the same endids in the buffer via linear scan.
	 * This is simple but scales poorly. */
	size_t naive_offset = STATE_OFFSET_NONE;
	for (size_t b_i = 0; b_i < config->endid_buf.used; b_i++) {
		size_t e_i;
		for (e_i = 0; e_i < endids->count; e_i++) {
			if (b_i + e_i >= config->endid_buf.used) {
				break; /* reached the end, not found */
			}
			if (config->endid_buf.buf[b_i + e_i] != endids->ids[e_i]) {
				break; /* mismatch */
			}
		}

		/* If there's a potential match, check that it is followed by
		 * a value <= the last, because otherwise it would falsely continue the run. */
		if (e_i == endids->count
		    && b_i + e_i + 1 < config->endid_buf.used
		    && config->endid_buf.buf[b_i + e_i + 1] <= endids->ids[e_i - 1]) {
			naive_offset = b_i;
			break;
		}
	}

	if (REUSE_NAIVE) {
		*offset = naive_offset;
	}
#endif	/* REUSE_NAIVE || EXPENSIVE_CHECKS */

	/* TODO: better impl? */

#if LOG_REUSE
	if (*offset == STATE_OFFSET_NONE) {
		config->reuse_stats_endid.miss++;
	} else {
		config->reuse_stats_endid.hit++;
	}
#endif

	if (*offset != STATE_OFFSET_NONE) {
		return true;
	}
#endif	/* REUSE_ENDID_SETS */

	/* If the first endid for this state is later than the last
	 * endid in the buffer, append an extra terminator 0 for the
	 * last run of endids. Otherwise, the last state with endids
	 * will be falsely associated with this state's as well. */
	if (config->endid_buf.used > 0
	    && endids->ids[0] > config->endid_buf.buf[config->endid_buf.used - 1]) {
		if (!append_endid(config->alloc, &config->endid_buf, 0)) {
			return false;
		}
	}

	const size_t base = config->endid_buf.used;

	for (size_t i = 0; i < endids->count; i++) {
		if (endids->ids[i] > config->max_endid) {
			config->max_endid = endids->ids[i];
		}
		if (!append_endid(config->alloc, &config->endid_buf, endids->ids[i])) {
			return false;
		}
	}

	assert(base != STATE_OFFSET_NONE);
	*offset = base;
	return true;
}

static bool
append_eager_output(const struct fsm_alloc *alloc, struct eager_output_buf *buf, uint64_t id)
{
	if (buf->used == buf->ceil) {
		const size_t nceil = buf->ceil == 0 ? 8 : 2*buf->ceil;
		uint64_t *nbuf = f_realloc(alloc, buf->buf, nceil * sizeof(nbuf[0]));
		if (nbuf == NULL) {
			return false;
		}
		buf->buf = nbuf;
		buf->ceil = nceil;
	}

	assert(buf->used < buf->ceil);
	buf->buf[buf->used++] = id;
	return true;
}

static bool
save_state_eager_outputs(struct cdata_config *config, const struct ir_state_eager_output *eager_outputs, size_t *offset)
{
	if (eager_outputs == NULL || eager_outputs->count == 0) {
		assert(*offset == STATE_OFFSET_NONE);
		return true;
	}

	/* These must be in ascending order. */
	for (size_t i = 1; i < eager_outputs->count; i++) {
		assert(eager_outputs->ids[i - 1] < eager_outputs->ids[i]);
	}

#if REUSE_EAGER_OUTPUT_SETS
#if REUSE_NAIVE || EXPENSIVE_CHECKS
	/* Linear scan. See comments about reuse in save_state_endids. */
	size_t naive_offset = STATE_OFFSET_NONE;
	for (size_t b_i = 0; b_i < config->eager_output_buf.used; b_i++) {
		size_t e_i;
		for (e_i = 0; e_i < eager_outputs->count; e_i++) {
			if (b_i + e_i >= config->eager_output_buf.used) {
				break; /* reached the end, not found */
			}
			if (config->eager_output_buf.buf[b_i + e_i] != eager_outputs->ids[e_i]) {
				break; /* mismatch */
			}
		}

		/* If there's a potential match, check that it isn't followed by
		 * a value > the last, because it would falsely continue the run. */
		if (e_i == eager_outputs->count
		    && b_i + e_i + 1 < config->eager_output_buf.used
		    && config->eager_output_buf.buf[b_i + e_i + 1] <= eager_outputs->ids[e_i - 1]) {
			naive_offset = b_i;
			break;
		}
	}

	if (REUSE_NAIVE) {
		*offset = naive_offset;
	}
#endif	/* REUSE_NAIVE || EXPENSIVE_CHECKS */

	/* TODO: better impl */

#if LOG_REUSE
	if (*offset == STATE_OFFSET_NONE) {
		config->reuse_stats_eager_output.miss++;
	} else {
		config->reuse_stats_eager_output.hit++;
	}
#endif

	if (*offset != STATE_OFFSET_NONE) {
		return true;
	}
#endif	/* REUSE_EAGER_OUTPUT_SETS */

	/* If necessary add a 0, as in save_state_endids above. */
	if (config->eager_output_buf.used > 0
	    && eager_outputs->ids[0] > config->eager_output_buf.buf[config->eager_output_buf.used - 1]) {
		if (!append_eager_output(config->alloc, &config->eager_output_buf, 0)) {
			return false;
		}
	}

	const size_t base = config->eager_output_buf.used;

	for (size_t i = 0; i < eager_outputs->count; i++) {
		if (eager_outputs->ids[i] > config->max_eager_output_id) {
			config->max_eager_output_id = eager_outputs->ids[i];
		}

		if (!append_eager_output(config->alloc, &config->eager_output_buf, eager_outputs->ids[i])) {
			return false;
		}
	}

	assert(base != STATE_OFFSET_NONE);
	*offset = base;
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
append_dst(const struct fsm_alloc *alloc, struct dst_buf *buf, uint32_t dst)
{
	if (buf->used == buf->ceil) {
		const size_t nceil = buf->ceil == 0 ? 8 : 2*buf->ceil;
		uint32_t *nbuf = f_realloc(alloc, buf->buf, nceil * sizeof(nbuf[0]));
		if (nbuf == NULL) {
			return false;
		}
		buf->buf = nbuf;
		buf->ceil = nceil;
	}

	assert(buf->used < buf->ceil);
	buf->buf[buf->used++] = dst;
	return true;
}

static int
cmp_bitset_word_pair(const void *pa, const void *pb)
{
	const struct bitset_word_pair *a = (const struct bitset_word_pair *)pa;
	const struct bitset_word_pair *b = (const struct bitset_word_pair *)pb;

	/* for sorting by descending count */
	return a->count < b->count ? 1 : a->count > b->count ? -1 : 0;
}

static bool
increment_bitset_word_count(const struct fsm_alloc *alloc, struct bitset_words *bws, uint64_t w)
{
	/* This table tends to stay fairly small, so linear search is probably good enough. */
	for (size_t i = 0; i < bws->used; i++) {
		if (bws->pairs[i].word == w) {
			bws->pairs[i].count++;
			return true;
		}
	}

	if (bws->used == bws->ceil) {
		const size_t nceil = (bws->ceil == 0 ? 8 : 2*bws->ceil);
		struct bitset_word_pair *npairs = f_realloc(alloc,
		    bws->pairs, nceil * sizeof(npairs[0]));
		if (npairs == NULL) {
			return false;
		}
		bws->ceil = nceil;
		bws->pairs = npairs;
	}

	struct bitset_word_pair *p = &bws->pairs[bws->used];
	p->word = w;
	p->count = 1;
	bws->used++;
	return true;
}

static bool
save_state_edge_group_destinations(struct cdata_config *config, struct state_info *si,
	size_t group_count, const struct ir_group *groups)
{
	/* Convert the group ranges to bitsets and an edge->destination state list. */
#define DUMP_GROUP 0
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

	for (size_t i = 0; i < 4; i++) {
		si->labels[i] = 0;
		si->label_group_starts[i] = 0;
	}

	/* First pass: populate the bitsets. */
	for (size_t o_i = 0; o_i < outgoing_used; o_i++) {
		const struct range_info *r = &outgoing[o_i];
		assert(!u64bitset_get(si->label_group_starts, r->start));
		u64bitset_set(si->label_group_starts, r->start);

		for (uint16_t c = r->start; c <= r->end; c++) {
			/* c is a uint16_t to avoid rollover for { .start=255,.end=255 }. */
			const uint8_t c8 = (uint8_t)c;
			assert(!u64bitset_get(si->labels, c8));
			u64bitset_set(si->labels, c8);
		}
	}

	struct bitset_words *bws = &config->bitset_words;
	for (size_t i = 0; i < 4; i++) {
		if (!increment_bitset_word_count(config->alloc, bws, si->labels[i])) {
			return false;
		}
		if (!increment_bitset_word_count(config->alloc, bws, si->label_group_starts[i])) {
			return false;
		}
	}

	/* Precompute label_group_starts[] rank sums so lookup only needs to
	 * compute rank for the label's word, not every word preceding it. */
	si->rank_sums[0] = 0;
	uint8_t total = 0;
	for (size_t i = 1; i < 4; i++) {
		total += u64bitset_popcount(si->label_group_starts[i - 1]);
		si->rank_sums[i] = total;
	}

	struct dst_buf *dst_buf = &config->dst_buf;

	/* Second pass: search for an previous intance of the same run
	 * of destination states in dst_buf, reusing that if possible. */
#if REUSE_DST_TABLE_SETS
#if REUSE_NAIVE || EXPENSIVE_CHECKS
	/* Linear scan. See comments about reuse in save_state_endids. */
	size_t naive_offset = STATE_OFFSET_NONE;
	for (size_t b_i = 0; b_i < dst_buf->used; b_i++) {
		size_t o_i;
		for (o_i = 0; o_i < outgoing_used; o_i++) {
			if (b_i + o_i >= dst_buf->used) {
				break; /* reached the end, not found */
			}
			if (dst_buf->buf[b_i + o_i] != outgoing[o_i].dst_state) {
				break; /* mismatch */
			}
		}
		if (o_i == outgoing_used) { /* got a match */
			naive_offset = b_i;
			break;
		}
	}

	if (REUSE_NAIVE) {
		si->dst = naive_offset;
	}
#endif	/* REUSE_NAIVE || EXPENSIVE_CHECKS */

	/* TODO: Better implementation. This should use the same
	 * backward chaining search index approach that heatshrink uses,
	 * and since the DFA is trimmed all states should have at least
	 * one edge leading to them: it doesn't need to be sparse.
	 * Making the dst_state table smaller will improve locality and
	 * make it faster. */

#if LOG_REUSE
	if (si->dst == STATE_OFFSET_NONE) {
		config->reuse_stats_dst.miss++;
	} else {
		config->reuse_stats_dst.hit++;
	}
#endif

	if (si->dst != STATE_OFFSET_NONE) {
		return true;
	}
#endif	/* REUSE_DST_TABLE_SETS */

	/* Otherwise, append the destination states to dst_buf. */
	const size_t base = dst_buf->used;
	for (size_t o_i = 0; o_i < outgoing_used; o_i++) {
		const struct range_info *r = &outgoing[o_i];
		if (!append_dst(config->alloc, dst_buf, r->dst_state)) {
			return false;
		}
	}

	assert(base != STATE_OFFSET_NONE);
	si->dst = base;
	return true;
}

static bool
populate_config_from_ir(struct cdata_config *config, const struct fsm_alloc *alloc, const struct ir *ir)
{
	memset(config, 0x00, sizeof(*config));
	config->alloc = alloc;
	config->start = ir->start;
	config->state_count = ir->n;

	config->state_info = f_calloc(config->alloc, ir->n, sizeof(config->state_info[0]));
	if (config->state_info == NULL) {
		goto alloc_fail;
	}

	/* could just memset this to 0xff, but this is explicit */
	for (size_t s_i = 0; s_i < ir->n; s_i++) {
		struct state_info *si = &config->state_info[s_i];
		si->dst = STATE_OFFSET_NONE;
		si->default_dst = STATE_OFFSET_NONE;
		si->endid = STATE_OFFSET_NONE;
		si->eager_output = STATE_OFFSET_NONE;
	}

	/* add a single entry for 0, in case the IR only has a single IR_NONE or IR_SAME state */
	config->bitset_words.ceil = 1;
	config->bitset_words.used = 1;
	config->bitset_words.pairs = f_calloc(config->alloc, 1, sizeof(config->bitset_words.pairs[0]));
	if (config->bitset_words.pairs == NULL) {
		goto alloc_fail;
	}
	config->bitset_words.pairs[0].word = 0x0;
	config->bitset_words.pairs[0].count = 1;

	for (size_t s_i = 0; s_i < ir->n; s_i++) {
		const struct ir_state *s = &ir->states[s_i];

		if (!save_state_endids(config, &s->endids, &config->state_info[s_i].endid)) {
			goto alloc_fail;
		}

		if (!save_state_eager_outputs(config, s->eager_outputs, &config->state_info[s_i].eager_output)) {
			goto alloc_fail;
		}

		struct state_info *si = &config->state_info[s_i];

		switch (s->strategy) {
		case IR_NONE:
			break;
		case IR_SAME:	/* all default */
			config->state_info[s_i].default_dst = s->u.same.to;
			break;
		case IR_COMPLETE:
			if (!save_state_edge_group_destinations(config,
				si, s->u.complete.n, s->u.complete.groups)) {
				goto alloc_fail;
			}
			break;
		case IR_PARTIAL:
			if (!save_state_edge_group_destinations(config,
				si, s->u.partial.n, s->u.partial.groups)) {
				goto alloc_fail;
			}
			break;
		case IR_DOMINANT:
			if (!save_state_edge_group_destinations(config,
				si, s->u.dominant.n, s->u.dominant.groups)) {
				goto alloc_fail;
			}
			config->state_info[s_i].default_dst = s->u.dominant.mode;
			break;
		case IR_ERROR:
			goto not_implemented;
		case IR_TABLE:
			goto not_implemented;
		default:
			goto not_implemented;
		}
	}

	if (!collect_distinct_eager_output_ids(config, ir)) {
		goto alloc_fail;
	}

	/* Get the smallest numeric type that will fit all state IDs in
	 * the current DFA, reserving one extra to use as an out-of-band
	 * "NONE" value for fields like default_dst. These also the values
	 * in the dst_state table (the destination state for every edge group),
	 * so storing them more densely has a big impact on the overall data size. */
	config->t_state_id = size_needed(config->state_count + 1);

	/* Offset into the dst_state table. */
	config->t_dst_state_offset = size_needed(config->dst_buf.used);

	/* Both of these also ensure there's space for at least one out-of-band value
	 * to use as "NONE". */
	config->t_endid_offset = size_needed(config->endid_buf.used + 1);
	config->t_eager_output_offset = size_needed(config->eager_output_buf.used + 1);

	/* The caller expects this to be unsigned, and the current interface just sets
	 * a pointer to the array of IDs. */
	config->t_endid_value = UNSIGNED; //size_needed(config->max_endid);

	/* Sort by use frequency, descending, so the most frequently used
	 * bitset words will stay in cache. */
	qsort(config->bitset_words.pairs, config->bitset_words.used,
	    sizeof(config->bitset_words.pairs[0]), cmp_bitset_word_pair);
	config->t_label_word_id = size_needed(config->bitset_words.used);

	config->t_eager_output_value = size_needed(config->max_eager_output_id);
	config->t_distinct_eager_output_offset = size_needed(config->distinct_eager_output_id_count);
	return true;

not_implemented:
	assert(!"not implemented");
	return false;

alloc_fail:
	return false;
}

int
fsm_print_cdata(FILE *f,
	const struct fsm_alloc *alloc,
	const struct fsm_options *opt,
	const struct fsm_hooks *hooks,
	const struct ir *ir)
{
	assert(f != NULL);
	assert(opt != NULL);
	assert(hooks != NULL);
	assert(ir != NULL);

	(void)alloc;
	(void)hooks;		/* ignored, for now */

	/* First pass, figure out totals and index sizes */
	struct cdata_config config;
	if (!populate_config_from_ir(&config, alloc, ir)) {
		return -1;
	}

#if LOG_SIZES
	fprintf(stderr, "// config: dst_state_count %zu, start %d, dst_buf.used %zd, endid_buf.used %zd, eager_output_buf.used %zd\n",
	    config.state_count,
	    config.start,
	    config.dst_buf.used,
	    config.endid_buf.used,
	    config.eager_output_buf.used);
#endif

#if LOG_REUSE
	fprintf(stderr, "// reuse: dst: hit %zu (%g%%), miss %zu\n",
	    config.reuse_stats_dst.hit, (100.0 * config.reuse_stats_dst.hit) / (config.reuse_stats_dst.hit + config.reuse_stats_dst.miss),
	    config.reuse_stats_dst.miss);
	if (config.reuse_stats_endid.hit + config.reuse_stats_endid.miss > 0) {
		fprintf(stderr, "// reuse: endids: hit %zu (%g%%), miss %zu\n",
		    config.reuse_stats_endid.hit, (100.0 * config.reuse_stats_endid.hit) / (config.reuse_stats_endid.hit + config.reuse_stats_endid.miss),
		    config.reuse_stats_endid.miss);
	}
	if (config.reuse_stats_eager_output.hit + config.reuse_stats_eager_output.miss > 0) {
		fprintf(stderr, "// reuse: eager_outputs: hit %zu (%g%%), miss %zu\n",
		    config.reuse_stats_eager_output.hit,
		    (100.0 * config.reuse_stats_eager_output.hit) / (config.reuse_stats_eager_output.hit + config.reuse_stats_eager_output.miss),
		    config.reuse_stats_eager_output.miss);
	}
#endif

	const char *prefix;
	if (opt->prefix != NULL) {
		prefix = opt->prefix;
	} else {
		prefix = "fsm_";
	}

	if (!opt->fragment) {	/* generate function head */
		fprintf(f, "\n");

		fprintf(f, "int\n%smain", prefix);
		fprintf(f, "(");

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

		/* TODO: add an opt flag for eager_output codegen */
		if (config.eager_output_buf.used > 0) {
			fprintf(f, ",\n");
			fprintf(f, "\tuint64_t *eager_output_buf");
		}

		/*
		 * unsigned rather than fsm_end_id_t here, so the generated code
		 * doesn't depend on fsm.h
		 */
		switch (opt->ambig) {
		case AMBIG_NONE:
			break;

		case AMBIG_ERROR:
		case AMBIG_EARLIEST:
			fprintf(f, ",\n");
			fprintf(f, "\tunsigned *id");
			break;

		case AMBIG_MULTIPLE:
			fprintf(f, ",\n");
			fprintf(f, "\tconst unsigned **ids, size_t *count");
			break;

		default:
			assert(!"unreached");
			abort();
		}

		if (hooks->args != NULL) {
			fprintf(f, ",\n");
			fprintf(f, "\t");

			if (-1 == print_hook_args(f, opt, hooks, NULL, NULL)) {
				return -1;
			}
		}
		fprintf(f, ")\n");
		fprintf(f, "{\n");

		generate_struct_definition(f, &config, opt->comments, prefix);
		generate_data(f, &config, opt->comments, prefix, ir);
		generate_interpreter(f, &config, opt, prefix);

		fprintf(f, "}\n");
		fprintf(f, "\n");
	} else {
		/* caller sets up the function head */
		generate_struct_definition(f, &config, opt->comments, prefix);
		generate_data(f, &config, opt->comments, prefix, ir);
		generate_interpreter(f, &config, opt, prefix);
	}

	f_free(alloc, config.dst_buf.buf);
	f_free(alloc, config.endid_buf.buf);
	f_free(alloc, config.eager_output_buf.buf);
	f_free(alloc, config.bitset_words.pairs);
	f_free(alloc, config.state_info);
	f_free(alloc, config.eager_output_ids);

	return 0;
}
