/*
 * Copyright 2020 Scott Vokes
 *
 * See LICENCE for the full copyright terms.
 */

/* fsm consolidate -> take an FSM and a mapping, produce a new FSM with combined states */

#include <assert.h>
#include <stddef.h>
#include <stdint.h>

#include <fsm/fsm.h>
#include <fsm/capture.h>
#include <fsm/pred.h>
#include <fsm/walk.h>

#include <adt/alloc.h>
#include <adt/set.h>
#include <adt/edgeset.h>
#include <adt/stateset.h>
#include <adt/hashset.h>
#include <adt/mappinghashset.h>
#include <adt/u64bitset.h>

#include "internal.h"
#include "capture.h"
#include "endids.h"

#define LOG_MAPPING 0
#define LOG_CONSOLIDATE_CAPTURES 0
#define LOG_CONSOLIDATE_END_METADATA 0

struct mapping_closure {
	size_t count;
	const fsm_state_t *mapping;
};

static int
consolidate_end_metadata(struct fsm *dst, struct fsm *src,
    const fsm_state_t *mapping, size_t mapping_count);

static fsm_state_t
mapping_cb(fsm_state_t id, const void *opaque)
{
	const struct mapping_closure *closure = opaque;
	assert(id < closure->count);
	return closure->mapping[id];
}

struct fsm *
fsm_consolidate(struct fsm *src,
    const fsm_state_t *mapping, size_t mapping_count)
{
	struct fsm *dst;
	fsm_state_t src_i;
	uint64_t *seen = NULL;
	struct mapping_closure closure;
	size_t max_used = 0;

	assert(src != NULL);
	if (mapping_count == 0) {
		return src;
	}
	assert(src->opt != NULL);

	dst = fsm_new(src->opt);
	if (dst == NULL) {
		goto cleanup;
	}

	for (src_i = 0; src_i < mapping_count; src_i++) {
		const fsm_state_t dst_i = mapping[src_i];
#if LOG_MAPPING
		fprintf(stderr, "consolidate_mapping[%u]: %u\n",
		    src_i, mapping[src_i]);
#endif
		if (dst_i > max_used) {
			assert(dst_i != FSM_STATE_REMAP_NO_STATE);
			max_used = dst_i;
		}
	}

	if (!fsm_addstate_bulk(dst, max_used + 1)) {
		goto cleanup;
	}
	assert(dst->statecount == max_used + 1);

	seen = f_calloc(src->opt->alloc,
	    mapping_count/64 + 1, sizeof(seen[0]));
	if (seen == NULL) {
		goto cleanup;
	}

#define DST_SEEN(I) u64bitset_get(seen, I)
#define SET_DST_SEEN(I) u64bitset_set(seen, I)

	/* map N states to M states, where N >= M.
	 * if it's the first time state[M] is seen,
	 * then copy it verbatim, otherwise only
	 * carryopaque. */

	closure.count = mapping_count;
	closure.mapping = mapping;

	for (src_i = 0; src_i < mapping_count; src_i++) {
		const fsm_state_t dst_i = mapping[src_i];

		/* fsm_consolidate does not currently support discarding states. */
		assert(dst_i != FSM_STATE_REMAP_NO_STATE);

		if (!DST_SEEN(dst_i)) {
			SET_DST_SEEN(dst_i);

			if (!state_set_copy(&dst->states[dst_i].epsilons,
				dst->opt->alloc, src->states[src_i].epsilons)) {
				goto cleanup;
			}
			state_set_compact(&dst->states[dst_i].epsilons,
			    mapping_cb, &closure);

			if (!edge_set_copy(&dst->states[dst_i].edges,
				dst->opt->alloc,
				src->states[src_i].edges)) {
				goto cleanup;
			}
			edge_set_compact(&dst->states[dst_i].edges,
			    dst->opt->alloc, mapping_cb, &closure);

			if (fsm_isend(src, src_i)) {
				fsm_setend(dst, dst_i, 1);
			}
		}
	}

	if (!fsm_capture_copy_programs(src, dst)) {
		goto cleanup;
	}

	if (!consolidate_end_metadata(dst, src, mapping, mapping_count)) {
		goto cleanup;
	}

	{
		fsm_state_t src_start, dst_start;
		if (fsm_getstart(src, &src_start)) {
			assert(src_start < mapping_count);
			dst_start = mapping[src_start];
			fsm_setstart(dst, dst_start);
		}
	}

	f_free(src->opt->alloc, seen);

	return dst;

cleanup:

	if (seen != NULL) { f_free(src->opt->alloc, seen); }
	return NULL;
}

struct consolidate_end_ids_env {
	char tag;
	struct fsm *dst;
	struct fsm *src;
	const fsm_state_t *mapping;
	size_t mapping_count;
	int ok;
};

static int
consolidate_end_ids_cb(const struct fsm *fsm, fsm_state_t state,
    size_t nth, const fsm_end_id_t id, void *opaque)
{
	struct consolidate_end_ids_env *env = opaque;
	enum fsm_endid_set_res sres;
	fsm_state_t s;
	assert(env->tag == 'C');

	(void)fsm;
	(void)nth;

#if LOG_CONSOLIDATE_END_METADATA > 1
	fprintf(stderr, "consolidate_end_ids_cb: state %u, ID[%zu]: %d\n",
	    state, nth, id);
	fprintf(stderr, "  -- mapping_count %zu\n",
	    env->mapping_count);
#endif

	s = env->mapping[state];

#if LOG_CONSOLIDATE_END_METADATA > 1
	fprintf(stderr, "consolidate[%d] <- %d\n", s, id);
#endif

	sres = fsm_endid_set(env->dst, s, id);
	if (sres == FSM_ENDID_SET_ERROR_ALLOC_FAIL) {
		env->ok = 0;
		return 0;
	}

	return 1;
}

static void
consolidate_active_captures_cb(fsm_state_t state, unsigned capture_id,
    void *opaque)
{
	struct consolidate_end_ids_env *env = opaque;
	fsm_state_t dst_s;
	assert(env->tag == 'C');

	assert(state < env->mapping_count);
	dst_s = env->mapping[state];

#if LOG_CONSOLIDATE_END_METADATA
	fprintf(stderr, "consolidate_active_captures_cb: state %d -> dst_s %d, capture_id %u\n",
	    state, dst_s, capture_id);
#endif

	if (!fsm_capture_set_active_for_end(env->dst, capture_id, dst_s)) {
		env->ok = 0;
	}
}

static void
consolidate_capture_programs_cb(fsm_state_t state, unsigned program_id,
    void *opaque)
{
	struct consolidate_end_ids_env *env = opaque;
	fsm_state_t dst_s;
	assert(env->tag == 'C');

	assert(state < env->mapping_count);
	dst_s = env->mapping[state];

#if LOG_CONSOLIDATE_END_METADATA
	fprintf(stderr, "%s: state %d -> dst_s %d, capture_id %u\n",
	    __func__, state, dst_s, program_id);
#endif

	if (!fsm_capture_associate_program_with_end_state(env->dst,
		(uint32_t)program_id, dst_s)) {
		env->ok = 0;
	}
}

static int
consolidate_end_metadata(struct fsm *dst, struct fsm *src,
    const fsm_state_t *mapping, size_t mapping_count)
{
	struct consolidate_end_ids_env env;
	env.tag = 'C';		/* for Consolidate */
	env.dst = dst;
	env.src = src;
	env.mapping = mapping;
	env.mapping_count = mapping_count;
	env.ok = 1;

	fsm_endid_iter(src, consolidate_end_ids_cb, &env);

	if (env.ok) {
		fsm_state_t s;
		const size_t src_state_count = fsm_countstates(src);
		for (s = 0; s < src_state_count; s++) {
			fsm_capture_iter_active_for_end_state(src, s,
			    consolidate_active_captures_cb, &env);
			if (!env.ok) {
				break;
			}

			fsm_capture_iter_program_ids_for_end_state(src, s,
			    consolidate_capture_programs_cb, &env);
			if (!env.ok) {
				break;
			}
		}
	}

#if LOG_CONSOLIDATE_END_METADATA > 1
	fprintf(stderr, "==== fsm_consolidate -- endid_info after:\n");
	fsm_endid_dump(stderr, dst);
	fsm_capture_dump_active_for_ends(stderr, dst);
#endif

	return env.ok;
}
