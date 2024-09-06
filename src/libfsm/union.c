/*
 * Copyright 2008-2017 Katherine Flavel
 *
 * See LICENCE for the full copyright terms.
 */

#include <assert.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>
#include <limits.h>
#include <errno.h>

#include <fsm/fsm.h>
#include <fsm/capture.h>
#include <fsm/bool.h>
#include <fsm/pred.h>

#include "internal.h"

#define LOG_UNION_ARRAY 0

struct fsm *
fsm_union(struct fsm *a, struct fsm *b,
	struct fsm_combine_info *combine_info)
{
	struct fsm *q;
	fsm_state_t sa, sb;
	fsm_state_t sq;
	struct fsm_combine_info combine_info_internal;

	if (combine_info == NULL) {
		combine_info = &combine_info_internal;
	}

	memset(combine_info, 0x00, sizeof(*combine_info));

	assert(a != NULL);
	assert(b != NULL);

	if (a->alloc != b->alloc) {
		errno = EINVAL;
		return NULL;
	}

	if (a->statecount == 0) { fsm_free(a); return b; }
	if (b->statecount == 0) { fsm_free(b); return a; }

	if (!fsm_getstart(a, &sa) || !fsm_getstart(b, &sb)) {
		errno = EINVAL;
		return NULL;
	}

	q = fsm_merge(a, b, combine_info);
	assert(q != NULL);

	sa += combine_info->base_a;
	sb += combine_info->base_b;

	/*
	 * The textbook approach is to create a new start state, with epsilon
	 * transitions to both a->start and b->start:
	 *
	 *     a: ⟶ ○ ··· ◎             ╭⟶ ○ ··· ◎
	 *                     a ∪ b: ⟶ ○
	 *     b: ⟶ ○ ··· ◎             ╰⟶ ○ ··· ◎
	 */

	if (!fsm_addstate(q, &sq)) {
		goto error;
	}

	fsm_setstart(q, sq);

	if (sq != sa) {
		if (!fsm_addedge_epsilon(q, sq, sa)) {
			goto error;
		}
	}

	if (sq != sb) {
		if (!fsm_addedge_epsilon(q, sq, sb)) {
			goto error;
		}
	}

	return q;

error:

	fsm_free(q);

	return NULL;
}

struct fsm *
fsm_union_array(size_t fsm_count,
    struct fsm **fsms, struct fsm_combined_base_pair *bases)
{
	if (getenv("GROUP") != NULL) {
		assert(fsms[0] != NULL);
		const struct fsm_alloc *alloc = fsms[0]->alloc;
		struct fsm_union_entry *entries = f_calloc(alloc,
		    fsm_count, sizeof(entries[0]));
		if (entries == NULL) {
			return NULL;  /* FIXME cleanup */
		}
		for (size_t i = 0; i < fsm_count; i++) {
			entries[i].fsm = fsms[i];
			fsms[i] = NULL;
		}

		struct fsm *res = fsm_union_repeated_pattern_group(fsm_count, entries, bases);
		f_free(alloc, entries);
		return res;
	}

	size_t i;
	struct fsm *res = fsms[0];

	fsms[0] = NULL;
	if (bases != NULL) {
		memset(bases, 0x00, fsm_count * sizeof(bases[0]));
	}

	for (i = 1; i < fsm_count; i++) {
		struct fsm_combine_info ci;
		struct fsm *combined = fsm_union(res, fsms[i], &ci);
		fsms[i] = NULL;
		if (combined == NULL) {
			while (i < fsm_count) {
				fsm_free(fsms[i]);
				i++;
			}

			fsm_free(res);
			return NULL;
		}

		res = combined;

		if (bases == NULL) {
			continue;
		}

		bases[i].state = ci.base_b;
		bases[i].capture = ci.capture_base_b;

		/* If the first argument didn't get its states put first
		 * in the union, then shift the bases for everything
		 * that has been combined into it so far. */
		if (ci.capture_base_a > 0) {
			size_t shift_i;
			for (shift_i = 0; shift_i < i; shift_i++) {
				bases[shift_i].state += ci.base_a;
				bases[shift_i].capture += ci.capture_base_a;
			}
		}
	}

#if LOG_UNION_ARRAY
	if (bases != NULL) {
		for (i = 0; i < fsm_count; i++) {
			fprintf(stderr, "union_array: bases %u: %zu, %zu\n",
				i, bases[i].state, bases[i].capture);
		}
	}
#endif

	return res;
}

struct fsm *
fsm_union_repeated_pattern_group(size_t entry_count,
    struct fsm_union_entry *entries, struct fsm_combined_base_pair *bases)
{
	/* combine a series of FSMs into a single FSM.
	 *
	 * Add a new global start state.
	 * Add a new global unanchored start loop, if anything is unanchored at the start.
	 * Add a new global end state.
	 * Add a new global unanchored end loop, if anything is unanchored at the end.
	 *
	 * For each FSM:
	 * - epsilon link to it from the appropriate start/start-loop state
	 * - link from every unanchored end state in it to a .* unanchored end loop
	 *   that ALSO links back to the start state, for further matches.
	 * - do the usual base pair offsets, etc., copying every FSM sequentially
	 *   into the new FSM
	 * - consume fsms[].
	 * */
	const struct fsm_alloc *alloc = entries[0].fsm->alloc;

	(void)bases;		/* TODO */

	if (entry_count == 1) {
		return entries[0].fsm;
	}

	size_t est_total_states = 0;
	for (size_t i = 0; i < entry_count; i++) {
		assert(entries[i].fsm);
		if (entries[i].fsm->alloc != alloc) {
			errno = EINVAL;
			return NULL;
		}
		const size_t count = fsm_countstates(entries[i].fsm);
		fprintf(stderr, "%s: entries[%zd].fsm: %zu states\n", __func__, i, count);
		est_total_states += count;
	}
	est_total_states += 4;	/* new start and end, new unanchored start and end loops */

	struct fsm *res = fsm_new_statealloc(alloc, est_total_states);
	if (res == NULL) { return NULL; }

	struct ends_buf {
		size_t ceil;
		size_t used;
		fsm_state_t *states;
	} ends = { .ceil = 0 };

	/* Could conditionally create these base on flags in entries[], but
	 * it's only a few extra states and later operations will sweep them up. */
	fsm_state_t global_start, global_start_loop, global_end, global_end_loop;
	if (!fsm_addstate(res, &global_start)) { goto fail; }
	if (!fsm_addstate(res, &global_start_loop)) { goto fail; }
	if (!fsm_addstate(res, &global_end)) { goto fail; }
	if (!fsm_addstate(res, &global_end_loop)) { goto fail; }

	if (!fsm_addedge_epsilon(res, global_start, global_start_loop)) { goto fail; }
	if (!fsm_addedge_epsilon(res, global_end_loop, global_end)) { goto fail; }

	if (!fsm_addedge_any(res, global_start_loop, global_start_loop)) { goto fail; }
	if (!fsm_addedge_any(res, global_end_loop, global_end_loop)) { goto fail; }

	if (bases != NULL) {
		memset(bases, 0x00, entry_count * sizeof(bases[0]));
	}

	for (size_t fsm_i = 0; fsm_i < entry_count; fsm_i++) {
		struct fsm *fsm = entries[fsm_i].fsm;
		entries[fsm_i].fsm = NULL;

		ends.used = 0;	/* reset */

		const size_t state_count = fsm_countstates(fsm);

		fsm_state_t start;
		if (!fsm_getstart(fsm, &start)) { /* no start */
			errno = EINVAL;
			goto fail;
		}

		for (fsm_state_t s_i = 0; s_i < state_count; s_i++) {
			if (fsm_isend(fsm, s_i)) {
				if (ends.used == ends.ceil) {
					size_t nceil = (ends.ceil == 0 ? 4 : 2*ends.ceil);
					fsm_state_t *nstates = f_realloc(alloc,
					    ends.states, nceil * sizeof(nstates[0]));
					if (nstates == NULL) { goto fail; }
					ends.ceil = nceil;
					ends.states = nstates;
				}
				ends.states[ends.used++] = s_i;
			}
		}

		if (ends.used == 0) { /* no ends */
			errno = EINVAL;
			goto fail;
		}

		/* call fsm_merge; we really don't care which is which */
		struct fsm_combine_info combine_info;
		struct fsm *merged = fsm_merge(res, fsm, &combine_info);
		if (merged == NULL) { goto fail; }

		fprintf(stderr, "%s: ci: b_a %d, b_b %d, cb_a %d, cb_b %d\n",
		    __func__,
		    combine_info.base_a,
		    combine_info.base_b,
		    combine_info.capture_base_a,
		    combine_info.capture_base_b);

		global_start += combine_info.base_a;
		global_start_loop += combine_info.base_a;
		global_end += combine_info.base_a;
		global_end_loop += combine_info.base_a;

		start += combine_info.base_b;
		for (size_t i = 0; i < ends.used; i++) {
			ends.states[i] += combine_info.base_b;
		}

		/* determinisation should figure this out */
#if 0
		/* every state gets an any edge to the global start, because any unmatched character resets the match */
		/* FIXME: should this be behind a distinct flag? */
		if (!entries[fsm_i].anchored_start && !entries[fsm_i].anchored_end) {
			for (fsm_state_t s_i = 0; s_i < state_count; s_i++) {
				if (!fsm_addedge_any(res, s_i + combine_info.base_b, global_start)) { goto fail; }
			}
		}
#endif

		/* copy states and metadata from fsm into res, save offsets */

		/* link to start/start_loop and end/end_loop */
		const fsm_state_t start_src = entries[fsm_i].anchored_start ? global_start : global_start_loop;
		if (!fsm_addedge_epsilon(merged, start_src, start)) { goto fail; }

		const fsm_state_t end_dst = entries[fsm_i].anchored_end ? global_end : global_end_loop;
		for (size_t i = 0; i < ends.used; i++) {
			if (!fsm_addedge_epsilon(merged, ends.states[i], end_dst)) { goto fail; }
		}

		if (bases != NULL) {
			bases[fsm_i].state = combine_info.base_b;
			bases[fsm_i].capture = combine_info.capture_base_b;
		}

		res = merged;
	}

	fsm_setstart(res, global_start);
	fsm_setend(res, global_end, 1);

	/* add loop */
	if (!fsm_addedge_epsilon(res, global_end_loop, global_start_loop)) { goto fail; }


	/* FIXME: cleanup */

	return res;

fail:
	return NULL;

}
