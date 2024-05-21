/*
 * Copyright 2024 Scott Vokes
 *
 * See LICENCE for the full copyright terms.
 */

#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <assert.h>
#include <ctype.h>

#include <fsm/fsm.h>
#include <fsm/walk.h>
#include <fsm/pred.h>

#include <adt/edgeset.h>
#include <adt/queue.h>
#include <adt/u64bitset.h>

#include "internal.h"

#define END_OF_FREELIST ((fsm_state_t)-1)
#define DEF_CURSOR_CEIL 1	/* force frequent realloc */

#define LOG_BASE 0
#define LOG_RMAP (LOG_BASE + 0)
#define LOG_QUEUE (LOG_BASE + 0)
#define LOG_MERGE (LOG_BASE + 0)
#define LOG_CURSOR (LOG_BASE + 0)
#define LOG_PROGRESS (LOG_BASE + 0)

#define USE_UNIQUE_ID 1

struct drc_cursor {
	struct bm bitmap;
	fsm_state_t state;	/* or freelist id, or END_OF_FREELIST */
#if USE_UNIQUE_ID
	size_t unique_id;
#endif
	uint64_t visited[/* u64bitset_words(state_count) */];
};

struct drc_state {
	const struct fsm_alloc *alloc;
	const struct fsm *dfa;
	const size_t state_count;
	const size_t visited_words;

#if USE_UNIQUE_ID
	size_t unique_id_counter;
#endif

	struct {
		size_t ceil;
		struct drc_cursor **cursors;

		/* This (and the cursor->state field) are used as a
		 * freelist. There can never be more cursors than
		 * there are end states, so the cursor ID must fit
		 * in an fsm_state_t. */
		fsm_state_t freelist;
	} cursor;

	size_t edge_count;
	size_t unique_edge_count;
	struct edge_alist {
		fsm_state_t from;
		fsm_state_t to;
		bool unique;
		uint8_t unique_char;
	} *rmap;

	/* Accumulator for intersection of bitmaps. Set to the bitmap of
	 * the first cursor to reach the start state, and intersected
	 * thereafter. */
	struct bm accum;
};

static int
cmp_rmap_by_to(const void *pa, const void *pb)
{
	const struct edge_alist *a = (const struct edge_alist *)pa;
	const struct edge_alist *b = (const struct edge_alist *)pb;

	/* this is a reverse mapping, so sort by the to state */
	if (a->to < b->to) { return -1; }
	if (a->to > b->to) { return 1; }

	if (a->from < b->from) { return -1; }
	if (a->from > b->from) { return 1; }

	/* shouldn't get here: should be unique */
	return 0;
}

static bool
init_rmap(const struct fsm *dfa, struct drc_state *state)
{
	struct edge_group_iter iter;
	struct edge_group_iter_info info;

	state->edge_count = 0;
	state->unique_edge_count = 0;

	/* first pass: count edges */
	for (fsm_state_t s_i = 0; s_i < state->state_count; s_i++) {
		edge_set_group_iter_reset(dfa->states[s_i].edges,
		    EDGE_GROUP_ITER_ALL, &iter);
		while (edge_set_group_iter_next(&iter, &info)) {
			if (info.to == s_i) { continue; } /* ignored */
			state->edge_count++;
		}
	}

	struct edge_alist *rmap = malloc(state->edge_count * sizeof(rmap[0]));
	if (rmap == NULL) { return false; }

	/* second pass: populate */
	size_t rmap_used = 0;
	for (fsm_state_t s_i = 0; s_i < state->state_count; s_i++) {
		edge_set_group_iter_reset(dfa->states[s_i].edges,
		    EDGE_GROUP_ITER_ALL, &iter);
		while (edge_set_group_iter_next(&iter, &info)) {
			/* filter self-edges, they don't impact the result */
			if (info.to == s_i) { continue; }

			struct edge_alist *elt = &rmap[rmap_used];
			elt->from = s_i;
			elt->to = info.to;

			size_t label_count = 0;
			for (size_t i = 0; i < 4; i++) {
				label_count += (size_t)u64bitset_popcount(info.symbols[i]);
			}
			assert(label_count > 0);

			if (label_count == 1) {
				state->unique_edge_count++;
				elt->unique = true;
				bool unique_char_found = false;
				for (size_t i = 0; i < 4; i++) {
					const uint64_t w = info.symbols[i];
					if (w == 0) { continue; }
					for (uint64_t bit_i = 0; bit_i < 64; bit_i++) {
						if (w & (1ULL << bit_i)) {
							elt->unique_char = 64*i + bit_i;
							unique_char_found = true;
							break;
						}
					}
				}
				assert(unique_char_found);
			} else {
				elt->unique = false;
			}

			rmap_used++;
		}
	}

	/* invert mapping */
	qsort(rmap, state->edge_count, sizeof(rmap[0]), cmp_rmap_by_to);

#if LOG_RMAP
	for (size_t i = 0; i < rmap_used; i++) {
		struct edge_alist *elt = &rmap[i];
		fprintf(stderr, "%s: rmap[%zu]: from %u, to %u, unique ? %d",
		    __func__, i, elt->from, elt->to, elt->unique);
		if (elt->unique) {
			fprintf(stderr, " -- 0x%02x\n", elt->unique_char);
		} else {
			fprintf(stderr, "\n");
		}
	}
#endif

	state->rmap = rmap;
	return true;
}

static bool
request_cursor(struct drc_state *state, fsm_state_t *cursor_id)
{
	fsm_state_t freelist = state->cursor.freelist;
	if (freelist == END_OF_FREELIST) {
		const size_t oceil = state->cursor.ceil;
		const size_t nceil = oceil == 0
		    ? DEF_CURSOR_CEIL
		    : 2*state->cursor.ceil;

#if LOG_CURSOR
		fprintf(stderr, "%s: growing %zu -> %zu\n", __func__, oceil, nceil);
#endif

		struct drc_cursor **ncursors = f_realloc(state->alloc,
		    state->cursor.cursors, nceil * sizeof(ncursors[0]));
		if (ncursors == NULL) { return false; }

		/* allocate new cursors */
		for (size_t i = oceil; i < nceil; i++) {
			struct drc_cursor *c = malloc(sizeof(*c)
			    + state->visited_words * sizeof(c->visited[0]));
			if (c == NULL) {
				return false;
			}
			ncursors[i] = c;
		}

		/* link on freelist */
		for (size_t i = oceil; i < nceil; i++) {
			struct drc_cursor *c = ncursors[i];
			fsm_state_t next = i + 1;
			if (next == nceil) { next = END_OF_FREELIST; }
			c->state = next;
		}

		state->cursor.ceil = nceil;
		state->cursor.cursors = ncursors;
		state->cursor.freelist = oceil;
		freelist = state->cursor.freelist;
	}

	assert(freelist < state->cursor.ceil);
	struct drc_cursor *c = state->cursor.cursors[freelist];
	state->cursor.freelist = c->state; /* next link */
	c->state = (fsm_state_t)-2;
	bm_clear(&c->bitmap);
	memset(c->visited, 0x00, state->visited_words * sizeof(c->visited[0]));

#if LOG_CURSOR > 1
	fprintf(stderr, "%s: requested cursor_id %u\n", __func__, freelist);
#endif
	*cursor_id = freelist;
	return true;
}

static void
release_cursor(struct drc_state *state, fsm_state_t cursor_id)
{
	assert(cursor_id < state->cursor.ceil);
	struct drc_cursor *c = state->cursor.cursors[cursor_id];
	c->state = state->cursor.freelist;

#if LOG_CURSOR > 1
	fprintf(stderr, "%s: released cursor_id %u\n", __func__, cursor_id);
#endif
	state->cursor.freelist = cursor_id;
}

static size_t
rmap_seek(const struct edge_alist *rmap, size_t edge_count, fsm_state_t state)
{
	/* FIXME linear search, use bsearch later */
	for (size_t i = 0; i < edge_count; i++) {
		if (rmap[i].to == state) { return i; }
	}

	return edge_count;	/* not found */
}

static struct drc_cursor *
get_cursor(struct drc_state *state, fsm_state_t cursor_id)
{
	/* this function exists to wrap the assert */
	assert(cursor_id < state->cursor.ceil);
	return state->cursor.cursors[cursor_id];
}

enum fsm_detect_required_characters_res
fsm_detect_required_characters(const struct fsm *dfa, size_t step_limit, struct bm *bitmap)
{
	assert(dfa != NULL);
	assert(bitmap != NULL);

	#if EXPENSIVE_CHECKS
	if (!fsm_all(dfa, fsm_isdfa)) {
		return FSM_DETECT_REQUIRED_CHARACTERS_ERROR_MISUSE;
	}
	#endif

	enum fsm_detect_required_characters_res res = FSM_DETECT_REQUIRED_CHARACTERS_ERROR_MISUSE;

	const size_t state_count = fsm_countstates(dfa);
	fsm_state_t start_state;
	if (!fsm_getstart(dfa, &start_state)) {
		goto cleanup;
	}

	struct drc_state state = {
		.alloc = dfa->opt->alloc,
		.dfa = dfa,
		.state_count = state_count,
		.visited_words = u64bitset_words(state_count),
		.cursor.freelist = END_OF_FREELIST,
	};

	struct queue *q = NULL;

	bm_clear(bitmap);

	q = queue_new_dynamic(dfa->opt->alloc, state_count);
	if (q == NULL) {
		res = FSM_DETECT_REQUIRED_CHARACTERS_ERROR_ALLOC;
		goto cleanup;
	}

	if (!init_rmap(dfa, &state)) {
		res = FSM_DETECT_REQUIRED_CHARACTERS_ERROR_ALLOC;
		goto cleanup;
	}

	/* If the DFA doesn't have any single-label edges, then walking
	 * the paths from every end state won't add any constraints. */
	if (state.unique_edge_count == 0) {
		res = FSM_DETECT_REQUIRED_CHARACTERS_WRITTEN;
		goto cleanup;
	}

	size_t steps = 0;

	/* Do the analysis for each end state, adding extra cursors
	 * wherever the path diverges, and intersect the requirement
	 * bitmaps across all cursors for all end states. The total cost
	 * is proportional to the number of states and the number of end
	 * states. */
	bool first_path = true;
	for (fsm_state_t s_i = 0; s_i < state_count; s_i++) {
		if (!fsm_isend(dfa, s_i)) { continue; }

#if LOG_PROGRESS
		fprintf(stderr, "-- analyzing end-state %u\n", s_i);
#endif

		fsm_state_t s;
		assert(!queue_pop(q, &s)); /* empty */

		/* This is managed by ID rather than pointer because the
		 * pointers become stale whenever the array is reallocated. */
		fsm_state_t cursor_id;
		if (!request_cursor(&state, &cursor_id)) {
			res = FSM_DETECT_REQUIRED_CHARACTERS_ERROR_ALLOC;
			goto cleanup;
		}

		{
			struct drc_cursor *cursor = get_cursor(&state, cursor_id);
			cursor->state = s_i;

#if LOG_QUEUE
			fprintf(stderr, "%s: queue pushing %u (at end state)\n", __func__, cursor_id);
#endif
			if (!queue_push(q, cursor_id)) {
				assert(!"internal error");
				goto cleanup;
			}

#if LOG_PROGRESS > 1
			fprintf(stderr, "%s: marking end state %u visited on cursor %u\n", __func__, s_i, cursor_id);
#endif
			u64bitset_set(cursor->visited, s_i);
		}

		while (queue_pop(q, &cursor_id)) {
			steps++;
			if ((steps % 10000) == 0) {
				fprintf(stderr, " -- %zu steps...\n", steps);
			}
			if (steps == step_limit) {
				res = FSM_DETECT_REQUIRED_CHARACTERS_STEP_LIMIT_REACHED;
				/* Note: this does not copy the partial info, since
				 * further processing might find alternate routes that
				 * clear the currently set constraints. */
				goto cleanup;
			}

			struct drc_cursor *cursor = get_cursor(&state, cursor_id);
#if LOG_QUEUE
			fprintf(stderr, "%s: queue popped %u -- state %u\n", __func__, cursor_id, cursor->state);
#endif
			assert(cursor->state < state_count);

			if (cursor->state == start_state) {
#if LOG_MERGE
				fprintf(stderr, "%s: cursor %u reached start_state %u with bitmap ",
				    __func__, cursor_id, start_state);
				bm_print(stderr, state.dfa->opt, &cursor->bitmap, 0, fsm_escputc);
				fprintf(stderr, "\n");
#endif
				if (first_path) {
					bm_copy(&state.accum, &cursor->bitmap);
					first_path = false;
				} else {
					bm_intersect(&state.accum, &cursor->bitmap);
				}

#if LOG_MERGE
				fprintf(stderr, "%s: merged accumulator is now ", __func__);
				bm_print(stderr, state.dfa->opt, &state.accum, 0, fsm_escputc);
				fprintf(stderr, "\n");
#endif

				if (!bm_any(&state.accum)) {
					/* unconstrained path found -- further work cannot
					 * add any new information, so we're done */
#if LOG_PROGRESS
					fprintf(stderr, "%s: unconstrained path found, we're done\n", __func__);
#endif
					res = FSM_DETECT_REQUIRED_CHARACTERS_WRITTEN;
					goto cleanup;
				}

				release_cursor(&state, cursor_id);
				continue;
			}

			/* start of reverse edges */
			size_t offset = rmap_seek(state.rmap, state.edge_count, cursor->state);

			while (offset < state.edge_count) {
				struct edge_alist *elt = &state.rmap[offset];

#if LOG_PROGRESS > 1
				fprintf(stderr, "%s: offset %zu, elt->from %u, elt->to %u, cursor->state %u, cursor->bitmap ",
				    __func__, offset, elt->from, elt->to, cursor->state);
				bm_print(stderr, state.dfa->opt, &cursor->bitmap, 0, fsm_escputc);
				fprintf(stderr, "\n");
#endif

				if (elt->to != cursor->state) {
					break;
				}
				assert(elt->to != elt->from); /* self-edges were filtered before */

				if (u64bitset_get(cursor->visited, elt->from)) {
#if LOG_PROGRESS > 2
					fprintf(stderr, "%s: skipping %u, visited\n", __func__, elt->from);
#endif
					offset++;
					continue;
				}

				fsm_state_t other_cursor_id;
				if (!request_cursor(&state, &other_cursor_id)) {
					res = FSM_DETECT_REQUIRED_CHARACTERS_ERROR_ALLOC;
					goto cleanup;
				}

				struct drc_cursor *ocursor = get_cursor(&state, other_cursor_id);
				ocursor->state = elt->from;
				bm_copy(&ocursor->bitmap, &cursor->bitmap);
				memcpy(ocursor->visited, cursor->visited,
				    state.visited_words * sizeof(cursor->visited[0]));

#if USE_UNIQUE_ID
				ocursor->unique_id = state.unique_id_counter++;
#endif

#if LOG_PROGRESS > 1
				fprintf(stderr, "%s: marking %u visited on cursor %u\n", __func__, elt->from, other_cursor_id);
#endif
				u64bitset_set(ocursor->visited, elt->from);

				if (elt->unique) {
#if LOG_PROGRESS
					fprintf(stderr, "%s: marking 0x%02x (%c) as required on cursor %u\n",
					    __func__, elt->unique_char,
					    isprint(elt->unique_char) ? elt->unique_char : '.',
					    other_cursor_id);
#endif
					bm_set(&ocursor->bitmap, (size_t)elt->unique_char);
				}

#if LOG_QUEUE
				fprintf(stderr, "%s: queue pushing %u, state %u (backlink %u -> %u)\n",
				    __func__, other_cursor_id, ocursor->state, elt->from, elt->to);
#endif
				/* fprintf(stdout, "-- %u <- %u, %zu to %zu\n", elt->to, elt->from, cursor->unique_id, ocursor->unique_id); */

				if (!queue_push(q, other_cursor_id)) {
					assert(!"internal error");
					goto cleanup;
				}

				offset++;
			}

			release_cursor(&state, cursor_id);
		}
	}

	/* The final result is the intersection of every bitmap
	 * reaching the start state. */
	bm_copy(bitmap, &state.accum);

#if LOG_PROGRESS
	fprintf(stderr, "%s: final result: ", __func__);
	bm_print(stderr, state.dfa->opt, &state.accum, 0, fsm_escputc);
	fprintf(stderr, "\n");
#endif

	res = FSM_DETECT_REQUIRED_CHARACTERS_WRITTEN;

cleanup:
	free(state.rmap);
	for (size_t i = 0; i < state.cursor.ceil; i++) {
		free(state.cursor.cursors[i]);
	}
	free(state.cursor.cursors);
	queue_free(q);

	return res;
}
