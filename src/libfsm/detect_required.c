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
#define LOG_STEPS (LOG_BASE + 1)

#define LABEL_GROUP ((uint16_t)-1)

struct dr2_env {
	const struct fsm *dfa;
	size_t steps;

	/* number of times a unique label has been required -- this is a count so that going
	 * from 0 <-> 1 can set/clear the accumulator, but going from 1 -> 2 etc. does not. */
	size_t counts[256];
	struct bm current;
	bool first_end_state;
	struct bm overall;

	struct dr2_stack {
		size_t used;
		size_t ceil;
		struct stack_frame {
			fsm_state_t state;
			uint16_t label; /* unique label followed to get here, or LABEL_GROUP */
			struct edge_group_iter iter;
		} *frames;
	} stack;
};

#define DEF_STACK_FRAMES 1000	/* FIXME: make dynamic */

/* Check symbols[]: if there's more than one bit set, then set label to
 * LABEL_GROUP, otherwise set it to the single bit's character value.
 * At least one bit must be set. */
static void check_symbols(const struct edge_group_iter_info *info, uint16_t *label)
{
	bool any = false;

	for (size_t i = 0; i < 256/64; i++) {
		uint64_t w = info->symbols[i];
		if (w == 0) { continue; }

		/* get position of lowest set bit */
		for (size_t b = 0; b < 64; b++) {
			const uint64_t bit = 1ULL << b;
			if (w & bit) {
				if (any) {
					*label = LABEL_GROUP;
					return;
				}

				/* clear it, check if there's anything else set */
				w &= ~bit;
				if (w != 0) {
					*label = LABEL_GROUP;
					return;
				}

				*label = 64*i + b;
				any = true;
				break;
			}
		}
	}

	/* there must be at least one bit set */
	assert(any);
}

static enum fsm_detect_required_characters_res
detect_required_characters_2(const struct fsm *dfa, size_t step_limit, struct bm *bitmap)
{
	assert(dfa != NULL);
	assert(bitmap != NULL);

	#if EXPENSIVE_CHECKS
	if (!fsm_all(dfa, fsm_isdfa)) {
		return FSM_DETECT_REQUIRED_CHARACTERS_ERROR_MISUSE;
	}
	#endif

	enum fsm_detect_required_characters_res res = FSM_DETECT_REQUIRED_CHARACTERS_ERROR_ALLOC;

	struct dr2_env env = {
		.dfa = dfa,
		.first_end_state = true,
	};

	assert(env.counts[0] == 0);

	const size_t state_count = fsm_countstates(dfa);
	fsm_state_t start_state;
	if (!fsm_getstart(dfa, &start_state)) {
		res = FSM_DETECT_REQUIRED_CHARACTERS_ERROR_MISUSE;
		goto cleanup;
	}

	#if EXPENSIVE_CHECKS || 1
	for (fsm_state_t s = 0; s < state_count; s++) {
		assert(!dfa->states[s].visited);
	}
	#endif

	bm_clear(bitmap);

	/* If the start state is also an end state, then
	 * it matches the empty string, so we're done. */
	if (fsm_isend(dfa, start_state)) {
		res = FSM_DETECT_REQUIRED_CHARACTERS_WRITTEN;
		goto cleanup;
	}

	env.stack.frames = f_malloc(dfa->opt->alloc, DEF_STACK_FRAMES * sizeof(env.stack.frames[0]));
	if (env.stack.frames == NULL) { goto cleanup; }
	env.stack.ceil = DEF_STACK_FRAMES;

	{			/* set up start state's stack frame */
		struct stack_frame *sf0 = &env.stack.frames[0];
		sf0->state = start_state;
		sf0->label = LABEL_GROUP;

		dfa->states[start_state].visited = true;

		edge_set_group_iter_reset(dfa->states[start_state].edges,
		    EDGE_GROUP_ITER_ALL, &sf0->iter);
		env.stack.used = 1;
	}

	while (env.stack.used > 0) {
		struct stack_frame *sf = &env.stack.frames[env.stack.used - 1];
		struct edge_group_iter_info info;
		env.steps++;
		if (LOG_STEPS > 1) {
			fprintf(stderr, "-- steps %zu/%zu\n", env.steps, step_limit);
		}
		if (env.steps == step_limit) {
			res = FSM_DETECT_REQUIRED_CHARACTERS_STEP_LIMIT_REACHED;
			goto cleanup;
		}

		if (edge_set_group_iter_next(&sf->iter, &info)) {
			assert(info.to < state_count);
			if (dfa->states[info.to].visited) {
				/* fprintf(stderr, "-- skipping visited state %u\n", info.to); */
				continue;
			}

			if (env.stack.used == env.stack.ceil) {
				assert(!"todo: grow");
			}

			/* enter state */
			/* fprintf(stderr, "-- entering state %u\n", info.to); */
			dfa->states[info.to].visited = true;

			struct stack_frame *nsf = &env.stack.frames[env.stack.used];
			nsf->state = info.to;
			check_symbols(&info, &nsf->label);
			/* fprintf(stderr, "-- check_symbols res 0x%04x\n", nsf->label); */

			if (nsf->label != LABEL_GROUP) {
				size_t offset = (nsf->label & 0xff);
				size_t count = ++env.counts[offset];
				/* fprintf(stderr, "-- count %zu (++)\n", count); */
				if (count == 1) {
					/* fprintf(stderr, "-- setting label 0x%02x\n", (uint8_t)offset); */
					bm_set(&env.current, offset);
				}
			}

			edge_set_group_iter_reset(dfa->states[info.to].edges,
			    EDGE_GROUP_ITER_ALL, &nsf->iter);
			env.stack.used++;

			if (fsm_isend(dfa, info.to)) {
				/* fprintf(stderr, "-- state %u is end\n", info.to); */
				if (env.first_end_state) {
					bm_copy(&env.overall, &env.current);
					env.first_end_state = false;
				} else { /* intersect */
					bm_intersect(&env.overall, &env.current);
				}

				if (LOG_PROGRESS) {
					fprintf(stderr, "-- current: ");
					bm_print(stderr, dfa->opt, &env.current, 0, fsm_escputc);
					fprintf(stderr, ", overall: ");
					bm_print(stderr, dfa->opt, &env.overall, 0, fsm_escputc);
					fprintf(stderr, "\n");
				}

				if (!bm_any(&env.overall)) {
					res = FSM_DETECT_REQUIRED_CHARACTERS_WRITTEN;
					break;
				}
			}

		} else {	/* done with state */
			/* If this state was reached via a unique label, then
			 * reduce the count. If the count returns to 0, remove
			 * it from the constraint set. */
			/* fprintf(stderr, "-- leaving state %u\n", sf->state); */
			if (sf->label != LABEL_GROUP) {
				size_t offset = (sf->label & 0xff);
				size_t count = --env.counts[offset];
				/* fprintf(stderr, "-- count %zu (--)\n", count); */
				if (count == 0) {
					/* fprintf(stderr, "-- clearing label 0x%02x\n", (uint8_t)offset); */
					bm_unset(&env.current, offset);
				}
			}

			/* clear visited */
			dfa->states[sf->state].visited = false;

			env.stack.used--;
		}
	}

	if (LOG_STEPS) {
		fprintf(stderr, "%s: finished in %zu/%zu steps\n", __func__, env.steps, step_limit);
	}

	res = FSM_DETECT_REQUIRED_CHARACTERS_WRITTEN;
	bm_copy(bitmap, &env.overall);

cleanup:
	f_free(dfa->opt->alloc, env.stack.frames);

	for (fsm_state_t s = 0; s < state_count; s++) {
		dfa->states[s].visited = false;
	}

	return res;
}

enum fsm_detect_required_characters_res
fsm_detect_required_characters(const struct fsm *dfa, size_t step_limit, struct bm *bitmap)
{
	return detect_required_characters_2(dfa, step_limit, bitmap);
}
