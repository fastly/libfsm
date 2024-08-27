/*
 * Copyright 2019 Katherine Flavel
 *
 * See LICENCE for the full copyright terms.
 */

#include <assert.h>
#include <stddef.h>
#include <stdio.h>
#include <errno.h>
#include <string.h>

#include <fsm/fsm.h>
#include <fsm/pred.h>

#include <adt/alloc.h>
#include <adt/set.h>
#include <adt/edgeset.h>
#include <adt/stateset.h>
#include <adt/u64bitset.h>

#include "internal.h"
#include "capture.h"
#include "endids.h"
#include "eager_endid.h"

#define DUMP_EPSILON_CLOSURES 0
#define DEF_PENDING_CAPTURE_ACTIONS_CEIL 2
#define LOG_RM_EPSILONS_CAPTURES 0
#define DEF_CARRY_ENDIDS_COUNT 2

#define LOG_LEVEL 3

#if LOG_LEVEL > 0
static bool log_it;
#define LOG(LVL, ...)					\
	do {						\
		if (log_it && LVL <= LOG_LEVEL) {	\
			fprintf(stderr, __VA_ARGS__);	\
		}					\
	} while (0)
#else
#define LOG(_LVL, ...)
#endif

struct remap_env {
	char tag;
	const struct fsm_alloc *alloc;
	struct state_set **rmap;
	int ok;

	size_t count;
	size_t ceil;
	struct remap_action {
		fsm_state_t state;
		enum capture_action_type type;
		unsigned capture_id;
		fsm_state_t to;
	} *actions;
};

static int
remap_capture_actions(struct fsm *nfa, struct state_set **eclosures);

static int
remap_capture_action_cb(fsm_state_t state,
    enum capture_action_type type, unsigned capture_id, fsm_state_t to,
    void *opaque);

static int
carry_endids(struct fsm *fsm, struct state_set *states,
    fsm_state_t s);

static int
remap_eager_endids(struct fsm *nfa, struct state_set **eclosures);

int
fsm_remove_epsilons(struct fsm *nfa)
{
	const size_t state_count = fsm_countstates(nfa);
	int res = 0;
	struct state_set **eclosures = NULL;
	fsm_state_t s;

	INIT_TIMERS();

	/* NOCOMMIT */
	log_it = getenv("LOG") != NULL;

	assert(nfa != NULL);

	TIME(&pre);
	eclosures = epsilon_closure(nfa);
	TIME(&post);
	DIFF_MSEC("epsilon_closure", pre, post, NULL);

	if (eclosures == NULL) {
		goto cleanup;
	}

#if DUMP_EPSILON_CLOSURES
	{
		struct state_iter kt;
		fsm_state_t es;
		fprintf(stderr, "# ==== epsilon_closures\n");
		for (s = 0; s < nfa->statecount; s++) {
			if (eclosures[s] == NULL) { continue; }
			fprintf(stderr, " -- %u:", s);
			for (state_set_reset(eclosures[s], &kt); state_set_next(&kt, &es); ) {
				fprintf(stderr, " %u", es);
			}
			fprintf(stderr, "\n");
		}
	}
#endif

	for (s = 0; s < state_count; s++) {
		struct state_iter si;
		fsm_state_t es_id;

		struct edge_group_iter egi;
		struct edge_group_iter_info info;

		/* Process the epsilon closure. */
		state_set_reset(eclosures[s], &si);
		while (state_set_next(&si, &es_id)) {
			struct fsm_state *es = &nfa->states[es_id];

			/* The current NFA state is an end state if any
			 * of its associated epsilon-clousure states are
			 * end states.
			 *
			 * Similarly, any end state metadata on states
			 * in its epsilon-closure is copied to it.
			 *
			 * Capture actions are copied in a later pass. */
			if (fsm_isend(nfa, es_id)) {
#if LOG_COPYING
				fprintf(stderr, "remove_epsilons: setting end on %d (due to %d)\n", s, es_id);
#endif
				fsm_setend(nfa, s, 1);

				/*
				 * Carry through end IDs, if present. This isn't anything to do
				 * with the NFA conversion; it's meaningful only to the caller.
				 */
				if (!carry_endids(nfa, eclosures[s], s)) {
					goto cleanup;
				}
			}

			/* For every state in this state's transitive
			 * epsilon closure, add all of their sets of
			 * labeled edges. */
			edge_set_group_iter_reset(es->edges, EDGE_GROUP_ITER_ALL, &egi);
			while (edge_set_group_iter_next(&egi, &info)) {
#if LOG_COPYING
				fprintf(stderr, "%s: bulk-copying edges leading to state %d onto state %d (from state %d)\n",
				    __func__, info.to, s, es_id);
#endif
				if (!edge_set_add_bulk(&nfa->states[s].edges, nfa->alloc,
					info.symbols, info.to)) {
					goto cleanup;
				}
			}
		}
	}

	/* Remap edge metadata for eagerly matching endids.
	 *
	 * This depends on the previous phase finishing (because it pulls end states forward to
	 * the last labeled edges) but has to happen before the epsilon-edge state sets are
	 * removed (because it has to explore those to copy over edge metadata). */
	if (!remap_eager_endids(nfa, eclosures)) {
		goto cleanup;
	}

	/* Remove the epsilon-edge state sets from everything.
	 * This can make states unreachable. */
	for (s = 0; s < state_count; s++) {
		struct fsm_state *state = &nfa->states[s];
		state_set_free(state->epsilons);
		state->epsilons = NULL;
	}

#if LOG_RESULT
	fprintf(stderr, "=== %s: about to update capture actions\n", __func__);
	fsm_dump(stderr, nfa);
#endif

	if (!remap_capture_actions(nfa, eclosures)) {
		goto cleanup;
	}

#if LOG_RESULT
	fsm_dump(stderr, nfa);
	fsm_capture_dump(stderr, "#### post_remove_epsilons", nfa);
#endif

	res = 1;
cleanup:
	if (eclosures != NULL) {
		closure_free(eclosures, state_count);
	}

	return res;
}

#define DEF_EDGES_CEIL 4

struct ee_cache {
	unsigned ceil;
	unsigned used;
	struct ee_edges {
		fsm_state_t to;
		fsm_end_id_t id;
	} *edges;
};

#define DEF_STATE_STACK_CEIL 8
#define DEF_DATA_STACK_CEIL 4

struct ee_cache_env {
	bool ok;
	struct fsm *nfa;
	struct ee_cache **cache;

	struct state_set **eclosures;

	/* Start state for all the epsilon closure paths being analyzed. */
	fsm_state_t start_of_path;

	struct ee_stack {
		struct ee_state_stack {
			unsigned ceil;
			unsigned used;
			struct ee_state_stack_frame {
				/* fsm_state_t labeled_edge_from; */
				fsm_state_t state;
				unsigned id_count; /* how many IDs were pushed on the data stack */
			} *frames;
		} state;

		struct ee_data_stack {
			unsigned ceil;
			unsigned used;
			struct ee_data_stack_frame {
				fsm_end_id_t id;
			} *frames;
		} data;
	} stack;
};

static int
save_edges_cb(fsm_state_t from, fsm_state_t to, fsm_end_id_t id, void *opaque)
{
	LOG(1, "%s: from %d, to %d, id %d\n", __func__, from, to, id);

	struct ee_cache_env *env = opaque;
	if (env->cache[from] == NULL) {
		struct ee_cache *c = f_calloc(env->nfa->alloc, 1, sizeof(*c));
		if (c == NULL) { goto fail; }

		struct ee_edges *edges = f_calloc(env->nfa->alloc, DEF_EDGES_CEIL, sizeof(edges[0]));
		if (edges == NULL) {
			f_free(env->nfa->alloc, c);
			goto fail;
		}

		c->edges = edges;
		c->ceil = DEF_EDGES_CEIL;
		env->cache[from] = c;
	}

	struct ee_cache *c = env->cache[from];
	if (c->used == c->ceil) {
		const size_t nceil = 2*c->ceil;
		struct ee_edges *nedges = f_realloc(env->nfa->alloc, c->edges,
		    nceil * sizeof(nedges[0]));
		if (nedges == NULL) { goto fail; }

		c->edges = nedges;
		c->ceil = nceil;
	}

	struct ee_edges *e = &c->edges[c->used];
	e->to = to;
	e->id = id;
	c->used++;
	return 1;

fail:
	env->ok = false;
	return 0;
}

/* These macros just exist so logging can use __func__ and __LINE__. */
#define MARK_VISITED(NFA, S_ID)						\
	do {								\
		LOG(1, "%s(%d): marking visited: %d\n",			\
		    __func__, __LINE__, S_ID);				\
		NFA->states[S_ID].visited = 1;				\
	} while(0)

#define CLEAR_VISITED(NFA, S_ID)					\
	do {								\
		LOG(1, "%s(%d): clearing visited: %d\n",		\
		    __func__, __LINE__, S_ID);				\
		NFA->states[S_ID].visited = 0;				\
	} while(0)

/* For every state, mark every state reached by a labeled edge as
 * reachable. This doesn't check that the FROM state is reachable from
 * the start state (trim will do that soon enough), it's just used to
 * check which states will become unreachable once epsilon edges are
 * removed. We don't need to add eager endids for them, because they
 * will soon be disconnected from the epsilon-free NFA. */
static void
mark_states_reachable_by_label(const struct fsm *nfa, uint64_t *reachable_by_label)
{
	fsm_state_t start;
	if (!fsm_getstart(nfa, &start)) {
		return;		/* nothing reachable */
	}
	u64bitset_set(reachable_by_label, start);

	const fsm_state_t state_count = fsm_countstates(nfa);

	for (size_t s_i = 0; s_i < state_count; s_i++) {
		struct edge_group_iter egi;
		struct edge_group_iter_info info;

		struct fsm_state *s = &nfa->states[s_i];

		/* Clear the visited flag, it will be used to avoid cycles. */
#if 1
		assert(s->visited == 0); /* stale */
#endif
		s->visited = 0;

		edge_set_group_iter_reset(s->edges, EDGE_GROUP_ITER_ALL, &egi);
		while (edge_set_group_iter_next(&egi, &info)) {
			LOG(1, "%s: reachable: %d\n", __func__, info.to);
			u64bitset_set(reachable_by_label, info.to);
		}
	}
}

static bool
remap_eager_endids__push_state_stack(struct ee_cache_env *env, /*fsm_state_t labeled_edge_from, */ fsm_state_t s_id)
{
	LOG(1, "%s: s_id %d\n", __func__, s_id);
	struct ee_state_stack *sstack = &env->stack.state;
	if (sstack->used == sstack->ceil) {
		const size_t nceil = sstack->ceil == 0
		    ? DEF_STATE_STACK_CEIL
		    : 2*sstack->ceil;
		struct ee_state_stack_frame *nframes = f_realloc(env->nfa->alloc,
		    sstack->frames, nceil * sizeof(nframes[0]));
		if (nframes == NULL) { return false; }

		sstack->ceil = nceil;
		sstack->frames = nframes;
	}

	struct ee_state_stack_frame *f = &sstack->frames[sstack->used];
	/* f->labeled_edge_from = labeled_edge_from; */
	f->state = s_id;
	f->id_count = 0;
	sstack->used++;
	return true;
}

static bool
remap_eager_endids__pop_state_stack(struct ee_cache_env *env, /*fsm_state_t *labeled_edge_from, */ fsm_state_t *state_id, unsigned *id_count)
{
	struct ee_state_stack *sstack = &env->stack.state;
	if (sstack->used == 0) { return false; }

	sstack->used--;
	struct ee_state_stack_frame *f = &sstack->frames[sstack->used];
	/* *labeled_edge_from = f->labeled_edge_from; */
	*state_id = f->state;
	*id_count = f->id_count;
	// labeled_edge_from %d, , *labeled_edge_from
	LOG(1, "%s: => state_id %d, id_count %d\n", __func__, *state_id, *id_count);
	return true;
}

static bool
remap_eager_endids__push_data_stack(struct ee_cache_env *env, fsm_end_id_t id)
{
	LOG(1, "%s: id %d\n", __func__, id);
	struct ee_data_stack *dstack = &env->stack.data;
	if (dstack->used == dstack->ceil) {
		const size_t nceil = dstack->ceil == 0
		    ? DEF_STATE_STACK_CEIL
		    : 2*dstack->ceil;
		struct ee_data_stack_frame *nframes = f_realloc(env->nfa->alloc,
		    dstack->frames, nceil * sizeof(nframes[0]));
		if (nframes == NULL) { return false; }

		dstack->ceil = nceil;
		dstack->frames = nframes;
	}

	struct ee_data_stack_frame *f = &dstack->frames[dstack->used];
	f->id = id;
	dstack->used++;

	struct ee_state_stack *sstack = &env->stack.state;
	assert(sstack->used > 0);
	sstack->frames[sstack->used - 1].id_count++;

	return true;
}

static bool
remap_eager_endids__pop_data_stack(struct ee_cache_env *env, unsigned id_count)
{
	if (id_count > 0) {
		LOG(1, "%s: count %d\n", __func__, id_count);
	}

	struct ee_data_stack *dstack = &env->stack.data;
	if (dstack->used < id_count) { return false; }

	dstack->used -= id_count;
	return true;
}

static int
push_on_data_stack_cb(fsm_state_t from, fsm_state_t to, fsm_end_id_t id, void *opaque)
{
	struct ee_cache_env *env = opaque;

	if (from != to) {	/* ignore self-edges, because they're always skippable */
		if (!remap_eager_endids__push_data_stack(env, id)) {
			env->ok = false;
			return 0;
		}
	}
	return 1;
}

static bool
remap_eager_endids__push_any_endids_on_epsilon_edge(struct ee_cache_env *env, fsm_state_t from, fsm_state_t to)
{
	fsm_eager_endid_iter_edges_between_states(env->nfa, from, to, push_on_data_stack_cb, env);
	return env->ok;
}

static bool
collect_labeled_endid_edges(struct ee_cache_env *env, fsm_state_t from, fsm_state_t to, size_t *count)
{
	*count = 0;
	const unsigned used_before = env->stack.data.used;
	fsm_eager_endid_iter_edges_between_states(env->nfa, from, to, push_on_data_stack_cb, env);
	if (env->ok) {
		*count = env->stack.data.used - used_before;
		LOG(1, "%s: collected %zd\n", __func__, *count);
	}

	return env->ok;
}

struct after_labeled_edge_info {
	fsm_state_t from;
	fsm_state_t to;
	unsigned data_stack_floor;
};

/* For each state, step through its epsilon closure and remap eager endid edge metadata to any new
 * labeled edges that have been added to the state. A stack is used to track edge metadata on the path
 * between the original state and states in the epsilon closure with labeled edges. The states' visited
 * flag is used to avoid cycles.
 *
 * - s_id: The current state being evaluated.
 *
 * - after_labeled_edge_info: FIXME
 * */
static bool
remap_eager_endids__step_for_state(struct ee_cache_env *env, fsm_state_t s_id,
    struct after_labeled_edge_info *after_labeled_edge_info)
{
	struct state_iter eps_iter;
	fsm_state_t eps_id;

	LOG(1, "%s: s_id %d\n", __func__, s_id);

	if (LOG_LEVEL > 0) {
		fprintf(stderr, "%s: current stacks:\n", __func__);
		for (size_t i = 0; i < env->stack.state.used; i++) {
			fprintf(stderr, "-- state %zd: id %d, count %u\n",
			    i,
			    //env->stack.state.frames[i].labeled_edge_from,
			    env->stack.state.frames[i].state, env->stack.state.frames[i].id_count);
		}
		for (size_t i = 0; i < env->stack.data.used; i++) {
			fprintf(stderr, "-- data %zd: %d\n", i, env->stack.data.frames[i].id);
		}
	}

	/* Explore each non-visited epsilon edge, pushing any edges with
	 * eager endid metadata to the stack. */
	/* state_set_reset(env->eclosures[s_id], &eps_iter); */
	const struct state_set *epsilons = env->nfa->states[s_id].epsilons;
	state_set_reset(epsilons, &eps_iter);
	LOG(1, "-- %s: checking epsilon edges on %d\n", __func__, s_id);
	while (state_set_next(&eps_iter, &eps_id)) {
		LOG(1, "%s: state_set_next s_id %d => eps_id %d\n", __func__, s_id, eps_id);
		struct fsm_state *es = &env->nfa->states[eps_id];
		if (es->visited) {
			LOG(1, "%s: already visited %d, skipping\n", __func__, eps_id);
			continue;
		}
		MARK_VISITED(env->nfa, eps_id);

		if (!remap_eager_endids__push_state_stack(env, s_id)) {
			LOG(0, "%s %d: returning false\n", __func__, __LINE__);
			return false;
		}

		/* If there is any endid edge metadata on this epsilon edge, save it
		 * on the stack, so it can be added to labeled edges later. */
	        if (!remap_eager_endids__push_any_endids_on_epsilon_edge(env, s_id, eps_id)) {
			LOG(0, "%s %d: returning false\n", __func__, __LINE__);
			return false;
		}

		if (!remap_eager_endids__step_for_state(env, eps_id, after_labeled_edge_info)) {
			LOG(0, "%s %d: returning false\n", __func__, __LINE__);
			return false;
		}

		fsm_state_t popped_s_id;
		unsigned id_count;
		if (!remap_eager_endids__pop_state_stack(env, &popped_s_id, &id_count)) {
			LOG(0, "%s %d: returning false\n", __func__, __LINE__);
			return false;
		}
		assert(popped_s_id == s_id);

		if (!remap_eager_endids__pop_data_stack(env, id_count)) {
			LOG(0, "%s %d: returning false\n", __func__, __LINE__);
			return false;
		}

		assert(es->visited);
		CLEAR_VISITED(env->nfa, eps_id);
	}

	/* For every end state EcS in the epsilon closure of the current state S
	 * where S is an end state
	 * directly after a labeled edge Prev->S
	 *
	 * for every eager endid edge (X->Y, Id) in the epsilon closure between S and EcS
	 *
	 * add an eager endid edge (Prev -> S, Id)
	 * */
	if (after_labeled_edge_info != NULL && fsm_isend(env->nfa, s_id)) {
		LOG(1, "%s: after_labeled_edge_info && is_end, data_stack_floor %d now %d\n",
		    __func__, after_labeled_edge_info->data_stack_floor, env->stack.data.used);

		for (size_t i = after_labeled_edge_info->data_stack_floor; i < env->stack.data.used; i++) {
			const fsm_end_id_t id = env->stack.data.frames[i].id;
			LOG(1, "%s: adding eager endid md for edge (%d -> %d, %d) in epsilon closure between labeled edge and end\n",
			    __func__, after_labeled_edge_info->from, after_labeled_edge_info->to, id);
			if (!fsm_eager_endid_insert_entry(env->nfa,
				after_labeled_edge_info->from, after_labeled_edge_info->to, id)) {
				LOG(0, "%s %d: returning false\n", __func__, __LINE__);
				return false;
			}
		}
	}

	if (after_labeled_edge_info != NULL) {
		LOG(1, "%s: after_labeled_edge_info != NULL, skipping labeled edge checks on %d\n", __func__, s_id);
		return true;
	}

	/* For each labeled edge (s_id -> Dst):
	 * - If there is an endid edge (s_id -> Dst, Id), add an endid edge (env->start_of_path -> Dst, Id)
	 * - For every id X on the data stack, add an endid edge (env->start_of_path -> Dst, X)
	 *  */
	struct edge_group_iter egi;
	struct edge_group_iter_info info;
	LOG(1, "-- %s: checking labeled edges on %d\n", __func__, s_id);
	edge_set_group_iter_reset(env->nfa->states[s_id].edges, EDGE_GROUP_ITER_ALL, &egi);
	while (edge_set_group_iter_next(&egi, &info)) {
		const size_t used_before = env->stack.data.used;
		const fsm_state_t dst = info.to;

		LOG(1, "%s: edge_set_group_iter_next => %d -> dst %d\n", __func__, s_id, dst);

		/* Collect any eager endids associated with this labeled edge on the data stack. */
		size_t endid_labeled_edges;
		assert(env->ok);
		if (!collect_labeled_endid_edges(env, s_id, dst, &endid_labeled_edges)) {
			LOG(0, "%s %d: returning false\n", __func__, __LINE__);
			return false;
		}

		/* If the destination state for the labeled edge is an end state (because
		 * the first phase of epsilon removal processing has carried any end-state-ness
		 * forward from its epsilon closure), then copy any eager endid metadata that
		 * appears on epsilon edges within its epsilon closure to the labeled edge. */
		if (fsm_isend(env->nfa, dst)) {
			/* Continue exploring (only) the epsilon closure after the labeled
			 * edge, so that this labeled edge can be associated with any
			 * eager endids on epsilon edges that lead to an end state. */
			struct after_labeled_edge_info labeled_edge = {
				.from = s_id,
				.to = dst,
				.data_stack_floor = env->stack.data.used,
			};

			LOG(0, "-- %s: %d is an end state, explore its epsilon closure, labeled_edge { from = %d, to = %d, data_stack_floor = %d } \n",
			    __func__, dst, labeled_edge.from, labeled_edge.to, labeled_edge.data_stack_floor);

			if (!remap_eager_endids__step_for_state(env, dst, &labeled_edge)) {
				LOG(0, "%s %d: returning false\n", __func__, __LINE__);
				return false;
			}

			/* Drop the data stack back to where it was before. */
			const size_t new_discoveries = env->stack.data.used - labeled_edge.data_stack_floor;
			LOG(0, "%s: dropping %zd new_discoveries\n", __func__, new_discoveries);
			if (!remap_eager_endids__pop_data_stack(env, new_discoveries)) {
				LOG(0, "%s %d: returning false\n", __func__, __LINE__);
				return false;
			}

		}

		const size_t used_after = env->stack.data.used;

		LOG(1, "### endid_labeled_edges %zd, used_before %zd, used_after %zd\n",
		    endid_labeled_edges, used_before, used_after);
		assert(used_before == used_after - endid_labeled_edges);

		/* Now that iteration is done, add the collected edges. */
		for (size_t i = 0; i < endid_labeled_edges; i++) {
			LOG(1, "%s: adding labeled edge (%d -> %d, %d)\n",
			    __func__, env->start_of_path, dst, env->stack.data.frames[used_before + i].id);
			if (!fsm_eager_endid_insert_entry(env->nfa,
				env->start_of_path, dst, env->stack.data.frames[used_before + i].id)) {
				LOG(0, "%s %d: returning false\n", __func__, __LINE__);
				return false;
			}
		}

		/* Drop the data stack back to where it was before. */
		if (!remap_eager_endids__pop_data_stack(env, endid_labeled_edges)) {
			LOG(0, "%s %d: returning false\n", __func__, __LINE__);
			return false;
		}

		/* Add any other eager endid IDs on the data stack, these represent edges passed
		 * through as the transitive closure's epsilon edges were collapsed into a
		 * single labeled edge.
		 *
		 * (This could be done by iterating over the entire data stack before dropping
		 * the labeled edge endids, rather than adding the labeled and epsilon edges'
		 * endids separately.) */
		for (size_t i = 0; i < env->stack.data.used; i++) {
			LOG(1, "%s: adding intermediate epsilon edge (%d -> %d, %d)\n",
			    __func__, env->start_of_path, dst, env->stack.data.frames[i].id);
			if (!fsm_eager_endid_insert_entry(env->nfa,
				env->start_of_path, dst, env->stack.data.frames[i].id)) {
				LOG(0, "%s %d: returning false\n", __func__, __LINE__);
				return false;
			}
		}
	}

	return true;
}

/* This could potentially be integrated into epsilon_closure_single. */
static int
remap_eager_endids(struct fsm *nfa, struct state_set **eclosures)
{
	if (!fsm_eager_endid_has_eager_endids(nfa)) {
		return 1;	/* nothing to do */
	}

	fprintf(stderr, "%s\n", __func__);

	const fsm_state_t state_count = fsm_countstates(nfa);
	const size_t state_words = u64bitset_words(state_count);
	int res = 0;

	struct ee_cache **cache = NULL;
	uint64_t *ends = NULL;
	uint64_t *enqueued = NULL;
	uint64_t *reachable_by_label = NULL;

	ends = f_calloc(nfa->alloc, state_words, sizeof(ends[0]));
	if (ends == NULL) { goto cleanup; }

	enqueued = f_calloc(nfa->alloc, state_words, sizeof(enqueued[0]));
	if (enqueued == NULL) { goto cleanup; }

	cache = f_calloc(nfa->alloc, state_count, sizeof(*cache));
	if (cache == NULL) { goto cleanup; }

	reachable_by_label = f_calloc(nfa->alloc, state_words, sizeof(reachable_by_label[0]));
	if (reachable_by_label == NULL) { goto cleanup; }

	INIT_TIMERS();

	TIME(&pre);
	mark_states_reachable_by_label(nfa, reachable_by_label);
	TIME(&post);
	DIFF_MSEC("epsilon_mark_states_reachable_by_label", pre, post, NULL);

	struct ee_cache_env env = {
		.ok = true,
		.nfa = nfa,
		.cache = cache,
		.eclosures = eclosures,
	};

	/* First pass: build edge cache. This avoids a great deal of redundant lookup. */
	for (fsm_state_t s_id = 0; s_id < state_count; s_id++) {
		const struct fsm_state *s = &nfa->states[s_id];
		if (!s->has_eager_endids) { continue; }

		fsm_eager_endid_iter_edges_from_state(nfa, s_id, save_edges_cb, &env);
		if (!env.ok) { goto cleanup; }
	}

	/* dump cache */
	if (false) {
		fprintf(stderr, "# caches:\n");
		for (fsm_state_t s_id = 0; s_id < state_count; s_id++) {
			const struct ee_cache *c = cache[s_id];
			if (c == NULL) { continue; }
			for (size_t i = 0; i < c->used; i++) {
				fprintf(stderr, "-- %d -> %d: %d\n",
				    s_id, c->edges[i].to, c->edges[i].id);
			}
		}
	}

	/* For each state, carry over eager endid edge metadata from its epsilon closure.
	 * The state order in which this happens shouldn't matter, but it depends on the
	 * previous epsilon removal pass carrying end-ness around. */
	for (fsm_state_t s_id = 0; s_id < state_count; s_id++) {
		/* must start and finish with empty stacks */
		assert(env.stack.state.used == 0);
		assert(env.stack.data.used == 0);

		if (!u64bitset_get(reachable_by_label, s_id)) {
			LOG(1, "\n%s: skipping state not directly reachable by label: %d\n", __func__, s_id);
			continue;
		}

		LOG(1, "\n%s: start_of_path = %d\n", __func__, s_id);
		assert(nfa->states[s_id].visited == 0);
		MARK_VISITED(nfa, s_id);

		env.start_of_path = s_id;

		if (!remap_eager_endids__step_for_state(&env, s_id, NULL)) {
			goto cleanup;
		}

		CLEAR_VISITED(nfa, s_id);

		assert(env.stack.state.used == 0);
		assert(env.stack.data.used == 0);
	}

	res = 1;
	LOG(0, "%s: finishing up... [[\n", __func__);
	fsm_eager_endid_dump(stderr, nfa);
	LOG(0, "]]\n");

cleanup:
	f_free(nfa->alloc, ends);
	f_free(nfa->alloc, enqueued);
	f_free(nfa->alloc, reachable_by_label);

	if (cache != NULL) {
		for (size_t i = 0; i < state_count; i++) {
			if (cache[i] == NULL) { continue; }
			f_free(nfa->alloc, cache[i]->edges);
			f_free(nfa->alloc, cache[i]);
		}
	}
	f_free(nfa->alloc, cache);

	for (size_t s_i = 0; s_i < state_count; s_i++) {
		if (res == 1) {
			/* These should be cleared during normal
			 * operation, but may remain set on error. */
			assert(nfa->states[s_i].visited == 0);
		}
		nfa->states[s_i].visited = 0;
	}

	return res;
}

static int
remap_capture_actions(struct fsm *nfa, struct state_set **eclosures)
{
	int res = 0;
	fsm_state_t s, i;
	struct state_set **rmap;
	struct state_iter si;
	fsm_state_t si_s;
	struct remap_env env = { 'R', NULL, NULL, 1, 0, 0, NULL };
	env.alloc = nfa->alloc;

	/* build a reverse mapping */
	rmap = f_calloc(nfa->alloc, nfa->statecount, sizeof(rmap[0]));
	if (rmap == NULL) {
		goto cleanup;
	}

	for (s = 0; s < nfa->statecount; s++) {
		if (eclosures[s] == NULL) { continue; }
		for (state_set_reset(eclosures[s], &si); state_set_next(&si, &si_s); ) {
			if (si_s == s) {
				continue; /* ignore identical states */
			}
#if LOG_RM_EPSILONS_CAPTURES
			fprintf(stderr, "remap_capture_actions: %u <- %u\n",
			    s, si_s);
#endif
			if (!state_set_add(&rmap[si_s], nfa->alloc, s)) {
				goto cleanup;
			}
		}
	}
	env.rmap = rmap;

	/* Iterate over the current set of actions with the reverse
	 * mapping (containing only states which will be skipped,
	 * collecting info about every new capture action that will need
	 * to be added.
	 *
	 * It can't be added during the iteration, because that would
	 * modify the hash table as it's being iterated over. */
	fsm_capture_action_iter(nfa, remap_capture_action_cb, &env);

	/* Now that we're done iterating, add those actions. */
	for (i = 0; i < env.count; i++) {
		const struct remap_action *a = &env.actions[i];
		if (!fsm_capture_add_action(nfa, a->state, a->type,
			a->capture_id, a->to)) {
			goto cleanup;
		}
	}

	res = 1;

cleanup:
	if (env.actions != NULL) {
		f_free(nfa->alloc, env.actions);
	}

	if (rmap != NULL) {
		for (i = 0; i < nfa->statecount; i++) {
			state_set_free(rmap[i]);
		}
		f_free(nfa->alloc, rmap);
	}
	return res;

}

static int
add_pending_capture_action(struct remap_env *env,
    fsm_state_t state, enum capture_action_type type,
    unsigned capture_id, fsm_state_t to)
{
	struct remap_action *a;
	if (env->count == env->ceil) {
		struct remap_action *nactions;
		const size_t nceil = (env->ceil == 0
		    ? DEF_PENDING_CAPTURE_ACTIONS_CEIL : 2*env->ceil);
		assert(nceil > 0);
		nactions = f_realloc(env->alloc,
		    env->actions,
		    nceil * sizeof(nactions[0]));
		if (nactions == NULL) {
			return 0;
		}

		env->ceil = nceil;
		env->actions = nactions;
	}

	a = &env->actions[env->count];
#if LOG_RM_EPSILONS_CAPTURES
	fprintf(stderr, "add_pending_capture_action: state %d, type %s, capture_id %u, to %d\n",
	    state, fsm_capture_action_type_name[type], capture_id, to);
#endif

	a->state = state;
	a->type = type;
	a->capture_id = capture_id;
	a->to = to;
	env->count++;
	return 1;
}

static int
remap_capture_action_cb(fsm_state_t state,
    enum capture_action_type type, unsigned capture_id, fsm_state_t to,
    void *opaque)
{
	struct state_iter si;
	fsm_state_t si_s;
	struct remap_env *env = opaque;
	assert(env->tag == 'R');

#if LOG_RM_EPSILONS_CAPTURES
	fprintf(stderr, "remap_capture_action_cb: state %d, type %s, capture_id %u, to %d\n",
	    state, fsm_capture_action_type_name[type], capture_id, to);
#endif

	for (state_set_reset(env->rmap[state], &si); state_set_next(&si, &si_s); ) {
		struct state_iter si_to;
		fsm_state_t si_tos;

#if LOG_RM_EPSILONS_CAPTURES
		fprintf(stderr, " -- rcac: state %d -> %d\n", state, si_s);
#endif

		if (!add_pending_capture_action(env, si_s, type, capture_id, to)) {
			goto fail;
		}

		if (to == CAPTURE_NO_STATE) {
			continue;
		}

		for (state_set_reset(env->rmap[to], &si_to); state_set_next(&si, &si_tos); ) {
#if LOG_RM_EPSILONS_CAPTURES
			fprintf(stderr, " -- rcac:     to %d -> %d\n", to, si_tos);
#endif

			if (!add_pending_capture_action(env, si_tos, type, capture_id, to)) {
				goto fail;
			}

		}
	}

	return 1;

fail:
	env->ok = 0;
	return 0;
}

struct collect_env {
	char tag;
	const struct fsm_alloc *alloc;
	size_t count;
	size_t ceil;
	fsm_end_id_t *ids;
	int ok;
};

static int
collect_cb(fsm_state_t state, fsm_end_id_t id, void *opaque)
{
	struct collect_env *env = opaque;
	assert(env->tag == 'E');

	(void)state;

	if (env->count == env->ceil) {
		const size_t nceil = 2 * env->ceil;
		fsm_end_id_t *nids;
		assert(nceil > env->ceil);
		nids = f_realloc(env->alloc, env->ids,
		    nceil * sizeof(*env->ids));
		if (nids == NULL) {
			env->ok = 0;
			return 0;
		}
		env->ceil = nceil;
		env->ids = nids;
	}

	env->ids[env->count] = id;
	env->count++;

	return 1;
}

/* fsm_remove_epsilons can't use fsm_endid_carry directly, because the src
 * and dst FSMs are the same -- that would lead to adding entries to a
 * hash table, possibly causing it to resize, while iterating over it.
 *
 * Instead, collect entries that need to be added (if not already
 * present), and then add them in a second pass. */
static int
carry_endids(struct fsm *fsm, struct state_set *states,
    fsm_state_t dst_state)
{
	struct state_iter it;
	fsm_state_t s;
	size_t i;

	struct collect_env env;
	env.tag = 'E';		/* for fsm_remove_epsilons */
	env.alloc = fsm->alloc;
	env.count = 0;
	env.ceil = DEF_CARRY_ENDIDS_COUNT;
	env.ids = f_malloc(fsm->alloc,
	    env.ceil * sizeof(*env.ids));
	if (env.ids == NULL) {
		return 0;
	}
	env.ok = 1;

	fsm_eager_endid_dump(stderr, fsm);

	/* collect from states */
	for (state_set_reset(states, &it); state_set_next(&it, &s); ) {
		if (!fsm_isend(fsm, s)) {
			continue;
		}

		fsm_endid_iter_state(fsm, s, collect_cb, &env);
		if (!env.ok) {
			goto cleanup;
		}
	}

	/* add them */
	for (i = 0; i < env.count; i++) {
		if (!fsm_endid_set(fsm, dst_state, env.ids[i])) {
			env.ok = 0;
			goto cleanup;
		}
	}

cleanup:
	f_free(fsm->alloc, env.ids);

	return env.ok;
}
