/*
 * Copyright 2019 Katherine Flavel
 *
 * See LICENCE for the full copyright terms.
 */

#include "determinise_internal.h"

#define LOG_DETERMINISATION_COUNTERS 0

static void
dump_labels(FILE *f, const uint64_t labels[4])
{
	size_t i;
	for (i = 0; i < 256; i++) {
		if (u64bitset_get(labels, i)) {
			fprintf(f, "%c", (char)(isprint(i) ? i : '.'));
		}
	}
}

int
fsm_determinise(struct fsm *nfa)
{
	int res = 0;
	struct mappingstack *stack = NULL;

	struct interned_state_set_pool *issp = NULL;
	struct map map = { NULL, 0, 0, NULL };
	struct mapping *curr = NULL;
	size_t dfacount = 0;

	struct analyze_closures_env ac_env = { 0 };
	INIT_TIMERS();
	INIT_TIMERS_NAMED(overall);

	assert(nfa != NULL);
	map.alloc = nfa->opt->alloc;

	/*
	 * This NFA->DFA implementation is for Glushkov NFA only; it keeps things
	 * a little simpler by avoiding epsilon closures here, and also a little
	 * faster where we can start with a Glushkov NFA in the first place.
	 */
	if (fsm_has(nfa, fsm_hasepsilons)) {
		TIME(&pre);
		if (!fsm_remove_epsilons(nfa)) {
			return 0;
		}
		TIME(&post);
		DIFF_MSEC("det_remove_eps", pre, post, NULL);
	}

#if LOG_DETERMINISE_CAPTURES
	fprintf(stderr, "# pre_determinise\n");
	fsm_print_fsm(stderr, nfa);
	fsm_capture_dump(stderr, "#### post_remove_epsilons", nfa);
#endif
	TIME(&overall_pre);

	issp = interned_state_set_pool_alloc(nfa->opt->alloc);
	if (issp == NULL) {
		return 0;
	}

	{
		fsm_state_t start;
		interned_state_set_id start_set;

		/*
		 * The starting condition is the epsilon closure of a set of states
		 * containing just the start state.
		 *
		 * You can think of this as having reached the FSM's start state by
		 * previously consuming some imaginary prefix symbol (giving the set
		 * containing just the start state), and then this epsilon closure
		 * is equivalent to the usual case of taking the epsilon closure after
		 * each symbol closure in the main loop.
		 *
		 * (We take a copy of this set for sake of memory ownership only,
		 * for freeing the epsilon closures later).
		 */

		if (!fsm_getstart(nfa, &start)) {
			res = 1;
			goto cleanup;
		}

#if LOG_DETERMINISE_CAPTURES
		fprintf(stderr, "#### Adding mapping for start state %u -> 0\n", start);
#endif
		if (!interned_state_set_intern_set(issp, 1, &start, &start_set)) {
			goto cleanup;
		}

		if (!map_add(&map, dfacount, start_set, &curr)) {
			goto cleanup;
		}
		dfacount++;
	}

	/*
	 * Our "todo" list. It needn't be a stack; we treat it as an unordered
	 * set where we can consume arbitrary items in turn.
	 */
	stack = stack_init(nfa->opt->alloc);
	if (stack == NULL) {
		goto cleanup;
	}

	ac_env.alloc = nfa->opt->alloc;
	ac_env.fsm = nfa;
	ac_env.issp = issp;

#if LOG_DETERMINISATION_STATS
	fprintf(stderr, "%s: determinising FSM with %d states\n", __func__, fsm_countstates(nfa));
#endif

	INIT_TIMERS_NAMED(iss);
	size_t iss_accum = 0;
	size_t iss_calls = 0;
	size_t stack_pushes = 0;
	size_t inner_steps = 0;

	TIME(&pre);
	do {
		size_t o_i;

#if LOG_SYMBOL_CLOSURE
		fprintf(stderr, "\nfsm_determinise: current dfacount %lu...\n",
		    dfacount);
#endif

		assert(curr != NULL);

		/* FIXME Essentially all the time in determinization is spent in
		 * here, most calls individually finish quickly but there are many. */
		TIME(&iss_pre);
		if (!analyze_closures_for_iss(&ac_env, curr->iss)) {
			goto cleanup;
		}
		TIME(&iss_post);
		DIFF_MSEC("det_iss", iss_pre, iss_post, &iss_accum);
		(void)iss_accum;
		iss_calls++;

		if (!edge_set_advise_growth(&curr->edges, nfa->opt->alloc, ac_env.output_count)) {
			goto cleanup;
		}

		/* each output is an outgoing (label set) -> interned_state_set pair */
		for (o_i = 0; o_i < ac_env.output_count; o_i++) {
			struct mapping *m;
			struct ac_output *output = &ac_env.outputs[o_i];
			interned_state_set_id iss = output->iss;
			inner_steps++;

#if LOG_DETERMINISE_CLOSURES
			fprintf(stderr, "fsm_determinise: cur (dfa %zu) label [", curr->dfastate);
			dump_labels(stderr, output->labels);
			fprintf(stderr, "] -> iss:%ld: ", output->iss);
			interned_state_set_dump(stderr, issp, output->iss);
			fprintf(stderr, "\n");
#endif

			/*
			 * The set of NFA states output->iss represents a single DFA state.
			 * We use the mappings as a de-duplication mechanism, keyed by the
			 * set of NFA states.
			 */

			/* If this interned_state_set isn't present, then save it as a new mapping.
			 * This is the interned set of states that the current ac_output (set of
			 * labels) leads to. */
			if (map_find(&map, iss, &m)) {
				/* we already have this closure interned, so reuse it */
				assert(m->dfastate < dfacount);
			} else {
				/* not found -- add a new one and push it to the stack for processing */
				if (!map_add(&map, dfacount, iss, &m)) {
					goto cleanup;
				}
				dfacount++;
				if (!stack_push(stack, m)) {
					goto cleanup;
				}
				stack_pushes++;
			}

#if LOG_SYMBOL_CLOSURE
			fprintf(stderr, "fsm_determinise: adding labels [");
			dump_labels(stderr, output->labels);
			fprintf(stderr, "] -> dfastate %zu on output state %zu\n", m->dfastate, curr->dfastate);
#endif

			if (!edge_set_add_bulk(&curr->edges, nfa->opt->alloc, output->labels, m->dfastate)) {
				goto cleanup;
			}
		}

		ac_env.output_count = 0;

		/* All elements in sclosures[] are interned, so they will be freed later. */
	} while ((curr = stack_pop(stack)));
	TIME(&post);
	DIFF_MSEC("det_stack_loop", pre, post, NULL);

	if (LOG_DETERMINISATION_COUNTERS) {
		fprintf(stderr, "%s: iss_accum total %zu (%zu calls, %g usec avg.), %zu stack pushes, %zu iterations, %zu inner_steps\n",
		    __func__, iss_accum, iss_calls, iss_accum / (1.0 * iss_calls), stack_pushes, iss_calls, inner_steps);
	}

	{
		struct map_iter it;
		struct mapping *m;
		struct fsm *dfa;

		dfa = fsm_new(nfa->opt);
		if (dfa == NULL) {
			goto cleanup;
		}

		TIME(&pre);
		if (!fsm_capture_copy_programs(nfa, dfa)) {
			goto cleanup;
		}
		TIME(&post);
		DIFF_MSEC("det_copy_captures", pre, post, NULL);

#if DUMP_MAPPING
		{
			fprintf(stderr, "#### fsm_determinise: mapping\n");

			/* build reverse mappings table: for every NFA state X, if X is part
			 * of the new DFA state Y, then add Y to a list for X */
			for (m = map_first(&map, &it); m != NULL; m = map_next(&it)) {
				interned_state_set_id iss_id = m->iss;
				struct state_iter si;
				fsm_state_t state;
				struct state_set *ss = interned_state_set_get_state_set(issp, iss_id);
				fprintf(stderr, "%zu:", m->dfastate);

				for (state_set_reset(ss, &si); state_set_next(&si, &state); ) {
					fprintf(stderr, " %u", state);
				}
				fprintf(stderr, "\n");
			}
			fprintf(stderr, "#### fsm_determinise: end of mapping\n");
		}
#endif
		if (!fsm_addstate_bulk(dfa, dfacount)) {
			goto cleanup;
		}

		assert(dfa->statecount == dfacount);

		/*
		 * We know state 0 is the start state, because its mapping
		 * was created first.
		 */
		fsm_setstart(dfa, 0);

		TIME(&pre);
		for (m = map_first(&map, &it); m != NULL; m = map_next(&it)) {
			struct state_set *ss;
			interned_state_set_id iss_id = m->iss;
			assert(m->dfastate < dfa->statecount);
			assert(dfa->states[m->dfastate].edges == NULL);

			dfa->states[m->dfastate].edges = m->edges;

			/*
			 * The current DFA state is an end state if any of its associated NFA
			 * states are end states.
			 */
			ss = interned_state_set_get_state_set(ac_env.issp, iss_id);
			if (!state_set_has(nfa, ss, fsm_isend)) {
				continue;
			}

			fsm_setend(dfa, m->dfastate, 1);

			/*
			 * Copy over metadata associated with end
			 * states, if present. This isn't anything to do
			 * with the DFA conversion; it's meaningful only
			 * to the caller.
			 *
			 * The closure may contain non-end states, but at least one state is
			 * known to have been an end state.
			 */
			if (!remap_end_metadata(nfa, ss, dfa, m->dfastate)) {
				goto cleanup;
			}
		}
		TIME(&post);
		DIFF_MSEC("det_map_loop", pre, post, NULL);

		fsm_capture_integrity_check(dfa);

		fsm_move(nfa, dfa);
	}

#if LOG_DETERMINISE_CAPTURES
	fprintf(stderr, "# post_determinise\n");
	fsm_print_fsm(stderr, nfa);
	fsm_capture_dump(stderr, "#### post_determinise", nfa);
#endif

	TIME(&overall_post);
	DIFF_MSEC("det_overall", overall_pre, overall_post, NULL);

#if LOG_DETERMINISATION_STATS
	fprintf(stderr, "%s: created DFA with %d states\n", __func__, fsm_countstates(nfa));
	fprintf(stderr, "%s: analyze_closures_env.analyze_usec: %zu\n",
	    __func__, ac_env.analyze_usec);
#endif

	res = 1;

cleanup:
	map_free(&map);
	stack_free(stack);
	interned_state_set_pool_free(issp);

	if (ac_env.iters != NULL) {
		f_free(ac_env.alloc, ac_env.iters);
	}
	if (ac_env.groups != NULL) {
		f_free(ac_env.alloc, ac_env.groups);
	}
	if (ac_env.outputs != NULL) {
		f_free(ac_env.alloc, ac_env.outputs);
	}
	if (ac_env.dst != NULL) {
		f_free(ac_env.alloc, ac_env.dst);
	}
	if (ac_env.pq != NULL) {
		ipriq_free(ac_env.pq);
	}
	if (ac_env.cvect.ids != NULL) {
		f_free(ac_env.alloc, ac_env.cvect.ids);
	}

	return res;
}

SUPPRESS_EXPECTED_UNSIGNED_INTEGER_OVERFLOW()
static unsigned long
hash_iss(interned_state_set_id iss)
{
	/* Just hashing the ID directly is fine here -- since they're
	 * interned, they're identified by pointer equality. */
	return FSM_PHI_32 * (uintptr_t)iss;
}

static struct mapping *
map_first(struct map *map, struct map_iter *iter)
{
	iter->m = map;
	iter->i = 0;
	return map_next(iter);
}

static struct mapping *
map_next(struct map_iter *iter)
{
	const size_t limit = iter->m->count;
	while (iter->i < limit) {
		struct mapping **m = &iter->m->buckets[iter->i];
		iter->i++;
		if (*m == NULL) {
			continue;
		}
		return *m;
	}

	return NULL;
}

static int
map_add(struct map *map,
	fsm_state_t dfastate, interned_state_set_id iss, struct mapping **new_mapping)
{
	size_t i;
	unsigned long h, mask;

	if (map->buckets == NULL) {
		assert(map->count == 0);
		assert(map->used == 0);

		map->buckets = f_calloc(map->alloc,
		    DEF_MAP_BUCKET_CEIL, sizeof(map->buckets[0]));
		if (map->buckets == NULL) {
			return 0;
		}
		map->count = DEF_MAP_BUCKET_CEIL;
	}

	if (map->used == map->count/2) {
		if (!grow_map(map)) {
			return 0;
		}
	}

	h = hash_iss(iss);
	mask = map->count - 1;

	for (i = 0; i < map->count; i++) {
		struct mapping **b = &map->buckets[(h + i) & mask];
		if (*b == NULL) {
			struct mapping *m = f_malloc(map->alloc, sizeof(*m));
			if (m == NULL) {
				return 0;
			}
			m->iss = iss;
			m->dfastate = dfastate;
			m->edges = NULL;

			*b = m;

			if (new_mapping != NULL) {
				*new_mapping = m;
			}
			map->used++;
			return 1;
		} else {
			continue; /* hash collision */
		}
	}

	assert(!"unreachable");
	return 0;
}

static int
grow_map(struct map *map)
{
	size_t nceil = 2 * map->count;
	struct mapping **nbuckets;
	size_t o_i, n_i;
	const size_t nmask = nceil - 1;

	assert(nceil > 0);

	nbuckets = f_calloc(map->alloc,
	    nceil, sizeof(nbuckets[0]));
	if (nbuckets == NULL) {
		return 0;
	}

	for (o_i = 0; o_i < map->count; o_i++) {
		unsigned long h;
		struct mapping *ob = map->buckets[o_i];
		if (ob == NULL) {
			continue; /* empty */
		}
		h = hash_iss(ob->iss);
		for (n_i = 0; n_i < nmask; n_i++) {
			struct mapping **nb = &nbuckets[(h + n_i) & nmask];
			if (*nb == NULL) {
				*nb = ob;
				break;
			}
		}
		assert(n_i < nmask); /* found a spot */
	}

	f_free(map->alloc, map->buckets);
	map->count = nceil;
	map->buckets = nbuckets;
	return 1;
}

static int
map_find(const struct map *map, interned_state_set_id iss,
	struct mapping **mapping)
{
	size_t i;
	unsigned long h, mask;

	if (map->buckets == NULL) {
		return 0;
	}

	h = hash_iss(iss);
	mask = map->count - 1;

	for (i = 0; i < map->count; i++) {
		struct mapping *b = map->buckets[(h + i) & mask];
		if (b == NULL) {
			return 0; /* not found */
		} else if (b->iss == iss) {
			*mapping = b;
			return 1;
		} else {
			continue; /* hash collision */
		}
	}

	assert(!"unreachable");
	return 0;
}

static void
map_free(struct map *map)
{
	size_t i;
	if (map->buckets == NULL) {
		return;
	}

	for (i = 0; i < map->count; i++) {
		struct mapping *b = map->buckets[i];
		if (b == NULL) {
			continue;
		}
		f_free(map->alloc, b);
	}

	f_free(map->alloc, map->buckets);
}

static struct mappingstack *
stack_init(const struct fsm_alloc *alloc)
{
	struct mapping **s;
	struct mappingstack *res = f_malloc(alloc, sizeof(*res));
	if (res == NULL) {
		return NULL;
	}

	s = f_malloc(alloc, MAPPINGSTACK_DEF_CEIL * sizeof(s[0]));
	if (s == NULL) {
		f_free(alloc, res);
		return NULL;
	}

	res->alloc = alloc;
	res->ceil = MAPPINGSTACK_DEF_CEIL;
	res->depth = 0;
	res->s = s;

	return res;
}

static void
stack_free(struct mappingstack *stack)
{
	if (stack == NULL) {
		return;
	}
	f_free(stack->alloc, stack->s);
	f_free(stack->alloc, stack);
}

static int
stack_push(struct mappingstack *stack, struct mapping *item)
{
	if (stack->depth + 1 == stack->ceil) {
		size_t nceil = 2 * stack->ceil;
#if AC_LOG
		fprintf(stderr, "stack_push: growing stack %zu -> %zu\n",
		    stack->ceil, nceil);
#endif

		struct mapping **ns = f_realloc(stack->alloc,
		    stack->s, nceil * sizeof(ns[0]));
		if (ns == NULL) {
			return 0;
		}
		stack->ceil = nceil;
		stack->s = ns;
	}

	stack->s[stack->depth] = item;
	stack->depth++;
	return 1;
}

static struct mapping *
stack_pop(struct mappingstack *stack)
{
	assert(stack != NULL);
	if (stack->depth == 0) {
		return 0;
	}

	stack->depth--;
	struct mapping *item = stack->s[stack->depth];
	return item;
}

#if LOG_AC
static void
dump_egi_info(size_t i, const struct edge_group_iter_info *info) {
	if (info->to == AC_NO_STATE) {
		fprintf(stderr, "%zu: DONE\n", i);
		return;
	}
	fprintf(stderr, "%zu: unique %d, to %d, symbols: [0x%lx, 0x%lx, 0x%lx, 0x%lx] -- ",
	    i, info->unique, info->to,
	    info->symbols[0], info->symbols[1],
	    info->symbols[2], info->symbols[3]);
	dump_labels(stderr, info->symbols);
	fprintf(stderr, "\n");
}
#endif

static int
group_labels_overlap(const struct ac_group *a, const struct ac_group *b)
{
	size_t i;

	if (a->words_used & b->words_used) {
		for (i = 0; i < 4; i++) {
			const uint64_t wa = a->labels[i];
			if (wa && (wa & b->labels[i])) {
				return 1;
			}
		}
	}

	return 0;
}

static void
intersect_with(uint64_t *a, const uint64_t *b)
{
	size_t i;
	for (i = 0; i < 4; i++) {
		const uint64_t aw = a[i];
		if (aw == 0) {
			continue;
		}
		a[i] = aw & b[i];
	}
}

static void
union_with(uint64_t *a, const uint64_t *b)
{
	size_t i;
	for (i = 0; i < 4; i++) {
		const uint64_t bw = b[i];
		if (bw == 0) {
			continue;
		}
		a[i] |= bw;
	}
}

static void
clear_group_labels(struct ac_group *g, const uint64_t *b)
{
	size_t i;
	uint8_t bit;
	uint64_t *a = g->labels;

	for (i = 0, bit = 0x01; i < 4; i++, bit <<= 1) {
		if (g->words_used & bit) {
			const uint64_t bw = b[i];
			a[i] &=~ bw;
			if (a[i] == 0) {
				g->words_used &=~ bit;
			}
		}
	}
}

static int
analyze_closures_for_iss(struct analyze_closures_env *env,
    interned_state_set_id cur_iss)
{
	int res = 0;

	/* Save the ID in a local variable, because release
	 * below needs to overwrite the reference. */
	interned_state_set_id iss_id = cur_iss;

	struct state_set *ss = interned_state_set_get_state_set(env->issp, iss_id);
	const size_t set_count = state_set_count(ss);

	INIT_TIMERS();

	assert(env != NULL);
	assert(set_count > 0);

	TIME(&pre);
	if (!analyze_closures__init_iterators(env, ss, set_count)) {
		goto cleanup;
	}
	TIME(&post);
	DIFF_MSEC("init_iterators", pre, post, NULL);

	env->output_count = 0;

	TIME(&pre);
	if (!analyze_closures__init_groups(env)) {
		goto cleanup;
	}
	TIME(&post);
	DIFF_MSEC("init_groups", pre, post, NULL);

	TIME(&pre);

	switch (analyze_closures__collect(env)) {
	case AC_COLLECT_DONE:
		TIME(&post);
		DIFF_MSEC("collect", pre, post, NULL);

		TIME(&pre);
		if (!analyze_closures__analyze(env)) {
			goto cleanup;
		}
		TIME(&post);
		DIFF_MSEC("analyze", pre, post, NULL);
		break;

	case AC_COLLECT_EMPTY:
		/* no analysis to do */
		break;

	default:
	case AC_COLLECT_ERROR:
		goto cleanup;
	}

	res = 1;

cleanup:
	return res;

}

static enum ipriq_cmp_res
cmp_iterator_cb(size_t a, size_t b, void *opaque)
{
	struct analyze_closures_env *env = opaque;
	assert(env != NULL);

	assert(a < env->iter_count);
	assert(b < env->iter_count);

	const fsm_state_t to_a = env->iters[a].info.to;
	const fsm_state_t to_b = env->iters[b].info.to;

#if LOG_AC
	fprintf(stderr, "cmp_iterator_ac: a %zu -> to_a %d, b %zu -> to_b %d\n",
	    a, to_a, b, to_b);
#endif

	return to_a < to_b ? IPRIQ_CMP_LT : to_a > to_b ? IPRIQ_CMP_GT : IPRIQ_CMP_EQ;
}

static int
analyze_closures__init_iterators(struct analyze_closures_env *env,
	const struct state_set *ss, size_t set_count)
{
	struct state_iter it;
	fsm_state_t s;
	size_t i_i;

	if (env->pq == NULL) {
		env->pq = ipriq_new(env->alloc,
		    cmp_iterator_cb, (void *)env);
		if (env->pq == NULL) {
			return 0;
		}
	} else {
		/* reuse, to avoid allocating in inner loop */
		assert(ipriq_empty(env->pq));
	}

#if LOG_AC
	fprintf(stderr, "ac_init: ceil %zu, count %zu\n",
	    env->iter_ceil, set_count);
#endif

	/* Grow backing array for iterators on demand */
	if (env->iter_ceil < set_count) {
		if (!analyze_closures__grow_iters(env, set_count)) {
			return 0;
		}
	}

	/* Init all the edge group iterators so we can step them in
	 * parallel and merge. Each will yield edge groups in order,
	 * sorted by .to, so we can merge them that way. */
	i_i = 0;
	state_set_reset(ss, &it);

#if LOG_AC
	fprintf(stderr, "ac_init: initializing iterators:");
#endif

	while (state_set_next(&it, &s)) {
		/* The edge set group iterator can partition them into
		 * unique (within the edge set) and non-unique label
		 * sets, but what we really care about is labels that
		 * are unique within the entire state set, so that
		 * doesn't actually help us much. */
#if LOG_AC
		fprintf(stderr, " %d", s);
#endif
		edge_set_group_iter_reset(env->fsm->states[s].edges,
		    EDGE_GROUP_ITER_ALL, &env->iters[i_i].iter);
		i_i++;
	}

#if LOG_AC
	fprintf(stderr, "\n");
#endif
	env->iter_count = set_count;

	assert(env->pq != NULL);
	assert(ipriq_empty(env->pq));

	for (i_i = 0; i_i < set_count; i_i++) {
		struct ac_iter *egi = &env->iters[i_i];
		if (edge_set_group_iter_next(&egi->iter, &egi->info)) {
#if LOG_AC
			fprintf(stderr, "ac_collect: iter[%zu]: to: %d\n",
			    i_i, egi->info.to);
			dump_egi_info(i_i, &egi->info);
#endif
			if (!ipriq_add(env->pq, i_i)) {
				return 0;
			}
		} else {
#if LOG_AC
			fprintf(stderr, "ac_collect: iter[%zu]: DONE\n", i_i);
#endif
			egi->info.to = AC_NO_STATE; /* done */
		}
	}

	return 1;
}

static int
analyze_closures__init_groups(struct analyze_closures_env *env)
{
	if (env->group_ceil == 0) {
		const size_t nceil = DEF_GROUP_CEIL;
		struct ac_group *ngs = f_malloc(env->alloc,
		    nceil * sizeof(env->groups[0]));
		if (ngs == NULL) {
			return 0;
		}
		env->groups = ngs;
		env->group_ceil = nceil;
	}

	assert(env->groups != NULL);
	env->group_count = 0;
	memset(&env->groups[0], 0x00, sizeof(env->groups[0]));
	env->groups[0].to = AC_NO_STATE;
	return 1;
}

static enum ac_collect_res
analyze_closures__collect(struct analyze_closures_env *env)
{
	/* All iterators have been stepped once, and any that didn't
	 * finish immediately were added to the queue. Keep stepping
	 * whichever is earliest (by .to state) until they're all done.
	 * Merge (label set -> state) info along the way. */

	if (ipriq_empty(env->pq)) {
#if LOG_AC
		fprintf(stderr, "ac_collect: empty\n");
#endif
		return AC_COLLECT_EMPTY;
	}

	size_t steps = 0;
	while (!ipriq_empty(env->pq)) {
		size_t next_i;
		steps++;

		if (!ipriq_pop(env->pq, &next_i)) {
			assert(!"unreachable: non-empty, but pop failed");
			return AC_COLLECT_ERROR;
		}

#if LOG_AC
		fprintf(stderr, "ac_collect: popped %zu\n", next_i);
#endif

		assert(next_i < env->iter_count);
		struct ac_iter *iter = &env->iters[next_i];
		assert(iter->info.to != AC_NO_STATE);

		/* If we are about to put the current iterator into the
		 * priority queue only to pop it right back out again,
		 * note what the next state is on the next iterator in
		 * the queue and resume the current iterator as long as
		 * we can. This saves a lot of time spent on pointless
		 * queue bookkeeping. */
		size_t next_next_i = 0;
		fsm_state_t resume_current_limit = AC_NO_STATE;
		if (ipriq_peek(env->pq, &next_next_i)) {
			assert(next_next_i < env->iter_count);
			struct ac_iter *next_iter = &env->iters[next_next_i];
			assert(next_iter->info.to != AC_NO_STATE);
			if (next_iter->info.to > iter->info.to) {
				resume_current_limit = next_iter->info.to;
			}
		}

advance_current_iterator:;

		if (env->group_count + 1 == env->group_ceil) {
			if (!analyze_closures__grow_groups(env)) {
				return AC_COLLECT_ERROR;
			}
		}

		assert(env->group_count < env->group_ceil);

		struct ac_group *g = &env->groups[env->group_count];

		if (g->to == AC_NO_STATE) { /* init new group */
			memset(g, 0x00, sizeof(*g));
			g->to = iter->info.to;
			union_with(g->labels, iter->info.symbols);
		} else if (g->to == iter->info.to) { /* update current group */
			union_with(g->labels, iter->info.symbols);
		} else {	/* switch to next group */
			assert(iter->info.to > g->to);
			env->group_count++;

			if (env->group_count + 1 == env->group_ceil) {
				if (!analyze_closures__grow_groups(env)) {
					return AC_COLLECT_ERROR;
				}
			}
			assert(env->group_count < env->group_ceil);

			struct ac_group *ng = &env->groups[env->group_count];
			memset(ng, 0x00, sizeof(*ng));
			ng->to = iter->info.to;
			union_with(ng->labels, iter->info.symbols);
		}

		if (edge_set_group_iter_next(&iter->iter, &iter->info)) {
#if LOG_AC
			fprintf(stderr, "ac_collect: iter %zu -- to %d\n",
			    next_i, iter->info.to);
#endif
			if (resume_current_limit != AC_NO_STATE
			    && iter->info.to < resume_current_limit) {
				goto advance_current_iterator;
			}
			if (!ipriq_add(env->pq, next_i)) {
				return AC_COLLECT_ERROR;
			}
		} else {
#if LOG_AC
			fprintf(stderr, "ac_collect: iter %zu -- DONE\n", next_i);
#endif
		}
	}

	env->group_count++;	/* commit current group */

	return AC_COLLECT_DONE;
}

static int
grow_clearing_vector(struct analyze_closures_env *env)
{
	const size_t nceil = (env->cvect.ceil == 0
	    ? DEF_CVECT_CEIL
	    : 2*env->cvect.ceil);
	fsm_state_t *nids = f_realloc(env->alloc,
	    env->cvect.ids, nceil * sizeof(nids[0]));
	if (nids == NULL) {
		return 0;
	}

	env->cvect.ceil = nceil;
	env->cvect.ids = nids;
	return 1;
}

static int
analyze_closures__analyze(struct analyze_closures_env *env)
{
#if LOG_AC
	/* Dump group table. */
	{
		size_t g_i;
		fprintf(stderr, "# group label/to closure table\n");
		for (g_i = 0; g_i < env->group_count; g_i++) {
			const struct ac_group *g = &env->groups[g_i];
			fprintf(stderr,
			    "g[%zu]: to %d: [0x%lx, 0x%lx, 0x%lx, 0x%lx] -- ",
			    g_i, g->to,
			    g->labels[0], g->labels[1],
			    g->labels[2], g->labels[3]);
			dump_labels(stderr, g->labels);
			fprintf(stderr, "\n");
		}
	}
#endif

	/* This partitions the table into an array of non-overlapping
	 * (label set -> state set) pairs.
	 *
	 * For the first group in the table, find labels in that group that
	 * are shared by later groups, create a set of the states those
	 * groups lead to, then clear those labels. If the first group is
	 * empty, advance base_i to the next group, and repeat until all
	 * the groups in the table have been cleared. Because each pass
	 * clears lables, this must eventually terminate.
	 *
	 * The pass that clears the labels on groups that were just
	 * added to the result set benefits from the groups being sorted
	 * by ascending .to fields, but other approaches may be faster.
	 * I tried sorting the table by ascending count of bits used in
	 * the label sets, so earlier groups with only a few labels
	 * would be cleared faster and reduce the overall working set
	 * sooner, but neither approach seemed to be clearly faster for
	 * my test data sets. There is also a lot of room here for
	 * speeding up the group label set unioning, intersecting, and
	 * clearing. Casual experiments suggested small improvements but
	 * not drastic improvements, so I'm leaving that performance
	 * work for later. */
	size_t base_i, g_i, o_i; /* base_i, group_i, other_i */

	base_i = 0;
	env->output_count = 0;

	if (env->dst_ceil == 0) {
		if (!analyze_closures__grow_dst(env)) {
			return 0;
		}
	}

	/* Initialize words_used for each group. */
	for (g_i = 0; g_i < env->group_count; g_i++) {
		size_t w_i;
		uint8_t bit;
		struct ac_group *g = &env->groups[g_i];
		g->words_used = 0;
		for (w_i = 0, bit = 0x01; w_i < 4; w_i++, bit <<= 1) {
			if (g->labels[w_i] != 0) {
				g->words_used |= bit;
			}
		}
	}

	while (base_i < env->group_count) {
		/* labels assigned in current sweep. The g_labels wrapper
		 * is used for g_labels.words_used. */
		struct ac_group g_labels = { 0 };
		uint64_t *labels = g_labels.labels;
		size_t dst_count = 0;

#if LOG_AC
		fprintf(stderr, "base_i %zu/%zu\n",
		    base_i, env->group_count);
#endif

		const struct ac_group *bg = &env->groups[base_i];
		memcpy(&g_labels, bg, sizeof(*bg));

		/* At least one bit should be set; otherwise
		 * we should have incremented base_i. */
		assert(labels[0] || labels[1]
		    || labels[2] || labels[3]);

#if LOG_AC
		fprintf(stderr, "ac_analyze: dst[%zu] <- %d (base)\n", dst_count, bg->to);
#endif

		if (dst_count + 1 == env->dst_ceil) {
			if (!analyze_closures__grow_dst(env)) {
				return 0;
			}
		}
		env->dst[dst_count] = bg->to;
		dst_count++;

		if (env->cvect.ceil == 0) {
			if (!grow_clearing_vector(env)) { return 0; }
		}
		env->cvect.ids[0] = base_i;
		env->cvect.used = 1;

		for (o_i = base_i + 1; o_i < env->group_count; o_i++) {
			const struct ac_group *og = &env->groups[o_i];
			if (og->words_used == 0) {
				continue; /* skip empty groups */
			}

			/* TODO: Combining checking for overlap and intersecting
			 * into one pass would be ugly, but a little faster, and
			 * this loop has a big impact on performance. */
			if (group_labels_overlap(&g_labels, og)) {
				intersect_with(labels, og->labels);
#if LOG_AC
				fprintf(stderr, "ac_analyze: dst[%zu] <- %d (other w/ overlapping labels)\n", dst_count, og->to);
#endif

				if (dst_count + 1 == env->dst_ceil) {
					if (!analyze_closures__grow_dst(env)) {
						return 0;
					}
				}

				env->dst[dst_count] = og->to;
				dst_count++;

				if (env->cvect.used == env->cvect.ceil) {
					if (!grow_clearing_vector(env)) { return 0; }
				}
				env->cvect.ids[env->cvect.used] = o_i;
				env->cvect.used++;
			}
		}

#if LOG_AC
		fprintf(stderr, "ac_analyze: dst_count: %zu\n", dst_count);
#endif

		assert(labels[0] || labels[1]
		    || labels[2] || labels[3]);

		for (size_t c_i = 0; c_i < env->cvect.used; c_i++) {
			const fsm_state_t g_id = env->cvect.ids[c_i];
			assert(g_id < env->group_count);
			struct ac_group *g = &env->groups[g_id];
			clear_group_labels(g, labels);
		}

		if (LOG_AC) {
			size_t i;
			fprintf(stderr, "new_edge_group:");
			for (i = 0; i < dst_count; i++) {
				fprintf(stderr, " %d", env->dst[i]);
			}
			fprintf(stderr, " -- ");
			dump_labels(stderr, labels);
			fprintf(stderr, "\n");
		}

		{		/* build the state set and add to the output */
#if LOG_AC > 1
			fprintf(stderr, "ac_analyze: building interned_state_set with %zu states:", dst_count);
#endif
			interned_state_set_id iss;
			if (!interned_state_set_intern_set(env->issp, dst_count, env->dst, &iss)) {
				return 0;
			}

			if (!analyze_closures__save_output(env, labels, iss)) {
				return 0;
			}
		}

		while (base_i < env->group_count && env->groups[base_i].words_used == 0) {
#if LOG_AC
			fprintf(stderr, "ac_analyze: base %zu all clear, advancing\n", base_i);
#endif
			base_i++;
		}
	}

#if LOG_AC
	fprintf(stderr, "ac_analyze: done\n");
#endif

	return 1;
}

static int
analyze_closures__save_output(struct analyze_closures_env *env,
    const uint64_t labels[256/4], interned_state_set_id iss)
{
	if (env->output_count + 1 >= env->output_ceil) {
		if (!analyze_closures__grow_outputs(env)) {
			return 0;
		}
	}

	struct ac_output *dst = &env->outputs[env->output_count];
	memcpy(dst->labels, labels, sizeof(dst->labels));
	dst->iss = iss;

#if LOG_AC
	fprintf(stderr, "ac_save_output: labels [");
	dump_labels(stderr, labels);
	fprintf(stderr, "] -> iss:%p\n", (void *)iss);
#endif

	env->output_count++;
	return 1;
}

static int
analyze_closures__grow_iters(struct analyze_closures_env *env,
    size_t set_count)
{
	size_t nceil = (env->iter_ceil == 0
	    ? DEF_ITER_CEIL : env->iter_ceil);
	while (nceil < set_count) {
		assert(nceil > 0);
		nceil *= 2;
	}

#if LOG_AC
	fprintf(stderr, "ac_init: growing iters to %zu\n", nceil);
#endif

	struct ac_iter *niters = f_realloc(env->alloc,
	    env->iters, nceil * sizeof(env->iters[0]));
	if (niters == NULL) {
		return 0;
	}
	env->iters = niters;
	env->iter_ceil = nceil;
	return 1;
}

static int
analyze_closures__grow_groups(struct analyze_closures_env *env)
{
	const size_t nceil = 2*env->group_ceil;
	struct ac_group *ngs = f_realloc(env->alloc,
	    env->groups, nceil * sizeof(env->groups[0]));
	if (ngs == NULL) {
		return 0;
	}

#if LOG_AC
	fprintf(stderr, "ac_grow_groups: growing groups %zu -> %zu\n",
	    env->group_ceil, nceil);
#endif

	env->groups = ngs;
	env->group_ceil = nceil;
	return 1;
}

static int
analyze_closures__grow_dst(struct analyze_closures_env *env)
{
	const size_t nceil = (env->dst_ceil == 0
	    ? DEF_DST_CEIL : 2*env->dst_ceil);
	fsm_state_t *ndst = f_realloc(env->alloc,
	    env->dst, nceil * sizeof(env->dst[0]));
	if (ndst == NULL) {
		return 0;
	}

#if LOG_AC
	fprintf(stderr, "ac_grow_dst: growing dst %zu -> %zu\n",
	    env->dst_ceil, nceil);
#endif

	env->dst = ndst;
	env->dst_ceil = nceil;
	return 1;

}

static int
analyze_closures__grow_outputs(struct analyze_closures_env *env)
{
	const size_t nceil = (env->output_ceil == 0
	    ? DEF_OUTPUT_CEIL : 2*env->output_ceil);
	struct ac_output *nos = f_realloc(env->alloc,
	    env->outputs, nceil * sizeof(env->outputs[0]));
	if (nos == NULL) {
		return 0;
	}

#if LOG_AC
	fprintf(stderr, "ac_grow_outputs: growing outputs %zu -> %zu\n",
	    env->output_ceil, nceil);
#endif

	env->outputs = nos;
	env->output_ceil = nceil;
	return 1;
}

static int
remap_end_metadata(const struct fsm *src_fsm, const struct state_set *src_set,
    struct fsm *dst_fsm, fsm_state_t dst_state)
{
	if (!fsm_endid_carry(src_fsm, src_set, dst_fsm, dst_state)) {
		return 0;
	}

	if (!fsm_capture_copy_active_for_ends(src_fsm, src_set, dst_fsm, dst_state)) {
		return 0;
	}

	if (!fsm_capture_copy_program_end_state_associations(src_fsm, src_set, dst_fsm, dst_state)) {
		return 0;
	}

	return 1;
}
