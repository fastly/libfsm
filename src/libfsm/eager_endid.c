/*
 * Copyright 2024 Scott Vokes
 *
 * See LICENCE for the full copyright terms.
 */

#include <stdio.h>
#include <assert.h>

#include "internal.h"

#include <fsm/pred.h>
#include <fsm/print.h>

#include <adt/edgeset.h>
#include <adt/stateset.h>

#include "eager_endid.h"

#define DEF_ENTRY_CEIL 256

#define LOG_LEVEL 2

#define EAGER_ENDID_EDGE_FROM_START ((fsm_state_t)-2)

struct eager_endid_info {
	/* janky vector impl, replace with something else later */
	size_t ceil;
	size_t used;

	fsm_eager_endid_cb *cb;
	void *opaque;

	struct eager_endid_entry {
		fsm_state_t from; /* or EAGER_ENDID_EDGE_FROM_START */
		fsm_state_t to;
		fsm_end_id_t id;
	} *entries;
};

void
fsm_eager_endid_set_cb(struct fsm *fsm, fsm_eager_endid_cb *cb, void *opaque)
{
#if LOG_LEVEL > 2
	fprintf(stderr, "-- fsm_eager_endid_set_cb %p\n", (void *)fsm);
#endif
	assert(fsm->eager_endid_info != NULL);
	fsm->eager_endid_info->cb = cb;
	fsm->eager_endid_info->opaque = opaque;
}

void
fsm_eager_endid_get_cb(const struct fsm *fsm, fsm_eager_endid_cb **cb, void **opaque)
{
	*cb = fsm->eager_endid_info->cb;
	*opaque = fsm->eager_endid_info->opaque;
}

int
fsm_eager_endid_init(struct fsm *fsm)
{
	struct eager_endid_info *ei = f_calloc(fsm->alloc, 1, sizeof(*ei));
	struct eager_endid_entry *entries = f_calloc(fsm->alloc, DEF_ENTRY_CEIL, sizeof(entries[0]));

	if (ei == NULL || entries == NULL) {
		f_free(fsm->alloc, ei);
		f_free(fsm->alloc, entries);
		return 0;
	}

	ei->ceil = DEF_ENTRY_CEIL;
	ei->entries = entries;

#if LOG_LEVEL > 2
	fprintf(stderr, "-- fsm_eager_endid_init %p\n", (void *)fsm);
#endif
	fsm->eager_endid_info = ei;
	return 1;
}

void
fsm_eager_endid_free(struct fsm *fsm)
{
	if (fsm == NULL || fsm->eager_endid_info == NULL) { return; }

	f_free(fsm->alloc, fsm->eager_endid_info->entries);
	f_free(fsm->alloc, fsm->eager_endid_info);
#if LOG_LEVEL > 2
	fprintf(stderr, "-- fsm_eager_endid_free %p\n", (void *)fsm);
#endif
	fsm->eager_endid_info = NULL;
}

bool
fsm_eager_endid_has_eager_endids(const struct fsm *fsm)
{
	return fsm->eager_endid_info && fsm->eager_endid_info->used > 0;
}

static int
insert_eager_endid_entry(const struct fsm_alloc *alloc, struct eager_endid_info *info,
    fsm_state_t from, fsm_state_t to, fsm_end_id_t id)
{
#if LOG_LEVEL > 0
	fprintf(stderr, "%s: %d, %d, %d\n", __func__, from, to, id);
#endif
	if (info->ceil == info->used) {
		(void)alloc;
		assert(!"todo: grow");
		return 0;
	}

	/* FIXME linear scan */
	for (size_t i = 0; i < info->used; i++) {
		struct eager_endid_entry *e = &info->entries[i];
		if (e->from == from && e->to == to && e->id == id) {
			return 1; /* already present, discarding duplicate */
		}
	}

	info->entries[info->used] = (struct eager_endid_entry){
		.from = from,
		.to = to,
		.id = id,
	};
	info->used++;
	return 1;
}

int
fsm_eager_endid_insert_entry(struct fsm *fsm,
    fsm_state_t from, fsm_state_t to, fsm_end_id_t id)
{
	if (from == to) {
#if LOG_LEVEL > 1
		fprintf(stderr, "%s: skipping adding entry (%d -> %d, %d) with self-edge \n",
		    __func__, from, to, id);
#endif
		return 1;
	}

	const int res = insert_eager_endid_entry(fsm->alloc, fsm->eager_endid_info,
	    from, to, id);
	if (res && from != EAGER_ENDID_EDGE_FROM_START) {
		assert(from < fsm->statecount);
		fsm->states[from].has_eager_endids = 1;
	}
	return res;
}

int
fsm_seteagerendid(struct fsm *fsm, fsm_end_id_t id)
{
	const size_t scount = fsm_countstates(fsm);

	fsm_state_t start;
	if (!fsm_getstart(fsm, &start)) {
		return 0;
	}

#if LOG_LEVEL > 0
	fprintf(stderr, "%s: id %d\n", __func__, id);
	fsm_dump(stderr, fsm);
#endif

	if (fsm_isend(fsm, start)) {
		/* Special case: The start state is an end, so add
		 * an edge of <start, start, ID>. This will be the
		 * only possible self-edge, and should be checked for
		 * at the start of FSM execution. */
		if (!insert_eager_endid_entry(fsm->alloc, fsm->eager_endid_info,
			start, start, id)) {
			return 0;
		}

		fsm->states[start].has_eager_endids = 1;
	}

	/* For every non-self edge leading to an end state, mark the
	 * edge with the eager endid. */
	for (fsm_state_t s_i = 0; s_i < scount; s_i++) {
		struct edge_group_iter iter;
		struct edge_group_iter_info info;
		struct state_iter epsilon_iter;
		fsm_state_t to;

		fprintf(stderr, "%s: s_i %d, is_end %d\n", __func__, s_i, fsm_isend(fsm, s_i));

		struct fsm_state *s = &fsm->states[s_i];

		/* mark epsilon edges to end states */
		state_set_reset(s->epsilons, &epsilon_iter);
		while (state_set_next(&epsilon_iter, &to)) {
			/* fprintf(stderr, "??? %d --eps--> %d: %d\n", s_i, to, fsm_isend(fsm, to)); */
			if (to != s_i && fsm_isend(fsm, to)) {
				if (!insert_eager_endid_entry(fsm->alloc, fsm->eager_endid_info,
					s_i, to, id)) {
					return 0;
				}
				s->has_eager_endids = 1;
			}
		}

		/* mark labeled edges to end states */
		edge_set_group_iter_reset(s->edges, EDGE_GROUP_ITER_ALL, &iter);
		while (edge_set_group_iter_next(&iter, &info)) {
			/* fprintf(stderr, "??? %d -> %d: %d\n", s_i, info.to, fsm_isend(fsm, info.to)); */
			if (info.to != s_i && fsm_isend(fsm, info.to)) {
				if (!insert_eager_endid_entry(fsm->alloc, fsm->eager_endid_info,
					s_i, info.to, id)) {
					return 0;
				}
				s->has_eager_endids = 1;
			}
		}
	}

	return 1;
}

void
fsm_eager_endid_iter_edges_from_state(const struct fsm *fsm,
    fsm_state_t from, fsm_eager_endid_iter_edges_cb *cb, void *opaque)
{
	assert(fsm != NULL);
	assert(fsm->eager_endid_info != NULL);
	assert(cb != NULL);

	const struct eager_endid_info *info = fsm->eager_endid_info;
	for (size_t i = 0; i < info->used; i++) {
		const struct eager_endid_entry *e = &info->entries[i];
		if (e->from == from) {
			if (!cb(e->from, e->to, e->id, opaque)) { return; }
		}
	}
}

void
fsm_eager_endid_iter_edges_between_states(const struct fsm *fsm,
    fsm_state_t from, fsm_state_t to, fsm_eager_endid_iter_edges_cb *cb, void *opaque)
{
	assert(fsm != NULL);
	assert(fsm->eager_endid_info != NULL);
	assert(cb != NULL);

	const struct eager_endid_info *info = fsm->eager_endid_info;
	for (size_t i = 0; i < info->used; i++) {
		const struct eager_endid_entry *e = &info->entries[i];
		if (e->from == from && e->to == to) {
			if (!cb(e->from, e->to, e->id, opaque)) { return; }
		}
	}
}

void
fsm_eager_endid_iter_edges_all(const struct fsm *fsm,
    fsm_eager_endid_iter_edges_cb *cb, void *opaque)
{
	assert(fsm != NULL);
	assert(fsm->eager_endid_info != NULL);
	assert(cb != NULL);

	const struct eager_endid_info *info = fsm->eager_endid_info;
	for (size_t i = 0; i < info->used; i++) {
		const struct eager_endid_entry *e = &info->entries[i];

#if 1
		if (e->from != EAGER_ENDID_EDGE_FROM_START) {
			assert(fsm->states[e->from].has_eager_endids);
		}
#endif

		if (!cb(e->from, e->to, e->id, opaque)) { return; }
	}
}

static int
dump_cb(fsm_state_t from, fsm_state_t to, fsm_end_id_t id, void *opaque)
{
	FILE *f = opaque;
	fprintf(f, "-- %d -> %d: id %d\n", from, to, id);
	return 1;
}

void
fsm_eager_endid_dump(FILE *f, const struct fsm *fsm)
{
	if (!fsm_eager_endid_has_eager_endids(fsm)) { return; }

	fprintf(f, "%s:\n", __func__);
	fsm_eager_endid_iter_edges_all(fsm, dump_cb, (void *)f);
}
