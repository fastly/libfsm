#ifndef EAGER_ENDID_H
#define EAGER_ENDID_H

#include <stddef.h>
#include <stdbool.h>
#include <inttypes.h>

struct eager_endid_info;

int
fsm_eager_endid_init(struct fsm *fsm);

void
fsm_eager_endid_free(struct fsm *fsm);

bool
fsm_eager_endid_has_eager_endids(const struct fsm *fsm);

void
fsm_eager_endid_dump(FILE *f, const struct fsm *fsm);

/* Internal interface, used during epsilon removal,
 * determinisation, and minimisation. */
int
fsm_eager_endid_insert_entry(struct fsm *fsm,
    fsm_state_t from, fsm_state_t to, fsm_end_id_t id);

/* Callback for fsm_eager_endid_iter_*.
 * The return value indicates whether iteration should continue.
 * The results may not be sorted in any particular order. */
typedef int
fsm_eager_endid_iter_edges_cb(fsm_state_t from, fsm_state_t to, fsm_end_id_t id, void *opaque);

void
fsm_eager_endid_iter_edges_from_state(const struct fsm *fsm,
    fsm_state_t from, fsm_eager_endid_iter_edges_cb *cb, void *opaque);

void
fsm_eager_endid_iter_edges_between_states(const struct fsm *fsm,
    fsm_state_t from, fsm_state_t to, fsm_eager_endid_iter_edges_cb *cb, void *opaque);

void
fsm_eager_endid_iter_edges_all(const struct fsm *fsm,
    fsm_eager_endid_iter_edges_cb *cb, void *opaque);

#endif
