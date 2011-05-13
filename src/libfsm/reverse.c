/* $Id$ */

#include <assert.h>
#include <stddef.h>

#include <fsm/fsm.h>
#include <fsm/graph.h>
#include <fsm/colour.h>

#include "internal.h"
#include "set.h"

/* TODO: centralise? */
static int
incomingedges(const struct fsm *fsm, const struct fsm_state *state)
{
	const struct fsm_state *s;
	int i;

	assert(fsm != NULL);
	assert(state != NULL);

	for (s = fsm->sl; s != NULL; s = s->next) {
		for (i = 0; i <= FSM_EDGE_MAX; i++) {
			if (set_contains(state, s->edges[i].sl)) {
				return 1;
			}
		}
	}

	return 0;
}

static struct fsm_state *
getequivalentstate(const struct fsm *new, const struct fsm *fsm, const struct fsm_state *state)
{
	struct fsm_state *s1;
	struct fsm_state *s2;

	assert(new != NULL);
	assert(fsm != NULL);
	assert(state != NULL);

	for (s1 = fsm->sl, s2 = new->sl; s1 != NULL; s1 = s1->next, s2 = s2->next) {
		assert(s2 != NULL);

		if (s1 == state) {
			return s2;
		}
	}

	return NULL;
}

static void
movetoend(struct fsm *fsm, struct fsm_state *state)
{
	struct fsm_state **s;

	assert(fsm != NULL);
	assert(fsm->start = state);

	fsm->sl = fsm->sl->next;

	for (s = &fsm->sl; *s != NULL; s = &(*s)->next) {
		/* nothing */
	}

	*s = state;
	state->next = NULL;
}

int
fsm_reverse(struct fsm *fsm)
{
	struct fsm *new;

	assert(fsm != NULL);

	new = fsm_new();
	if (new == NULL) {
		return 0;
	}

	fsm_setcolourhooks(new, &fsm->colour_hooks);

	/*
	 * Create states corresponding to the origional FSM's states.
	 * These are created in reverse order, but that's okay.
	 *
	 * TODO: possibly centralise as a state-copying function
	 */
	{
		struct fsm_state *s;

		for (s = fsm->sl; s != NULL; s = s->next) {
			struct fsm_state *n;

			n = fsm_addstate(new);
			if (n == NULL) {
				fsm_free(new);
				return 0;
			}
		}
	}

	/*
	 * The new end state is the previous start state. Because there is (at most)
	 * one start state, the new FSM will have at most one end state.
	 *
	 * End colours are carried through from the previous end states.
	 */
	{
		struct fsm_state *end;
		struct fsm_state *s;
		struct colour_set *c;

		end = getequivalentstate(new, fsm, fsm->start);
		if (end != NULL) {
			for (s = fsm->sl; s != NULL; s = s->next) {
				for (c = s->cl; c != NULL; c = c->next) {
					if (!fsm_addend(new, end, c->colour)) {
						fsm_free(new);
						return 0;
					}
				}
			}
		}
	}

	/* Create reversed edges */
	{
		struct fsm_state *s;

		for (s = fsm->sl; s != NULL; s = s->next) {
			struct fsm_state *to;
			struct state_set *e;
			struct colour_set *c;
			int i;

			to = getequivalentstate(new, fsm, s);

			assert(to != NULL);

			for (i = 0; i <= FSM_EDGE_MAX; i++) {
				for (e = s->edges[i].sl; e != NULL; e = e->next) {
					struct fsm_state *from;
					struct fsm_edge *edge;

					assert(e->state != NULL);

					from = getequivalentstate(new, fsm, e->state);

					assert(from != NULL);

					switch (i) {
					case FSM_EDGE_EPSILON:
						edge = fsm_addedge_epsilon(new, from, to);
						if (edge == NULL) {
							fsm_free(new);
							return 0;
						}
						break;

					default:
						assert(i >= 0);
						assert(i <= UCHAR_MAX);

						edge = fsm_addedge_literal(new, from, to, i);
						if (edge == NULL) {
							fsm_free(new);
							return 0;
						}
					}

					/* TODO: centralise */
					for (c = s->edges[i].cl; c != NULL; c = c->next) {
						if (!fsm_addedgecolour(new, edge, c->colour)) {
							fsm_free(new);
							return 0;
						}
					}
				}
			}
		}
	}

	/*
	 * Mark the new start state. If there's only one state, we can indicate it
	 * directly. Otherwise we will be starting from a group of states, linked
	 * together by epsilon transitions.
	 */
	{
		struct fsm_state *s;
		int endcount;

		endcount = 0;
		for (s = fsm->sl; s != NULL; s = s->next) {
			endcount += !!fsm_isend(fsm, s);
		}

		switch (endcount) {
		case 1:
			for (s = fsm->sl; s != NULL; s = s->next) {
				if (fsm_isend(fsm, s)) {
					break;
				}
			}

			assert(s != NULL);

			new->start = getequivalentstate(new, fsm, s);
			assert(new->start != NULL);
			break;

		case 0:
			/*
			 * Transition to all states. I don't like this at all, but it is
			 * required to be able to minimize automata with no end states.
			 */

		default:
			for (s = fsm->sl; s != NULL; s = s->next) {
				struct fsm_state *state;

				if (endcount > 0 && !fsm_isend(fsm, s)) {
					continue;
				}

				state = getequivalentstate(new, fsm, s);
				assert(state != NULL);

				if (!incomingedges(new, state)) {
					break;
				}
			}

			/*
			 * The typical case here is to create a new start state, and to
			 * link it to end states by epsilon transitions.
			 *
			 * An optimisation: if we found an end state with no incoming
			 * edges, that state is nominated as a new start state. This is
			 * equivalent to adding a new start state, and linking out from
			 * that, except it does not need to introduce a new state.
			 * Otherwise, we need to create a new start state as per usual.
			 *
			 * In either case, the start is linked to the other new start
			 * states by epsilons.
			 *
			 * It is important to use a start state with no incoming edges as
			 * this prevents accidentally transitioning to another route.
			 */
			if (s != NULL) {
				new->start = getequivalentstate(new, fsm, s);
				assert(new->start != NULL);
			} else {
				new->start = fsm_addstate(new);
				if (new->start == NULL) {
					fsm_free(new);
					return 0;
				}

				/*
				 * XXX: This hacky mess moves the newly-created start state
				 * to the end of new->sl, for the sake of getequivalentstate().
				 */
				movetoend(new, new->start);
			}

			for (s = fsm->sl; s != NULL; s = s->next) {
				struct fsm_state *state;

				if (endcount > 0 && !fsm_isend(fsm, s)) {
					continue;
				}

				state = getequivalentstate(new, fsm, s);
				assert(state != NULL);

				if (state == new->start) {
					continue;
				}

				if (!fsm_addedge_epsilon(new, new->start, state)) {
					fsm_free(new);
					return 0;
				}
			}
			break;
		}
	}

	fsm_move(fsm, new);

	return 1;
}
