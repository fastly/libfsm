/*
 * Copyright 2019 Scott Vokes
 *
 * See LICENCE for the full copyright terms.
 */

#include <string.h>
#include <assert.h>

#include <fsm/fsm.h>

#include <adt/alloc.h>
#include <adt/queue.h>

struct queue {
	const struct fsm_alloc *alloc;
	/* Read and write offsets. When rd == wr, the queue is empty. rd
	 * will always be <= wr, and wr <= capacity. */
	size_t rd;
	size_t wr;
	size_t capacity;
	int dynamic;
	fsm_state_t *q;
};

struct queue *
queue_new(const struct fsm_alloc *a, size_t max_capacity)
{
	struct queue *q;
	if (max_capacity == 0) { return NULL; }

	q = f_calloc(a, 1, sizeof(*q));
	if (q == NULL) { return NULL; }

	q->q = f_calloc(a, max_capacity, sizeof(q->q[0]));
	if (q->q == NULL) {
		f_free(a, q);
		return NULL;
	}

	q->alloc = a;
	q->capacity = max_capacity;

	return q;
}

struct queue *
queue_new_dynamic(const struct fsm_alloc *a, size_t hint)
{
	struct queue *q = queue_new(a, hint);
	if (q == NULL) { return NULL; }
	q->dynamic = 1;

	return q;
}

int
queue_push(struct queue *q, fsm_state_t state)
{
	assert(q->rd <= q->wr);
	assert(q->wr <= q->capacity);

	if (q->wr == q->capacity) {
		/* If there's no room but some have been read, shift all
		 * the entries down. In the worst case, this will
		 * memmove everything after reading 1. */
		if (q->rd > 0 && q->rd < q->wr) {
			memmove(&q->q[0], &q->q[q->rd],
			    (q->capacity - q->rd) * sizeof(q->q[0]));
			q->wr -= q->rd;
			q->rd = 0;
		} else if (q->dynamic) {
			const size_t ncap = 2*q->capacity;
			fsm_state_t *nq = f_realloc(q->alloc,
			    q->q, ncap * sizeof(q->q[0]));
			if (nq == NULL) {
				return 0;
			}

			q->capacity = ncap;
			q->q = nq;
		} else {
			return 0;
		}
	}

	q->q[q->wr] = state;
	q->wr++;
	return 1;
}

int
queue_pop(struct queue *q, fsm_state_t *state)
{
	assert(q != NULL);
	assert(state != NULL);
	assert(q->rd <= q->wr);
	assert(q->wr <= q->capacity);

	if (q->rd == q->wr) { return 0; }

	*state = q->q[q->rd];
	q->rd++;

	if (q->rd == q->wr) {
		q->rd = 0;
		q->wr = 0;
	}

	return 1;
}

void
queue_free(struct queue *q)
{
	f_free(q->alloc, q->q);
	f_free(q->alloc, q);
}
