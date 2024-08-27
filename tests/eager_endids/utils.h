#ifndef UTILS_H
#define UTILS_H

#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

#include <errno.h>

#include <assert.h>

#include <re/re.h>

#include <fsm/fsm.h>
#include <fsm/bool.h>
#include <fsm/pred.h>
#include <fsm/print.h>
#include <fsm/walk.h>

#define MAX_IDS 10

#include <assert.h>

#include <fsm/fsm.h>

#define MAX_PATTERNS 8
#define MAX_INPUTS 8
#define MAX_ENDIDS 8

struct eager_endid_test {
	const char *patterns[MAX_PATTERNS];

	struct {
		const char *input;
		/* Terminated by 0. pattern[i] => id of i+1. Must be sorted. */
		fsm_end_id_t expected_ids[MAX_ENDIDS];
	} inputs[MAX_INPUTS];
};

int
run_test(const struct eager_endid_test *test, bool minimise, bool allow_extra_endids);

struct cb_info {
	size_t used;
	fsm_end_id_t ids[MAX_IDS];
};

void
append_eager_endid_cb(fsm_end_id_t id, void *opaque);

#endif
