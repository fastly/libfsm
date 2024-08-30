#include "utils.h"

void
append_eager_endid_cb(fsm_end_id_t id, void *opaque)
{
	struct cb_info *info = (struct cb_info *)opaque;
	assert(info->used < MAX_IDS);

	for (size_t i = 0; i < info->used; i++) {
		if (info->ids[i] == id) {
			return;	/* already present */
		}
	}

	info->ids[info->used++] = id;
}

static int
cmp_endid(const void *pa, const void *pb)
{
	const fsm_end_id_t a = *(fsm_end_id_t *)pa;
	const fsm_end_id_t b = *(fsm_end_id_t *)pb;
	return a < b ? -1 : a > b ? 1 : 0;
}

int
run_test(const struct eager_endid_test *test, bool minimise, bool allow_extra_endids)
{
	struct fsm *fsms[MAX_PATTERNS] = {0};
	size_t fsms_used = 0;
	int ret;

	const bool log = getenv("LOG") != NULL;

	for (size_t i = 0; i < MAX_PATTERNS; i++) {
		const char *p = test->patterns[i];
		if (test->patterns[i] == NULL) { break; }

		struct fsm *fsm = re_comp(RE_NATIVE, fsm_sgetc, &p, NULL, 0, NULL);
		assert(fsm != NULL);

		/* Zero is used to terminate expected_ids, so don't use it here. */
		const fsm_end_id_t endid = (fsm_end_id_t) (i + 1);
		ret = fsm_seteagerendid(fsm, endid);
		assert(ret == 1);

		if (log) {
			fprintf(stderr, "==== source DFA %zd (pre det+min)\\n", i);
			fsm_dump_dot(stderr, fsm);
			fsm_eager_endid_dump(stderr, fsm);
			fprintf(stderr, "====\n");
		}

		// consolidate_edges

		ret = fsm_determinise(fsm);
		assert(ret == 1);

		if (minimise) {
			ret = fsm_minimise(fsm);
			assert(ret == 1);
		}

		/* TODO: assert that it doesn't match the empty string?
		 * Eager endids will always report true for those, no matter the input. */

		if (log) {
			fprintf(stderr, "==== source DFA %zd (post det+min)\\n", i);
			fsm_dump_dot(stderr, fsm);
			fsm_eager_endid_dump(stderr, fsm);
			fprintf(stderr, "====\n");
		}

		fsms[fsms_used++] = fsm;
	}

	/* If there's only one pattern this just returns fsms[0]. */
	struct fsm *fsm = fsm_union_array(fsms_used, fsms, NULL);
	assert(fsm != NULL);

	if (log) {
		fprintf(stderr, "==== combined (pre det+min)\\n");
		fsm_dump_dot(stderr, fsm);
		fsm_eager_endid_dump(stderr, fsm);
		fprintf(stderr, "====\n");
	}

	ret = fsm_determinise(fsm);
	assert(ret == 1);

	if (minimise) {
		ret = fsm_minimise(fsm);
		assert(ret == 1);
	}

	if (log) {
		fprintf(stderr, "==== combined (post det+min)\n");
		fsm_dump_dot(stderr, fsm);
		fsm_eager_endid_dump(stderr, fsm);
		fprintf(stderr, "====\n");
	}


	struct cb_info endids = { 0 };
	fsm_eager_endid_set_cb(fsm, append_eager_endid_cb, &endids);

	for (size_t i_i = 0; i_i < MAX_INPUTS; i_i++) {
		endids.used = 0;
		const char *input = test->inputs[i_i].input;
		if (input == NULL) { break; }

		size_t expected_id_count = 0;
		for (size_t id_i = 0; id_i < MAX_ENDIDS; id_i++) {
			const fsm_end_id_t id = test->inputs[i_i].expected_ids[id_i];
			if (id == 0) { break; }
			expected_id_count++;

			/* must be ascending */
			if (id_i > 0) {
				assert(id > test->inputs[i_i].expected_ids[id_i - 1]);
			}
		}

		if (log) {
			fprintf(stderr, "%s: input %zd: \"%s\", expecting %zd ids:",
			    __func__, i_i, input, expected_id_count);
			for (size_t i = 0; i < expected_id_count; i++) {
				fprintf(stderr, " %d", test->inputs[i_i].expected_ids[i]);
			}
			fprintf(stderr, "\n");
		}

		fsm_state_t end;
		ret = fsm_exec(fsm, fsm_sgetc, &input, &end, NULL);
		if (expected_id_count == 0) {
			assert(ret == 0); /* no match */
		} else {
			assert(ret == 1);
		}

		/* NEXT match IDs, sort endids[] buffer first */
		qsort(endids.ids, endids.used, sizeof(endids.ids[0]), cmp_endid);

		if (log) {
			fprintf(stderr, "-- got %zd:", endids.used);
			for (size_t i = 0; i < endids.used; i++) {
				fprintf(stderr, " %d", endids.ids[i]);
			}
			fprintf(stderr, "\n");
		}

		if (!allow_extra_endids) {
			assert(endids.used == expected_id_count);
		} else {
			assert(endids.used >= expected_id_count);
		}

		size_t floor = 0;
		for (size_t exp_i = 0; exp_i < endids.used; exp_i++) {
			bool found = false;
			for (size_t got_i = floor; got_i < endids.used; got_i++) {
				if (endids.ids[got_i] == test->inputs[i_i].expected_ids[exp_i]) {
					floor = got_i + 1;
					found = true;
					break;
				}
			}
			assert(found);
		}
	}

        fsm_free(fsm);

	return EXIT_SUCCESS;;
}
