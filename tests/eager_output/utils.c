#include "utils.h"

void
fsm_eager_output_dump(FILE *f, const struct fsm *fsm);

void
fsm_endid_dump(FILE *f, const struct fsm *fsm);

void
append_eager_output_cb(fsm_output_id_t id, void *opaque)
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

int
cmp_output(const void *pa, const void *pb)
{
	const fsm_output_id_t a = *(fsm_output_id_t *)pa;
	const fsm_output_id_t b = *(fsm_output_id_t *)pb;
	return a < b ? -1 : a > b ? 1 : 0;
}

struct fsm_options print_options = {
	.consolidate_edges = 1,
	.comments = 0,
	.group_edges = 1,
};

void
dump(const struct fsm *fsm)
{
	fsm_print(stderr, fsm,
	    &print_options, NULL, FSM_PRINT_DOT);
}

int
run_test(const struct eager_output_test *test, bool minimise, bool allow_extra_outputs)
{
	struct fsm_union_entry entries[MAX_PATTERNS] = {0};

	allow_extra_outputs = false;

	size_t fsms_used = 0;
	int ret;

	int log = 0;
	{
		const char *logstr = getenv("LOG");
		if (logstr != NULL) {
			if (logstr[0] == 'y') { /* make "y" or "yes" non-zero */
				logstr = "1";
			}
			log = atoi(logstr);
		}
	}

	for (size_t i = 0; i < MAX_PATTERNS; i++) {
		const char *p = test->patterns[i];
		if (test->patterns[i] == NULL) { break; }
		const size_t len = strlen(p);
		struct fsm_union_entry *e = &entries[fsms_used];

		/* For sake of these patterns, they are anchored if the first/last
		 * character is '^' and '$', respectively. This is too simplistic
		 * for the general case, though. */
		if (len > 0) {
			if (p[0] == '^') { e->anchored_start = true; }
			if (p[len - 1] == '$') { e->anchored_end = true; }
			/* fprintf(stderr, "%s: p[%zd]: '%s', start %d, end %d\n", */
			/*     __func__, fsms_used, p, e->anchored_start, e->anchored_end); */
		}

		struct fsm *fsm = re_comp(RE_NATIVE, fsm_sgetc, &p, NULL, 0, NULL);
		assert(fsm != NULL);

		/* Zero is used to terminate expected_ids, so don't use it here. */
		const fsm_output_id_t output_id = (fsm_output_id_t) (i + 1);
		const fsm_end_id_t end_id = (fsm_end_id_t) (i + 1);

		/* Set either an end ID or an eager output ID, depending on
		 * whether the fsm is anchored at the end or not. */
		if (e->anchored_end) {
			ret = fsm_setendid(fsm, end_id);
		} else {
			ret = fsm_seteageroutputonends(fsm, output_id);
		}
		assert(ret == 1);

		if (log) {
			fprintf(stderr, "==== source DFA %zd (pre det+min)\n", i);
			if (log > 1) { dump(fsm); }
			fsm_eager_output_dump(stderr, fsm);
			fsm_endid_dump(stderr, fsm);
			fprintf(stderr, "====\n");
		}

		ret = fsm_determinise(fsm);
		assert(ret == 1);

		if (log) {
			fprintf(stderr, "==== source DFA %zd (post det)\n", i);
			if (log > 1) { dump(fsm); }
			fsm_eager_output_dump(stderr, fsm);
			fprintf(stderr, "====\n");
		}

		if (minimise) {
			ret = fsm_minimise(fsm);
			assert(ret == 1);
		}

		/* TODO: assert that it doesn't match the empty string?
		 * Eager outputs will always report true for those, no matter the input. */

		if (log) {
			fprintf(stderr, "==== source DFA %zd (post det+min)\n", i);
			if (log > 1) { dump(fsm); }
			fsm_eager_output_dump(stderr, fsm);
			fprintf(stderr, "====\n");
		}

		e->fsm = fsm;
		fsms_used++;
	}

	/* If there's only one pattern this just returns fsms[0]. */
	/* struct fsm *fsm = fsm_union_array(fsms_used, fsms, NULL); */
	struct fsm *fsm = fsm_union_repeated_pattern_group(fsms_used, entries, NULL);
	assert(fsm != NULL);

	if (log) {
		fprintf(stderr, "==== combined (pre det+min)\n");
		if (log > 1) { dump(fsm); }
		fsm_eager_output_dump(stderr, fsm);
		fprintf(stderr, "--- endids:\n");
		fsm_endid_dump(stderr, fsm);
		fprintf(stderr, "====\n");
	}

	fprintf(stderr, "=== determinising combined... NFA has %u states\n", fsm_countstates(fsm));
	ret = fsm_determinise(fsm);
	assert(ret == 1);
	fprintf(stderr, "=== determinising combined...done, DFA has %u states\n", fsm_countstates(fsm));

	if (log) {
		fprintf(stderr, "==== combined (post det)\n");
		if (log > 1) { dump(fsm); }
		fsm_eager_output_dump(stderr, fsm);
		fprintf(stderr, "====\n");
	}

	if (minimise) {
		ret = fsm_minimise(fsm);
		fprintf(stderr, "=== minimised combined...done, DFA has %u states\n", fsm_countstates(fsm));
		assert(ret == 1);
	}

	if (log) {
		fprintf(stderr, "==== combined (post det+min)\n");
		if (log > 1) { dump(fsm); }
		fsm_eager_output_dump(stderr, fsm);
		fprintf(stderr, "--- endids:\n");
		fsm_endid_dump(stderr, fsm);
		fprintf(stderr, "====\n");
	}

	struct cb_info outputs = { 0 };
	fsm_eager_output_set_cb(fsm, append_eager_output_cb, &outputs);

	for (size_t i_i = 0; i_i < MAX_INPUTS; i_i++) {
		outputs.used = 0;
		const char *input = test->inputs[i_i].input;
		if (input == NULL) { break; }

		size_t expected_id_count = 0;
		for (size_t id_i = 0; id_i < MAX_ENDIDS; id_i++) {
			const fsm_output_id_t id = test->inputs[i_i].expected_ids[id_i];
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
		}

		if (test->inputs[i_i].expect_fail) {
			expected_id_count = 0;
		}

		fsm_state_t end;
		ret = fsm_exec(fsm, fsm_sgetc, &input, &end, NULL);

		{
#define ENDID_BUF_SIZE 32
			fsm_end_id_t endid_buf[ENDID_BUF_SIZE] = {0};
			const size_t endid_count = fsm_endid_count(fsm, end);
			/* fprintf(stderr, "%s: endid_count %zd for state %d\n", __func__, endid_count, end); */
			assert(endid_count < ENDID_BUF_SIZE);
			if (!fsm_endid_get(fsm, end, /*ENDID_BUF_SIZE*/ endid_count, endid_buf)) {
				assert(!"fsm_endid_get failed");
			}

			/* Copy endid outputs into outputs.ids[], since for testing
			 * purposes we don't care about the difference between eager
			 * output and endids here -- the values don't overlap. */
			assert(outputs.used + endid_count <= MAX_IDS);
			for (size_t endid_i = 0; endid_i < endid_count; endid_i++) {
				fprintf(stderr, "-- adding endid %zd: %d\n", endid_i, endid_buf[endid_i]);
				outputs.ids[outputs.used++] = (fsm_output_id_t)endid_buf[endid_i];
			}
		}

		if (ret == 0) {
			/* if it didn't match, ignore the eager output IDs. this should
			 * eventually happen internal to fsm_exec or codegen. */
			outputs.used = 0;
		}

		/* NEXT match IDs, sort outputs[] buffer first */
		qsort(outputs.ids, outputs.used, sizeof(outputs.ids[0]), cmp_output);

		if (log) {
			fprintf(stderr, "-- got %zd:", outputs.used);
			for (size_t i = 0; i < outputs.used; i++) {
				fprintf(stderr, " %d", outputs.ids[i]);
			}
			fprintf(stderr, "\n");
		}

		if (expected_id_count == 0) {
			assert(ret == 0 || outputs.used == 0); /* no match */
			continue;
		} else {
			assert(ret == 1);
		}

		if (!allow_extra_outputs) {
			assert(outputs.used == expected_id_count);
		} else {
			assert(outputs.used >= expected_id_count);
		}

		size_t floor = 0;
		for (size_t exp_i = 0; exp_i < outputs.used; exp_i++) {
			bool found = false;
			for (size_t got_i = floor; got_i < outputs.used; got_i++) {
				if (outputs.ids[got_i] == test->inputs[i_i].expected_ids[exp_i]) {
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
