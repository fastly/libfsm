#include "utils.h"

void
fsm_eager_output_dump(FILE *f, const struct fsm *fsm);

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

		struct fsm *fsm = re_comp(RE_NATIVE, fsm_sgetc, &p, NULL, 0, NULL);
		assert(fsm != NULL);

		/* Zero is used to terminate expected_ids, so don't use it here. */
		const fsm_output_id_t output = (fsm_output_id_t) (i + 1);
		ret = fsm_seteageroutputonends(fsm, output);
		assert(ret == 1);

		if (log) {
			fprintf(stderr, "==== source DFA %zd (pre det+min)\n", i);
			if (log > 1) { dump(fsm); }
			fsm_eager_output_dump(stderr, fsm);
			fprintf(stderr, "====\n");
		}

		// consolidate_edges

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

		entries[fsms_used++].fsm = fsm;
	}

	/* If there's only one pattern this just returns fsms[0]. */
	/* struct fsm *fsm = fsm_union_array(fsms_used, fsms, NULL); */
	struct fsm *fsm = fsm_union_repeated_pattern_group(fsms_used, entries, NULL);
	assert(fsm != NULL);

	if (log) {
		fprintf(stderr, "==== combined (pre det+min)\n");
		if (log > 1) { dump(fsm); }
		fsm_eager_output_dump(stderr, fsm);
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
			fprintf(stderr, "\n");
		}

		fsm_state_t end;
		ret = fsm_exec(fsm, fsm_sgetc, &input, &end, NULL);
		if (expected_id_count == 0) {
			assert(ret == 0); /* no match */
		} else {
			assert(ret == 1);
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
