#include "utils.h"

void
fsm_eager_output_dump(FILE *f, const struct fsm *fsm);

static bool
link_repeated_char(struct fsm *fsm, char c, size_t count,
    fsm_state_t from, fsm_state_t end, fsm_state_t loop_back_to, fsm_output_id_t output_id)
{
	fsm_state_t eps;
	if (!fsm_addstate(fsm, &eps)) { return false; }
	if (!fsm_addedge_epsilon(fsm, from, eps)) { return false; }

	fsm_state_t cur = eps;
	fsm_state_t new;
	for (size_t i = 0; i < count; i++) {
		if (!fsm_addstate(fsm, &new)) { return false; }
		if (!fsm_addedge_literal(fsm, cur, new, c)) { return false; }
		cur = new;
	}

	/* fsm_setend(fsm, cur, 1); */

	if (!fsm_seteageroutput(fsm, cur, output_id)) { return false; }

	if (!fsm_addedge_epsilon(fsm, cur, end)) { return false; }
	if (!fsm_addedge_epsilon(fsm, cur, loop_back_to)) { return false; }
	
	return true;
}

static bool
link_string(struct fsm *fsm, const char *s,
    fsm_state_t from, fsm_state_t end, fsm_state_t loop_back_to, fsm_output_id_t output_id)
{
	fsm_state_t eps;
	if (!fsm_addstate(fsm, &eps)) { return false; }
	if (!fsm_addedge_epsilon(fsm, from, eps)) { return false; }

	const size_t len = strlen(s);

	fsm_state_t cur = eps;
	fsm_state_t new;
	for (size_t i = 0; i < len; i++) {
		if (!fsm_addstate(fsm, &new)) { return false; }
		if (!fsm_addedge_literal(fsm, cur, new, s[i])) { return false; }
		if (!fsm_addedge_any(fsm, cur, loop_back_to)) { return false; }
		cur = new;
	}

	if (!fsm_seteageroutput(fsm, cur, output_id)) { return false; }

	if (!fsm_addedge_epsilon(fsm, cur, end)) { return false; }
	if (!fsm_addedge_epsilon(fsm, cur, loop_back_to)) { return false; }
	
	return true;
}

#define ALL 1
const char *strings[] = {
			"apple",
			"banana",
			"carrot",
			"durian",
#if ALL
			"eggplant",
			"fig",
			"grapefruit",
			"hazelnut",
			"iceberg lettuce",
			"jicama",
			"kiwano",
			"lemon",
			"mango",
			"nectarine",
			"orange",
			"plum",
			"quince",
			"radish",
			"strawberry",
			"turnip",
			"ube",
			"vanilla",
			"watermelon",
			"xigua watermelon", /* Chinese */
			"yam",
			"zucchini",
#endif
};

int main(void)
{
	/* construct fsm with aa, bb, cc, dd and eager endids */
	struct fsm *fsm = fsm_new_statealloc(NULL, 20);
	assert(fsm != NULL);

	bool log = getenv("LOG");

	fsm_state_t start, end;
	if (!fsm_addstate(fsm, &start)) { goto fail; }
	if (!fsm_addstate(fsm, &end)) { goto fail; }

	fsm_setstart(fsm, start);
	fsm_setend(fsm, end, 1);

	/* if (!link_repeated_char(fsm, 'a', 3, start, end, start, 1)) { goto fail; } */
	/* if (!link_repeated_char(fsm, 'b', 3, start, end, start, 2)) { goto fail; } */
	/* if (!link_repeated_char(fsm, 'c', 3, start, end, start, 3)) { goto fail; } */
	/* if (!link_repeated_char(fsm, 'd', 3, start, end, start, 4)) { goto fail; } */
	(void)link_repeated_char;

	/* unanchored start */
	if (!fsm_addedge_epsilon(fsm, start, start)) { return false; }

	/* unanchored end */
	if (!fsm_addedge_epsilon(fsm, end, end)) { return false; }


	const size_t string_count = sizeof(strings)/sizeof(strings[0]);
	for (size_t i = 0; i < string_count; i++) {
		const char *s = strings[i];
		if (!link_string(fsm, s, start, end, start, i + 1)) { goto fail; }
	}
	

	fprintf(stderr, "==== pre det: %d states\n", fsm_countstates(fsm));
	if (log) {
		dump(fsm);
		fsm_eager_output_dump(stderr, fsm);
		fprintf(stderr, "====\n");
	}

	if (!fsm_determinise(fsm)) { goto fail; }

	fprintf(stderr, "==== post det: %d states\n", fsm_countstates(fsm));
	if (log) {
		dump(fsm);
		fsm_eager_output_dump(stderr, fsm);
		fprintf(stderr, "====\n");
	}

	if (!fsm_minimise(fsm)) { goto fail; }

	fprintf(stderr, "==== post min: %d states\n", fsm_countstates(fsm));
	if (log) {
		dump(fsm);
		fsm_eager_output_dump(stderr, fsm);
		fprintf(stderr, "====\n");
	}

	const char *input = getenv("INPUT");
	if (input) {
		struct cb_info outputs = { 0 };
		fsm_eager_output_set_cb(fsm, append_eager_output_cb, &outputs);
		fsm_state_t end;
		int ret = fsm_exec(fsm, fsm_sgetc, &input, &end, NULL);

		qsort(outputs.ids, outputs.used, sizeof(outputs.ids[0]), cmp_output);

		fprintf(stderr, "-- got ret %d, %zd:", ret, outputs.used);
		for (size_t i = 0; i < outputs.used; i++) {
			fprintf(stderr, " %d", outputs.ids[i]);
		}
		fprintf(stderr, "\n");
	}

	fsm_free(fsm);
	return EXIT_SUCCESS;

fail:
	fprintf(stderr, "%s: failed\n", __func__);
	return EXIT_FAILURE;
}
