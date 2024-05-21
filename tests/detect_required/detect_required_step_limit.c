#include "testutil.h"

#include <re/re.h>
#include <fsm/fsm.h>
#include <fsm/options.h>
#include <fsm/walk.h>
#include <adt/bitmap.h>
#include <fsm/print.h>

static const struct fsm_options opt;

int main()
{
	enum re_flags flags = 0;
	struct re_err err;
	const char *regex = "^abcde$";
	
	struct fsm *fsm = re_comp(RE_PCRE, fsm_sgetc, &regex, &opt, flags, &err);
	assert(fsm != NULL);

	if (!fsm_determinise(fsm)) {
		assert(!"determinise");
		return EXIT_FAILURE;
	}
	if (!fsm_minimise(fsm)) {
		assert(!"minimise");
		return EXIT_FAILURE;
	}

	struct bm bitmap;

	/* keep decreasing the step limit until it's hit, and check that
	 * the bitmap is cleared. */
	bool hit_step_limit = false;
	size_t step_limit = 25;
	while (!hit_step_limit) {
		assert(step_limit > 0);

		const enum fsm_detect_required_characters_res res = fsm_detect_required_characters(fsm, step_limit, &bitmap);
		if (res == FSM_DETECT_REQUIRED_CHARACTERS_STEP_LIMIT_REACHED) {
			hit_step_limit = true;

			/* this should not contain any partially complete information */
			for (size_t i = 0; i < 4; i++) {
				const uint64_t *w = bm_nth_word(&bitmap, i);
				if (*w != 0) {
					fprintf(stderr, "-- Test failure: partial information set when step limit reached\n");
					return EXIT_FAILURE;
				}
			}
		}
		
		step_limit--;
	}

	fsm_free(fsm);
	return EXIT_SUCCESS;
}
