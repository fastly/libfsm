/* Generated by libfsm */

#include LF_HEADER

#include <stddef.h>

#include <fsm/fsm.h>

struct fsm *
class_cntrl_fsm(const struct fsm_options *opt)
{
	struct fsm *fsm;
	size_t i;

	struct fsm_state *s[2] = { 0 };

	fsm = fsm_new(opt);
	if (fsm == NULL) {
		return NULL;
	}

	for (i = 0; i < 2; i++) {
		s[i] = fsm_addstate(fsm);
		if (s[i] == NULL) {
			goto error;
		}
	}

	if (!fsm_addedge_literal(fsm, s[0], s[1], '\000')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\001')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\002')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\003')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\004')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\005')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\006')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\007')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\010')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\t')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\n')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\v')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\f')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\r')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\016')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\017')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\020')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\021')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\022')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\023')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\024')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\025')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\026')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\027')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\030')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\031')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\032')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\033')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\034')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\035')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\036')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\037')) { goto error; }
	if (!fsm_addedge_literal(fsm, s[0], s[1], '\177')) { goto error; }

	fsm_setstart(fsm, s[0]);
	fsm_setend(fsm, s[1], 1);

	return fsm;

error:

	fsm_free(fsm);

	return NULL;
}
