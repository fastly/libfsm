/* Generated by libfsm */

#include LF_HEADER

#include <stddef.h>

#include <fsm/fsm.h>

int
utf8_Tai_Le_fsm(struct fsm *fsm, fsm_state_t x, fsm_state_t y)
{
	fsm_state_t s[4];
	size_t i;

	for (i = 0; i < 4; i++) {
		if (i == 0) {
			s[0] = x;
			continue;
		}

		if (i == 3) {
			s[3] = y;
			continue;
		}

		if (!fsm_addstate(fsm, &s[i])) {
			return 0;
		}
	}

	if (!fsm_addedge_literal(fsm, s[0], s[1], 0xe1)) { return 0; }
	if (!fsm_addedge_literal(fsm, s[1], s[2], 0xa5)) { return 0; }
	for (i = 0x90; i <= 0xad; i++) {
		if (!fsm_addedge_literal(fsm, s[2], s[3], i)) { return 0; }
	}
	for (i = 0xb0; i <= 0xb4; i++) {
		if (!fsm_addedge_literal(fsm, s[2], s[3], i)) { return 0; }
	}

	return 1;
}

