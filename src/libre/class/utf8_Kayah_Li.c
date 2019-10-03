/* Generated by libfsm */

#include LF_HEADER

#include <stddef.h>

#include <fsm/fsm.h>

int
utf8_Kayah_Li_fsm(struct fsm *fsm, fsm_state_t x, fsm_state_t y)
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

	if (!fsm_addedge_literal(fsm, s[0], s[1], 0xea)) { return 0; }
	if (!fsm_addedge_literal(fsm, s[1], s[2], 0xa4)) { return 0; }
	for (i = 0x80; i <= 0xad; i++) {
		if (!fsm_addedge_literal(fsm, s[2], s[3], i)) { return 0; }
	}
	if (!fsm_addedge_literal(fsm, s[2], s[3], 0xaf)) { return 0; }

	return 1;
}

