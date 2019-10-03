/* Generated by libfsm */

#include LF_HEADER

#include <stddef.h>

#include <fsm/fsm.h>

int
utf8_Balinese_fsm(struct fsm *fsm, fsm_state_t x, fsm_state_t y)
{
	fsm_state_t s[5];
	size_t i;

	for (i = 0; i < 5; i++) {
		if (i == 0) {
			s[0] = x;
			continue;
		}

		if (i == 4) {
			s[4] = y;
			continue;
		}

		if (!fsm_addstate(fsm, &s[i])) {
			return 0;
		}
	}

	if (!fsm_addedge_literal(fsm, s[0], s[1], 0xe1)) { return 0; }
	if (!fsm_addedge_literal(fsm, s[1], s[2], 0xac)) { return 0; }
	if (!fsm_addedge_literal(fsm, s[1], s[3], 0xad)) { return 0; }
	for (i = 0x80; i <= 0xbf; i++) {
		if (!fsm_addedge_literal(fsm, s[2], s[4], i)) { return 0; }
	}
	for (i = 0x80; i <= 0x8b; i++) {
		if (!fsm_addedge_literal(fsm, s[3], s[4], i)) { return 0; }
	}
	for (i = 0x90; i <= 0xbc; i++) {
		if (!fsm_addedge_literal(fsm, s[3], s[4], i)) { return 0; }
	}

	return 1;
}

