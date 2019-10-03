/* Generated by libfsm */

#include LF_HEADER

#include <stddef.h>

#include <fsm/fsm.h>

int
utf8_Tibetan_fsm(struct fsm *fsm, fsm_state_t x, fsm_state_t y)
{
	fsm_state_t s[7];
	size_t i;

	for (i = 0; i < 7; i++) {
		if (i == 0) {
			s[0] = x;
			continue;
		}

		if (i == 6) {
			s[6] = y;
			continue;
		}

		if (!fsm_addstate(fsm, &s[i])) {
			return 0;
		}
	}

	if (!fsm_addedge_literal(fsm, s[0], s[1], 0xe0)) { return 0; }
	if (!fsm_addedge_literal(fsm, s[1], s[2], 0xbc)) { return 0; }
	if (!fsm_addedge_literal(fsm, s[1], s[3], 0xbd)) { return 0; }
	if (!fsm_addedge_literal(fsm, s[1], s[4], 0xbe)) { return 0; }
	if (!fsm_addedge_literal(fsm, s[1], s[5], 0xbf)) { return 0; }
	for (i = 0x80; i <= 0xbf; i++) {
		if (!fsm_addedge_literal(fsm, s[2], s[6], i)) { return 0; }
	}
	for (i = 0x80; i <= 0x87; i++) {
		if (!fsm_addedge_literal(fsm, s[3], s[6], i)) { return 0; }
	}
	for (i = 0x89; i <= 0xac; i++) {
		if (!fsm_addedge_literal(fsm, s[3], s[6], i)) { return 0; }
	}
	for (i = 0xb1; i <= 0xbf; i++) {
		if (!fsm_addedge_literal(fsm, s[3], s[6], i)) { return 0; }
	}
	for (i = 0x80; i <= 0x97; i++) {
		if (!fsm_addedge_literal(fsm, s[4], s[6], i)) { return 0; }
	}
	for (i = 0x99; i <= 0xbc; i++) {
		if (!fsm_addedge_literal(fsm, s[4], s[6], i)) { return 0; }
	}
	for (i = 0xbe; i <= 0xbf; i++) {
		if (!fsm_addedge_literal(fsm, s[4], s[6], i)) { return 0; }
	}
	for (i = 0x80; i <= 0x8c; i++) {
		if (!fsm_addedge_literal(fsm, s[5], s[6], i)) { return 0; }
	}
	for (i = 0x8e; i <= 0x94; i++) {
		if (!fsm_addedge_literal(fsm, s[5], s[6], i)) { return 0; }
	}
	for (i = 0x99; i <= 0x9a; i++) {
		if (!fsm_addedge_literal(fsm, s[5], s[6], i)) { return 0; }
	}

	return 1;
}

