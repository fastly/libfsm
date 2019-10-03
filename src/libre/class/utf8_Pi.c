/* Generated by libfsm */

#include LF_HEADER

#include <stddef.h>

#include <fsm/fsm.h>

int
utf8_Pi_fsm(struct fsm *fsm, fsm_state_t x, fsm_state_t y)
{
	fsm_state_t s[6];
	size_t i;

	for (i = 0; i < 6; i++) {
		if (i == 0) {
			s[0] = x;
			continue;
		}

		if (i == 5) {
			s[5] = y;
			continue;
		}

		if (!fsm_addstate(fsm, &s[i])) {
			return 0;
		}
	}

	if (!fsm_addedge_literal(fsm, s[0], s[1], 0xc2)) { return 0; }
	if (!fsm_addedge_literal(fsm, s[0], s[2], 0xe2)) { return 0; }
	if (!fsm_addedge_literal(fsm, s[1], s[5], 0xab)) { return 0; }
	if (!fsm_addedge_literal(fsm, s[2], s[3], 0x80)) { return 0; }
	if (!fsm_addedge_literal(fsm, s[2], s[4], 0xb8)) { return 0; }
	if (!fsm_addedge_literal(fsm, s[3], s[5], 0x98)) { return 0; }
	for (i = 0x9b; i <= 0x9c; i++) {
		if (!fsm_addedge_literal(fsm, s[3], s[5], i)) { return 0; }
	}
	if (!fsm_addedge_literal(fsm, s[3], s[5], 0x9f)) { return 0; }
	if (!fsm_addedge_literal(fsm, s[3], s[5], 0xb9)) { return 0; }
	if (!fsm_addedge_literal(fsm, s[4], s[5], 0x82)) { return 0; }
	if (!fsm_addedge_literal(fsm, s[4], s[5], 0x84)) { return 0; }
	if (!fsm_addedge_literal(fsm, s[4], s[5], 0x89)) { return 0; }
	if (!fsm_addedge_literal(fsm, s[4], s[5], 0x8c)) { return 0; }
	if (!fsm_addedge_literal(fsm, s[4], s[5], 0x9c)) { return 0; }
	if (!fsm_addedge_literal(fsm, s[4], s[5], 0xa0)) { return 0; }

	return 1;
}

