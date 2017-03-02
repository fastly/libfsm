/* Generated by lx */

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <errno.h>

#include LX_HEADER

static enum lx_token z0(struct lx *lx);
static enum lx_token z1(struct lx *lx);
static enum lx_token z2(struct lx *lx);
static enum lx_token z3(struct lx *lx);

static int
lx_getc(struct lx *lx)
{
	int c;

	assert(lx != NULL);
	assert(lx->lgetc != NULL);

	if (lx->c != EOF) {
		c = lx->c, lx->c = EOF;
	} else {
		c = lx->lgetc(lx);
		if (c == EOF) {
			return EOF;
		}
	}

	lx->end.byte++;
	lx->end.col++;

	if (c == '\n') {
		lx->end.line++;
		lx->end.col = 1;
	}

	return c;
}

static void
lx_ungetc(struct lx *lx, int c)
{
	assert(lx != NULL);
	assert(lx->c == EOF);

	lx->c = c;

	if (lx->pop != NULL) {
		lx->pop(lx);
	}

	lx->end.byte--;
	lx->end.col--;

	if (c == '\n') {
		lx->end.line--;
		lx->end.col = 0; /* XXX: lost information */
	}
}

int
lx_fgetc(struct lx *lx)
{
	assert(lx != NULL);
	assert(lx->opaque != NULL);

	return fgetc(lx->opaque);
}

int
lx_dynpush(struct lx *lx, char c)
{
	struct lx_dynbuf *t;

	assert(lx != NULL);
	assert(c != EOF);

	t = lx->buf;

	assert(t != NULL);

	if (t->p == t->a + t->len) {
		size_t len;
		char *tmp;

		if (t->len == 0) {
			assert(LX_DYN_LOW > 0);
			len = LX_DYN_LOW;
		} else {
			len = t->len * LX_DYN_FACTOR;
			if (len < t->len) {
				errno = ERANGE;
				return -1;
			}
		}

		tmp = realloc(t->a, len);
		if (tmp == NULL) {
			return -1;
		}

		t->p   = tmp + (t->p - t->a);
		t->a   = tmp;
		t->len = len;
	}

	assert(t->p != NULL);
	assert(t->a != NULL);

	*t->p++ = c;

	return 0;
}

void
lx_dynpop(struct lx *lx)
{
	struct lx_dynbuf *t;

	assert(lx != NULL);

	t = lx->buf;

	assert(t != NULL);
	assert(t->a != NULL);
	assert(t->p >= t->a);

	if (t->p == t->a) {
		return;
	}

	t->p--;
}

int
lx_dynclear(struct lx *lx)
{
	struct lx_dynbuf *t;

	assert(lx != NULL);

	t = lx->buf;

	assert(t != NULL);

	if (t->len > LX_DYN_HIGH) {
		size_t len;
		char *tmp;

		len = t->len / LX_DYN_FACTOR;

		tmp = realloc(t->a, len);
		if (tmp == NULL) {
			return -1;
		}

		t->a   = tmp;
		t->len = len;
	}

	t->p = t->a;

	return 0;
}

void
lx_dynfree(struct lx *lx)
{
	struct lx_dynbuf *t;

	assert(lx != NULL);

	t = lx->buf;

	assert(t != NULL);

	free(t->a);
}
static enum lx_token
z0(struct lx *lx)
{
	int c;

	enum {
		S0, S1, S2
	} state;

	assert(lx != NULL);

	if (lx->clear != NULL) {
		lx->clear(lx);
	}

	state = S2;

	lx->start = lx->end;

	while (c = lx_getc(lx), c != EOF) {
		if (lx->push != NULL) {
			if (-1 == lx->push(lx, c)) {
				return TOK_ERROR;
			}
		}

		switch (state) {
		case S0: /* e.g. "a" */
			lx_ungetc(lx, c); return TOK_CHAR;

		case S1: /* e.g. "\'" */
			lx_ungetc(lx, c); return lx->z = z3, TOK_LABEL;

		case S2: /* start */
			switch (c) {
			case '\'': state = S1; continue;
			default:  state = S0; continue;
			}
		}
	}

	lx->lgetc = NULL;

	switch (state) {
	case S0: return TOK_CHAR;
	case S1: return TOK_LABEL;
	default: errno = EINVAL; return TOK_ERROR;
	}
}

static enum lx_token
z1(struct lx *lx)
{
	int c;

	enum {
		S0, S1, S2, S3, S4, S5, S6, S7
	} state;

	assert(lx != NULL);

	if (lx->clear != NULL) {
		lx->clear(lx);
	}

	state = S7;

	lx->start = lx->end;

	while (c = lx_getc(lx), c != EOF) {
		if (lx->push != NULL) {
			if (-1 == lx->push(lx, c)) {
				return TOK_ERROR;
			}
		}

		switch (state) {
		case S0: /* e.g. "\\xa" */
			switch (c) {
			case '0':
			case '1':
			case '2':
			case '3':
			case '4':
			case '5':
			case '6':
			case '7':
			case '8':
			case '9':             continue;
			case 'A':
			case 'B':
			case 'C':
			case 'D':
			case 'E':
			case 'F':             continue;
			case 'a':
			case 'b':
			case 'c':
			case 'd':
			case 'e':
			case 'f':             continue;
			default:  lx_ungetc(lx, c); return TOK_HEX;
			}

		case S1: /* e.g. "\\f" */
			lx_ungetc(lx, c); return TOK_ESC;

		case S2: /* e.g. "\\0" */
			switch (c) {
			case '0':
			case '1':
			case '2':
			case '3':
			case '4':
			case '5':
			case '6':
			case '7':             continue;
			default:  lx_ungetc(lx, c); return TOK_OCT;
			}

		case S3: /* e.g. "\\x" */
			switch (c) {
			case '0':
			case '1':
			case '2':
			case '3':
			case '4':
			case '5':
			case '6':
			case '7':
			case '8':
			case '9': state = S0; continue;
			case 'A':
			case 'B':
			case 'C':
			case 'D':
			case 'E':
			case 'F': state = S0; continue;
			case 'a':
			case 'b':
			case 'c':
			case 'd':
			case 'e':
			case 'f': state = S0; continue;
			default:  lx_ungetc(lx, c); return TOK_CHAR;
			}

		case S4: /* e.g. "\\" */
			switch (c) {
			case '"': state = S1; continue;
			case '0':
			case '1':
			case '2':
			case '3':
			case '4':
			case '5':
			case '6':
			case '7': state = S2; continue;
			case '\\': state = S1; continue;
			case 'f': state = S1; continue;
			case 'n': state = S1; continue;
			case 'r': state = S1; continue;
			case 't': state = S1; continue;
			case 'v': state = S1; continue;
			case 'x': state = S3; continue;
			default:  lx_ungetc(lx, c); return TOK_CHAR;
			}

		case S5: /* e.g. """ */
			lx_ungetc(lx, c); return lx->z = z3, TOK_LABEL;

		case S6: /* e.g. "a" */
			lx_ungetc(lx, c); return TOK_CHAR;

		case S7: /* start */
			switch (c) {
			case '"': state = S5; continue;
			case '\\': state = S4; continue;
			default:  state = S6; continue;
			}
		}
	}

	lx->lgetc = NULL;

	switch (state) {
	case S0: return TOK_HEX;
	case S1: return TOK_ESC;
	case S2: return TOK_OCT;
	case S3: return TOK_CHAR;
	case S4: return TOK_CHAR;
	case S5: return TOK_LABEL;
	case S6: return TOK_CHAR;
	default: errno = EINVAL; return TOK_ERROR;
	}
}

static enum lx_token
z2(struct lx *lx)
{
	int c;

	enum {
		S0, S1, S2
	} state;

	assert(lx != NULL);

	if (lx->clear != NULL) {
		lx->clear(lx);
	}

	state = S2;

	lx->start = lx->end;

	while (c = lx_getc(lx), c != EOF) {
		switch (state) {
		case S0:
		case S1:
		case S2:
			break;

		default:
			if (lx->push != NULL) {
				if (-1 == lx->push(lx, c)) {
					return TOK_ERROR;
				}
			}
			break;

		}

		switch (state) {
		case S0: /* e.g. "a" */
			lx_ungetc(lx, c); return lx->z(lx);

		case S1: /* e.g. "\n" */
			lx_ungetc(lx, c); return lx->z = z3, lx->z(lx);

		case S2: /* start */
			switch (c) {
			case '\n': state = S1; continue;
			default:  state = S0; continue;
			}
		}
	}

	lx->lgetc = NULL;

	switch (state) {
	case S0: return TOK_EOF;
	case S1: return TOK_EOF;
	default: errno = EINVAL; return TOK_ERROR;
	}
}

static enum lx_token
z3(struct lx *lx)
{
	int c;

	enum {
		S0, S1, S2, S3, S4, S5, S6, S7, S8, S9, 
		S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, 
		S20
	} state;

	assert(lx != NULL);

	if (lx->clear != NULL) {
		lx->clear(lx);
	}

	state = S20;

	lx->start = lx->end;

	while (c = lx_getc(lx), c != EOF) {
		switch (state) {
		case S9:
		case S10:
		case S12:
		case S18:
			break;

		default:
			if (lx->push != NULL) {
				if (-1 == lx->push(lx, c)) {
					return TOK_ERROR;
				}
			}
			break;

		}

		switch (state) {
		case S0: /* e.g. "->" */
			lx_ungetc(lx, c); return TOK_TO;

		case S1: /* e.g. "end:" */
			lx_ungetc(lx, c); return TOK_END;

		case S2: /* e.g. "end" */
			switch (c) {
			case '0':
			case '1':
			case '2':
			case '3':
			case '4':
			case '5':
			case '6':
			case '7':
			case '8':
			case '9': state = S15; continue;
			case ':': state = S1; continue;
			case 'A':
			case 'B':
			case 'C':
			case 'D':
			case 'E':
			case 'F':
			case 'G':
			case 'H':
			case 'I':
			case 'J':
			case 'K':
			case 'L':
			case 'M':
			case 'N':
			case 'O':
			case 'P':
			case 'Q':
			case 'R':
			case 'S':
			case 'T':
			case 'U':
			case 'V':
			case 'W':
			case 'X':
			case 'Y':
			case 'Z': state = S15; continue;
			case '_': state = S15; continue;
			case 'a':
			case 'b':
			case 'c':
			case 'd':
			case 'e':
			case 'f':
			case 'g':
			case 'h':
			case 'i':
			case 'j':
			case 'k':
			case 'l':
			case 'm':
			case 'n':
			case 'o':
			case 'p':
			case 'q':
			case 'r':
			case 's':
			case 't':
			case 'u':
			case 'v':
			case 'w':
			case 'x':
			case 'y':
			case 'z': state = S15; continue;
			default:  lx_ungetc(lx, c); return TOK_IDENT;
			}

		case S3: /* e.g. "en" */
			switch (c) {
			case '0':
			case '1':
			case '2':
			case '3':
			case '4':
			case '5':
			case '6':
			case '7':
			case '8':
			case '9': state = S15; continue;
			case 'A':
			case 'B':
			case 'C':
			case 'D':
			case 'E':
			case 'F':
			case 'G':
			case 'H':
			case 'I':
			case 'J':
			case 'K':
			case 'L':
			case 'M':
			case 'N':
			case 'O':
			case 'P':
			case 'Q':
			case 'R':
			case 'S':
			case 'T':
			case 'U':
			case 'V':
			case 'W':
			case 'X':
			case 'Y':
			case 'Z': state = S15; continue;
			case '_': state = S15; continue;
			case 'a':
			case 'b':
			case 'c': state = S15; continue;
			case 'd': state = S2; continue;
			case 'e':
			case 'f':
			case 'g':
			case 'h':
			case 'i':
			case 'j':
			case 'k':
			case 'l':
			case 'm':
			case 'n':
			case 'o':
			case 'p':
			case 'q':
			case 'r':
			case 's':
			case 't':
			case 'u':
			case 'v':
			case 'w':
			case 'x':
			case 'y':
			case 'z': state = S15; continue;
			default:  lx_ungetc(lx, c); return TOK_IDENT;
			}

		case S4: /* e.g. "start:" */
			lx_ungetc(lx, c); return TOK_START;

		case S5: /* e.g. "start" */
			switch (c) {
			case '0':
			case '1':
			case '2':
			case '3':
			case '4':
			case '5':
			case '6':
			case '7':
			case '8':
			case '9': state = S15; continue;
			case ':': state = S4; continue;
			case 'A':
			case 'B':
			case 'C':
			case 'D':
			case 'E':
			case 'F':
			case 'G':
			case 'H':
			case 'I':
			case 'J':
			case 'K':
			case 'L':
			case 'M':
			case 'N':
			case 'O':
			case 'P':
			case 'Q':
			case 'R':
			case 'S':
			case 'T':
			case 'U':
			case 'V':
			case 'W':
			case 'X':
			case 'Y':
			case 'Z': state = S15; continue;
			case '_': state = S15; continue;
			case 'a':
			case 'b':
			case 'c':
			case 'd':
			case 'e':
			case 'f':
			case 'g':
			case 'h':
			case 'i':
			case 'j':
			case 'k':
			case 'l':
			case 'm':
			case 'n':
			case 'o':
			case 'p':
			case 'q':
			case 'r':
			case 's':
			case 't':
			case 'u':
			case 'v':
			case 'w':
			case 'x':
			case 'y':
			case 'z': state = S15; continue;
			default:  lx_ungetc(lx, c); return TOK_IDENT;
			}

		case S6: /* e.g. "star" */
			switch (c) {
			case '0':
			case '1':
			case '2':
			case '3':
			case '4':
			case '5':
			case '6':
			case '7':
			case '8':
			case '9': state = S15; continue;
			case 'A':
			case 'B':
			case 'C':
			case 'D':
			case 'E':
			case 'F':
			case 'G':
			case 'H':
			case 'I':
			case 'J':
			case 'K':
			case 'L':
			case 'M':
			case 'N':
			case 'O':
			case 'P':
			case 'Q':
			case 'R':
			case 'S':
			case 'T':
			case 'U':
			case 'V':
			case 'W':
			case 'X':
			case 'Y':
			case 'Z': state = S15; continue;
			case '_': state = S15; continue;
			case 'a':
			case 'b':
			case 'c':
			case 'd':
			case 'e':
			case 'f':
			case 'g':
			case 'h':
			case 'i':
			case 'j':
			case 'k':
			case 'l':
			case 'm':
			case 'n':
			case 'o':
			case 'p':
			case 'q':
			case 'r':
			case 's': state = S15; continue;
			case 't': state = S5; continue;
			case 'u':
			case 'v':
			case 'w':
			case 'x':
			case 'y':
			case 'z': state = S15; continue;
			default:  lx_ungetc(lx, c); return TOK_IDENT;
			}

		case S7: /* e.g. "sta" */
			switch (c) {
			case '0':
			case '1':
			case '2':
			case '3':
			case '4':
			case '5':
			case '6':
			case '7':
			case '8':
			case '9': state = S15; continue;
			case 'A':
			case 'B':
			case 'C':
			case 'D':
			case 'E':
			case 'F':
			case 'G':
			case 'H':
			case 'I':
			case 'J':
			case 'K':
			case 'L':
			case 'M':
			case 'N':
			case 'O':
			case 'P':
			case 'Q':
			case 'R':
			case 'S':
			case 'T':
			case 'U':
			case 'V':
			case 'W':
			case 'X':
			case 'Y':
			case 'Z': state = S15; continue;
			case '_': state = S15; continue;
			case 'a':
			case 'b':
			case 'c':
			case 'd':
			case 'e':
			case 'f':
			case 'g':
			case 'h':
			case 'i':
			case 'j':
			case 'k':
			case 'l':
			case 'm':
			case 'n':
			case 'o':
			case 'p':
			case 'q': state = S15; continue;
			case 'r': state = S6; continue;
			case 's':
			case 't':
			case 'u':
			case 'v':
			case 'w':
			case 'x':
			case 'y':
			case 'z': state = S15; continue;
			default:  lx_ungetc(lx, c); return TOK_IDENT;
			}

		case S8: /* e.g. "st" */
			switch (c) {
			case '0':
			case '1':
			case '2':
			case '3':
			case '4':
			case '5':
			case '6':
			case '7':
			case '8':
			case '9': state = S15; continue;
			case 'A':
			case 'B':
			case 'C':
			case 'D':
			case 'E':
			case 'F':
			case 'G':
			case 'H':
			case 'I':
			case 'J':
			case 'K':
			case 'L':
			case 'M':
			case 'N':
			case 'O':
			case 'P':
			case 'Q':
			case 'R':
			case 'S':
			case 'T':
			case 'U':
			case 'V':
			case 'W':
			case 'X':
			case 'Y':
			case 'Z': state = S15; continue;
			case '_': state = S15; continue;
			case 'a': state = S7; continue;
			case 'b':
			case 'c':
			case 'd':
			case 'e':
			case 'f':
			case 'g':
			case 'h':
			case 'i':
			case 'j':
			case 'k':
			case 'l':
			case 'm':
			case 'n':
			case 'o':
			case 'p':
			case 'q':
			case 'r':
			case 's':
			case 't':
			case 'u':
			case 'v':
			case 'w':
			case 'x':
			case 'y':
			case 'z': state = S15; continue;
			default:  lx_ungetc(lx, c); return TOK_IDENT;
			}

		case S9: /* e.g. "#" */
			lx_ungetc(lx, c); return lx->z = z2, lx->z(lx);

		case S10: /* e.g. """ */
			lx_ungetc(lx, c); return lx->z = z1, lx->z(lx);

		case S11: /* e.g. "," */
			lx_ungetc(lx, c); return TOK_COMMA;

		case S12: /* e.g. "\'" */
			lx_ungetc(lx, c); return lx->z = z0, lx->z(lx);

		case S13: /* e.g. "s" */
			switch (c) {
			case '0':
			case '1':
			case '2':
			case '3':
			case '4':
			case '5':
			case '6':
			case '7':
			case '8':
			case '9': state = S15; continue;
			case 'A':
			case 'B':
			case 'C':
			case 'D':
			case 'E':
			case 'F':
			case 'G':
			case 'H':
			case 'I':
			case 'J':
			case 'K':
			case 'L':
			case 'M':
			case 'N':
			case 'O':
			case 'P':
			case 'Q':
			case 'R':
			case 'S':
			case 'T':
			case 'U':
			case 'V':
			case 'W':
			case 'X':
			case 'Y':
			case 'Z': state = S15; continue;
			case '_': state = S15; continue;
			case 'a':
			case 'b':
			case 'c':
			case 'd':
			case 'e':
			case 'f':
			case 'g':
			case 'h':
			case 'i':
			case 'j':
			case 'k':
			case 'l':
			case 'm':
			case 'n':
			case 'o':
			case 'p':
			case 'q':
			case 'r':
			case 's': state = S15; continue;
			case 't': state = S8; continue;
			case 'u':
			case 'v':
			case 'w':
			case 'x':
			case 'y':
			case 'z': state = S15; continue;
			default:  lx_ungetc(lx, c); return TOK_IDENT;
			}

		case S14: /* e.g. "e" */
			switch (c) {
			case '0':
			case '1':
			case '2':
			case '3':
			case '4':
			case '5':
			case '6':
			case '7':
			case '8':
			case '9': state = S15; continue;
			case 'A':
			case 'B':
			case 'C':
			case 'D':
			case 'E':
			case 'F':
			case 'G':
			case 'H':
			case 'I':
			case 'J':
			case 'K':
			case 'L':
			case 'M':
			case 'N':
			case 'O':
			case 'P':
			case 'Q':
			case 'R':
			case 'S':
			case 'T':
			case 'U':
			case 'V':
			case 'W':
			case 'X':
			case 'Y':
			case 'Z': state = S15; continue;
			case '_': state = S15; continue;
			case 'a':
			case 'b':
			case 'c':
			case 'd':
			case 'e':
			case 'f':
			case 'g':
			case 'h':
			case 'i':
			case 'j':
			case 'k':
			case 'l':
			case 'm': state = S15; continue;
			case 'n': state = S3; continue;
			case 'o':
			case 'p':
			case 'q':
			case 'r':
			case 's':
			case 't':
			case 'u':
			case 'v':
			case 'w':
			case 'x':
			case 'y':
			case 'z': state = S15; continue;
			default:  lx_ungetc(lx, c); return TOK_IDENT;
			}

		case S15: /* e.g. "a" */
			switch (c) {
			case '0':
			case '1':
			case '2':
			case '3':
			case '4':
			case '5':
			case '6':
			case '7':
			case '8':
			case '9':             continue;
			case 'A':
			case 'B':
			case 'C':
			case 'D':
			case 'E':
			case 'F':
			case 'G':
			case 'H':
			case 'I':
			case 'J':
			case 'K':
			case 'L':
			case 'M':
			case 'N':
			case 'O':
			case 'P':
			case 'Q':
			case 'R':
			case 'S':
			case 'T':
			case 'U':
			case 'V':
			case 'W':
			case 'X':
			case 'Y':
			case 'Z':             continue;
			case '_':             continue;
			case 'a':
			case 'b':
			case 'c':
			case 'd':
			case 'e':
			case 'f':
			case 'g':
			case 'h':
			case 'i':
			case 'j':
			case 'k':
			case 'l':
			case 'm':
			case 'n':
			case 'o':
			case 'p':
			case 'q':
			case 'r':
			case 's':
			case 't':
			case 'u':
			case 'v':
			case 'w':
			case 'x':
			case 'y':
			case 'z':             continue;
			default:  lx_ungetc(lx, c); return TOK_IDENT;
			}

		case S16: /* e.g. "-" */
			switch (c) {
			case '>': state = S0; continue;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}

		case S17: /* e.g. "?" */
			lx_ungetc(lx, c); return TOK_ANY;

		case S18: /* e.g. "\t" */
			switch (c) {
			case '\t':
			case '\n':             continue;
			case '\r':             continue;
			case ' ':             continue;
			default:  lx_ungetc(lx, c); return lx->z(lx);
			}

		case S19: /* e.g. ";" */
			lx_ungetc(lx, c); return TOK_SEP;

		case S20: /* start */
			switch (c) {
			case '\t':
			case '\n': state = S18; continue;
			case '\r': state = S18; continue;
			case ' ': state = S18; continue;
			case '"': state = S10; continue;
			case '#': state = S9; continue;
			case '\'': state = S12; continue;
			case ',': state = S11; continue;
			case '-': state = S16; continue;
			case '0':
			case '1':
			case '2':
			case '3':
			case '4':
			case '5':
			case '6':
			case '7':
			case '8':
			case '9': state = S15; continue;
			case ';': state = S19; continue;
			case '?': state = S17; continue;
			case 'A':
			case 'B':
			case 'C':
			case 'D':
			case 'E':
			case 'F':
			case 'G':
			case 'H':
			case 'I':
			case 'J':
			case 'K':
			case 'L':
			case 'M':
			case 'N':
			case 'O':
			case 'P':
			case 'Q':
			case 'R':
			case 'S':
			case 'T':
			case 'U':
			case 'V':
			case 'W':
			case 'X':
			case 'Y':
			case 'Z': state = S15; continue;
			case '_': state = S15; continue;
			case 'a':
			case 'b':
			case 'c':
			case 'd': state = S15; continue;
			case 'e': state = S14; continue;
			case 'f':
			case 'g':
			case 'h':
			case 'i':
			case 'j':
			case 'k':
			case 'l':
			case 'm':
			case 'n':
			case 'o':
			case 'p':
			case 'q':
			case 'r': state = S15; continue;
			case 's': state = S13; continue;
			case 't':
			case 'u':
			case 'v':
			case 'w':
			case 'x':
			case 'y':
			case 'z': state = S15; continue;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}
		}
	}

	lx->lgetc = NULL;

	switch (state) {
	case S0: return TOK_TO;
	case S1: return TOK_END;
	case S2: return TOK_IDENT;
	case S3: return TOK_IDENT;
	case S4: return TOK_START;
	case S5: return TOK_IDENT;
	case S6: return TOK_IDENT;
	case S7: return TOK_IDENT;
	case S8: return TOK_IDENT;
	case S9: return TOK_EOF;
	case S10: return TOK_EOF;
	case S11: return TOK_COMMA;
	case S12: return TOK_EOF;
	case S13: return TOK_IDENT;
	case S14: return TOK_IDENT;
	case S15: return TOK_IDENT;
	case S17: return TOK_ANY;
	case S18: return TOK_EOF;
	case S19: return TOK_SEP;
	default: errno = EINVAL; return TOK_ERROR;
	}
}

const char *
lx_name(enum lx_token t)
{
	switch (t) {
	case TOK_COMMA: return "COMMA";
	case TOK_SEP: return "SEP";
	case TOK_ANY: return "ANY";
	case TOK_TO: return "TO";
	case TOK_IDENT: return "IDENT";
	case TOK_END: return "END";
	case TOK_START: return "START";
	case TOK_CHAR: return "CHAR";
	case TOK_HEX: return "HEX";
	case TOK_OCT: return "OCT";
	case TOK_ESC: return "ESC";
	case TOK_LABEL: return "LABEL";
	case TOK_EOF:     return "EOF";
	case TOK_ERROR:   return "ERROR";
	case TOK_UNKNOWN: return "UNKNOWN";
	default: return "?";
	}
}

const char *
lx_example(enum lx_token (*z)(struct lx *), enum lx_token t)
{
	assert(z != NULL);

	if (z == z0) {
		switch (t) {
		case TOK_CHAR: return "a";
		case TOK_LABEL: return "\'";
		default: goto error;
		}
	} else
	if (z == z1) {
		switch (t) {
		case TOK_CHAR: return "\\";
		case TOK_HEX: return "\\xa";
		case TOK_OCT: return "\\0";
		case TOK_ESC: return "\\f";
		case TOK_LABEL: return "\"";
		default: goto error;
		}
	} else
	if (z == z2) {
		switch (t) {
		default: goto error;
		}
	} else
	if (z == z3) {
		switch (t) {
		case TOK_COMMA: return ",";
		case TOK_SEP: return ";";
		case TOK_ANY: return "?";
		case TOK_TO: return "->";
		case TOK_IDENT: return "s";
		case TOK_END: return "end:";
		case TOK_START: return "start:";
		default: goto error;
		}
	}

error:

	errno = EINVAL;
	return NULL;
}

void
lx_init(struct lx *lx)
{
	static const struct lx lx_default;

	assert(lx != NULL);

	*lx = lx_default;

	lx->c = EOF;
	lx->z = NULL;

	lx->end.byte = 0;
	lx->end.line = 1;
	lx->end.col  = 1;
}

enum lx_token
lx_next(struct lx *lx)
{
	enum lx_token t;

	assert(lx != NULL);

	if (lx->lgetc == NULL) {
		return TOK_EOF;
	}

	if (lx->z == NULL) {
		lx->z = z3;
	}

	t = lx->z(lx);

	if (lx->push != NULL) {
		if (-1 == lx->push(lx, '\0')) {
			return TOK_ERROR;
		}
	}

	return t;
}

