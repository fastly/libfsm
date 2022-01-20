/* Generated by lx */

#include <assert.h>
#include <stdio.h>
#include <stddef.h>
#include <stdlib.h>
#include <errno.h>

#include LX_HEADER

static enum lx_sql_token z0(struct lx_sql_lx *lx);
static enum lx_sql_token z1(struct lx_sql_lx *lx);
static enum lx_sql_token z2(struct lx_sql_lx *lx);

#if __STDC_VERSION__ >= 199901L
inline
#endif
static int
lx_getc(struct lx_sql_lx *lx)
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
		lx->end.saved_col = lx->end.col - 1;
		lx->end.col = 1;
	}

	return c;
}

#if __STDC_VERSION__ >= 199901L
inline
#endif
static void
lx_sql_ungetc(struct lx_sql_lx *lx, int c)
{
	assert(lx != NULL);
	assert(lx->c == EOF);

	lx->c = c;


	lx->end.byte--;
	lx->end.col--;

	if (c == '\n') {
		lx->end.line--;
		lx->end.col = lx->end.saved_col;
	}
}

int
lx_sql_dynpush(void *buf_opaque, char c)
{
	struct lx_dynbuf *t = buf_opaque;

	assert(t != NULL);

	if (t->a == NULL || t->p == t->a + t->len) {
		size_t len;
		ptrdiff_t off;
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

		off = t->p - t->a;
		tmp = realloc(t->a, len);
		if (tmp == NULL) {
			return -1;
		}

		t->p   = tmp + off;
		t->a   = tmp;
		t->len = len;
	}

	assert(t->p != NULL);
	assert(t->a != NULL);

	*t->p++ = c;

	return 0;
}

int
lx_sql_dynclear(void *buf_opaque)
{
	struct lx_dynbuf *t = buf_opaque;

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
lx_sql_dynfree(void *buf_opaque)
{
	struct lx_dynbuf *t = buf_opaque;

	assert(t != NULL);

	free(t->a);
}
static enum lx_sql_token
z0(struct lx_sql_lx *lx)
{
	int c;

	enum {
		S0, S1, S2, S3, NONE
	} state;

	assert(lx != NULL);

	if (lx->clear != NULL) {
		lx->clear(lx->buf_opaque);
	}

	state = NONE;

	lx->start = lx->end;

	while (c = lx_getc(lx), c != EOF) {
		if (state == NONE) {
			state = S0;
		}

		switch (state) {
		case S0: /* start */
			switch ((unsigned char) c) {
			case ',': state = S1; break;
			case '0':
			case '1':
			case '2':
			case '3':
			case '4':
			case '5':
			case '6':
			case '7':
			case '8':
			case '9': state = S2; break;
			case '}': state = S3; break;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}
			break;

		case S1: /* e.g. "," */
			lx_sql_ungetc(lx, c); return TOK_SEP;

		case S2: /* e.g. "0" */
			switch ((unsigned char) c) {
			case '0':
			case '1':
			case '2':
			case '3':
			case '4':
			case '5':
			case '6':
			case '7':
			case '8':
			case '9': break;
			default:  lx_sql_ungetc(lx, c); return TOK_COUNT;
			}
			break;

		case S3: /* e.g. "}" */
			lx_sql_ungetc(lx, c); return lx->z = z2, TOK_CLOSECOUNT;

		default:
			; /* unreached */
		}

		if (lx->push != NULL) {
			if (-1 == lx->push(lx->buf_opaque, c)) {
				return TOK_ERROR;
			}
		}
	}

	lx->lgetc = NULL;

	switch (state) {
	case NONE: return TOK_EOF;
	case S1: return TOK_SEP;
	case S2: return TOK_COUNT;
	case S3: return TOK_CLOSECOUNT;
	default: errno = EINVAL; return TOK_ERROR;
	}
}

static enum lx_sql_token
z1(struct lx_sql_lx *lx)
{
	int c;

	enum {
		S0, S1, S2, S3, S4, S5, S6, S7, S8, S9, 
		S10, S11, S12, S13, S14, S15, S16, S17, S18, S19, 
		S20, S21, S22, S23, S24, S25, S26, S27, S28, S29, 
		S30, S31, S32, S33, S34, NONE
	} state;

	assert(lx != NULL);

	if (lx->clear != NULL) {
		lx->clear(lx->buf_opaque);
	}

	state = NONE;

	lx->start = lx->end;

	while (c = lx_getc(lx), c != EOF) {
		if (state == NONE) {
			state = S0;
		}

		switch (state) {
		case S0: /* start */
			switch ((unsigned char) c) {
			case '-': state = S2; break;
			case '[': state = S3; break;
			case ']': state = S4; break;
			case '^': state = S5; break;
			default: state = S1; break;
			}
			break;

		case S1: /* e.g. "a" */
			lx_sql_ungetc(lx, c); return TOK_CHAR;

		case S2: /* e.g. "-" */
			lx_sql_ungetc(lx, c); return TOK_RANGE;

		case S3: /* e.g. "[" */
			switch ((unsigned char) c) {
			case ':': state = S6; break;
			default:  lx_sql_ungetc(lx, c); return TOK_CHAR;
			}
			break;

		case S4: /* e.g. "]" */
			lx_sql_ungetc(lx, c); return lx->z = z2, TOK_CLOSEGROUP;

		case S5: /* e.g. "^" */
			lx_sql_ungetc(lx, c); return TOK_INVERT;

		case S6: /* e.g. "[:" */
			switch ((unsigned char) c) {
			case 'A': state = S7; break;
			case 'D': state = S8; break;
			case 'L': state = S9; break;
			case 'S': state = S10; break;
			case 'U': state = S11; break;
			case 'W': state = S12; break;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}
			break;

		case S7: /* e.g. "[:A" */
			switch ((unsigned char) c) {
			case 'L': state = S30; break;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}
			break;

		case S8: /* e.g. "[:D" */
			switch ((unsigned char) c) {
			case 'I': state = S27; break;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}
			break;

		case S9: /* e.g. "[:L" */
			switch ((unsigned char) c) {
			case 'O': state = S26; break;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}
			break;

		case S10: /* e.g. "[:S" */
			switch ((unsigned char) c) {
			case 'P': state = S23; break;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}
			break;

		case S11: /* e.g. "[:U" */
			switch ((unsigned char) c) {
			case 'P': state = S17; break;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}
			break;

		case S12: /* e.g. "[:W" */
			switch ((unsigned char) c) {
			case 'H': state = S13; break;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}
			break;

		case S13: /* e.g. "[:WH" */
			switch ((unsigned char) c) {
			case 'I': state = S14; break;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}
			break;

		case S14: /* e.g. "[:WHI" */
			switch ((unsigned char) c) {
			case 'T': state = S15; break;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}
			break;

		case S15: /* e.g. "[:WHIT" */
			switch ((unsigned char) c) {
			case 'E': state = S16; break;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}
			break;

		case S16: /* e.g. "[:WHITE" */
			switch ((unsigned char) c) {
			case 'S': state = S10; break;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}
			break;

		case S17: /* e.g. "[:UP" */
			switch ((unsigned char) c) {
			case 'P': state = S18; break;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}
			break;

		case S18: /* e.g. "[:LOW" */
			switch ((unsigned char) c) {
			case 'E': state = S19; break;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}
			break;

		case S19: /* e.g. "[:LOWE" */
			switch ((unsigned char) c) {
			case 'R': state = S20; break;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}
			break;

		case S20: /* e.g. "[:ALPHA" */
			switch ((unsigned char) c) {
			case ':': state = S21; break;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}
			break;

		case S21: /* e.g. "[:ALPHA:" */
			switch ((unsigned char) c) {
			case ']': state = S22; break;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}
			break;

		case S22: /* e.g. "[:ALPHA:]" */
			lx_sql_ungetc(lx, c); return TOK_NAMED__CLASS;

		case S23: /* e.g. "[:SP" */
			switch ((unsigned char) c) {
			case 'A': state = S24; break;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}
			break;

		case S24: /* e.g. "[:SPA" */
			switch ((unsigned char) c) {
			case 'C': state = S25; break;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}
			break;

		case S25: /* e.g. "[:SPAC" */
			switch ((unsigned char) c) {
			case 'E': state = S20; break;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}
			break;

		case S26: /* e.g. "[:LO" */
			switch ((unsigned char) c) {
			case 'W': state = S18; break;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}
			break;

		case S27: /* e.g. "[:DI" */
			switch ((unsigned char) c) {
			case 'G': state = S28; break;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}
			break;

		case S28: /* e.g. "[:DIG" */
			switch ((unsigned char) c) {
			case 'I': state = S29; break;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}
			break;

		case S29: /* e.g. "[:DIGI" */
			switch ((unsigned char) c) {
			case 'T': state = S20; break;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}
			break;

		case S30: /* e.g. "[:AL" */
			switch ((unsigned char) c) {
			case 'N': state = S31; break;
			case 'P': state = S32; break;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}
			break;

		case S31: /* e.g. "[:ALN" */
			switch ((unsigned char) c) {
			case 'U': state = S34; break;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}
			break;

		case S32: /* e.g. "[:ALP" */
			switch ((unsigned char) c) {
			case 'H': state = S33; break;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}
			break;

		case S33: /* e.g. "[:ALPH" */
			switch ((unsigned char) c) {
			case 'A': state = S20; break;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}
			break;

		case S34: /* e.g. "[:ALNU" */
			switch ((unsigned char) c) {
			case 'M': state = S20; break;
			default:  lx->lgetc = NULL; return TOK_UNKNOWN;
			}
			break;

		default:
			; /* unreached */
		}

		if (lx->push != NULL) {
			if (-1 == lx->push(lx->buf_opaque, c)) {
				return TOK_ERROR;
			}
		}
	}

	lx->lgetc = NULL;

	switch (state) {
	case NONE: return TOK_EOF;
	case S1: return TOK_CHAR;
	case S2: return TOK_RANGE;
	case S3: return TOK_CHAR;
	case S4: return TOK_CLOSEGROUP;
	case S5: return TOK_INVERT;
	case S22: return TOK_NAMED__CLASS;
	default: errno = EINVAL; return TOK_ERROR;
	}
}

static enum lx_sql_token
z2(struct lx_sql_lx *lx)
{
	int c;

	enum {
		S0, S1, S2, S3, S4, S5, S6, S7, S8, S9, 
		S10, S11, NONE
	} state;

	assert(lx != NULL);

	if (lx->clear != NULL) {
		lx->clear(lx->buf_opaque);
	}

	state = NONE;

	lx->start = lx->end;

	while (c = lx_getc(lx), c != EOF) {
		if (state == NONE) {
			state = S0;
		}

		switch (state) {
		case S0: /* start */
			switch ((unsigned char) c) {
			case '%': state = S2; break;
			case '(': state = S3; break;
			case ')': state = S4; break;
			case '*': state = S5; break;
			case '+': state = S6; break;
			case '?': state = S7; break;
			case '[': state = S8; break;
			case '_': state = S9; break;
			case '{': state = S10; break;
			case '|': state = S11; break;
			default: state = S1; break;
			}
			break;

		case S1: /* e.g. "a" */
			lx_sql_ungetc(lx, c); return TOK_CHAR;

		case S2: /* e.g. "%" */
			lx_sql_ungetc(lx, c); return TOK_MANY;

		case S3: /* e.g. "(" */
			lx_sql_ungetc(lx, c); return TOK_OPENSUB;

		case S4: /* e.g. ")" */
			lx_sql_ungetc(lx, c); return TOK_CLOSESUB;

		case S5: /* e.g. "*" */
			lx_sql_ungetc(lx, c); return TOK_STAR;

		case S6: /* e.g. "+" */
			lx_sql_ungetc(lx, c); return TOK_PLUS;

		case S7: /* e.g. "?" */
			lx_sql_ungetc(lx, c); return TOK_OPT;

		case S8: /* e.g. "[" */
			lx_sql_ungetc(lx, c); return lx->z = z1, TOK_OPENGROUP;

		case S9: /* e.g. "_" */
			lx_sql_ungetc(lx, c); return TOK_ANY;

		case S10: /* e.g. "{" */
			lx_sql_ungetc(lx, c); return lx->z = z0, TOK_OPENCOUNT;

		case S11: /* e.g. "|" */
			lx_sql_ungetc(lx, c); return TOK_ALT;

		default:
			; /* unreached */
		}

		if (lx->push != NULL) {
			if (-1 == lx->push(lx->buf_opaque, c)) {
				return TOK_ERROR;
			}
		}
	}

	lx->lgetc = NULL;

	switch (state) {
	case NONE: return TOK_EOF;
	case S1: return TOK_CHAR;
	case S2: return TOK_MANY;
	case S3: return TOK_OPENSUB;
	case S4: return TOK_CLOSESUB;
	case S5: return TOK_STAR;
	case S6: return TOK_PLUS;
	case S7: return TOK_OPT;
	case S8: return TOK_OPENGROUP;
	case S9: return TOK_ANY;
	case S10: return TOK_OPENCOUNT;
	case S11: return TOK_ALT;
	default: errno = EINVAL; return TOK_ERROR;
	}
}

const char *
lx_sql_name(enum lx_sql_token t)
{
	switch (t) {
	case TOK_SEP: return "SEP";
	case TOK_COUNT: return "COUNT";
	case TOK_CLOSECOUNT: return "CLOSECOUNT";
	case TOK_OPENCOUNT: return "OPENCOUNT";
	case TOK_CHAR: return "CHAR";
	case TOK_NAMED__CLASS: return "NAMED__CLASS";
	case TOK_RANGE: return "RANGE";
	case TOK_INVERT: return "INVERT";
	case TOK_CLOSEGROUP: return "CLOSEGROUP";
	case TOK_OPENGROUP: return "OPENGROUP";
	case TOK_ALT: return "ALT";
	case TOK_PLUS: return "PLUS";
	case TOK_STAR: return "STAR";
	case TOK_OPT: return "OPT";
	case TOK_CLOSESUB: return "CLOSESUB";
	case TOK_OPENSUB: return "OPENSUB";
	case TOK_MANY: return "MANY";
	case TOK_ANY: return "ANY";
	case TOK_EOF:     return "EOF";
	case TOK_ERROR:   return "ERROR";
	case TOK_UNKNOWN: return "UNKNOWN";
	default: return "?";
	}
}

const char *
lx_sql_example(enum lx_sql_token (*z)(struct lx_sql_lx *), enum lx_sql_token t)
{
	assert(z != NULL);

	if (z == z0) {
		switch (t) {
		case TOK_SEP: return "";
		case TOK_COUNT: return "";
		case TOK_CLOSECOUNT: return "";
		case TOK_OPENCOUNT: return "";
		case TOK_CHAR: return "";
		case TOK_NAMED__CLASS: return "";
		case TOK_RANGE: return "";
		case TOK_INVERT: return "";
		case TOK_CLOSEGROUP: return "";
		case TOK_OPENGROUP: return "";
		case TOK_ALT: return "";
		case TOK_PLUS: return "";
		case TOK_STAR: return "";
		case TOK_OPT: return "";
		case TOK_CLOSESUB: return "";
		case TOK_OPENSUB: return "";
		case TOK_MANY: return "";
		case TOK_ANY: return "";
		default: goto error;
		}
	} else
	if (z == z1) {
		switch (t) {
		case TOK_SEP: return "";
		case TOK_COUNT: return "";
		case TOK_CLOSECOUNT: return "";
		case TOK_OPENCOUNT: return "";
		case TOK_CHAR: return "";
		case TOK_NAMED__CLASS: return "";
		case TOK_RANGE: return "";
		case TOK_INVERT: return "";
		case TOK_CLOSEGROUP: return "";
		case TOK_OPENGROUP: return "";
		case TOK_ALT: return "";
		case TOK_PLUS: return "";
		case TOK_STAR: return "";
		case TOK_OPT: return "";
		case TOK_CLOSESUB: return "";
		case TOK_OPENSUB: return "";
		case TOK_MANY: return "";
		case TOK_ANY: return "";
		default: goto error;
		}
	} else
	if (z == z2) {
		switch (t) {
		case TOK_SEP: return "";
		case TOK_COUNT: return "";
		case TOK_CLOSECOUNT: return "";
		case TOK_OPENCOUNT: return "";
		case TOK_CHAR: return "";
		case TOK_NAMED__CLASS: return "";
		case TOK_RANGE: return "";
		case TOK_INVERT: return "";
		case TOK_CLOSEGROUP: return "";
		case TOK_OPENGROUP: return "";
		case TOK_ALT: return "";
		case TOK_PLUS: return "";
		case TOK_STAR: return "";
		case TOK_OPT: return "";
		case TOK_CLOSESUB: return "";
		case TOK_OPENSUB: return "";
		case TOK_MANY: return "";
		case TOK_ANY: return "";
		default: goto error;
		}
	}

error:

	errno = EINVAL;
	return NULL;
}

void
lx_sql_init(struct lx_sql_lx *lx)
{
	static const struct lx_sql_lx lx_default;

	assert(lx != NULL);

	*lx = lx_default;

	lx->c = EOF;
	lx->z = z2;

	lx->end.byte = 0;
	lx->end.line = 1;
	lx->end.col  = 1;
}

enum lx_sql_token
lx_sql_next(struct lx_sql_lx *lx)
{
	enum lx_sql_token t;

	assert(lx != NULL);
	assert(lx->z != NULL);

	if (lx->lgetc == NULL) {
		return TOK_EOF;
	}

	t = lx->z(lx);

	if (lx->push != NULL) {
		if (-1 == lx->push(lx->buf_opaque, '\0')) {
			return TOK_ERROR;
		}
	}

	return t;
}

