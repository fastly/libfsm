/*
 * Automatically generated from the files:
 *	src/libre/dialect/pcre/parser.sid
 * and
 *	src/libre/parser.act
 * by:
 *	sid
 */

/* BEGINNING OF HEADER */

#line 22 "src/libre/parser.act"


	#include <assert.h>
	#include <limits.h>
	#include <string.h>
	#include <stdint.h>
	#include <stdlib.h>
	#include <stdio.h>
	#include <errno.h>
	#include <ctype.h>

	#include <re/re.h>
	#include <adt/common.h>

	#include "libre/class.h"
	#include "libre/class_lookup.h"
	#include "libre/ast.h"

	#ifndef DIALECT
	#error DIALECT required
	#endif

	#define PASTE(a, b) a ## b
	#define CAT(a, b)   PASTE(a, b)

	#define LX_PREFIX CAT(lx_, DIALECT)

	#define LX_TOKEN   CAT(LX_PREFIX, _token)
	#define LX_STATE   CAT(LX_PREFIX, _lx)
	#define LX_NEXT    CAT(LX_PREFIX, _next)
	#define LX_INIT    CAT(LX_PREFIX, _init)

	#define DIALECT_PARSE  CAT(parse_re_, DIALECT)
	#define DIALECT_CLASS  CAT(re_class_, DIALECT)

	/* XXX: get rid of this; use same %entry% for all grammars */
	#define DIALECT_ENTRY CAT(p_re__, DIALECT)

	#define TOK_CLASS__alnum  TOK_CLASS_ALNUM
	#define TOK_CLASS__alpha  TOK_CLASS_ALPHA
	#define TOK_CLASS__any    TOK_CLASS_ANY
	#define TOK_CLASS__ascii  TOK_CLASS_ASCII
	#define TOK_CLASS__blank  TOK_CLASS_BLANK
	#define TOK_CLASS__cntrl  TOK_CLASS_CNTRL
	#define TOK_CLASS__digit  TOK_CLASS_DIGIT
	#define TOK_CLASS__graph  TOK_CLASS_GRAPH
	#define TOK_CLASS__lower  TOK_CLASS_LOWER
	#define TOK_CLASS__print  TOK_CLASS_PRINT
	#define TOK_CLASS__punct  TOK_CLASS_PUNCT
	#define TOK_CLASS__space  TOK_CLASS_SPACE
	#define TOK_CLASS__spchr  TOK_CLASS_SPCHR
	#define TOK_CLASS__upper  TOK_CLASS_UPPER
	#define TOK_CLASS__word   TOK_CLASS_WORD
	#define TOK_CLASS__xdigit TOK_CLASS_XDIGIT

	#define TOK_CLASS__nspace  TOK_CLASS_NSPACE
	#define TOK_CLASS__ndigit  TOK_CLASS_NDIGIT

	#include "parser.h"
	#include "lexer.h"

	#include "../comp.h"
	#include "../../class.h"

	typedef char     t_char;
	typedef unsigned t_unsigned;
	typedef unsigned t_pred; /* TODO */

	typedef struct lx_pos t_pos;
	typedef enum re_flags t_re__flags;
	typedef const struct class * t_ast__class__id;
	typedef struct ast_count t_ast__count;
	typedef struct ast_endpoint t_endpoint;
	typedef unsigned t_group__id;

	struct act_state {
		struct ast_expr_pool **poolp;

		enum LX_TOKEN lex_tok;
		enum LX_TOKEN lex_tok_save;
		int overlap; /* permit overlap in groups */

		/*
		 * Lexical position stored for syntax errors.
		 */
		struct re_pos synstart;
		struct re_pos synend;

		/*
		 * Lexical positions stored for errors which describe multiple tokens.
		 * We're able to store these without needing a stack, because these are
		 * non-recursive productions.
		 */
		struct re_pos groupstart; struct re_pos groupend;
		struct re_pos rangestart; struct re_pos rangeend;
		struct re_pos countstart; struct re_pos countend;

		/*
		 * Numbering for capturing groups. By convention these start from 1,
		 * and 0 represents the entire matching text.
		 */
		unsigned group_id;
	};

	struct lex_state {
		struct LX_STATE lx;
		struct lx_dynbuf buf; /* XXX: unneccessary since we're lexing from a string */

		re_getchar_fun *f;
		void *opaque;

		/* TODO: use lx's generated conveniences for the pattern buffer */
		char a[512];
		char *p;

#if PCRE_DIALECT
		int extended_mode_comment;
		enum re_flags *flags_ptr;
#endif /* PCRE_DIALECT */
	};

	static void
	mark(struct re_pos *r, const struct lx_pos *pos)
	{
		assert(r != NULL);
		assert(pos != NULL);

		r->byte = pos->byte;
	}

	/* TODO: centralise perhaps */
	static void
	snprintdots(char *s, size_t sz, const char *msg)
	{
		size_t n;

		assert(s != NULL);
		assert(sz > 3);
		assert(msg != NULL);

		n = sprintf(s, "%.*s", (int) sz - 3 - 1, msg);
		if (n == sz - 3 - 1) {
			strcpy(s + n, "...");
		}
	}

	/* TODO: centralise */
	/* XXX: escaping really depends on dialect */
	static const char *
	escchar(char *s, size_t sz, int c)
	{
		size_t i;

		const struct {
			int c;
			const char *s;
		} a[] = {
			{ '\\', "\\\\" },

			{ '^',  "\\^"  },
			{ '-',  "\\-"  },
			{ ']',  "\\]"  },
			{ '[',  "\\["  },

			{ '\f', "\\f"  },
			{ '\n', "\\n"  },
			{ '\r', "\\r"  },
			{ '\t', "\\t"  },
			{ '\v', "\\v"  }
		};

		assert(s != NULL);
		assert(sz >= 5);

		(void) sz;

		for (i = 0; i < sizeof a / sizeof *a; i++) {
			if (a[i].c == c) {
				return a[i].s;
			}
		}

		if (!isprint((unsigned char) c)) {
			sprintf(s, "\\x%02X", (unsigned char) c);
			return s;
		}

		sprintf(s, "%c", c);
		return s;
	}

	static void
	advance_lexer(struct lex_state *lex_state, struct act_state *act_state)
	{
		mark(&act_state->synstart, &lex_state->lx.start);
		mark(&act_state->synend,   &lex_state->lx.end);
		act_state->lex_tok = LX_NEXT(&lex_state->lx);
	}

	static enum LX_TOKEN
	current_token(struct lex_state *lex_state, struct act_state *act_state)
	{
#ifndef PCRE_DIALECT
		(void) lex_state;
		return act_state->lex_tok;
#else
		enum re_flags fl = (lex_state->flags_ptr != NULL) ? lex_state->flags_ptr[0] : 0;
		enum LX_TOKEN tok;

		if ((fl & RE_EXTENDED) == 0) {
			tok = act_state->lex_tok;

			switch (tok) {
			case TOK_WHITESPACE:
			case TOK_NEWLINE:
			case TOK_MAYBE_COMMENT:
				return TOK_CHAR;

			default:
				return tok;
			}
		} 

	restart:

		tok = act_state->lex_tok;
		if (lex_state->extended_mode_comment) {
			switch (tok) {
			case TOK_EOF:
			case TOK_ERROR:
			case TOK_UNKNOWN:
				/* don't eat EOF or errors */
				return tok;

			case TOK_NEWLINE:
				lex_state->extended_mode_comment = 0;
				/* fall through */
			default:
				advance_lexer(lex_state, act_state);
				goto restart;
			}
		} else {
			switch (tok) {
			case TOK_MAYBE_COMMENT:
				lex_state->extended_mode_comment = 1;
				/* fall through */
			case TOK_WHITESPACE:
			case TOK_NEWLINE:
				advance_lexer(lex_state, act_state);
				goto restart;

			default:
				return tok;
			}
		}
#endif
	}

	#define ADVANCE_LEXER    (advance_lexer(lex_state, act_state))
	#define CURRENT_TERMINAL (current_token(lex_state, act_state))
	#define ERROR_TERMINAL   (TOK_ERROR)

	#define SAVE_LEXER(tok)  do { act_state->lex_tok_save = act_state->lex_tok; \
	                              act_state->lex_tok = tok;                     } while (0)
	#define RESTORE_LEXER    do { act_state->lex_tok = act_state->lex_tok_save; } while (0)

#line 280 "src/libre/dialect/pcre/parser.c"


#ifndef ERROR_TERMINAL
#error "-s no-numeric-terminals given and ERROR_TERMINAL is not defined"
#endif

/* BEGINNING OF FUNCTION DECLARATIONS */

static void p_expr_C_Cflags_C_Cflag__set(flags, lex_state, act_state, err, t_re__flags, t_re__flags *);
static void p_expr_C_Ccharacter_Hclass_C_Crange_Hendpoint_C_Crange_Hendpoint_Hliteral(flags, lex_state, act_state, err, t_endpoint *, t_pos *, t_pos *);
static void p_expr_C_Ccharacter_Hclass_C_Clist_Hof_Hclass_Hterms(flags, lex_state, act_state, err, t_ast__expr);
static void p_expr_C_Clist_Hof_Hpieces(flags, lex_state, act_state, err, t_ast__expr);
static void p_293(flags, lex_state, act_state, err, t_ast__class__id *, t_pos *, t_ast__expr *);
static void p_168(flags, lex_state, act_state, err);
static void p_expr_C_Cliteral(flags, lex_state, act_state, err, t_ast__expr *);
static void p_expr_C_Ccharacter_Hclass_C_Cclass_Hterm(flags, lex_state, act_state, err, t_ast__expr *);
static void p_expr_C_Ccomment(flags, lex_state, act_state, err);
static void p_expr_C_Ccharacter_Hclass_C_Crange_Hendpoint_C_Crange_Hendpoint_Hclass(flags, lex_state, act_state, err, t_endpoint *, t_pos *, t_pos *);
static void p_expr_C_Ccharacter_Hclass(flags, lex_state, act_state, err, t_ast__expr *);
static void p_expr_C_Ccharacter_Hclass_C_Crange_Hendpoint_Hend(flags, lex_state, act_state, err, t_endpoint *, t_pos *);
static void p_317(flags, lex_state, act_state, err, t_char *, t_pos *, t_ast__expr *);
static void p_expr_C_Cpiece(flags, lex_state, act_state, err, t_ast__expr *);
static void p_320(flags, lex_state, act_state, err, t_pos *, t_unsigned *, t_ast__count *);
static void p_expr(flags, lex_state, act_state, err, t_ast__expr *);
static void p_321(flags, lex_state, act_state, err, t_pos *, t_unsigned *, t_ast__count *);
static void p_194(flags, lex_state, act_state, err, t_ast__expr *);
static void p_expr_C_Cflags(flags, lex_state, act_state, err, t_ast__expr *);
static void p_expr_C_Cpiece_C_Clist_Hof_Hcounts(flags, lex_state, act_state, err, t_ast__expr, t_ast__expr *);
static void p_expr_C_Ccharacter_Hclass_C_Crange_Hendpoint(flags, lex_state, act_state, err, t_endpoint *, t_pos *, t_pos *);
static void p_class_Hnamed(flags, lex_state, act_state, err, t_ast__expr *, t_pos *, t_pos *);
static void p_209(flags, lex_state, act_state, err, t_pos *, t_char *, t_ast__expr *);
static void p_expr_C_Clist_Hof_Halts(flags, lex_state, act_state, err, t_ast__expr);
static void p_expr_C_Cpiece_C_Ccount(flags, lex_state, act_state, err, t_ast__count *);
extern void p_re__pcre(flags, lex_state, act_state, err, t_ast__expr *);
static void p_expr_C_Cpiece_C_Catom(flags, lex_state, act_state, err, t_ast__expr *);
static void p_expr_C_Calt(flags, lex_state, act_state, err, t_ast__expr *);
static void p_expr_C_Ctype(flags, lex_state, act_state, err, t_ast__expr *);

/* BEGINNING OF STATIC VARIABLES */


/* BEGINNING OF FUNCTION DEFINITIONS */

static void
p_expr_C_Cflags_C_Cflag__set(flags flags, lex_state lex_state, act_state act_state, err err, t_re__flags ZIi, t_re__flags *ZOo)
{
	t_re__flags ZIo;

	switch (CURRENT_TERMINAL) {
	case (TOK_FLAG__EXTENDED):
		{
			t_re__flags ZIc;

			/* BEGINNING OF EXTRACT: FLAG_EXTENDED */
			{
#line 672 "src/libre/parser.act"

		ZIc = RE_EXTENDED;
	
#line 340 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF EXTRACT: FLAG_EXTENDED */
			ADVANCE_LEXER;
			/* BEGINNING OF ACTION: re-flag-union */
			{
#line 807 "src/libre/parser.act"

		(ZIo) = (ZIi) | (ZIc);
	
#line 350 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: re-flag-union */
		}
		break;
	case (TOK_FLAG__IGNORE):
		{
			ADVANCE_LEXER;
			ZIo = ZIi;
		}
		break;
	case (TOK_FLAG__INSENSITIVE):
		{
			t_re__flags ZIc;

			/* BEGINNING OF EXTRACT: FLAG_INSENSITIVE */
			{
#line 668 "src/libre/parser.act"

		ZIc = RE_ICASE;
	
#line 371 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF EXTRACT: FLAG_INSENSITIVE */
			ADVANCE_LEXER;
			/* BEGINNING OF ACTION: re-flag-union */
			{
#line 807 "src/libre/parser.act"

		(ZIo) = (ZIi) | (ZIc);
	
#line 381 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: re-flag-union */
		}
		break;
	case (TOK_FLAG__SINGLE):
		{
			t_re__flags ZIc;

			/* BEGINNING OF EXTRACT: FLAG_SINGLE */
			{
#line 676 "src/libre/parser.act"

		ZIc = RE_SINGLE;
	
#line 396 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF EXTRACT: FLAG_SINGLE */
			ADVANCE_LEXER;
			/* BEGINNING OF ACTION: re-flag-union */
			{
#line 807 "src/libre/parser.act"

		(ZIo) = (ZIi) | (ZIc);
	
#line 406 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: re-flag-union */
		}
		break;
	case (TOK_FLAG__UNKNOWN):
		{
			ADVANCE_LEXER;
			ZIo = ZIi;
			/* BEGINNING OF ACTION: err-unknown-flag */
			{
#line 746 "src/libre/parser.act"

		if (err->e == RE_ESUCCESS) {
			err->e = RE_EFLAG;
		}
		goto ZL1;
	
#line 424 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: err-unknown-flag */
		}
		break;
	case (ERROR_TERMINAL):
		return;
	default:
		goto ZL1;
	}
	goto ZL0;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
ZL0:;
	*ZOo = ZIo;
}

static void
p_expr_C_Ccharacter_Hclass_C_Crange_Hendpoint_C_Crange_Hendpoint_Hliteral(flags flags, lex_state lex_state, act_state act_state, err err, t_endpoint *ZOr, t_pos *ZOstart, t_pos *ZOend)
{
	t_endpoint ZIr;
	t_pos ZIstart;
	t_pos ZIend;

	if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
		return;
	}
	{
		t_char ZIc;

		/* BEGINNING OF INLINE: 155 */
		{
			switch (CURRENT_TERMINAL) {
			case (TOK_CHAR):
				{
					/* BEGINNING OF EXTRACT: CHAR */
					{
#line 582 "src/libre/parser.act"

		/* the first byte may be '\x00' */
		assert(lex_state->buf.a[1] == '\0');

		ZIstart = lex_state->lx.start;
		ZIend   = lex_state->lx.end;

		(void) ZIstart;
		(void) ZIend;

		ZIc = lex_state->buf.a[0];
	
#line 475 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF EXTRACT: CHAR */
					ADVANCE_LEXER;
				}
				break;
			case (TOK_CONTROL):
				{
					/* BEGINNING OF EXTRACT: CONTROL */
					{
#line 449 "src/libre/parser.act"

		assert(lex_state->buf.a[0] == '\\');
		assert(lex_state->buf.a[1] == 'c');
		assert(lex_state->buf.a[2] != '\0');
		assert(lex_state->buf.a[3] == '\0');

		ZIc = lex_state->buf.a[2];

		/*
		 * From http://www.pcre.org/current/doc/html/pcre2pattern.html#SEC5
		 * 
		 *  The precise effect of \cx on ASCII characters is as follows:
		 *  if x is a lower case letter, it is converted to upper case.
		 *  Then bit 6 of the character (hex 40) is inverted.
		 *  Thus \cA to \cZ become hex 01 to hex 1A (A is 41, Z is 5A),
		 *  but \c{ becomes hex 3B ({ is 7B), and \c; becomes hex 7B (; is 3B).
		 *  If the code unit following \c has a value less than 32
		 *  or greater than 126, a compile-time error occurs. 
		 */

		{
			unsigned char cc = (unsigned char) ZIc;
			if (cc > 126 || cc < 32) {
				goto ZL1;
			}
			
			if (islower(cc)) {
				cc = toupper(cc);
			}

			cc ^= 0x40;

			ZIc = cc;
		}

		ZIstart = lex_state->lx.start;
		ZIend   = lex_state->lx.end;

		(void) ZIstart;
		(void) ZIend;
	
#line 527 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF EXTRACT: CONTROL */
					ADVANCE_LEXER;
					/* BEGINNING OF ACTION: err-unsupported */
					{
#line 767 "src/libre/parser.act"

		if (err->e == RE_ESUCCESS) {
			err->e = RE_EUNSUPPORTED;
		}
		goto ZL1;
	
#line 540 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF ACTION: err-unsupported */
				}
				break;
			case (TOK_ESC):
				{
					/* BEGINNING OF EXTRACT: ESC */
					{
#line 393 "src/libre/parser.act"

		assert(lex_state->buf.a[0] == '\\');
		assert(lex_state->buf.a[1] != '\0');
		assert(lex_state->buf.a[2] == '\0');

		ZIc = lex_state->buf.a[1];

		switch (ZIc) {
		case 'a': ZIc = '\a'; break;
		case 'b': ZIc = '\b'; break;
		case 'e': ZIc = '\033'; break;
		case 'f': ZIc = '\f'; break;
		case 'n': ZIc = '\n'; break;
		case 'r': ZIc = '\r'; break;
		case 't': ZIc = '\t'; break;
		case 'v': ZIc = '\v'; break;
		default:             break;
		}

		ZIstart = lex_state->lx.start;
		ZIend   = lex_state->lx.end;

		(void) ZIstart;
		(void) ZIend;
	
#line 575 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF EXTRACT: ESC */
					ADVANCE_LEXER;
				}
				break;
			case (TOK_HEX):
				{
					/* BEGINNING OF EXTRACT: HEX */
					{
#line 534 "src/libre/parser.act"

		unsigned long u;
		char *s, *e;
		int brace = 0;

		assert(0 == strncmp(lex_state->buf.a, "\\x", 2));
		assert(strlen(lex_state->buf.a) >= 2);  /* pcre allows \x without a suffix */

		ZIstart = lex_state->lx.start;
		ZIend   = lex_state->lx.end;

		(void) ZIstart;
		(void) ZIend;

		errno = 0;

		s = lex_state->buf.a + 2;

		if (*s == '{') {
			s++;
			brace = 1;
		}

		if (*s == '\0') {
			u = 0;
			e = s;
		} else {
			u = strtoul(s, &e, 16);
		}

		if ((u == ULONG_MAX && errno == ERANGE) || u > UCHAR_MAX) {
			err->e = RE_EHEXRANGE;
			snprintdots(err->esc, sizeof err->esc, lex_state->buf.a);
			goto ZL1;
		}

		if (brace && *e == '}') {
			e++;
		}

		if ((u == ULONG_MAX && errno != 0) || (*e != '\0')) {
			err->e = RE_EXESC;
			goto ZL1;
		}

		ZIc = (char) (unsigned char) u;
	
#line 633 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF EXTRACT: HEX */
					ADVANCE_LEXER;
				}
				break;
			case (TOK_OCT):
				{
					/* BEGINNING OF EXTRACT: OCT */
					{
#line 491 "src/libre/parser.act"

		unsigned long u;
		char *s, *e;
		int brace = 0;

		assert(0 == strncmp(lex_state->buf.a, "\\", 1));
		assert(strlen(lex_state->buf.a) >= 2);

		ZIstart = lex_state->lx.start;
		ZIend   = lex_state->lx.end;

		(void) ZIstart;
		(void) ZIend;

		errno = 0;

		s = lex_state->buf.a + 1;

		if (s[0] == 'o' && s[1] == '{') {
			s += 2;
			brace = 1;
		}

		u = strtoul(s, &e, 8);

		if ((u == ULONG_MAX && errno == ERANGE) || u > UCHAR_MAX) {
			err->e = RE_EOCTRANGE;
			snprintdots(err->esc, sizeof err->esc, lex_state->buf.a);
			goto ZL1;
		}

		if (brace && *e == '}') {
			e++;
		}

		if ((u == ULONG_MAX && errno != 0) || *e != '\0') {
			err->e = RE_EXESC;
			goto ZL1;
		}

		ZIc = (char) (unsigned char) u;
	
#line 686 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF EXTRACT: OCT */
					ADVANCE_LEXER;
				}
				break;
			case (TOK_UNSUPPORTED):
				{
					/* BEGINNING OF EXTRACT: UNSUPPORTED */
					{
#line 433 "src/libre/parser.act"

		/* handle \1-\9 back references */
		if (lex_state->buf.a[0] == '\\' && lex_state->buf.a[1] != '\0' && lex_state->buf.a[2] == '\0') {
			ZIc = lex_state->buf.a[1];
		}
		else {
			ZIc = lex_state->buf.a[0];
		}

		ZIstart = lex_state->lx.start;
		ZIend   = lex_state->lx.end;

		(void) ZIstart;
		(void) ZIend;
	
#line 712 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF EXTRACT: UNSUPPORTED */
					ADVANCE_LEXER;
					/* BEGINNING OF ACTION: err-unsupported */
					{
#line 767 "src/libre/parser.act"

		if (err->e == RE_ESUCCESS) {
			err->e = RE_EUNSUPPORTED;
		}
		goto ZL1;
	
#line 725 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF ACTION: err-unsupported */
				}
				break;
			default:
				goto ZL1;
			}
		}
		/* END OF INLINE: 155 */
		/* BEGINNING OF ACTION: ast-range-endpoint-literal */
		{
#line 846 "src/libre/parser.act"

		(ZIr).type = AST_ENDPOINT_LITERAL;
		(ZIr).u.literal.c = (unsigned char) (ZIc);
	
#line 742 "src/libre/dialect/pcre/parser.c"
		}
		/* END OF ACTION: ast-range-endpoint-literal */
	}
	goto ZL0;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
ZL0:;
	*ZOr = ZIr;
	*ZOstart = ZIstart;
	*ZOend = ZIend;
}

static void
p_expr_C_Ccharacter_Hclass_C_Clist_Hof_Hclass_Hterms(flags flags, lex_state lex_state, act_state act_state, err err, t_ast__expr ZIclass)
{
ZL2_expr_C_Ccharacter_Hclass_C_Clist_Hof_Hclass_Hterms:;
	switch (CURRENT_TERMINAL) {
	case (TOK_NAMED__CLASS): case (TOK_ESC): case (TOK_NOESC): case (TOK_CONTROL):
	case (TOK_OCT): case (TOK_HEX): case (TOK_CHAR): case (TOK_UNSUPPORTED):
		{
			t_ast__expr ZInode;

			p_expr_C_Ccharacter_Hclass_C_Cclass_Hterm (flags, lex_state, act_state, err, &ZInode);
			if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
				RESTORE_LEXER;
				goto ZL1;
			}
			/* BEGINNING OF ACTION: ast-add-alt */
			{
#line 1053 "src/libre/parser.act"

		if (!ast_add_expr_alt((ZIclass), (ZInode))) {
			goto ZL1;
		}
	
#line 779 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-add-alt */
			/* BEGINNING OF INLINE: expr::character-class::list-of-class-terms */
			goto ZL2_expr_C_Ccharacter_Hclass_C_Clist_Hof_Hclass_Hterms;
			/* END OF INLINE: expr::character-class::list-of-class-terms */
		}
		/* UNREACHED */
	case (ERROR_TERMINAL):
		return;
	default:
		break;
	}
	return;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
}

static void
p_expr_C_Clist_Hof_Hpieces(flags flags, lex_state lex_state, act_state act_state, err err, t_ast__expr ZIcat)
{
	if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
		return;
	}
ZL2_expr_C_Clist_Hof_Hpieces:;
	{
		/* BEGINNING OF INLINE: 271 */
		{
			switch (CURRENT_TERMINAL) {
			case (TOK_INVALID__COMMENT):
				{
					p_expr_C_Ccomment (flags, lex_state, act_state, err);
					if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
						RESTORE_LEXER;
						goto ZL1;
					}
				}
				break;
			case (TOK_ANY): case (TOK_EOL): case (TOK_START): case (TOK_END):
			case (TOK_END__NL): case (TOK_OPEN): case (TOK_OPENGROUP): case (TOK_OPENGROUPINV):
			case (TOK_OPENGROUPCB): case (TOK_OPENGROUPINVCB): case (TOK_NAMED__CLASS): case (TOK_FLAGS):
			case (TOK_ESC): case (TOK_NOESC): case (TOK_CONTROL): case (TOK_OCT):
			case (TOK_HEX): case (TOK_CHAR): case (TOK_UNSUPPORTED):
				{
					t_ast__expr ZIa;

					p_expr_C_Cpiece (flags, lex_state, act_state, err, &ZIa);
					if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
						RESTORE_LEXER;
						goto ZL1;
					}
					/* BEGINNING OF ACTION: ast-add-concat */
					{
#line 1047 "src/libre/parser.act"

		if (!ast_add_expr_concat((ZIcat), (ZIa))) {
			goto ZL1;
		}
	
#line 839 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF ACTION: ast-add-concat */
				}
				break;
			default:
				goto ZL1;
			}
		}
		/* END OF INLINE: 271 */
		/* BEGINNING OF INLINE: 272 */
		{
			switch (CURRENT_TERMINAL) {
			case (TOK_ANY): case (TOK_EOL): case (TOK_START): case (TOK_END):
			case (TOK_END__NL): case (TOK_OPEN): case (TOK_OPENGROUP): case (TOK_OPENGROUPINV):
			case (TOK_OPENGROUPCB): case (TOK_OPENGROUPINVCB): case (TOK_NAMED__CLASS): case (TOK_FLAGS):
			case (TOK_ESC): case (TOK_NOESC): case (TOK_CONTROL): case (TOK_OCT):
			case (TOK_HEX): case (TOK_CHAR): case (TOK_UNSUPPORTED): case (TOK_INVALID__COMMENT):
				{
					/* BEGINNING OF INLINE: expr::list-of-pieces */
					goto ZL2_expr_C_Clist_Hof_Hpieces;
					/* END OF INLINE: expr::list-of-pieces */
				}
				/* UNREACHED */
			default:
				break;
			}
		}
		/* END OF INLINE: 272 */
	}
	return;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
}

static void
p_293(flags flags, lex_state lex_state, act_state act_state, err err, t_ast__class__id *ZI290, t_pos *ZI291, t_ast__expr *ZOnode)
{
	t_ast__expr ZInode;

	switch (CURRENT_TERMINAL) {
	default:
		{
			/* BEGINNING OF ACTION: ast-make-named */
			{
#line 1040 "src/libre/parser.act"

		(ZInode) = ast_make_expr_named(act_state->poolp, *flags, (*ZI290));
		if ((ZInode) == NULL) {
			goto ZL1;
		}
	
#line 892 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-make-named */
		}
		break;
	case (TOK_RANGE):
		{
			t_endpoint ZIlower;
			t_endpoint ZIupper;
			t_pos ZIend;

			/* BEGINNING OF ACTION: ast-range-endpoint-class */
			{
#line 851 "src/libre/parser.act"

		(ZIlower).type = AST_ENDPOINT_NAMED;
		(ZIlower).u.named.class = (*ZI290);
	
#line 910 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-range-endpoint-class */
			p_168 (flags, lex_state, act_state, err);
			p_expr_C_Ccharacter_Hclass_C_Crange_Hendpoint_Hend (flags, lex_state, act_state, err, &ZIupper, &ZIend);
			if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
				RESTORE_LEXER;
				goto ZL1;
			}
			/* BEGINNING OF ACTION: mark-range */
			{
#line 779 "src/libre/parser.act"

		mark(&act_state->rangestart, &(*ZI291));
		mark(&act_state->rangeend,   &(ZIend));
	
#line 926 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: mark-range */
			/* BEGINNING OF ACTION: ast-make-range */
			{
#line 1011 "src/libre/parser.act"

		unsigned char lower, upper;

		if ((ZIlower).type != AST_ENDPOINT_LITERAL ||
			(ZIupper).type != AST_ENDPOINT_LITERAL) {
			err->e = RE_EUNSUPPORTED;
			goto ZL1;
		}

		lower = (ZIlower).u.literal.c;
		upper = (ZIupper).u.literal.c;

		if (lower > upper) {
			char a[5], b[5];
			
			assert(sizeof err->set >= 1 + sizeof a + 1 + sizeof b + 1 + 1);
			
			sprintf(err->set, "%s-%s",
				escchar(a, sizeof a, lower), escchar(b, sizeof b, upper));
			err->e = RE_ENEGRANGE;
			goto ZL1;
		}

		(ZInode) = ast_make_expr_range(act_state->poolp, *flags, &(ZIlower), &(ZIupper));
		if ((ZInode) == NULL) {
			goto ZL1;
		}
	
#line 960 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-make-range */
		}
		break;
	case (ERROR_TERMINAL):
		return;
	}
	goto ZL0;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
ZL0:;
	*ZOnode = ZInode;
}

static void
p_168(flags flags, lex_state lex_state, act_state act_state, err err)
{
	if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
		return;
	}
	{
		t_char ZI169;
		t_pos ZI170;
		t_pos ZI171;

		switch (CURRENT_TERMINAL) {
		case (TOK_RANGE):
			/* BEGINNING OF EXTRACT: RANGE */
			{
#line 315 "src/libre/parser.act"

		ZI169 = '-';
		ZI170 = lex_state->lx.start;
		ZI171   = lex_state->lx.end;

		(void) ZI169;
		(void) ZI170;
		(void) ZI171;
	
#line 1001 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF EXTRACT: RANGE */
			break;
		default:
			goto ZL1;
		}
		ADVANCE_LEXER;
	}
	return;
ZL1:;
	{
		/* BEGINNING OF ACTION: err-expected-range */
		{
#line 725 "src/libre/parser.act"

		if (err->e == RE_ESUCCESS) {
			err->e = RE_EXRANGE;
		}
		goto ZL2;
	
#line 1022 "src/libre/dialect/pcre/parser.c"
		}
		/* END OF ACTION: err-expected-range */
	}
	goto ZL0;
ZL2:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
ZL0:;
}

static void
p_expr_C_Cliteral(flags flags, lex_state lex_state, act_state act_state, err err, t_ast__expr *ZOnode)
{
	t_ast__expr ZInode;

	if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
		return;
	}
	{
		t_char ZIc;

		/* BEGINNING OF INLINE: 111 */
		{
			switch (CURRENT_TERMINAL) {
			case (TOK_CHAR):
				{
					t_pos ZI121;
					t_pos ZI122;

					/* BEGINNING OF EXTRACT: CHAR */
					{
#line 582 "src/libre/parser.act"

		/* the first byte may be '\x00' */
		assert(lex_state->buf.a[1] == '\0');

		ZI121 = lex_state->lx.start;
		ZI122   = lex_state->lx.end;

		(void) ZI121;
		(void) ZI122;

		ZIc = lex_state->buf.a[0];
	
#line 1067 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF EXTRACT: CHAR */
					ADVANCE_LEXER;
				}
				break;
			case (TOK_CONTROL):
				{
					t_pos ZI123;
					t_pos ZI124;

					/* BEGINNING OF EXTRACT: CONTROL */
					{
#line 449 "src/libre/parser.act"

		assert(lex_state->buf.a[0] == '\\');
		assert(lex_state->buf.a[1] == 'c');
		assert(lex_state->buf.a[2] != '\0');
		assert(lex_state->buf.a[3] == '\0');

		ZIc = lex_state->buf.a[2];

		/*
		 * From http://www.pcre.org/current/doc/html/pcre2pattern.html#SEC5
		 * 
		 *  The precise effect of \cx on ASCII characters is as follows:
		 *  if x is a lower case letter, it is converted to upper case.
		 *  Then bit 6 of the character (hex 40) is inverted.
		 *  Thus \cA to \cZ become hex 01 to hex 1A (A is 41, Z is 5A),
		 *  but \c{ becomes hex 3B ({ is 7B), and \c; becomes hex 7B (; is 3B).
		 *  If the code unit following \c has a value less than 32
		 *  or greater than 126, a compile-time error occurs. 
		 */

		{
			unsigned char cc = (unsigned char) ZIc;
			if (cc > 126 || cc < 32) {
				goto ZL1;
			}
			
			if (islower(cc)) {
				cc = toupper(cc);
			}

			cc ^= 0x40;

			ZIc = cc;
		}

		ZI123 = lex_state->lx.start;
		ZI124   = lex_state->lx.end;

		(void) ZI123;
		(void) ZI124;
	
#line 1122 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF EXTRACT: CONTROL */
					ADVANCE_LEXER;
				}
				break;
			case (TOK_ESC):
				{
					t_pos ZI113;
					t_pos ZI114;

					/* BEGINNING OF EXTRACT: ESC */
					{
#line 393 "src/libre/parser.act"

		assert(lex_state->buf.a[0] == '\\');
		assert(lex_state->buf.a[1] != '\0');
		assert(lex_state->buf.a[2] == '\0');

		ZIc = lex_state->buf.a[1];

		switch (ZIc) {
		case 'a': ZIc = '\a'; break;
		case 'b': ZIc = '\b'; break;
		case 'e': ZIc = '\033'; break;
		case 'f': ZIc = '\f'; break;
		case 'n': ZIc = '\n'; break;
		case 'r': ZIc = '\r'; break;
		case 't': ZIc = '\t'; break;
		case 'v': ZIc = '\v'; break;
		default:             break;
		}

		ZI113 = lex_state->lx.start;
		ZI114   = lex_state->lx.end;

		(void) ZI113;
		(void) ZI114;
	
#line 1161 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF EXTRACT: ESC */
					ADVANCE_LEXER;
				}
				break;
			case (TOK_HEX):
				{
					t_pos ZI119;
					t_pos ZI120;

					/* BEGINNING OF EXTRACT: HEX */
					{
#line 534 "src/libre/parser.act"

		unsigned long u;
		char *s, *e;
		int brace = 0;

		assert(0 == strncmp(lex_state->buf.a, "\\x", 2));
		assert(strlen(lex_state->buf.a) >= 2);  /* pcre allows \x without a suffix */

		ZI119 = lex_state->lx.start;
		ZI120   = lex_state->lx.end;

		(void) ZI119;
		(void) ZI120;

		errno = 0;

		s = lex_state->buf.a + 2;

		if (*s == '{') {
			s++;
			brace = 1;
		}

		if (*s == '\0') {
			u = 0;
			e = s;
		} else {
			u = strtoul(s, &e, 16);
		}

		if ((u == ULONG_MAX && errno == ERANGE) || u > UCHAR_MAX) {
			err->e = RE_EHEXRANGE;
			snprintdots(err->esc, sizeof err->esc, lex_state->buf.a);
			goto ZL1;
		}

		if (brace && *e == '}') {
			e++;
		}

		if ((u == ULONG_MAX && errno != 0) || (*e != '\0')) {
			err->e = RE_EXESC;
			goto ZL1;
		}

		ZIc = (char) (unsigned char) u;
	
#line 1222 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF EXTRACT: HEX */
					ADVANCE_LEXER;
				}
				break;
			case (TOK_NOESC):
				{
					t_pos ZI115;
					t_pos ZI116;

					/* BEGINNING OF EXTRACT: NOESC */
					{
#line 419 "src/libre/parser.act"

		assert(lex_state->buf.a[0] == '\\');
		assert(lex_state->buf.a[1] != '\0');
		assert(lex_state->buf.a[2] == '\0');

		ZIc = lex_state->buf.a[1];

		ZI115 = lex_state->lx.start;
		ZI116   = lex_state->lx.end;

		(void) ZI115;
		(void) ZI116;
	
#line 1249 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF EXTRACT: NOESC */
					ADVANCE_LEXER;
				}
				break;
			case (TOK_OCT):
				{
					t_pos ZI117;
					t_pos ZI118;

					/* BEGINNING OF EXTRACT: OCT */
					{
#line 491 "src/libre/parser.act"

		unsigned long u;
		char *s, *e;
		int brace = 0;

		assert(0 == strncmp(lex_state->buf.a, "\\", 1));
		assert(strlen(lex_state->buf.a) >= 2);

		ZI117 = lex_state->lx.start;
		ZI118   = lex_state->lx.end;

		(void) ZI117;
		(void) ZI118;

		errno = 0;

		s = lex_state->buf.a + 1;

		if (s[0] == 'o' && s[1] == '{') {
			s += 2;
			brace = 1;
		}

		u = strtoul(s, &e, 8);

		if ((u == ULONG_MAX && errno == ERANGE) || u > UCHAR_MAX) {
			err->e = RE_EOCTRANGE;
			snprintdots(err->esc, sizeof err->esc, lex_state->buf.a);
			goto ZL1;
		}

		if (brace && *e == '}') {
			e++;
		}

		if ((u == ULONG_MAX && errno != 0) || *e != '\0') {
			err->e = RE_EXESC;
			goto ZL1;
		}

		ZIc = (char) (unsigned char) u;
	
#line 1305 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF EXTRACT: OCT */
					ADVANCE_LEXER;
				}
				break;
			case (TOK_UNSUPPORTED):
				{
					t_pos ZI125;
					t_pos ZI126;

					/* BEGINNING OF EXTRACT: UNSUPPORTED */
					{
#line 433 "src/libre/parser.act"

		/* handle \1-\9 back references */
		if (lex_state->buf.a[0] == '\\' && lex_state->buf.a[1] != '\0' && lex_state->buf.a[2] == '\0') {
			ZIc = lex_state->buf.a[1];
		}
		else {
			ZIc = lex_state->buf.a[0];
		}

		ZI125 = lex_state->lx.start;
		ZI126   = lex_state->lx.end;

		(void) ZI125;
		(void) ZI126;
	
#line 1334 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF EXTRACT: UNSUPPORTED */
					ADVANCE_LEXER;
					/* BEGINNING OF ACTION: err-unsupported */
					{
#line 767 "src/libre/parser.act"

		if (err->e == RE_ESUCCESS) {
			err->e = RE_EUNSUPPORTED;
		}
		goto ZL1;
	
#line 1347 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF ACTION: err-unsupported */
				}
				break;
			default:
				goto ZL1;
			}
		}
		/* END OF INLINE: 111 */
		/* BEGINNING OF ACTION: ast-make-literal */
		{
#line 881 "src/libre/parser.act"

		(ZInode) = ast_make_expr_literal(act_state->poolp, *flags, (ZIc));
		if ((ZInode) == NULL) {
			goto ZL1;
		}
	
#line 1366 "src/libre/dialect/pcre/parser.c"
		}
		/* END OF ACTION: ast-make-literal */
	}
	goto ZL0;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
ZL0:;
	*ZOnode = ZInode;
}

static void
p_expr_C_Ccharacter_Hclass_C_Cclass_Hterm(flags flags, lex_state lex_state, act_state act_state, err err, t_ast__expr *ZOnode)
{
	t_ast__expr ZInode;

	switch (CURRENT_TERMINAL) {
	case (TOK_CHAR):
		{
			t_char ZI306;
			t_pos ZI307;
			t_pos ZI308;

			/* BEGINNING OF EXTRACT: CHAR */
			{
#line 582 "src/libre/parser.act"

		/* the first byte may be '\x00' */
		assert(lex_state->buf.a[1] == '\0');

		ZI307 = lex_state->lx.start;
		ZI308   = lex_state->lx.end;

		(void) ZI307;
		(void) ZI308;

		ZI306 = lex_state->buf.a[0];
	
#line 1405 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF EXTRACT: CHAR */
			ADVANCE_LEXER;
			p_317 (flags, lex_state, act_state, err, &ZI306, &ZI307, &ZInode);
			if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
				RESTORE_LEXER;
				goto ZL1;
			}
		}
		break;
	case (TOK_CONTROL):
		{
			t_char ZI310;
			t_pos ZI311;
			t_pos ZI312;

			/* BEGINNING OF EXTRACT: CONTROL */
			{
#line 449 "src/libre/parser.act"

		assert(lex_state->buf.a[0] == '\\');
		assert(lex_state->buf.a[1] == 'c');
		assert(lex_state->buf.a[2] != '\0');
		assert(lex_state->buf.a[3] == '\0');

		ZI310 = lex_state->buf.a[2];

		/*
		 * From http://www.pcre.org/current/doc/html/pcre2pattern.html#SEC5
		 * 
		 *  The precise effect of \cx on ASCII characters is as follows:
		 *  if x is a lower case letter, it is converted to upper case.
		 *  Then bit 6 of the character (hex 40) is inverted.
		 *  Thus \cA to \cZ become hex 01 to hex 1A (A is 41, Z is 5A),
		 *  but \c{ becomes hex 3B ({ is 7B), and \c; becomes hex 7B (; is 3B).
		 *  If the code unit following \c has a value less than 32
		 *  or greater than 126, a compile-time error occurs. 
		 */

		{
			unsigned char cc = (unsigned char) ZI310;
			if (cc > 126 || cc < 32) {
				goto ZL1;
			}
			
			if (islower(cc)) {
				cc = toupper(cc);
			}

			cc ^= 0x40;

			ZI310 = cc;
		}

		ZI311 = lex_state->lx.start;
		ZI312   = lex_state->lx.end;

		(void) ZI311;
		(void) ZI312;
	
#line 1466 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF EXTRACT: CONTROL */
			ADVANCE_LEXER;
			/* BEGINNING OF ACTION: err-unsupported */
			{
#line 767 "src/libre/parser.act"

		if (err->e == RE_ESUCCESS) {
			err->e = RE_EUNSUPPORTED;
		}
		goto ZL1;
	
#line 1479 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: err-unsupported */
			p_317 (flags, lex_state, act_state, err, &ZI310, &ZI311, &ZInode);
			if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
				RESTORE_LEXER;
				goto ZL1;
			}
		}
		break;
	case (TOK_ESC):
		{
			t_char ZI294;
			t_pos ZI295;
			t_pos ZI296;

			/* BEGINNING OF EXTRACT: ESC */
			{
#line 393 "src/libre/parser.act"

		assert(lex_state->buf.a[0] == '\\');
		assert(lex_state->buf.a[1] != '\0');
		assert(lex_state->buf.a[2] == '\0');

		ZI294 = lex_state->buf.a[1];

		switch (ZI294) {
		case 'a': ZI294 = '\a'; break;
		case 'b': ZI294 = '\b'; break;
		case 'e': ZI294 = '\033'; break;
		case 'f': ZI294 = '\f'; break;
		case 'n': ZI294 = '\n'; break;
		case 'r': ZI294 = '\r'; break;
		case 't': ZI294 = '\t'; break;
		case 'v': ZI294 = '\v'; break;
		default:             break;
		}

		ZI295 = lex_state->lx.start;
		ZI296   = lex_state->lx.end;

		(void) ZI295;
		(void) ZI296;
	
#line 1523 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF EXTRACT: ESC */
			ADVANCE_LEXER;
			p_317 (flags, lex_state, act_state, err, &ZI294, &ZI295, &ZInode);
			if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
				RESTORE_LEXER;
				goto ZL1;
			}
		}
		break;
	case (TOK_HEX):
		{
			t_char ZI302;
			t_pos ZI303;
			t_pos ZI304;

			/* BEGINNING OF EXTRACT: HEX */
			{
#line 534 "src/libre/parser.act"

		unsigned long u;
		char *s, *e;
		int brace = 0;

		assert(0 == strncmp(lex_state->buf.a, "\\x", 2));
		assert(strlen(lex_state->buf.a) >= 2);  /* pcre allows \x without a suffix */

		ZI303 = lex_state->lx.start;
		ZI304   = lex_state->lx.end;

		(void) ZI303;
		(void) ZI304;

		errno = 0;

		s = lex_state->buf.a + 2;

		if (*s == '{') {
			s++;
			brace = 1;
		}

		if (*s == '\0') {
			u = 0;
			e = s;
		} else {
			u = strtoul(s, &e, 16);
		}

		if ((u == ULONG_MAX && errno == ERANGE) || u > UCHAR_MAX) {
			err->e = RE_EHEXRANGE;
			snprintdots(err->esc, sizeof err->esc, lex_state->buf.a);
			goto ZL1;
		}

		if (brace && *e == '}') {
			e++;
		}

		if ((u == ULONG_MAX && errno != 0) || (*e != '\0')) {
			err->e = RE_EXESC;
			goto ZL1;
		}

		ZI302 = (char) (unsigned char) u;
	
#line 1590 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF EXTRACT: HEX */
			ADVANCE_LEXER;
			p_317 (flags, lex_state, act_state, err, &ZI302, &ZI303, &ZInode);
			if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
				RESTORE_LEXER;
				goto ZL1;
			}
		}
		break;
	case (TOK_NAMED__CLASS):
		{
			t_ast__class__id ZI290;
			t_pos ZI291;
			t_pos ZI292;

			/* BEGINNING OF EXTRACT: NAMED_CLASS */
			{
#line 654 "src/libre/parser.act"

		ZI290 = DIALECT_CLASS(lex_state->buf.a);
		if (ZI290 == NULL) {
			/* syntax error -- unrecognized class */
			goto ZL1;
		}

		ZI291 = lex_state->lx.start;
		ZI292   = lex_state->lx.end;

		(void) ZI291;
		(void) ZI292;
	
#line 1623 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF EXTRACT: NAMED_CLASS */
			ADVANCE_LEXER;
			p_293 (flags, lex_state, act_state, err, &ZI290, &ZI291, &ZInode);
			if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
				RESTORE_LEXER;
				goto ZL1;
			}
		}
		break;
	case (TOK_NOESC):
		{
			t_char ZIc;
			t_pos ZI134;
			t_pos ZI135;

			/* BEGINNING OF EXTRACT: NOESC */
			{
#line 419 "src/libre/parser.act"

		assert(lex_state->buf.a[0] == '\\');
		assert(lex_state->buf.a[1] != '\0');
		assert(lex_state->buf.a[2] == '\0');

		ZIc = lex_state->buf.a[1];

		ZI134 = lex_state->lx.start;
		ZI135   = lex_state->lx.end;

		(void) ZI134;
		(void) ZI135;
	
#line 1656 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF EXTRACT: NOESC */
			ADVANCE_LEXER;
			/* BEGINNING OF ACTION: ast-make-literal */
			{
#line 881 "src/libre/parser.act"

		(ZInode) = ast_make_expr_literal(act_state->poolp, *flags, (ZIc));
		if ((ZInode) == NULL) {
			goto ZL1;
		}
	
#line 1669 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-make-literal */
		}
		break;
	case (TOK_OCT):
		{
			t_char ZI298;
			t_pos ZI299;
			t_pos ZI300;

			/* BEGINNING OF EXTRACT: OCT */
			{
#line 491 "src/libre/parser.act"

		unsigned long u;
		char *s, *e;
		int brace = 0;

		assert(0 == strncmp(lex_state->buf.a, "\\", 1));
		assert(strlen(lex_state->buf.a) >= 2);

		ZI299 = lex_state->lx.start;
		ZI300   = lex_state->lx.end;

		(void) ZI299;
		(void) ZI300;

		errno = 0;

		s = lex_state->buf.a + 1;

		if (s[0] == 'o' && s[1] == '{') {
			s += 2;
			brace = 1;
		}

		u = strtoul(s, &e, 8);

		if ((u == ULONG_MAX && errno == ERANGE) || u > UCHAR_MAX) {
			err->e = RE_EOCTRANGE;
			snprintdots(err->esc, sizeof err->esc, lex_state->buf.a);
			goto ZL1;
		}

		if (brace && *e == '}') {
			e++;
		}

		if ((u == ULONG_MAX && errno != 0) || *e != '\0') {
			err->e = RE_EXESC;
			goto ZL1;
		}

		ZI298 = (char) (unsigned char) u;
	
#line 1725 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF EXTRACT: OCT */
			ADVANCE_LEXER;
			p_317 (flags, lex_state, act_state, err, &ZI298, &ZI299, &ZInode);
			if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
				RESTORE_LEXER;
				goto ZL1;
			}
		}
		break;
	case (TOK_UNSUPPORTED):
		{
			t_char ZI314;
			t_pos ZI315;
			t_pos ZI316;

			/* BEGINNING OF EXTRACT: UNSUPPORTED */
			{
#line 433 "src/libre/parser.act"

		/* handle \1-\9 back references */
		if (lex_state->buf.a[0] == '\\' && lex_state->buf.a[1] != '\0' && lex_state->buf.a[2] == '\0') {
			ZI314 = lex_state->buf.a[1];
		}
		else {
			ZI314 = lex_state->buf.a[0];
		}

		ZI315 = lex_state->lx.start;
		ZI316   = lex_state->lx.end;

		(void) ZI315;
		(void) ZI316;
	
#line 1760 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF EXTRACT: UNSUPPORTED */
			ADVANCE_LEXER;
			/* BEGINNING OF ACTION: err-unsupported */
			{
#line 767 "src/libre/parser.act"

		if (err->e == RE_ESUCCESS) {
			err->e = RE_EUNSUPPORTED;
		}
		goto ZL1;
	
#line 1773 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: err-unsupported */
			p_317 (flags, lex_state, act_state, err, &ZI314, &ZI315, &ZInode);
			if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
				RESTORE_LEXER;
				goto ZL1;
			}
		}
		break;
	case (ERROR_TERMINAL):
		return;
	default:
		goto ZL1;
	}
	goto ZL0;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
ZL0:;
	*ZOnode = ZInode;
}

static void
p_expr_C_Ccomment(flags flags, lex_state lex_state, act_state act_state, err err)
{
	if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
		return;
	}
	{
		switch (CURRENT_TERMINAL) {
		case (TOK_INVALID__COMMENT):
			break;
		default:
			goto ZL1;
		}
		ADVANCE_LEXER;
		/* BEGINNING OF ACTION: err-invalid-comment */
		{
#line 690 "src/libre/parser.act"

		if (err->e == RE_ESUCCESS) {
			err->e = RE_EBADCOMMENT;
		}
		goto ZL1;
	
#line 1819 "src/libre/dialect/pcre/parser.c"
		}
		/* END OF ACTION: err-invalid-comment */
	}
	return;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
}

static void
p_expr_C_Ccharacter_Hclass_C_Crange_Hendpoint_C_Crange_Hendpoint_Hclass(flags flags, lex_state lex_state, act_state act_state, err err, t_endpoint *ZOr, t_pos *ZOstart, t_pos *ZOend)
{
	t_endpoint ZIr;
	t_pos ZIstart;
	t_pos ZIend;

	if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
		return;
	}
	{
		t_ast__class__id ZIid;

		switch (CURRENT_TERMINAL) {
		case (TOK_NAMED__CLASS):
			/* BEGINNING OF EXTRACT: NAMED_CLASS */
			{
#line 654 "src/libre/parser.act"

		ZIid = DIALECT_CLASS(lex_state->buf.a);
		if (ZIid == NULL) {
			/* syntax error -- unrecognized class */
			goto ZL1;
		}

		ZIstart = lex_state->lx.start;
		ZIend   = lex_state->lx.end;

		(void) ZIstart;
		(void) ZIend;
	
#line 1860 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF EXTRACT: NAMED_CLASS */
			break;
		default:
			goto ZL1;
		}
		ADVANCE_LEXER;
		/* BEGINNING OF ACTION: ast-range-endpoint-class */
		{
#line 851 "src/libre/parser.act"

		(ZIr).type = AST_ENDPOINT_NAMED;
		(ZIr).u.named.class = (ZIid);
	
#line 1875 "src/libre/dialect/pcre/parser.c"
		}
		/* END OF ACTION: ast-range-endpoint-class */
	}
	goto ZL0;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
ZL0:;
	*ZOr = ZIr;
	*ZOstart = ZIstart;
	*ZOend = ZIend;
}

static void
p_expr_C_Ccharacter_Hclass(flags flags, lex_state lex_state, act_state act_state, err err, t_ast__expr *ZOnode)
{
	t_ast__expr ZInode;

	if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
		return;
	}
	{
		t_pos ZIstart;
		t_ast__expr ZItmp;

		/* BEGINNING OF INLINE: 180 */
		{
			switch (CURRENT_TERMINAL) {
			case (TOK_OPENGROUP):
				{
					t_pos ZI181;

					/* BEGINNING OF EXTRACT: OPENGROUP */
					{
#line 325 "src/libre/parser.act"

		ZIstart = lex_state->lx.start;
		ZI181   = lex_state->lx.end;

		(void) ZIstart;
		(void) ZI181;
	
#line 1918 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF EXTRACT: OPENGROUP */
					ADVANCE_LEXER;
					/* BEGINNING OF ACTION: ast-make-alt */
					{
#line 874 "src/libre/parser.act"

		(ZInode) = ast_make_expr_alt(act_state->poolp, *flags);
		if ((ZInode) == NULL) {
			goto ZL1;
		}
	
#line 1931 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF ACTION: ast-make-alt */
					ZItmp = ZInode;
					p_194 (flags, lex_state, act_state, err, &ZItmp);
					p_expr_C_Ccharacter_Hclass_C_Clist_Hof_Hclass_Hterms (flags, lex_state, act_state, err, ZItmp);
					if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
						RESTORE_LEXER;
						goto ZL1;
					}
				}
				break;
			case (TOK_OPENGROUPCB):
				{
					t_pos ZI200;
					t_char ZIcbrak;
					t_ast__expr ZInode1;

					/* BEGINNING OF EXTRACT: OPENGROUPCB */
					{
#line 341 "src/libre/parser.act"

		ZIstart = lex_state->lx.start;
		ZI200   = lex_state->lx.end;

		(void) ZIstart;
		(void) ZI200;
	
#line 1959 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF EXTRACT: OPENGROUPCB */
					ADVANCE_LEXER;
					/* BEGINNING OF ACTION: ast-make-alt */
					{
#line 874 "src/libre/parser.act"

		(ZInode) = ast_make_expr_alt(act_state->poolp, *flags);
		if ((ZInode) == NULL) {
			goto ZL1;
		}
	
#line 1972 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF ACTION: ast-make-alt */
					ZItmp = ZInode;
					/* BEGINNING OF ACTION: make-literal-cbrak */
					{
#line 892 "src/libre/parser.act"

		(ZIcbrak) = ']';
	
#line 1982 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF ACTION: make-literal-cbrak */
					p_209 (flags, lex_state, act_state, err, &ZIstart, &ZIcbrak, &ZInode1);
					if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
						RESTORE_LEXER;
						goto ZL1;
					}
					/* BEGINNING OF ACTION: ast-add-alt */
					{
#line 1053 "src/libre/parser.act"

		if (!ast_add_expr_alt((ZItmp), (ZInode1))) {
			goto ZL1;
		}
	
#line 1998 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF ACTION: ast-add-alt */
					p_expr_C_Ccharacter_Hclass_C_Clist_Hof_Hclass_Hterms (flags, lex_state, act_state, err, ZItmp);
					if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
						RESTORE_LEXER;
						goto ZL1;
					}
				}
				break;
			case (TOK_OPENGROUPINV):
				{
					t_pos ZI192;

					/* BEGINNING OF EXTRACT: OPENGROUPINV */
					{
#line 333 "src/libre/parser.act"

		ZIstart = lex_state->lx.start;
		ZI192   = lex_state->lx.end;

		(void) ZIstart;
		(void) ZI192;
	
#line 2022 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF EXTRACT: OPENGROUPINV */
					ADVANCE_LEXER;
					/* BEGINNING OF ACTION: ast-make-alt */
					{
#line 874 "src/libre/parser.act"

		(ZInode) = ast_make_expr_alt(act_state->poolp, *flags);
		if ((ZInode) == NULL) {
			goto ZL1;
		}
	
#line 2035 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF ACTION: ast-make-alt */
					ZItmp = ZInode;
					/* BEGINNING OF ACTION: ast-make-invert */
					{
#line 973 "src/libre/parser.act"

		struct ast_expr *any;

		/*
		 * Here we're using an AST_EXPR_SUBTRACT node to implement inversion.
		 *
		 * Inversion is not quite equivalent to fsm_complement, because the
		 * complement of a class FSM (which is structured always left-to-right
		 * with no repetition) will effectively create .* anchors at the start
		 * and end (because the class didn't contain those).
		 *
		 * If those were added to a class beforehand, then fsm_complement()
		 * would suffice here (which would be attractive because it's much
		 * cheaper than constructing two FSM and subtracting them). However
		 * that would entail the assumption of having no transitions back to
		 * the start and end nodes, or introducing guard epsilons.
		 *
		 * I'd like to avoid those guards. And, unfortunately we'd still need
		 * to construct an intermediate FSM for fsm_complement() in any case.
		 * (And less typical, but we do still need AST_EXPR_SUBTRACT for sake
		 * of the SQL 2003 dialect anyway).
		 *
		 * So that idea doesn't satisfy my goal of avoiding intermediate FSM,
		 * and so I'm going with the simpler thing here until we come across
		 * a better idea.
		 */

		any = ast_make_expr_named(act_state->poolp, *flags, &class_any);
		if (any == NULL) {
			goto ZL1;
		}

		(ZInode) = ast_make_expr_subtract(act_state->poolp, *flags, any, (ZInode));
		if ((ZInode) == NULL) {
			goto ZL1;
		}
	
#line 2079 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF ACTION: ast-make-invert */
					p_194 (flags, lex_state, act_state, err, &ZItmp);
					p_expr_C_Ccharacter_Hclass_C_Clist_Hof_Hclass_Hterms (flags, lex_state, act_state, err, ZItmp);
					if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
						RESTORE_LEXER;
						goto ZL1;
					}
				}
				break;
			case (TOK_OPENGROUPINVCB):
				{
					t_pos ZI207;
					t_char ZIcbrak;
					t_ast__expr ZInode1;

					/* BEGINNING OF EXTRACT: OPENGROUPINVCB */
					{
#line 349 "src/libre/parser.act"

		ZIstart = lex_state->lx.start;
		ZI207   = lex_state->lx.end;

		(void) ZIstart;
		(void) ZI207;
	
#line 2106 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF EXTRACT: OPENGROUPINVCB */
					ADVANCE_LEXER;
					/* BEGINNING OF ACTION: ast-make-alt */
					{
#line 874 "src/libre/parser.act"

		(ZInode) = ast_make_expr_alt(act_state->poolp, *flags);
		if ((ZInode) == NULL) {
			goto ZL1;
		}
	
#line 2119 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF ACTION: ast-make-alt */
					ZItmp = ZInode;
					/* BEGINNING OF ACTION: ast-make-invert */
					{
#line 973 "src/libre/parser.act"

		struct ast_expr *any;

		/*
		 * Here we're using an AST_EXPR_SUBTRACT node to implement inversion.
		 *
		 * Inversion is not quite equivalent to fsm_complement, because the
		 * complement of a class FSM (which is structured always left-to-right
		 * with no repetition) will effectively create .* anchors at the start
		 * and end (because the class didn't contain those).
		 *
		 * If those were added to a class beforehand, then fsm_complement()
		 * would suffice here (which would be attractive because it's much
		 * cheaper than constructing two FSM and subtracting them). However
		 * that would entail the assumption of having no transitions back to
		 * the start and end nodes, or introducing guard epsilons.
		 *
		 * I'd like to avoid those guards. And, unfortunately we'd still need
		 * to construct an intermediate FSM for fsm_complement() in any case.
		 * (And less typical, but we do still need AST_EXPR_SUBTRACT for sake
		 * of the SQL 2003 dialect anyway).
		 *
		 * So that idea doesn't satisfy my goal of avoiding intermediate FSM,
		 * and so I'm going with the simpler thing here until we come across
		 * a better idea.
		 */

		any = ast_make_expr_named(act_state->poolp, *flags, &class_any);
		if (any == NULL) {
			goto ZL1;
		}

		(ZInode) = ast_make_expr_subtract(act_state->poolp, *flags, any, (ZInode));
		if ((ZInode) == NULL) {
			goto ZL1;
		}
	
#line 2163 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF ACTION: ast-make-invert */
					/* BEGINNING OF ACTION: make-literal-cbrak */
					{
#line 892 "src/libre/parser.act"

		(ZIcbrak) = ']';
	
#line 2172 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF ACTION: make-literal-cbrak */
					p_209 (flags, lex_state, act_state, err, &ZIstart, &ZIcbrak, &ZInode1);
					if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
						RESTORE_LEXER;
						goto ZL1;
					}
					/* BEGINNING OF ACTION: ast-add-alt */
					{
#line 1053 "src/libre/parser.act"

		if (!ast_add_expr_alt((ZItmp), (ZInode1))) {
			goto ZL1;
		}
	
#line 2188 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF ACTION: ast-add-alt */
					p_expr_C_Ccharacter_Hclass_C_Clist_Hof_Hclass_Hterms (flags, lex_state, act_state, err, ZItmp);
					if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
						RESTORE_LEXER;
						goto ZL1;
					}
				}
				break;
			default:
				goto ZL1;
			}
		}
		/* END OF INLINE: 180 */
		/* BEGINNING OF INLINE: 213 */
		{
			switch (CURRENT_TERMINAL) {
			case (TOK_CLOSEGROUP):
				{
					t_char ZI214;
					t_pos ZI215;
					t_pos ZIend;

					/* BEGINNING OF EXTRACT: CLOSEGROUP */
					{
#line 357 "src/libre/parser.act"

		ZI214 = ']';
		ZI215 = lex_state->lx.start;
		ZIend   = lex_state->lx.end;

		(void) ZI214;
		(void) ZI215;
		(void) ZIend;
	
#line 2224 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF EXTRACT: CLOSEGROUP */
					ADVANCE_LEXER;
					/* BEGINNING OF ACTION: mark-group */
					{
#line 774 "src/libre/parser.act"

		mark(&act_state->groupstart, &(ZIstart));
		mark(&act_state->groupend,   &(ZIend));
	
#line 2235 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF ACTION: mark-group */
				}
				break;
			case (TOK_CLOSEGROUPRANGE):
				{
					t_char ZIcrange;
					t_pos ZI217;
					t_pos ZIend;
					t_ast__expr ZIrange;

					/* BEGINNING OF EXTRACT: CLOSEGROUPRANGE */
					{
#line 367 "src/libre/parser.act"

		ZIcrange = '-';
		ZI217 = lex_state->lx.start;
		ZIend   = lex_state->lx.end;

		(void) ZIcrange;
		(void) ZI217;
		(void) ZIend;
	
#line 2259 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF EXTRACT: CLOSEGROUPRANGE */
					ADVANCE_LEXER;
					/* BEGINNING OF ACTION: ast-make-literal */
					{
#line 881 "src/libre/parser.act"

		(ZIrange) = ast_make_expr_literal(act_state->poolp, *flags, (ZIcrange));
		if ((ZIrange) == NULL) {
			goto ZL4;
		}
	
#line 2272 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF ACTION: ast-make-literal */
					/* BEGINNING OF ACTION: ast-add-alt */
					{
#line 1053 "src/libre/parser.act"

		if (!ast_add_expr_alt((ZItmp), (ZIrange))) {
			goto ZL4;
		}
	
#line 2283 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF ACTION: ast-add-alt */
					/* BEGINNING OF ACTION: mark-group */
					{
#line 774 "src/libre/parser.act"

		mark(&act_state->groupstart, &(ZIstart));
		mark(&act_state->groupend,   &(ZIend));
	
#line 2293 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF ACTION: mark-group */
				}
				break;
			default:
				goto ZL4;
			}
			goto ZL3;
		ZL4:;
			{
				/* BEGINNING OF ACTION: err-expected-closegroup */
				{
#line 732 "src/libre/parser.act"

		if (err->e == RE_ESUCCESS) {
			err->e = RE_EXCLOSEGROUP;
		}
		goto ZL1;
	
#line 2313 "src/libre/dialect/pcre/parser.c"
				}
				/* END OF ACTION: err-expected-closegroup */
			}
		ZL3:;
		}
		/* END OF INLINE: 213 */
	}
	goto ZL0;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
ZL0:;
	*ZOnode = ZInode;
}

static void
p_expr_C_Ccharacter_Hclass_C_Crange_Hendpoint_Hend(flags flags, lex_state lex_state, act_state act_state, err err, t_endpoint *ZOr, t_pos *ZOend)
{
	t_endpoint ZIr;
	t_pos ZIend;

	if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
		return;
	}
	{
		/* BEGINNING OF INLINE: 161 */
		{
			switch (CURRENT_TERMINAL) {
			case (TOK_RANGE):
				{
					t_char ZIc;
					t_pos ZI163;

					/* BEGINNING OF EXTRACT: RANGE */
					{
#line 315 "src/libre/parser.act"

		ZIc = '-';
		ZI163 = lex_state->lx.start;
		ZIend   = lex_state->lx.end;

		(void) ZIc;
		(void) ZI163;
		(void) ZIend;
	
#line 2359 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF EXTRACT: RANGE */
					ADVANCE_LEXER;
					/* BEGINNING OF ACTION: ast-range-endpoint-literal */
					{
#line 846 "src/libre/parser.act"

		(ZIr).type = AST_ENDPOINT_LITERAL;
		(ZIr).u.literal.c = (unsigned char) (ZIc);
	
#line 2370 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF ACTION: ast-range-endpoint-literal */
				}
				break;
			case (TOK_NAMED__CLASS): case (TOK_ESC): case (TOK_CONTROL): case (TOK_OCT):
			case (TOK_HEX): case (TOK_CHAR): case (TOK_UNSUPPORTED):
				{
					t_pos ZI162;

					p_expr_C_Ccharacter_Hclass_C_Crange_Hendpoint (flags, lex_state, act_state, err, &ZIr, &ZI162, &ZIend);
					if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
						RESTORE_LEXER;
						goto ZL1;
					}
				}
				break;
			default:
				goto ZL1;
			}
		}
		/* END OF INLINE: 161 */
	}
	goto ZL0;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
ZL0:;
	*ZOr = ZIr;
	*ZOend = ZIend;
}

static void
p_317(flags flags, lex_state lex_state, act_state act_state, err err, t_char *ZI314, t_pos *ZI315, t_ast__expr *ZOnode)
{
	t_ast__expr ZInode;

	switch (CURRENT_TERMINAL) {
	default:
		{
			/* BEGINNING OF ACTION: ast-make-literal */
			{
#line 881 "src/libre/parser.act"

		(ZInode) = ast_make_expr_literal(act_state->poolp, *flags, (*ZI314));
		if ((ZInode) == NULL) {
			goto ZL1;
		}
	
#line 2419 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-make-literal */
		}
		break;
	case (TOK_RANGE):
		{
			t_endpoint ZIlower;
			t_endpoint ZIupper;
			t_pos ZIend;

			/* BEGINNING OF ACTION: ast-range-endpoint-literal */
			{
#line 846 "src/libre/parser.act"

		(ZIlower).type = AST_ENDPOINT_LITERAL;
		(ZIlower).u.literal.c = (unsigned char) (*ZI314);
	
#line 2437 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-range-endpoint-literal */
			p_168 (flags, lex_state, act_state, err);
			p_expr_C_Ccharacter_Hclass_C_Crange_Hendpoint_Hend (flags, lex_state, act_state, err, &ZIupper, &ZIend);
			if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
				RESTORE_LEXER;
				goto ZL1;
			}
			/* BEGINNING OF ACTION: mark-range */
			{
#line 779 "src/libre/parser.act"

		mark(&act_state->rangestart, &(*ZI315));
		mark(&act_state->rangeend,   &(ZIend));
	
#line 2453 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: mark-range */
			/* BEGINNING OF ACTION: ast-make-range */
			{
#line 1011 "src/libre/parser.act"

		unsigned char lower, upper;

		if ((ZIlower).type != AST_ENDPOINT_LITERAL ||
			(ZIupper).type != AST_ENDPOINT_LITERAL) {
			err->e = RE_EUNSUPPORTED;
			goto ZL1;
		}

		lower = (ZIlower).u.literal.c;
		upper = (ZIupper).u.literal.c;

		if (lower > upper) {
			char a[5], b[5];
			
			assert(sizeof err->set >= 1 + sizeof a + 1 + sizeof b + 1 + 1);
			
			sprintf(err->set, "%s-%s",
				escchar(a, sizeof a, lower), escchar(b, sizeof b, upper));
			err->e = RE_ENEGRANGE;
			goto ZL1;
		}

		(ZInode) = ast_make_expr_range(act_state->poolp, *flags, &(ZIlower), &(ZIupper));
		if ((ZInode) == NULL) {
			goto ZL1;
		}
	
#line 2487 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-make-range */
		}
		break;
	case (ERROR_TERMINAL):
		return;
	}
	goto ZL0;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
ZL0:;
	*ZOnode = ZInode;
}

static void
p_expr_C_Cpiece(flags flags, lex_state lex_state, act_state act_state, err err, t_ast__expr *ZOnode)
{
	t_ast__expr ZInode;

	if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
		return;
	}
	{
		t_ast__expr ZIe;

		p_expr_C_Cpiece_C_Catom (flags, lex_state, act_state, err, &ZIe);
		/* BEGINNING OF INLINE: 265 */
		{
			switch (CURRENT_TERMINAL) {
			case (TOK_OPT): case (TOK_PLUS): case (TOK_STAR): case (TOK_OPENCOUNT):
				{
					p_expr_C_Cpiece_C_Clist_Hof_Hcounts (flags, lex_state, act_state, err, ZIe, &ZInode);
					if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
						RESTORE_LEXER;
						goto ZL1;
					}
				}
				break;
			default:
				{
					t_ast__count ZIc;

					/* BEGINNING OF ACTION: count-one */
					{
#line 827 "src/libre/parser.act"

		(ZIc) = ast_make_count(1, 1);
	
#line 2537 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF ACTION: count-one */
					/* BEGINNING OF ACTION: ast-make-piece */
					{
#line 904 "src/libre/parser.act"

		if ((ZIc).min == 0 && (ZIc).max == 0) {
			(ZInode) = ast_make_expr_empty(act_state->poolp, *flags);
		} else if ((ZIc).min == 1 && (ZIc).max == 1) {
			(ZInode) = (ZIe);
		} else {
			(ZInode) = ast_make_expr_repeat(act_state->poolp, *flags, (ZIe), (ZIc));
		}
		if ((ZInode) == NULL) {
			err->e = RE_EXEOF;
			goto ZL1;
		}
	
#line 2556 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF ACTION: ast-make-piece */
				}
				break;
			case (ERROR_TERMINAL):
				RESTORE_LEXER;
				goto ZL1;
			}
		}
		/* END OF INLINE: 265 */
	}
	goto ZL0;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
ZL0:;
	*ZOnode = ZInode;
}

static void
p_320(flags flags, lex_state lex_state, act_state act_state, err err, t_pos *ZI318, t_unsigned *ZIm, t_ast__count *ZOc)
{
	t_ast__count ZIc;

	switch (CURRENT_TERMINAL) {
	case (TOK_CLOSECOUNT):
		{
			t_pos ZI256;
			t_pos ZIend;

			/* BEGINNING OF EXTRACT: CLOSECOUNT */
			{
#line 385 "src/libre/parser.act"

		ZI256 = lex_state->lx.start;
		ZIend   = lex_state->lx.end;

		(void) ZI256;
		(void) ZIend;
	
#line 2597 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF EXTRACT: CLOSECOUNT */
			ADVANCE_LEXER;
			/* BEGINNING OF ACTION: mark-count */
			{
#line 784 "src/libre/parser.act"

		mark(&act_state->countstart, &(*ZI318));
		mark(&act_state->countend,   &(ZIend));
	
#line 2608 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: mark-count */
			/* BEGINNING OF ACTION: count-range */
			{
#line 831 "src/libre/parser.act"

		if ((*ZIm) < (*ZIm)) {
			err->e = RE_ENEGCOUNT;
			err->m = (*ZIm);
			err->n = (*ZIm);

			mark(&act_state->countstart, &(*ZI318));
			mark(&act_state->countend,   &(ZIend));

			goto ZL1;
		}

		(ZIc) = ast_make_count((*ZIm), (*ZIm));
	
#line 2628 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: count-range */
		}
		break;
	case (TOK_SEP):
		{
			ADVANCE_LEXER;
			p_321 (flags, lex_state, act_state, err, ZI318, ZIm, &ZIc);
			if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
				RESTORE_LEXER;
				goto ZL1;
			}
		}
		break;
	case (ERROR_TERMINAL):
		return;
	default:
		goto ZL1;
	}
	goto ZL0;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
ZL0:;
	*ZOc = ZIc;
}

static void
p_expr(flags flags, lex_state lex_state, act_state act_state, err err, t_ast__expr *ZOnode)
{
	t_ast__expr ZInode;

	if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
		return;
	}
	{
		/* BEGINNING OF ACTION: ast-make-alt */
		{
#line 874 "src/libre/parser.act"

		(ZInode) = ast_make_expr_alt(act_state->poolp, *flags);
		if ((ZInode) == NULL) {
			goto ZL1;
		}
	
#line 2674 "src/libre/dialect/pcre/parser.c"
		}
		/* END OF ACTION: ast-make-alt */
		p_expr_C_Clist_Hof_Halts (flags, lex_state, act_state, err, ZInode);
		if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
			RESTORE_LEXER;
			goto ZL1;
		}
	}
	goto ZL0;
ZL1:;
	{
		/* BEGINNING OF ACTION: err-expected-alts */
		{
#line 718 "src/libre/parser.act"

		if (err->e == RE_ESUCCESS) {
			err->e = RE_EXALTS;
		}
		goto ZL2;
	
#line 2695 "src/libre/dialect/pcre/parser.c"
		}
		/* END OF ACTION: err-expected-alts */
		/* BEGINNING OF ACTION: ast-make-empty */
		{
#line 860 "src/libre/parser.act"

		(ZInode) = ast_make_expr_empty(act_state->poolp, *flags);
		if ((ZInode) == NULL) {
			goto ZL2;
		}
	
#line 2707 "src/libre/dialect/pcre/parser.c"
		}
		/* END OF ACTION: ast-make-empty */
	}
	goto ZL0;
ZL2:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
ZL0:;
	*ZOnode = ZInode;
}

static void
p_321(flags flags, lex_state lex_state, act_state act_state, err err, t_pos *ZI318, t_unsigned *ZIm, t_ast__count *ZOc)
{
	t_ast__count ZIc;

	switch (CURRENT_TERMINAL) {
	case (TOK_CLOSECOUNT):
		{
			t_pos ZI261;
			t_pos ZIend;
			t_unsigned ZIn;

			/* BEGINNING OF EXTRACT: CLOSECOUNT */
			{
#line 385 "src/libre/parser.act"

		ZI261 = lex_state->lx.start;
		ZIend   = lex_state->lx.end;

		(void) ZI261;
		(void) ZIend;
	
#line 2741 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF EXTRACT: CLOSECOUNT */
			ADVANCE_LEXER;
			/* BEGINNING OF ACTION: mark-count */
			{
#line 784 "src/libre/parser.act"

		mark(&act_state->countstart, &(*ZI318));
		mark(&act_state->countend,   &(ZIend));
	
#line 2752 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: mark-count */
			/* BEGINNING OF ACTION: count-unbounded */
			{
#line 811 "src/libre/parser.act"

		(ZIn) = AST_COUNT_UNBOUNDED;
	
#line 2761 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: count-unbounded */
			/* BEGINNING OF ACTION: count-range */
			{
#line 831 "src/libre/parser.act"

		if ((ZIn) < (*ZIm)) {
			err->e = RE_ENEGCOUNT;
			err->m = (*ZIm);
			err->n = (ZIn);

			mark(&act_state->countstart, &(*ZI318));
			mark(&act_state->countend,   &(ZIend));

			goto ZL1;
		}

		(ZIc) = ast_make_count((*ZIm), (ZIn));
	
#line 2781 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: count-range */
		}
		break;
	case (TOK_COUNT):
		{
			t_unsigned ZIn;
			t_pos ZI259;
			t_pos ZIend;

			/* BEGINNING OF EXTRACT: COUNT */
			{
#line 634 "src/libre/parser.act"

		unsigned long u;
		char *e;

		u = strtoul(lex_state->buf.a, &e, 10);

		if ((u == ULONG_MAX && errno == ERANGE) || u > UINT_MAX) {
			err->e = RE_ECOUNTRANGE;
			snprintdots(err->esc, sizeof err->esc, lex_state->buf.a);
			goto ZL1;
		}

		if ((u == ULONG_MAX && errno != 0) || *e != '\0') {
			err->e = RE_EXCOUNT;
			goto ZL1;
		}

		ZIn = (unsigned int) u;
	
#line 2814 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF EXTRACT: COUNT */
			ADVANCE_LEXER;
			switch (CURRENT_TERMINAL) {
			case (TOK_CLOSECOUNT):
				/* BEGINNING OF EXTRACT: CLOSECOUNT */
				{
#line 385 "src/libre/parser.act"

		ZI259 = lex_state->lx.start;
		ZIend   = lex_state->lx.end;

		(void) ZI259;
		(void) ZIend;
	
#line 2830 "src/libre/dialect/pcre/parser.c"
				}
				/* END OF EXTRACT: CLOSECOUNT */
				break;
			default:
				goto ZL1;
			}
			ADVANCE_LEXER;
			/* BEGINNING OF ACTION: mark-count */
			{
#line 784 "src/libre/parser.act"

		mark(&act_state->countstart, &(*ZI318));
		mark(&act_state->countend,   &(ZIend));
	
#line 2845 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: mark-count */
			/* BEGINNING OF ACTION: count-range */
			{
#line 831 "src/libre/parser.act"

		if ((ZIn) < (*ZIm)) {
			err->e = RE_ENEGCOUNT;
			err->m = (*ZIm);
			err->n = (ZIn);

			mark(&act_state->countstart, &(*ZI318));
			mark(&act_state->countend,   &(ZIend));

			goto ZL1;
		}

		(ZIc) = ast_make_count((*ZIm), (ZIn));
	
#line 2865 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: count-range */
		}
		break;
	case (ERROR_TERMINAL):
		return;
	default:
		goto ZL1;
	}
	goto ZL0;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
ZL0:;
	*ZOc = ZIc;
}

static void
p_194(flags flags, lex_state lex_state, act_state act_state, err err, t_ast__expr *ZItmp)
{
	switch (CURRENT_TERMINAL) {
	case (TOK_RANGE):
		{
			t_char ZIc;
			t_pos ZIrstart;
			t_pos ZI195;
			t_ast__expr ZInode1;

			/* BEGINNING OF EXTRACT: RANGE */
			{
#line 315 "src/libre/parser.act"

		ZIc = '-';
		ZIrstart = lex_state->lx.start;
		ZI195   = lex_state->lx.end;

		(void) ZIc;
		(void) ZIrstart;
		(void) ZI195;
	
#line 2906 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF EXTRACT: RANGE */
			ADVANCE_LEXER;
			/* BEGINNING OF INLINE: 196 */
			{
				switch (CURRENT_TERMINAL) {
				default:
					{
						/* BEGINNING OF ACTION: ast-make-literal */
						{
#line 881 "src/libre/parser.act"

		(ZInode1) = ast_make_expr_literal(act_state->poolp, *flags, (ZIc));
		if ((ZInode1) == NULL) {
			goto ZL1;
		}
	
#line 2924 "src/libre/dialect/pcre/parser.c"
						}
						/* END OF ACTION: ast-make-literal */
					}
					break;
				case (TOK_RANGE):
					{
						t_endpoint ZIlower;
						t_char ZI197;
						t_pos ZI198;
						t_pos ZI199;
						t_endpoint ZIupper;
						t_pos ZIend;

						/* BEGINNING OF ACTION: ast-range-endpoint-literal */
						{
#line 846 "src/libre/parser.act"

		(ZIlower).type = AST_ENDPOINT_LITERAL;
		(ZIlower).u.literal.c = (unsigned char) (ZIc);
	
#line 2945 "src/libre/dialect/pcre/parser.c"
						}
						/* END OF ACTION: ast-range-endpoint-literal */
						/* BEGINNING OF EXTRACT: RANGE */
						{
#line 315 "src/libre/parser.act"

		ZI197 = '-';
		ZI198 = lex_state->lx.start;
		ZI199   = lex_state->lx.end;

		(void) ZI197;
		(void) ZI198;
		(void) ZI199;
	
#line 2960 "src/libre/dialect/pcre/parser.c"
						}
						/* END OF EXTRACT: RANGE */
						ADVANCE_LEXER;
						p_expr_C_Ccharacter_Hclass_C_Crange_Hendpoint_Hend (flags, lex_state, act_state, err, &ZIupper, &ZIend);
						if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
							RESTORE_LEXER;
							goto ZL1;
						}
						/* BEGINNING OF ACTION: ast-make-range */
						{
#line 1011 "src/libre/parser.act"

		unsigned char lower, upper;

		if ((ZIlower).type != AST_ENDPOINT_LITERAL ||
			(ZIupper).type != AST_ENDPOINT_LITERAL) {
			err->e = RE_EUNSUPPORTED;
			goto ZL1;
		}

		lower = (ZIlower).u.literal.c;
		upper = (ZIupper).u.literal.c;

		if (lower > upper) {
			char a[5], b[5];
			
			assert(sizeof err->set >= 1 + sizeof a + 1 + sizeof b + 1 + 1);
			
			sprintf(err->set, "%s-%s",
				escchar(a, sizeof a, lower), escchar(b, sizeof b, upper));
			err->e = RE_ENEGRANGE;
			goto ZL1;
		}

		(ZInode1) = ast_make_expr_range(act_state->poolp, *flags, &(ZIlower), &(ZIupper));
		if ((ZInode1) == NULL) {
			goto ZL1;
		}
	
#line 3000 "src/libre/dialect/pcre/parser.c"
						}
						/* END OF ACTION: ast-make-range */
					}
					break;
				}
			}
			/* END OF INLINE: 196 */
			/* BEGINNING OF ACTION: ast-add-alt */
			{
#line 1053 "src/libre/parser.act"

		if (!ast_add_expr_alt((*ZItmp), (ZInode1))) {
			goto ZL1;
		}
	
#line 3016 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-add-alt */
		}
		break;
	case (ERROR_TERMINAL):
		return;
	default:
		break;
	}
	return;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
}

static void
p_expr_C_Cflags(flags flags, lex_state lex_state, act_state act_state, err err, t_ast__expr *ZOnode)
{
	t_ast__expr ZInode;

	if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
		return;
	}
	{
		t_re__flags ZIempty__pos;
		t_re__flags ZIempty__neg;
		t_re__flags ZIpos;
		t_re__flags ZIneg;

		switch (CURRENT_TERMINAL) {
		case (TOK_FLAGS):
			break;
		default:
			goto ZL1;
		}
		ADVANCE_LEXER;
		/* BEGINNING OF ACTION: re-flag-none */
		{
#line 803 "src/libre/parser.act"

		(ZIempty__pos) = RE_FLAGS_NONE;
	
#line 3059 "src/libre/dialect/pcre/parser.c"
		}
		/* END OF ACTION: re-flag-none */
		/* BEGINNING OF ACTION: re-flag-none */
		{
#line 803 "src/libre/parser.act"

		(ZIempty__neg) = RE_FLAGS_NONE;
	
#line 3068 "src/libre/dialect/pcre/parser.c"
		}
		/* END OF ACTION: re-flag-none */
		/* BEGINNING OF INLINE: 231 */
		{
			switch (CURRENT_TERMINAL) {
			case (TOK_FLAG__IGNORE): case (TOK_FLAG__UNKNOWN): case (TOK_FLAG__INSENSITIVE): case (TOK_FLAG__EXTENDED):
			case (TOK_FLAG__SINGLE):
				{
					p_expr_C_Cflags_C_Cflag__set (flags, lex_state, act_state, err, ZIempty__pos, &ZIpos);
					if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
						RESTORE_LEXER;
						goto ZL1;
					}
				}
				break;
			default:
				{
					ZIpos = ZIempty__pos;
				}
				break;
			}
		}
		/* END OF INLINE: 231 */
		/* BEGINNING OF INLINE: 233 */
		{
			switch (CURRENT_TERMINAL) {
			case (TOK_NEGATE):
				{
					ADVANCE_LEXER;
					p_expr_C_Cflags_C_Cflag__set (flags, lex_state, act_state, err, ZIempty__neg, &ZIneg);
					if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
						RESTORE_LEXER;
						goto ZL1;
					}
				}
				break;
			default:
				{
					ZIneg = ZIempty__neg;
				}
				break;
			}
		}
		/* END OF INLINE: 233 */
		/* BEGINNING OF INLINE: 236 */
		{
			switch (CURRENT_TERMINAL) {
			case (TOK_CLOSE):
				{
					ADVANCE_LEXER;
					/* BEGINNING OF ACTION: ast-mask-re-flags */
					{
#line 933 "src/libre/parser.act"

		/*
		 * Note: in cases like `(?i-i)`, the negative is
		 * required to take precedence.
		 */
		*flags |= (ZIpos);
		*flags &= ~(ZIneg);
	
#line 3130 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF ACTION: ast-mask-re-flags */
					/* BEGINNING OF ACTION: ast-make-empty */
					{
#line 860 "src/libre/parser.act"

		(ZInode) = ast_make_expr_empty(act_state->poolp, *flags);
		if ((ZInode) == NULL) {
			goto ZL5;
		}
	
#line 3142 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF ACTION: ast-make-empty */
				}
				break;
			case (TOK_SUB):
				{
					t_re__flags ZIflags;
					t_ast__expr ZIe;

					ADVANCE_LEXER;
					/* BEGINNING OF ACTION: ast-get-re-flags */
					{
#line 925 "src/libre/parser.act"

		(ZIflags) = *flags;
	
#line 3159 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF ACTION: ast-get-re-flags */
					/* BEGINNING OF ACTION: ast-mask-re-flags */
					{
#line 933 "src/libre/parser.act"

		/*
		 * Note: in cases like `(?i-i)`, the negative is
		 * required to take precedence.
		 */
		*flags |= (ZIpos);
		*flags &= ~(ZIneg);
	
#line 3173 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF ACTION: ast-mask-re-flags */
					p_expr (flags, lex_state, act_state, err, &ZIe);
					if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
						RESTORE_LEXER;
						goto ZL5;
					}
					/* BEGINNING OF ACTION: ast-set-re-flags */
					{
#line 929 "src/libre/parser.act"

		*flags = (ZIflags);
	
#line 3187 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF ACTION: ast-set-re-flags */
					switch (CURRENT_TERMINAL) {
					case (TOK_CLOSE):
						break;
					default:
						goto ZL5;
					}
					ADVANCE_LEXER;
					ZInode = ZIe;
				}
				break;
			default:
				goto ZL5;
			}
			goto ZL4;
		ZL5:;
			{
				/* BEGINNING OF ACTION: err-expected-closeflags */
				{
#line 753 "src/libre/parser.act"

		if (err->e == RE_ESUCCESS) {
			err->e = RE_EXCLOSEFLAGS;
		}
		goto ZL1;
	
#line 3215 "src/libre/dialect/pcre/parser.c"
				}
				/* END OF ACTION: err-expected-closeflags */
				/* BEGINNING OF ACTION: ast-make-empty */
				{
#line 860 "src/libre/parser.act"

		(ZInode) = ast_make_expr_empty(act_state->poolp, *flags);
		if ((ZInode) == NULL) {
			goto ZL1;
		}
	
#line 3227 "src/libre/dialect/pcre/parser.c"
				}
				/* END OF ACTION: ast-make-empty */
			}
		ZL4:;
		}
		/* END OF INLINE: 236 */
	}
	goto ZL0;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
ZL0:;
	*ZOnode = ZInode;
}

static void
p_expr_C_Cpiece_C_Clist_Hof_Hcounts(flags flags, lex_state lex_state, act_state act_state, err err, t_ast__expr ZIe, t_ast__expr *ZOnode)
{
	t_ast__expr ZInode;

	if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
		return;
	}
	{
		t_ast__count ZIc;

		p_expr_C_Cpiece_C_Ccount (flags, lex_state, act_state, err, &ZIc);
		if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
			RESTORE_LEXER;
			goto ZL1;
		}
		/* BEGINNING OF ACTION: ast-make-piece */
		{
#line 904 "src/libre/parser.act"

		if ((ZIc).min == 0 && (ZIc).max == 0) {
			(ZInode) = ast_make_expr_empty(act_state->poolp, *flags);
		} else if ((ZIc).min == 1 && (ZIc).max == 1) {
			(ZInode) = (ZIe);
		} else {
			(ZInode) = ast_make_expr_repeat(act_state->poolp, *flags, (ZIe), (ZIc));
		}
		if ((ZInode) == NULL) {
			err->e = RE_EXEOF;
			goto ZL1;
		}
	
#line 3275 "src/libre/dialect/pcre/parser.c"
		}
		/* END OF ACTION: ast-make-piece */
		/* BEGINNING OF INLINE: 264 */
		{
			switch (CURRENT_TERMINAL) {
			case (TOK_OPT):
				{
					ADVANCE_LEXER;
					/* BEGINNING OF ACTION: err-unsupported */
					{
#line 767 "src/libre/parser.act"

		if (err->e == RE_ESUCCESS) {
			err->e = RE_EUNSUPPORTED;
		}
		goto ZL1;
	
#line 3293 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF ACTION: err-unsupported */
				}
				break;
			case (TOK_PLUS):
				{
					ADVANCE_LEXER;
					/* BEGINNING OF ACTION: err-unsupported */
					{
#line 767 "src/libre/parser.act"

		if (err->e == RE_ESUCCESS) {
			err->e = RE_EUNSUPPORTED;
		}
		goto ZL1;
	
#line 3310 "src/libre/dialect/pcre/parser.c"
					}
					/* END OF ACTION: err-unsupported */
				}
				break;
			default:
				break;
			}
		}
		/* END OF INLINE: 264 */
	}
	goto ZL0;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
ZL0:;
	*ZOnode = ZInode;
}

static void
p_expr_C_Ccharacter_Hclass_C_Crange_Hendpoint(flags flags, lex_state lex_state, act_state act_state, err err, t_endpoint *ZOr, t_pos *ZOstart, t_pos *ZOend)
{
	t_endpoint ZIr;
	t_pos ZIstart;
	t_pos ZIend;

	if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
		return;
	}
	{
		/* BEGINNING OF INLINE: 158 */
		{
			switch (CURRENT_TERMINAL) {
			case (TOK_NAMED__CLASS):
				{
					p_expr_C_Ccharacter_Hclass_C_Crange_Hendpoint_C_Crange_Hendpoint_Hclass (flags, lex_state, act_state, err, &ZIr, &ZIstart, &ZIend);
					if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
						RESTORE_LEXER;
						goto ZL1;
					}
				}
				break;
			case (TOK_ESC): case (TOK_CONTROL): case (TOK_OCT): case (TOK_HEX):
			case (TOK_CHAR): case (TOK_UNSUPPORTED):
				{
					p_expr_C_Ccharacter_Hclass_C_Crange_Hendpoint_C_Crange_Hendpoint_Hliteral (flags, lex_state, act_state, err, &ZIr, &ZIstart, &ZIend);
					if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
						RESTORE_LEXER;
						goto ZL1;
					}
				}
				break;
			default:
				goto ZL1;
			}
		}
		/* END OF INLINE: 158 */
	}
	goto ZL0;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
ZL0:;
	*ZOr = ZIr;
	*ZOstart = ZIstart;
	*ZOend = ZIend;
}

static void
p_class_Hnamed(flags flags, lex_state lex_state, act_state act_state, err err, t_ast__expr *ZOnode, t_pos *ZOstart, t_pos *ZOend)
{
	t_ast__expr ZInode;
	t_pos ZIstart;
	t_pos ZIend;

	if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
		return;
	}
	{
		t_ast__class__id ZIid;

		switch (CURRENT_TERMINAL) {
		case (TOK_NAMED__CLASS):
			/* BEGINNING OF EXTRACT: NAMED_CLASS */
			{
#line 654 "src/libre/parser.act"

		ZIid = DIALECT_CLASS(lex_state->buf.a);
		if (ZIid == NULL) {
			/* syntax error -- unrecognized class */
			goto ZL1;
		}

		ZIstart = lex_state->lx.start;
		ZIend   = lex_state->lx.end;

		(void) ZIstart;
		(void) ZIend;
	
#line 3409 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF EXTRACT: NAMED_CLASS */
			break;
		default:
			goto ZL1;
		}
		ADVANCE_LEXER;
		/* BEGINNING OF ACTION: ast-make-named */
		{
#line 1040 "src/libre/parser.act"

		(ZInode) = ast_make_expr_named(act_state->poolp, *flags, (ZIid));
		if ((ZInode) == NULL) {
			goto ZL1;
		}
	
#line 3426 "src/libre/dialect/pcre/parser.c"
		}
		/* END OF ACTION: ast-make-named */
	}
	goto ZL0;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
ZL0:;
	*ZOnode = ZInode;
	*ZOstart = ZIstart;
	*ZOend = ZIend;
}

static void
p_209(flags flags, lex_state lex_state, act_state act_state, err err, t_pos *ZIstart, t_char *ZIcbrak, t_ast__expr *ZOnode1)
{
	t_ast__expr ZInode1;

	switch (CURRENT_TERMINAL) {
	default:
		{
			/* BEGINNING OF ACTION: ast-make-literal */
			{
#line 881 "src/libre/parser.act"

		(ZInode1) = ast_make_expr_literal(act_state->poolp, *flags, (*ZIcbrak));
		if ((ZInode1) == NULL) {
			goto ZL1;
		}
	
#line 3457 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-make-literal */
		}
		break;
	case (TOK_RANGE):
		{
			t_endpoint ZIr;
			t_char ZI210;
			t_pos ZI211;
			t_pos ZI212;
			t_endpoint ZIupper;
			t_pos ZIend;
			t_endpoint ZIlower;

			/* BEGINNING OF ACTION: ast-range-endpoint-literal */
			{
#line 846 "src/libre/parser.act"

		(ZIr).type = AST_ENDPOINT_LITERAL;
		(ZIr).u.literal.c = (unsigned char) (*ZIcbrak);
	
#line 3479 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-range-endpoint-literal */
			/* BEGINNING OF EXTRACT: RANGE */
			{
#line 315 "src/libre/parser.act"

		ZI210 = '-';
		ZI211 = lex_state->lx.start;
		ZI212   = lex_state->lx.end;

		(void) ZI210;
		(void) ZI211;
		(void) ZI212;
	
#line 3494 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF EXTRACT: RANGE */
			ADVANCE_LEXER;
			p_expr_C_Ccharacter_Hclass_C_Crange_Hendpoint_Hend (flags, lex_state, act_state, err, &ZIupper, &ZIend);
			if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
				RESTORE_LEXER;
				goto ZL1;
			}
			/* BEGINNING OF ACTION: ast-range-endpoint-literal */
			{
#line 846 "src/libre/parser.act"

		(ZIlower).type = AST_ENDPOINT_LITERAL;
		(ZIlower).u.literal.c = (unsigned char) (*ZIcbrak);
	
#line 3510 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-range-endpoint-literal */
			/* BEGINNING OF ACTION: ast-make-range */
			{
#line 1011 "src/libre/parser.act"

		unsigned char lower, upper;

		if ((ZIlower).type != AST_ENDPOINT_LITERAL ||
			(ZIupper).type != AST_ENDPOINT_LITERAL) {
			err->e = RE_EUNSUPPORTED;
			goto ZL1;
		}

		lower = (ZIlower).u.literal.c;
		upper = (ZIupper).u.literal.c;

		if (lower > upper) {
			char a[5], b[5];
			
			assert(sizeof err->set >= 1 + sizeof a + 1 + sizeof b + 1 + 1);
			
			sprintf(err->set, "%s-%s",
				escchar(a, sizeof a, lower), escchar(b, sizeof b, upper));
			err->e = RE_ENEGRANGE;
			goto ZL1;
		}

		(ZInode1) = ast_make_expr_range(act_state->poolp, *flags, &(ZIlower), &(ZIupper));
		if ((ZInode1) == NULL) {
			goto ZL1;
		}
	
#line 3544 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-make-range */
		}
		break;
	case (ERROR_TERMINAL):
		return;
	}
	goto ZL0;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
ZL0:;
	*ZOnode1 = ZInode1;
}

static void
p_expr_C_Clist_Hof_Halts(flags flags, lex_state lex_state, act_state act_state, err err, t_ast__expr ZIalts)
{
	if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
		return;
	}
ZL2_expr_C_Clist_Hof_Halts:;
	{
		t_ast__expr ZIa;

		p_expr_C_Calt (flags, lex_state, act_state, err, &ZIa);
		if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
			RESTORE_LEXER;
			goto ZL1;
		}
		/* BEGINNING OF ACTION: ast-add-alt */
		{
#line 1053 "src/libre/parser.act"

		if (!ast_add_expr_alt((ZIalts), (ZIa))) {
			goto ZL1;
		}
	
#line 3583 "src/libre/dialect/pcre/parser.c"
		}
		/* END OF ACTION: ast-add-alt */
		/* BEGINNING OF INLINE: 278 */
		{
			switch (CURRENT_TERMINAL) {
			case (TOK_ALT):
				{
					ADVANCE_LEXER;
					/* BEGINNING OF INLINE: expr::list-of-alts */
					goto ZL2_expr_C_Clist_Hof_Halts;
					/* END OF INLINE: expr::list-of-alts */
				}
				/* UNREACHED */
			default:
				break;
			}
		}
		/* END OF INLINE: 278 */
	}
	return;
ZL1:;
	{
		/* BEGINNING OF ACTION: err-expected-alts */
		{
#line 718 "src/libre/parser.act"

		if (err->e == RE_ESUCCESS) {
			err->e = RE_EXALTS;
		}
		goto ZL4;
	
#line 3615 "src/libre/dialect/pcre/parser.c"
		}
		/* END OF ACTION: err-expected-alts */
	}
	goto ZL0;
ZL4:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
ZL0:;
}

static void
p_expr_C_Cpiece_C_Ccount(flags flags, lex_state lex_state, act_state act_state, err err, t_ast__count *ZOc)
{
	t_ast__count ZIc;

	switch (CURRENT_TERMINAL) {
	case (TOK_OPENCOUNT):
		{
			t_pos ZI318;
			t_pos ZI319;
			t_unsigned ZIm;

			/* BEGINNING OF EXTRACT: OPENCOUNT */
			{
#line 377 "src/libre/parser.act"

		ZI318 = lex_state->lx.start;
		ZI319   = lex_state->lx.end;

		(void) ZI318;
		(void) ZI319;
	
#line 3648 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF EXTRACT: OPENCOUNT */
			ADVANCE_LEXER;
			switch (CURRENT_TERMINAL) {
			case (TOK_COUNT):
				/* BEGINNING OF EXTRACT: COUNT */
				{
#line 634 "src/libre/parser.act"

		unsigned long u;
		char *e;

		u = strtoul(lex_state->buf.a, &e, 10);

		if ((u == ULONG_MAX && errno == ERANGE) || u > UINT_MAX) {
			err->e = RE_ECOUNTRANGE;
			snprintdots(err->esc, sizeof err->esc, lex_state->buf.a);
			goto ZL1;
		}

		if ((u == ULONG_MAX && errno != 0) || *e != '\0') {
			err->e = RE_EXCOUNT;
			goto ZL1;
		}

		ZIm = (unsigned int) u;
	
#line 3676 "src/libre/dialect/pcre/parser.c"
				}
				/* END OF EXTRACT: COUNT */
				break;
			default:
				goto ZL1;
			}
			ADVANCE_LEXER;
			p_320 (flags, lex_state, act_state, err, &ZI318, &ZIm, &ZIc);
			if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
				RESTORE_LEXER;
				goto ZL1;
			}
		}
		break;
	case (TOK_OPT):
		{
			ADVANCE_LEXER;
			/* BEGINNING OF ACTION: count-zero-or-one */
			{
#line 823 "src/libre/parser.act"

		(ZIc) = ast_make_count(0, 1);
	
#line 3700 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: count-zero-or-one */
		}
		break;
	case (TOK_PLUS):
		{
			ADVANCE_LEXER;
			/* BEGINNING OF ACTION: count-one-or-more */
			{
#line 819 "src/libre/parser.act"

		(ZIc) = ast_make_count(1, AST_COUNT_UNBOUNDED);
	
#line 3714 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: count-one-or-more */
		}
		break;
	case (TOK_STAR):
		{
			ADVANCE_LEXER;
			/* BEGINNING OF ACTION: count-zero-or-more */
			{
#line 815 "src/libre/parser.act"

		(ZIc) = ast_make_count(0, AST_COUNT_UNBOUNDED);
	
#line 3728 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: count-zero-or-more */
		}
		break;
	case (ERROR_TERMINAL):
		return;
	default:
		goto ZL1;
	}
	goto ZL0;
ZL1:;
	{
		/* BEGINNING OF ACTION: err-expected-count */
		{
#line 704 "src/libre/parser.act"

		if (err->e == RE_ESUCCESS) {
			err->e = RE_EXCOUNT;
		}
		goto ZL2;
	
#line 3750 "src/libre/dialect/pcre/parser.c"
		}
		/* END OF ACTION: err-expected-count */
		/* BEGINNING OF ACTION: count-one */
		{
#line 827 "src/libre/parser.act"

		(ZIc) = ast_make_count(1, 1);
	
#line 3759 "src/libre/dialect/pcre/parser.c"
		}
		/* END OF ACTION: count-one */
	}
	goto ZL0;
ZL2:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
ZL0:;
	*ZOc = ZIc;
}

void
p_re__pcre(flags flags, lex_state lex_state, act_state act_state, err err, t_ast__expr *ZOnode)
{
	t_ast__expr ZInode;

	if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
		return;
	}
	{
		t_group__id ZIid;
		t_ast__expr ZIe;

		/* BEGINNING OF ACTION: make-group-id */
		{
#line 888 "src/libre/parser.act"

		(ZIid) = act_state->group_id++;
	
#line 3789 "src/libre/dialect/pcre/parser.c"
		}
		/* END OF ACTION: make-group-id */
		p_expr (flags, lex_state, act_state, err, &ZIe);
		if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
			RESTORE_LEXER;
			goto ZL1;
		}
		/* BEGINNING OF ACTION: ast-make-group */
		{
#line 918 "src/libre/parser.act"

		(ZInode) = ast_make_expr_group(act_state->poolp, *flags, (ZIe), (ZIid));
		if ((ZInode) == NULL) {
			goto ZL1;
		}
	
#line 3806 "src/libre/dialect/pcre/parser.c"
		}
		/* END OF ACTION: ast-make-group */
		/* BEGINNING OF INLINE: 280 */
		{
			{
				switch (CURRENT_TERMINAL) {
				case (TOK_EOF):
					break;
				default:
					goto ZL3;
				}
				ADVANCE_LEXER;
			}
			goto ZL2;
		ZL3:;
			{
				/* BEGINNING OF ACTION: err-expected-eof */
				{
#line 760 "src/libre/parser.act"

		if (err->e == RE_ESUCCESS) {
			err->e = RE_EXEOF;
		}
		goto ZL1;
	
#line 3832 "src/libre/dialect/pcre/parser.c"
				}
				/* END OF ACTION: err-expected-eof */
			}
		ZL2:;
		}
		/* END OF INLINE: 280 */
	}
	goto ZL0;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
ZL0:;
	*ZOnode = ZInode;
}

static void
p_expr_C_Cpiece_C_Catom(flags flags, lex_state lex_state, act_state act_state, err err, t_ast__expr *ZOe)
{
	t_ast__expr ZIe;

	switch (CURRENT_TERMINAL) {
	case (TOK_ANY):
		{
			t_ast__class__id ZIa;

			ADVANCE_LEXER;
			/* BEGINNING OF ACTION: class-any */
			{
#line 789 "src/libre/parser.act"

		/* TODO: or the unicode equivalent */
		(ZIa) = (*flags & RE_SINGLE) ? &class_any : &class_notnl;
	
#line 3866 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: class-any */
			/* BEGINNING OF ACTION: ast-make-named */
			{
#line 1040 "src/libre/parser.act"

		(ZIe) = ast_make_expr_named(act_state->poolp, *flags, (ZIa));
		if ((ZIe) == NULL) {
			goto ZL1;
		}
	
#line 3878 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-make-named */
		}
		break;
	case (TOK_END):
		{
			ADVANCE_LEXER;
			/* BEGINNING OF ACTION: ast-make-anchor-end */
			{
#line 949 "src/libre/parser.act"

		(ZIe) = ast_make_expr_anchor(act_state->poolp, *flags, AST_ANCHOR_END);
		if ((ZIe) == NULL) {
			goto ZL1;
		}
	
#line 3895 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-make-anchor-end */
		}
		break;
	case (TOK_END__NL):
		{
			ADVANCE_LEXER;
			/* BEGINNING OF ACTION: ast-make-anchor-end-nl */
			{
#line 956 "src/libre/parser.act"

		(ZIe) = ast_make_expr_anchor(act_state->poolp, *flags, AST_ANCHOR_END);
		if ((ZIe) == NULL) {
			goto ZL1;
		}
		if (!(*flags & RE_ANCHORED)) {
			(ZIe)->u.anchor.is_end_nl = 1;
		}
	
#line 3915 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-make-anchor-end-nl */
		}
		break;
	case (TOK_EOL):
		{
			t_ast__class__id ZIclass__bsr;
			t_ast__expr ZIbsr;
			t_ast__expr ZIcrlf;
			t_char ZIcr;
			t_ast__expr ZIecr;
			t_char ZInl;
			t_ast__expr ZIenl;

			ADVANCE_LEXER;
			/* BEGINNING OF ACTION: class-bsr */
			{
#line 794 "src/libre/parser.act"

		/* TODO: or the unicode equivalent */
		(ZIclass__bsr) = &class_bsr;
	
#line 3938 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: class-bsr */
			/* BEGINNING OF ACTION: ast-make-named */
			{
#line 1040 "src/libre/parser.act"

		(ZIbsr) = ast_make_expr_named(act_state->poolp, *flags, (ZIclass__bsr));
		if ((ZIbsr) == NULL) {
			goto ZL1;
		}
	
#line 3950 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-make-named */
			/* BEGINNING OF ACTION: ast-make-concat */
			{
#line 867 "src/libre/parser.act"

		(ZIcrlf) = ast_make_expr_concat(act_state->poolp, *flags);
		if ((ZIcrlf) == NULL) {
			goto ZL1;
		}
	
#line 3962 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-make-concat */
			/* BEGINNING OF ACTION: make-literal-cr */
			{
#line 896 "src/libre/parser.act"

		(ZIcr) = '\r';
	
#line 3971 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: make-literal-cr */
			/* BEGINNING OF ACTION: ast-make-literal */
			{
#line 881 "src/libre/parser.act"

		(ZIecr) = ast_make_expr_literal(act_state->poolp, *flags, (ZIcr));
		if ((ZIecr) == NULL) {
			goto ZL1;
		}
	
#line 3983 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-make-literal */
			/* BEGINNING OF ACTION: make-literal-nl */
			{
#line 900 "src/libre/parser.act"

		(ZInl) = '\n';
	
#line 3992 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: make-literal-nl */
			/* BEGINNING OF ACTION: ast-make-literal */
			{
#line 881 "src/libre/parser.act"

		(ZIenl) = ast_make_expr_literal(act_state->poolp, *flags, (ZInl));
		if ((ZIenl) == NULL) {
			goto ZL1;
		}
	
#line 4004 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-make-literal */
			/* BEGINNING OF ACTION: ast-add-concat */
			{
#line 1047 "src/libre/parser.act"

		if (!ast_add_expr_concat((ZIcrlf), (ZIecr))) {
			goto ZL1;
		}
	
#line 4015 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-add-concat */
			/* BEGINNING OF ACTION: ast-add-concat */
			{
#line 1047 "src/libre/parser.act"

		if (!ast_add_expr_concat((ZIcrlf), (ZIenl))) {
			goto ZL1;
		}
	
#line 4026 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-add-concat */
			/* BEGINNING OF ACTION: ast-make-alt */
			{
#line 874 "src/libre/parser.act"

		(ZIe) = ast_make_expr_alt(act_state->poolp, *flags);
		if ((ZIe) == NULL) {
			goto ZL1;
		}
	
#line 4038 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-make-alt */
			/* BEGINNING OF ACTION: ast-add-alt */
			{
#line 1053 "src/libre/parser.act"

		if (!ast_add_expr_alt((ZIe), (ZIcrlf))) {
			goto ZL1;
		}
	
#line 4049 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-add-alt */
			/* BEGINNING OF ACTION: ast-add-alt */
			{
#line 1053 "src/libre/parser.act"

		if (!ast_add_expr_alt((ZIe), (ZIbsr))) {
			goto ZL1;
		}
	
#line 4060 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-add-alt */
		}
		break;
	case (TOK_OPEN):
		{
			t_re__flags ZIflags;
			t_group__id ZIid;
			t_ast__expr ZIg;

			ADVANCE_LEXER;
			/* BEGINNING OF ACTION: ast-get-re-flags */
			{
#line 925 "src/libre/parser.act"

		(ZIflags) = *flags;
	
#line 4078 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-get-re-flags */
			/* BEGINNING OF ACTION: make-group-id */
			{
#line 888 "src/libre/parser.act"

		(ZIid) = act_state->group_id++;
	
#line 4087 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: make-group-id */
			p_expr (flags, lex_state, act_state, err, &ZIg);
			if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
				RESTORE_LEXER;
				goto ZL1;
			}
			/* BEGINNING OF ACTION: ast-set-re-flags */
			{
#line 929 "src/libre/parser.act"

		*flags = (ZIflags);
	
#line 4101 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-set-re-flags */
			/* BEGINNING OF ACTION: ast-make-group */
			{
#line 918 "src/libre/parser.act"

		(ZIe) = ast_make_expr_group(act_state->poolp, *flags, (ZIg), (ZIid));
		if ((ZIe) == NULL) {
			goto ZL1;
		}
	
#line 4113 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-make-group */
			switch (CURRENT_TERMINAL) {
			case (TOK_CLOSE):
				break;
			default:
				goto ZL1;
			}
			ADVANCE_LEXER;
		}
		break;
	case (TOK_START):
		{
			ADVANCE_LEXER;
			/* BEGINNING OF ACTION: ast-make-anchor-start */
			{
#line 942 "src/libre/parser.act"

		(ZIe) = ast_make_expr_anchor(act_state->poolp, *flags, AST_ANCHOR_START);
		if ((ZIe) == NULL) {
			goto ZL1;
		}
	
#line 4137 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-make-anchor-start */
		}
		break;
	case (TOK_OPENGROUP): case (TOK_OPENGROUPINV): case (TOK_OPENGROUPCB): case (TOK_OPENGROUPINVCB):
		{
			p_expr_C_Ccharacter_Hclass (flags, lex_state, act_state, err, &ZIe);
			if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
				RESTORE_LEXER;
				goto ZL1;
			}
		}
		break;
	case (TOK_FLAGS):
		{
			p_expr_C_Cflags (flags, lex_state, act_state, err, &ZIe);
			if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
				RESTORE_LEXER;
				goto ZL1;
			}
		}
		break;
	case (TOK_ESC): case (TOK_NOESC): case (TOK_CONTROL): case (TOK_OCT):
	case (TOK_HEX): case (TOK_CHAR): case (TOK_UNSUPPORTED):
		{
			p_expr_C_Cliteral (flags, lex_state, act_state, err, &ZIe);
			if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
				RESTORE_LEXER;
				goto ZL1;
			}
		}
		break;
	case (TOK_NAMED__CLASS):
		{
			p_expr_C_Ctype (flags, lex_state, act_state, err, &ZIe);
			if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
				RESTORE_LEXER;
				goto ZL1;
			}
		}
		break;
	case (ERROR_TERMINAL):
		return;
	default:
		goto ZL1;
	}
	goto ZL0;
ZL1:;
	{
		/* BEGINNING OF ACTION: err-expected-atom */
		{
#line 711 "src/libre/parser.act"

		if (err->e == RE_ESUCCESS) {
			err->e = RE_EXATOM;
		}
		goto ZL2;
	
#line 4196 "src/libre/dialect/pcre/parser.c"
		}
		/* END OF ACTION: err-expected-atom */
		/* BEGINNING OF ACTION: ast-make-empty */
		{
#line 860 "src/libre/parser.act"

		(ZIe) = ast_make_expr_empty(act_state->poolp, *flags);
		if ((ZIe) == NULL) {
			goto ZL2;
		}
	
#line 4208 "src/libre/dialect/pcre/parser.c"
		}
		/* END OF ACTION: ast-make-empty */
	}
	goto ZL0;
ZL2:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
ZL0:;
	*ZOe = ZIe;
}

static void
p_expr_C_Calt(flags flags, lex_state lex_state, act_state act_state, err err, t_ast__expr *ZOnode)
{
	t_ast__expr ZInode;

	switch (CURRENT_TERMINAL) {
	case (TOK_ANY): case (TOK_EOL): case (TOK_START): case (TOK_END):
	case (TOK_END__NL): case (TOK_OPEN): case (TOK_OPENGROUP): case (TOK_OPENGROUPINV):
	case (TOK_OPENGROUPCB): case (TOK_OPENGROUPINVCB): case (TOK_NAMED__CLASS): case (TOK_FLAGS):
	case (TOK_ESC): case (TOK_NOESC): case (TOK_CONTROL): case (TOK_OCT):
	case (TOK_HEX): case (TOK_CHAR): case (TOK_UNSUPPORTED): case (TOK_INVALID__COMMENT):
		{
			/* BEGINNING OF ACTION: ast-make-concat */
			{
#line 867 "src/libre/parser.act"

		(ZInode) = ast_make_expr_concat(act_state->poolp, *flags);
		if ((ZInode) == NULL) {
			goto ZL1;
		}
	
#line 4241 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-make-concat */
			p_expr_C_Clist_Hof_Hpieces (flags, lex_state, act_state, err, ZInode);
			if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
				RESTORE_LEXER;
				goto ZL1;
			}
		}
		break;
	default:
		{
			/* BEGINNING OF ACTION: ast-make-empty */
			{
#line 860 "src/libre/parser.act"

		(ZInode) = ast_make_expr_empty(act_state->poolp, *flags);
		if ((ZInode) == NULL) {
			goto ZL1;
		}
	
#line 4262 "src/libre/dialect/pcre/parser.c"
			}
			/* END OF ACTION: ast-make-empty */
		}
		break;
	case (ERROR_TERMINAL):
		return;
	}
	goto ZL0;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
ZL0:;
	*ZOnode = ZInode;
}

static void
p_expr_C_Ctype(flags flags, lex_state lex_state, act_state act_state, err err, t_ast__expr *ZOnode)
{
	t_ast__expr ZInode;

	if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
		return;
	}
	{
		t_ast__expr ZIclass;
		t_pos ZIstart;
		t_pos ZIend;

		p_class_Hnamed (flags, lex_state, act_state, err, &ZIclass, &ZIstart, &ZIend);
		if ((CURRENT_TERMINAL) == (ERROR_TERMINAL)) {
			RESTORE_LEXER;
			goto ZL1;
		}
		/* BEGINNING OF ACTION: ast-make-alt */
		{
#line 874 "src/libre/parser.act"

		(ZInode) = ast_make_expr_alt(act_state->poolp, *flags);
		if ((ZInode) == NULL) {
			goto ZL1;
		}
	
#line 4305 "src/libre/dialect/pcre/parser.c"
		}
		/* END OF ACTION: ast-make-alt */
		/* BEGINNING OF ACTION: ast-add-alt */
		{
#line 1053 "src/libre/parser.act"

		if (!ast_add_expr_alt((ZInode), (ZIclass))) {
			goto ZL1;
		}
	
#line 4316 "src/libre/dialect/pcre/parser.c"
		}
		/* END OF ACTION: ast-add-alt */
	}
	goto ZL0;
ZL1:;
	SAVE_LEXER ((ERROR_TERMINAL));
	return;
ZL0:;
	*ZOnode = ZInode;
}

/* BEGINNING OF TRAILER */

#line 1059 "src/libre/parser.act"


	static int
	lgetc(struct LX_STATE *lx)
	{
		struct lex_state *lex_state;

		assert(lx != NULL);
		assert(lx->getc_opaque != NULL);

		lex_state = lx->getc_opaque;

		assert(lex_state->f != NULL);

		return lex_state->f(lex_state->opaque);
	}

	struct ast *
	DIALECT_PARSE(re_getchar_fun *f, void *opaque,
		const struct fsm_options *opt,
		enum re_flags flags, int overlap,
		struct re_err *err)
	{
		struct ast *ast;

		struct act_state  act_state_s;
		struct act_state *act_state;
		struct lex_state  lex_state_s;
		struct lex_state *lex_state;
		struct re_err dummy;

		struct LX_STATE *lx;

		assert(f != NULL);

		ast = ast_new();

		if (err == NULL) {
			err = &dummy;
		}

		lex_state    = &lex_state_s;
		lex_state->p = lex_state->a;

		lx = &lex_state->lx;

		LX_INIT(lx);

		lx->lgetc       = lgetc;
		lx->getc_opaque = lex_state;

		lex_state->f       = f;
		lex_state->opaque  = opaque;

		lex_state->buf.a   = NULL;
		lex_state->buf.len = 0;

#if PCRE_DIALECT
		lex_state->extended_mode_comment = 0;
		lex_state->flags_ptr = &flags;
#endif /* PCRE_DIALECT */

		/* XXX: unneccessary since we're lexing from a string */
		/* (except for pushing "[" and "]" around ::group-$dialect) */
		lx->buf_opaque = &lex_state->buf;
		lx->push       = CAT(LX_PREFIX, _dynpush);
		lx->clear      = CAT(LX_PREFIX, _dynclear);
		lx->free       = CAT(LX_PREFIX, _dynfree);

		/* This is a workaround for ADVANCE_LEXER assuming a pointer */
		act_state = &act_state_s;

		act_state->overlap = overlap;
		act_state->poolp   = &ast->pool;

		act_state->group_id = 0;

		err->e = RE_ESUCCESS;

		ADVANCE_LEXER;

#if BUILD_FOR_FUZZER
		/* these errors currently are not handled properly */
		if (act_state->lex_tok == TOK_ERROR) {
			fprintf(stderr, "syntax error\n");
			lx->free(lx->buf_opaque);
			goto error;
		}
#endif

		DIALECT_ENTRY(&flags, lex_state, act_state, err, &ast->expr);

		lx->free(lx->buf_opaque);

		if (err->e != RE_ESUCCESS) {
			/* TODO: free internals allocated during parsing (are there any?) */
			goto error;
		}

		if (ast->expr == NULL) {
			/* We shouldn't get here, it means there's error
			 * checking missing elsewhere. */
			if (err->e == RE_ESUCCESS) { assert(!"unreached"); }
			goto error;
		}

		return ast;

	error:

		/*
		 * Some errors describe multiple tokens; for these, the start and end
		 * positions belong to potentially different tokens, and therefore need
		 * to be stored statefully (in act_state). These are all from
		 * non-recursive productions by design, and so a stack isn't needed.
		 *
		 * Lexical errors describe a problem with a single token; for these,
		 * the start and end positions belong to that token.
		 *
		 * Syntax errors occur at the first point the order of tokens is known
		 * to be incorrect, rather than describing a span of bytes. For these,
		 * the start of the next token is most relevant.
		 */

		switch (err->e) {
		case RE_ENEGRANGE: err->start = act_state->rangestart; err->end = act_state->rangeend; break;
		case RE_ENEGCOUNT: err->start = act_state->countstart; err->end = act_state->countend; break;

		case RE_EHEXRANGE:
		case RE_EOCTRANGE:
		case RE_ECOUNTRANGE:
			/*
			 * Lexical errors: These are always generated for the current token,
			 * so lx->start/end here is correct because ADVANCE_LEXER has
			 * not been called.
			 */
			mark(&err->start, &lx->start);
			mark(&err->end,   &lx->end);
			break;

		default:
			/*
			 * Due to LL(1) lookahead, lx->start/end is the next token.
			 * This is approximately correct as the position of an error,
			 * but to be exactly correct, we store the pos for the previous token.
			 * This is more visible when whitespace exists.
			 */
			err->start = act_state->synstart;
			err->end   = act_state->synstart; /* single point */
			break;
		}

		ast_free(ast);

		return NULL;
	}

#line 4488 "src/libre/dialect/pcre/parser.c"

/* END OF FILE */
