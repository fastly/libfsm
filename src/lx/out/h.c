/* $Id$ */

#include <assert.h>
#include <stdio.h>
#include <ctype.h>

#include "../ast.h"
#include "../internal.h"


/* TODO: centralise */
static void
out_esctok(FILE *f, const char *s)
{
	const char *p;

	assert(f != NULL);
	assert(s != NULL);

	for (p = s; *p != '\0'; p++) {
		fputc(isalnum(*p) ? toupper(*p) : '_', f);
	}
}

static void
out_tokens(const struct ast *ast, FILE *f)
{
	struct ast_token *t;

	assert(ast != NULL);
	assert(f != NULL);

	fprintf(f, "enum lx_token {\n");

	/* TODO: the token prefix needs to be configurable */
	for (t = ast->tl; t != NULL; t = t->next) {
		fprintf(f, "\tTOK_");
		out_esctok(f, t->s);
		fprintf(f, ",\n");
	}

	fprintf(f, "\tTOK_EOF,\n");
	fprintf(f, "\tTOK_SKIP,\n");
	fprintf(f, "\tTOK_ERROR\n");

	fprintf(f, "};\n");
}

void
lx_out_h(const struct ast *ast, FILE *f)
{
	assert(ast != NULL);
	assert(f != NULL);

	fprintf(f, "/* Generated by lx */\n");	/* TODO: date, input etc */
	fprintf(f, "\n");

	/* TODO: this guard macro needs to be configurable */
	fprintf(f, "#ifndef LX_H\n");
	fprintf(f, "#define LX_H\n");
	fprintf(f, "\n");

	out_tokens(ast, f);
	fprintf(f, "\n");

	fprintf(f, "struct lx {\n");
	fprintf(f, "\tint (*lgetc)(struct lx *lx);\n");
	fprintf(f, "\tvoid *opaque;\n");
	fprintf(f, "\n");
	fprintf(f, "\tint c; /* lx_ungetc buffer */\n");
	fprintf(f, "\tunsigned line;\n");
	fprintf(f, "\tunsigned byte;\n");
	fprintf(f, "\n");
	/* TODO: push/pop/clear for token buffer */
	fprintf(f, "\tint (*push) (struct lx *lx, int c);\n");
	fprintf(f, "\tint (*pop)  (struct lx *lx);\n");
	fprintf(f, "\tint (*clear)(struct lx *lx);\n");
	fprintf(f, "\n");
	fprintf(f, "\tenum lx_token (*z)(struct lx *lx);\n");
	fprintf(f, "};\n");
	fprintf(f, "\n");

	fprintf(f, "/* opaque for lx_agetc */\n");
	fprintf(f, "struct lx_arr {\n");
	fprintf(f, "\tchar *p;\n");
	fprintf(f, "\tsize_t len;\n");
	fprintf(f, "};\n");
	fprintf(f, "\n");

	/* TODO: posix only */
	fprintf(f, "/* opaque for lx_fdgetc */\n");
	fprintf(f, "struct lx_fd {\n");
	fprintf(f, "\tchar *p;\n");
	fprintf(f, "\tsize_t len;\n");
	fprintf(f, "\n");
	fprintf(f, "\tint fd;\n");
	fprintf(f, "\tsize_t bufsz; /* number of bytes allocated after this struct */\n");
	fprintf(f, "};\n");
	fprintf(f, "\n");

	fprintf(f, "const char *lx_name(enum lx_token t);\n");
	fprintf(f, "\n");

	fprintf(f, "enum lx_token lx_next(struct lx *lx);\n");
	fprintf(f, "\n");

	fprintf(f, "int lx_fgetc(struct lx *lx);\n"); /* TODO: stdio only */
	fprintf(f, "int lx_sgetc(struct lx *lx);\n");
	fprintf(f, "int lx_agetc(struct lx *lx);\n");
	fprintf(f, "int lx_dgetc(struct lx *lx);\n");
	fprintf(f, "\n");

	fprintf(f, "#endif\n");
	fprintf(f, "\n");
}
