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

	for (t = ast->tl; t != NULL; t = t->next) {
		fprintf(f, "\tLX_");
		out_esctok(f, t->s);
		fprintf(f, ",\n");
	}

	fprintf(f, "\tLX_EOF,\n");
	fprintf(f, "\tLX_ERROR\n");

	fprintf(f, "}\n");
}

void
out_h(const struct ast *ast, FILE *f)
{
	assert(ast != NULL);
	assert(f != NULL);

	fprintf(f, "/* Generated by lx */\n");	/* TODO: date, input etc */
	fprintf(f, "\n");

	/* TODO: this guard macros needs to be configurable */
	fprintf(f, "#ifndef LX_H\n");
	fprintf(f, "#define LX_H\n");
	fprintf(f, "\n");

	out_tokens(ast, f);
	fprintf(f, "\n");

	fprintf(f, "enum lx_token lx_nexttoken(struct lx *lx);\n");
	fprintf(f, "\n");

	fprintf(f, "#endif\n");
	fprintf(f, "\n");
}
