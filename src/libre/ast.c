/*
 * Copyright 2018 Scott Vokes
 *
 * See LICENCE for the full copyright terms.
 */

#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include <limits.h>

#include <re/re.h>

#include "class.h"
#include "ast.h"

/*
 * This is a placeholder for a node that has already been freed.
 * Note: this is a single-instance node, which other functions
 * should not modify.
 */
static struct ast_expr the_tombstone;
struct ast_expr *ast_expr_tombstone = &the_tombstone;

/* FIXME: this isn't safe for multiple threads! */
static struct ast_expr_pool *global_pool = NULL;

struct ast_expr *
ast_expr_pool_new(struct ast_expr_pool **poolp) 
{
	struct ast_expr_pool *p;

	assert(poolp != NULL);

	p = *poolp;
	if (p == NULL || p->count >= AST_EXPR_POOL_SIZE) {
		p = calloc(1, sizeof *p);
		if (p == NULL) {
			return NULL;
		}

		p->next = *poolp;
		*poolp = p;
	}

	assert(p != NULL && p->count < AST_EXPR_POOL_SIZE);

	return &p->pool[p->count++];
}

struct ast_expr *
ast_expr_new(void)
{
	return ast_expr_pool_new(&global_pool);
}

struct ast_expr_pool *
ast_expr_pool_save(void)
{
	struct ast_expr_pool *p = global_pool;
	global_pool = NULL;
	return p;
}

struct ast *
ast_new(void)
{
	struct ast *res;

	assert(global_pool == NULL);

	res = calloc(1, sizeof *res);
	if (res == NULL) {
		return NULL;
	}

	/* XXX: not thread-safe */
	the_tombstone.type = AST_EXPR_TOMBSTONE;

	return res;
}

void
ast_pool_free(struct ast_expr_pool *pool)
{
	struct ast_expr_pool *curr;
	for (curr=pool; curr != NULL; curr=curr->next) {
		unsigned i;

		for (i=0; i < curr->count; i++) {
			ast_expr_free(&curr->pool[i]);
		}
	}

	while (pool != NULL) {
		curr = pool;
		pool = pool->next;

		free(curr);
	}
}

void
ast_free(struct ast *ast)
{
	ast_expr_free(ast->expr);
	ast_pool_free(ast->pool);
	free(ast);
}

struct ast_count
ast_make_count(unsigned min, const struct ast_pos *start,
    unsigned max, const struct ast_pos *end)
{
	struct ast_count res;

	memset(&res, 0x00, sizeof res);

	res.min = min;
	res.max = max;

	if (start != NULL) {
		res.start = *start;
	}
	if (end != NULL) {
		res.end = *end;
	}

	return res;
}

/*
 * Expressions
 */

void
ast_expr_free(struct ast_expr *n)
{
	static const struct ast_expr zero;

	if (n == NULL) {
		return;
	}
	
	switch (n->type) {
	case AST_EXPR_EMPTY:
	case AST_EXPR_LITERAL:
	case AST_EXPR_CODEPOINT:
	case AST_EXPR_ANCHOR:
	case AST_EXPR_RANGE:
		/* these nodes have no subnodes or dynamic allocation */
		break;

	case AST_EXPR_SUBTRACT:
		ast_expr_free(n->u.subtract.a);
		ast_expr_free(n->u.subtract.b);
		break;

	case AST_EXPR_CONCAT: {
		size_t i;

		for (i = 0; i < n->u.concat.count; i++) {
			ast_expr_free(n->u.concat.n[i]);
		}

		free(n->u.concat.n);
		break;
	}

	case AST_EXPR_ALT: {
		size_t i;

		for (i = 0; i < n->u.alt.count; i++) {
			ast_expr_free(n->u.alt.n[i]);
		}

		free(n->u.alt.n);
		break;
	}

	case AST_EXPR_REPEAT:
		ast_expr_free(n->u.repeat.e);
		break;

	case AST_EXPR_GROUP:
		ast_expr_free(n->u.group.e);
		break;

	case AST_EXPR_TOMBSTONE:
		/* do not free */
		return;

	default:
		assert(!"unreached");
	}

	*n = zero;
}

int
ast_expr_clone(struct ast_expr **n)
{
	struct ast_expr *old;
	struct ast_expr *new;

	assert(n != NULL);

	old = *n;

	if (old == NULL || old->type == AST_EXPR_TOMBSTONE) {
		return 1;
	}

	new = malloc(sizeof *new);
	if (new == NULL) {
		*n = NULL;
		return 0;
	}

	*new = *old;

	switch (new->type) {
	case AST_EXPR_EMPTY:
	case AST_EXPR_LITERAL:
	case AST_EXPR_CODEPOINT:
	case AST_EXPR_ANCHOR:
	case AST_EXPR_RANGE:
		break;

	case AST_EXPR_SUBTRACT:
		if (!ast_expr_clone(&new->u.subtract.a)) {
			free(new);
			new = NULL;
			break;
		}
		if (!ast_expr_clone(&new->u.subtract.b)) {
			ast_expr_free(new);
			new = NULL;
			break;
		}
		break;

	case AST_EXPR_CONCAT: {
		size_t i;

		new->u.concat.n = malloc(new->u.concat.alloc * sizeof *new->u.concat.n);
		if (new->u.concat.n == NULL) {
			free(new);
			new = NULL;
			break;
		}

		for (i = 0; i < old->u.concat.count; i++) {
			new->u.concat.n[i] = NULL;
		}

		for (i = 0; i < old->u.concat.count; i++) {
			new->u.concat.n[i] = old->u.concat.n[i];
			if (!ast_expr_clone(&new->u.concat.n[i])) {
				ast_expr_free(new);
				new = NULL;
				break;
			}
		}
		break;
	}

	case AST_EXPR_ALT: {
		size_t i;

		new->u.alt.n = malloc(new->u.alt.alloc * sizeof *new->u.alt.n);
		if (new->u.alt.n == NULL) {
			free(new);
			new = NULL;
			break;
		}

		for (i = 0; i < old->u.alt.count; i++) {
			new->u.alt.n[i] = NULL;
		}

		for (i = 0; i < old->u.alt.count; i++) {
			new->u.alt.n[i] = old->u.alt.n[i];
			if (!ast_expr_clone(&new->u.alt.n[i])) {
				ast_expr_free(new);
				new = NULL;
				break;
			}
		}
		break;
	}

	case AST_EXPR_REPEAT:
		if (!ast_expr_clone(&new->u.repeat.e)) {
			free(new);
			new = NULL;
			break;
		}
		break;

	case AST_EXPR_GROUP:
		if (!ast_expr_clone(&new->u.group.e)) {
			free(new);
			new = NULL;
			break;
		}
		break;

	default:
		assert(!"unreached");
	}

	*n = new;
	return new != NULL;
}

static int
ast_class_cmp(const struct class *a, const struct class *b)
{
	size_t i;

	assert(a != NULL);
	assert(b != NULL);

	if (a->count < b->count) { return -1; }
	if (a->count > b->count) { return +1; }

	for (i = 0; i < a->count; i++) {
		const struct range *ra, *rb;

		ra = &a->ranges[i];
		rb = &b->ranges[i];

		if (ra->a < rb->a) { return -1; }
		if (ra->a > rb->a) { return +1; }

		if (ra->b < rb->b) { return -1; }
		if (ra->b > rb->b) { return +1; }
	}

	return 0;
}

static int
ast_endpoint_cmp(const struct ast_endpoint *a, const struct ast_endpoint *b)
{
	assert(a != NULL);
	assert(b != NULL);

	if (a->type < b->type) { return -1; }
	if (a->type > b->type) { return +1; }

	switch (a->type) {
	case AST_ENDPOINT_LITERAL:
		if (a->u.literal.c < b->u.literal.c) { return -1; }
		if (a->u.literal.c > b->u.literal.c) { return +1; }

		return 0;

	case AST_ENDPOINT_NAMED: {
		int r;

		r = ast_class_cmp(a->u.named.class, b->u.named.class);
		if (r != 0) {
			return r;
		}

		return 0;
	}

	default:
		assert(!"unreached");
	}
}

int
ast_expr_cmp(const struct ast_expr *a, const struct ast_expr *b)
{
	assert(a != NULL);
	assert(b != NULL);

	if (a->type < b->type) { return -1; }
	if (a->type > b->type) { return +1; }

	if (a->flags < b->flags) { return -1; }
	if (a->flags > b->flags) { return +1; }

	if (a->re_flags < b->re_flags) { return -1; }
	if (a->re_flags > b->re_flags) { return +1; }

	switch (a->type) {
	case AST_EXPR_EMPTY:
		return 0;

	case AST_EXPR_CONCAT: {
		size_t i;

		if (a->u.concat.count < b->u.concat.count) { return -1; }
		if (a->u.concat.count > b->u.concat.count) { return +1; }

		for (i = 0; i < a->u.concat.count; i++) {
			int r;

			r = ast_expr_cmp(a->u.concat.n[i], b->u.concat.n[i]);
			if (r != 0) {
				return r;
			}
		}

		return 0;
	}

	case AST_EXPR_ALT: {
		size_t i;

		if (a->u.alt.count < b->u.alt.count) { return -1; }
		if (a->u.alt.count > b->u.alt.count) { return +1; }

		for (i = 0; i < a->u.alt.count; i++) {
			int r;

			r = ast_expr_cmp(a->u.alt.n[i], b->u.alt.n[i]);
			if (r != 0) {
				return r;
			}
		}

		return 0;
	}

	case AST_EXPR_LITERAL:
		if ((unsigned char) a->u.literal.c < (unsigned char) b->u.literal.c) { return -1; }
		if ((unsigned char) a->u.literal.c > (unsigned char) b->u.literal.c) { return +1; }

		return 0;

	case AST_EXPR_CODEPOINT:
		if (a->u.codepoint.u < b->u.codepoint.u) { return -1; }
		if (a->u.codepoint.u > b->u.codepoint.u) { return +1; }

		return 0;

	case AST_EXPR_REPEAT:
		if (a->u.repeat.min < b->u.repeat.min) { return -1; }
		if (a->u.repeat.min > b->u.repeat.min) { return +1; }

		if (a->u.repeat.max < b->u.repeat.max) { return -1; }
		if (a->u.repeat.max > b->u.repeat.max) { return +1; }

		return ast_expr_cmp(a->u.repeat.e, b->u.repeat.e);

	case AST_EXPR_GROUP:
		if (a->u.group.id < b->u.group.id) { return -1; }
		if (a->u.group.id > b->u.group.id) { return +1; }

		return ast_expr_cmp(a->u.group.e, b->u.group.e);

	case AST_EXPR_ANCHOR:
		if (a->u.anchor.type < b->u.anchor.type) { return -1; }
		if (a->u.anchor.type < b->u.anchor.type) { return +1; }

		return 0;

	case AST_EXPR_SUBTRACT: {
		int r;

		r = ast_expr_cmp(a->u.subtract.a, b->u.subtract.a);
		if (r != 0) {
			return r;
		}

		r = ast_expr_cmp(a->u.subtract.b, b->u.subtract.b);
		if (r != 0) {
			return r;
		}

		return 0;
	}

	case AST_EXPR_RANGE: {
		int r;

		r = ast_endpoint_cmp(&a->u.range.from, &b->u.range.from);
		if (r != 0) {
			return r;
		}

		r = ast_endpoint_cmp(&a->u.range.to, &b->u.range.to);
		if (r != 0) {
			return r;
		}

		/* we intentionally ignore .start and .end pos values for finding equality;
		 * these are considered just annotation metatdata for error reporting */

		return 0;
	}

	case AST_EXPR_TOMBSTONE:
		return 0;

	default:
		assert(!"unreached");
		abort();
	}
}

int
ast_expr_equal(const struct ast_expr *a, const struct ast_expr *b)
{
	return ast_expr_cmp(a, b) == 0;
}

int
ast_contains_expr(const struct ast_expr *node, struct ast_expr * const *a, size_t n)
{
	size_t i;

	assert(a != NULL);

	for (i = 0; i < n; i++) {
		if (ast_expr_equal(node, a[i])) {
			return 1;
		}
	}

	return 0;
}

struct ast_expr *
ast_make_expr_empty(enum re_flags re_flags)
{
	struct ast_expr *res;

	res = ast_expr_new();
	if (res == NULL) {
		return NULL;
	}

	res->type = AST_EXPR_EMPTY;
	res->re_flags = re_flags;

	return res;
}

struct ast_expr *
ast_make_expr_concat(enum re_flags re_flags)
{
	struct ast_expr *res;

	res = ast_expr_new();
	if (res == NULL) {
		return NULL;
	}

	res->type = AST_EXPR_CONCAT;
	res->re_flags = re_flags;
	res->u.concat.alloc = 8; /* arbitrary initial value */
	res->u.concat.count = 0;

	res->u.concat.n = malloc(res->u.concat.alloc * sizeof *res->u.concat.n);
	if (res->u.concat.n == NULL) {
		return NULL;
	}

	return res;
}

int
ast_add_expr_concat(struct ast_expr *cat, struct ast_expr *node)
{
	assert(cat != NULL);
	assert(cat->type == AST_EXPR_CONCAT);

	if (cat->u.concat.count == cat->u.concat.alloc) {
		void *tmp;

		tmp = realloc(cat->u.concat.n, cat->u.concat.alloc * 2 * sizeof *cat->u.concat.n);
		if (tmp == NULL) {
			return 0;
		}

		cat->u.concat.alloc *= 2;
		cat->u.concat.n = tmp;
	}

	cat->u.concat.n[cat->u.concat.count] = node;
	cat->u.concat.count++;

	return 1;
}

struct ast_expr *
ast_make_expr_alt(enum re_flags re_flags)
{
	struct ast_expr *res;

	res = ast_expr_new();
	if (res == NULL) {
		return NULL;
	}

	res->type = AST_EXPR_ALT;
	res->re_flags = re_flags;
	res->u.alt.alloc = 8; /* arbitrary initial value */
	res->u.alt.count = 0;

	res->u.alt.n = malloc(res->u.alt.alloc * sizeof *res->u.alt.n);
	if (res->u.alt.n == NULL) {
		return NULL;
	}

	return res;
}

int
ast_add_expr_alt(struct ast_expr *cat, struct ast_expr *node)
{
	assert(cat != NULL);
	assert(cat->type == AST_EXPR_ALT);

	if (cat->u.alt.count == cat->u.alt.alloc) {
		void *tmp;

		tmp = realloc(cat->u.alt.n, cat->u.alt.alloc * 2 * sizeof *cat->u.alt.n);
		if (tmp == NULL) {
			return 0;
		}

		cat->u.alt.alloc *= 2;
		cat->u.alt.n = tmp;
	}

	cat->u.alt.n[cat->u.alt.count] = node;
	cat->u.alt.count++;

	return 1;
}

struct ast_expr *
ast_make_expr_literal(enum re_flags re_flags, char c)
{
	struct ast_expr *res;

	res = ast_expr_new();
	if (res == NULL) {
		return NULL;
	}

	res->type = AST_EXPR_LITERAL;
	res->re_flags = re_flags;
	res->u.literal.c = c;

	return res;
}

struct ast_expr *
ast_make_expr_codepoint(enum re_flags re_flags, uint32_t u)
{
	struct ast_expr *res;

	res = ast_expr_new();
	if (res == NULL) {
		return NULL;
	}

	res->type = AST_EXPR_CODEPOINT;
	res->re_flags = re_flags;
	res->u.codepoint.u = u;

	return res;
}

struct ast_expr *
ast_make_expr_repeat(enum re_flags re_flags, struct ast_expr *e, struct ast_count count)
{
	struct ast_expr *res = NULL;

	assert(count.min <= count.max);

	/* Applying a count to a start/end anchor is a syntax error. */
	if (e->type == AST_EXPR_ANCHOR) {
		return NULL;
	}

	res = ast_expr_new();
	if (res == NULL) {
		return NULL;
	}

	res->type = AST_EXPR_REPEAT;
	res->re_flags = re_flags;
	res->u.repeat.e = e;
	res->u.repeat.min = count.min;
	res->u.repeat.max = count.max;

	return res;
}

struct ast_expr *
ast_make_expr_group(enum re_flags re_flags, struct ast_expr *e)
{
	struct ast_expr *res;

	res = ast_expr_new();
	if (res == NULL) {
		return NULL;
	}

	res->type = AST_EXPR_GROUP;
	res->re_flags = re_flags;
	res->u.group.e = e;
	res->u.group.id = NO_GROUP_ID; /* not yet assigned */

	return res;
}

struct ast_expr *
ast_make_expr_anchor(enum re_flags re_flags, enum ast_anchor_type type)
{
	struct ast_expr *res;

	res = ast_expr_new();
	if (res == NULL) {
		return NULL;
	}

	res->type = AST_EXPR_ANCHOR;
	res->re_flags = re_flags;
	res->u.anchor.type = type;

	return res;
}

struct ast_expr *
ast_make_expr_subtract(enum re_flags re_flags, struct ast_expr *a, struct ast_expr *b)
{
	struct ast_expr *res;

	res = ast_expr_new();
	if (res == NULL) {
		return NULL;
	}

	res->type = AST_EXPR_SUBTRACT;
	res->re_flags = re_flags;
	res->u.subtract.a = a;
	res->u.subtract.b = b;

	return res;
}

struct ast_expr *
ast_make_expr_range(enum re_flags re_flags,
    const struct ast_endpoint *from, struct ast_pos start,
    const struct ast_endpoint *to, struct ast_pos end)
{
	struct ast_expr *res;

	res = ast_expr_new();
	if (res == NULL) {
		return NULL;
	}

	assert(from != NULL);
	assert(to != NULL);

	res->type = AST_EXPR_RANGE;
	res->re_flags = re_flags;
	res->u.range.from = *from;
	res->u.range.start = start;
	res->u.range.to = *to;
	res->u.range.end = end;

	return res;
}

struct ast_expr *
ast_make_expr_named(enum re_flags re_flags, const struct class *class)
{
	struct ast_expr *res;
	size_t i;

	assert(class != NULL);

	res = ast_expr_new();
	if (res == NULL) {
		return NULL;
	}

	res->type = AST_EXPR_ALT;
	res->re_flags = re_flags;
	res->u.alt.alloc = class->count;
	res->u.alt.count = class->count;

	res->u.alt.n = malloc(res->u.alt.alloc * sizeof *res->u.alt.n);
	if (res->u.alt.n == NULL) {
		return NULL;
	}

	for (i = 0; i < class->count; i++) {
		if (class->ranges[i].a == class->ranges[i].b) {
			if (class->ranges[i].a <= UCHAR_MAX) {
				res->u.alt.n[i] = ast_make_expr_literal(re_flags, (unsigned char) class->ranges[i].a);
			} else {
				res->u.alt.n[i] = ast_make_expr_codepoint(re_flags, class->ranges[i].a);
			}
			if (res->u.alt.n[i] == NULL) {
				goto error;
			}
		} else {
			struct ast_endpoint from, to;
			struct ast_pos pos = { 0, 0, 0 }; /* XXX: pass in pos */

			from.type = AST_ENDPOINT_LITERAL;
			if (class->ranges[i].a <= UCHAR_MAX) {
				from.u.literal.c = (unsigned char) class->ranges[i].a;
			} else {
				from.u.codepoint.u = class->ranges[i].a;
			}

			to.type = AST_ENDPOINT_LITERAL;
			if (class->ranges[i].b <= UCHAR_MAX) {
				to.u.literal.c = (unsigned char) class->ranges[i].b;
			} else {
				to.u.codepoint.u = class->ranges[i].b;
			}

			res->u.alt.n[i] = ast_make_expr_range(re_flags, &from, pos, &to, pos);
			if (res->u.alt.n[i] == NULL) {
				goto error;
			}
		}
	}

	return res;

error:

	for (i = 0; i < class->count; i++) {
		if (res->u.alt.n[i] == NULL) {
			break;
		}

		ast_expr_free(res->u.alt.n[i]);
	}

	res->u.alt.count = 0;

	ast_expr_free(res);

	return NULL;
}

