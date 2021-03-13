/* -*- mode: c; indent-tabs-mode: t; c-file-style: "awk"; indent-tabs-mode: t ; c-basic-offset: 2 ; tab-width: 2 -*- */

/* Runtime */

#include <stdio.h>
#include <stdlib.h>

typedef struct value (*lambdafn)();

struct lambda /* closure */ {
	void* ctx;
	lambdafn fun;
	// char* name;
};

union uvalue {
	char* string;
	unsigned char u8;
	struct lambda lambda;
};

enum runtime_type {
	STRING,
	U8,
	LAMBDA
};

struct value {
	enum runtime_type type;
	union uvalue actual_value;
};

struct genericContext {
	void* parent;
};
struct global_context {
	void* parent;
};

struct value callLambda(struct lambda lam, struct value arg) {
	// after CPS transform, when applications always continue and never return, this shall be GOTO
	return lam.fun(lam.ctx, arg);
};

struct value makeLambda(lambdafn fn, struct genericContext* ctx) {
	struct lambda* lam = (struct lambda*)malloc(sizeof(struct lambda));
	lam->fun = fn;
	lam->ctx = ctx;

	union uvalue* uv = (union uvalue*)malloc(sizeof(union uvalue));
	struct value* v = (struct value*)malloc(sizeof(struct value));
	uv->lambda = *lam;
	v->type = LAMBDA;
	v->actual_value = *uv;
	return *v;
}

struct genericContext* makeContext(size_t size, void* parent) {
	struct genericContext* ctx = (struct genericContext*)malloc(size);
	ctx->parent = parent;
	return ctx;
}

struct value makeString(char* s) {
	union uvalue* uv = (union uvalue*)malloc(sizeof(union uvalue));
	struct value* v = (struct value*)malloc(sizeof(struct value));
	uv->string = s;
	v->type = STRING;
	v->actual_value = *uv;
	return *v;
}

struct value makeU8(unsigned char i) { /* used to be int */
	union uvalue* uv = (union uvalue*)malloc(sizeof(union uvalue));
	struct value* v = (struct value*)malloc(sizeof(struct value));
	uv->u8 = i;
	v->type = U8;
	v->actual_value = *uv;
	return *v;
}

void print(struct value v) {
	if (v.type == LAMBDA) {
		printf("<procedure %ld %ld>", (long)v.actual_value.lambda.fun, (long)v.actual_value.lambda.ctx);
	} else if (v.type == STRING) {
		printf("%s", v.actual_value.string);
	} else if (v.type == U8) {
		printf("%hhu", v.actual_value.u8);
	} else {
		printf("Runtime type error in `print`!");
		exit(1);
	}
}
