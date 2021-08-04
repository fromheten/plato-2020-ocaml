/* -*- mode: c; indent-tabs-mode: t; c-file-style: "awk"; indent-tabs-mode: t ; c-basic-offset: 2 ; tab-width: 2 -*- */

/* Runtime */

#include <stdio.h>
#include <stdlib.h>
#include <gc.h>
#include <rrb.h>

typedef struct value (*lambdafn)();

struct lambda /* closure */ {
	void* ctx;
	lambdafn fun;
	// char* name;
};

union uvalue {
	char* string;
	unsigned char u8;
	const RRB* vector;
	struct lambda lambda;
};

enum runtime_type {
	STRING,
	U8,
	VECTOR,
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

struct value makeVector(const RRB* rrb) {
	union uvalue* uv = (union uvalue*)malloc(sizeof(union uvalue));
	struct value* v = (struct value*)malloc(sizeof(struct value));
	uv->vector = rrb;
	v->type = VECTOR;
	v->actual_value = *uv;
	return *v;
}

void * mallocValue(struct value v) {
	struct value * ptr = malloc(sizeof(struct value));
	ptr->type = v.type;
	ptr->actual_value = v.actual_value;
	return (void*) ptr;
}

struct value toString(struct value expr) {
  if (expr.type == LAMBDA) {
    ssize_t buffer_size =
      snprintf(NULL,
               0,
               "<procedure %ld %ld>",
               (long)expr.actual_value.lambda.fun,
               (long)expr.actual_value.lambda.ctx);
    char *return_string = (char*)malloc(buffer_size + 1);
    sprintf(return_string,
            "<procedure %ld %ld>",
            (long)expr.actual_value.lambda.fun,
            (long)expr.actual_value.lambda.ctx);
    return makeString(return_string);
  } else if (expr.type == U8) {
    // Allocates storage
    ssize_t buffer_size = snprintf(NULL, 0, "%u", expr.actual_value.u8);
    char *return_string = (char*)malloc(buffer_size + 1);
    // Prints "Hello world!" on hello_world
    snprintf(return_string, buffer_size + 1, "%u", expr.actual_value.u8);
    return makeString(return_string);
  } else if (expr.type == STRING) {
		return expr;
  } else if (expr.type == VECTOR) {
		return makeString("VECTOR YOOOO");
	} else {
    puts("Bad! toString got something it does not recognize. Error in the compiler :o!");
    exit(1337);
  };
}

void print(struct value v) {
  printf("%s", v.actual_value.string);
}
