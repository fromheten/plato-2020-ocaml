/* -*- mode: c; indent-tabs-mode: nil; c-file-style: "llvm"; c-basic-offset: 2 ;
 * tab-width: 2 -*- */

/* Runtime */
#include <gc.h>
#include <hamt.h>
#include <rrb.h>
#include <sds.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct value (*lambdafn)();

/* closure */
struct lambda {
  void *ctx;
  lambdafn fun;
  // char* name;
};

/* Predefine `value_hamt`. `uvalue` depends on `value_hamt`, but `value_hamt`
depends on `value`, which depends on `uvalue`. */
typedef struct value_hamt value_hamt;

struct tagged_value {
  char *tag;
  struct value *val;
};

union uvalue {
  char *string;
  unsigned char u8;
  bool b;
  const RRB *vector;
  struct lambda lambda;
  value_hamt *dict;
  char *enum_declaration; /* The type declaration, but as a string -
                             something to uniquely identify it.
                             Should maybe be structured better than a
                             string, but maybe it does not matter at
                             runtime - types are unused at runtime
                             anyways. */
  struct tagged_value tagged_value;
  int unit; /* should always be '\0' but not important - never read */
};

enum runtime_type {
  STRING,
  U8,
  BOOL,
  LAMBDA,
  VECTOR,
  DICT,
  ENUM,
  TAGGED_VALUE,
  UNIT
};

typedef struct value {
  enum runtime_type type;
  union uvalue actual_value;
} value;

struct value toString(value expr);

static inline unsigned int get_hash_from_value(value *expr) {
  switch (expr->type) {
  case STRING:
    return get_hash(expr->actual_value.string);
  case U8:
    return get_hash(toString(*expr).actual_value.string);
  case BOOL:
    return get_hash(toString(*expr).actual_value.string);
  case LAMBDA:
    return get_hash(toString(*expr).actual_value.string);
  case VECTOR:
    return get_hash(toString(*expr).actual_value.string);
  case DICT:
    return get_hash(toString(*expr).actual_value.string);
  case ENUM:
    return get_hash(toString(*expr).actual_value.string);
  case TAGGED_VALUE:
    return get_hash(toString(*expr).actual_value.string);
  case UNIT:
    return 0;
  }
}
static inline int value_equals(void *v0, void *v1) {
  /* "Equality is the ideal of the ugly loser" */
  value *vptr0 = (value *)v0;
  value *vptr1 = (value *)v1;
  value val0 = *vptr0;
  value val1 = *vptr1;
  if (val0.type == STRING && val1.type == STRING) {
    return strcmp(val0.actual_value.string, val1.actual_value.string) == 0;
  } else if (val0.type == U8 && val1.type == U8) {
    return val0.actual_value.u8 == val1.actual_value.u8;
  } else if (val0.type == LAMBDA && val1.type == LAMBDA) {
    return (strcmp(toString(val0).actual_value.string,
                   toString(val1).actual_value.string) == 0);
  } else if (val0.type == VECTOR && val1.type == VECTOR) {
    return (strcmp(toString(val0).actual_value.string,
                   toString(val1).actual_value.string) == 0);
  } else if (val0.type == DICT && val1.type == DICT) {
    return (strcmp(toString(val0).actual_value.string,
                   toString(val1).actual_value.string) == 0);
  } else {
    printf("Equals is given data that is not an expression, or runtime type "
           "error, exiting\n");
    exit(1);
  }
}
HAMT_DEFINE(value, get_hash_from_value, value_equals)

struct genericContext {
  void *parent;
};
struct global_context {
  void *parent;
};

struct value callLambda(struct lambda lam, struct value arg) {
  // after CPS transform, when applications always continue and never return,
  // this shall be GOTO
  return lam.fun(lam.ctx, arg);
};

struct value makeLambda(lambdafn fn, struct genericContext *ctx) {
  struct lambda *lam = (struct lambda *)malloc(sizeof(struct lambda));
  lam->fun = fn;
  lam->ctx = ctx;

  union uvalue *uv = (union uvalue *)malloc(sizeof(union uvalue));
  struct value *v = (struct value *)malloc(sizeof(struct value));
  uv->lambda = *lam;
  v->type = LAMBDA;
  v->actual_value = *uv;
  return *v;
}

struct genericContext *makeContext(size_t size, void *parent) {
  struct genericContext *ctx = (struct genericContext *)malloc(size);
  ctx->parent = parent;
  return ctx;
}

struct value makeUnit() {
  struct value *v = (struct value *)malloc(sizeof(struct value));
  union uvalue *uv = (union uvalue *)malloc(sizeof(union uvalue));
  uv->unit = '\0';
  v->type = UNIT;
  v->actual_value = *uv;
  return *v;
}

struct value makeString(char *s) {
  union uvalue *uv = (union uvalue *)malloc(sizeof(union uvalue));
  struct value *v = (struct value *)malloc(sizeof(struct value));
  uv->string = s;
  v->type = STRING;
  v->actual_value = *uv;
  return *v;
}

struct value makeU8(unsigned char i) { /* used to be int */
  union uvalue *uv = (union uvalue *)malloc(sizeof(union uvalue));
  struct value *v = (struct value *)malloc(sizeof(struct value));
  uv->u8 = i;
  v->type = U8;
  v->actual_value = *uv;
  return *v;
}

struct value makeVector(const RRB *rrb) {
  union uvalue *uv = (union uvalue *)malloc(sizeof(union uvalue));
  struct value *v = (struct value *)malloc(sizeof(struct value));
  uv->vector = rrb;
  v->type = VECTOR;
  v->actual_value = *uv;
  return *v;
}

value makeDict(value_hamt *hamt) {
  union uvalue *uv = (union uvalue *)malloc(sizeof(union uvalue));
  struct value *v = (struct value *)malloc(sizeof(struct value));

  uv->dict = hamt;
  v->type = DICT;
  v->actual_value = *uv;
  return *v;
}

value makeEnum(char *enum_declaration) {
  union uvalue *uv = (union uvalue *)malloc(sizeof(union uvalue));
  struct value *v = (struct value *)malloc(sizeof(struct value));

  uv->enum_declaration = enum_declaration;
  v->type = ENUM;
  v->actual_value = *uv;
  return *v;
}

value makeTaggedValue(char *tag, value *val) {
  union uvalue *uv = (union uvalue *)malloc(sizeof(union uvalue));
  struct value *v = (struct value *)malloc(sizeof(struct value));

  struct tagged_value tagged_value;
  /* tagged_value = malloc(sizeof(struct tagged_value)); */
  tagged_value.tag = tag;
  tagged_value.val = val;
  uv->tagged_value = tagged_value;
  v->type = TAGGED_VALUE;
  v->actual_value = *uv;
  return *v;
}

/* If/Else */
static inline value makeBool(bool b) {
  union uvalue *uv = (union uvalue *)malloc(sizeof(union uvalue));
  struct value *v = (struct value *)malloc(sizeof(struct value));
  uv->b = b;
  v->type = BOOL;
  v->actual_value = *uv;
  return *v;
}

static inline value callIf(value cond, value then_, value else_) {
  if (cond.type == BOOL && cond.actual_value.b == true) {
    return then_;
  } else {
    return else_;
  }
}

/* /\** */
/*  * Reduce for dictionaries */
/*  *\/ */
/* value data_reduce_inner(value *key, void *value_ptr) { */
/*   value *value = (value *)value_ptr; */
/*   return reducer() */
/* } */
value dict_reduce(value_hamt *hamt, value (*reducer)(value *, value *),
                  value acc) {
  /* value_hamt_visit_all(hamt, void (*visitor)(value *, void *)); */
  /* TODO implement reduce, after which every other operation can be implemented
   */
  return acc;
}

/* takes a hamt and two values, returns hamt */
static inline value_hamt *dict_set(value_hamt *hamt, value *key, value *val) {
  return value_hamt_set(hamt, key, val);
}

/* Takes nothing, returns a hamt */
static inline value_hamt *dict_new() { return value_hamt_new(); }

void *mallocValue(struct value v) {
  struct value *ptr = malloc(sizeof(struct value));
  ptr->type = v.type;
  ptr->actual_value = v.actual_value;
  return (void *)ptr;
}

static inline value equals(value e0, value e1) {
  return makeBool(
      value_equals((void *)mallocValue(e0), (void *)mallocValue(e1)));
}

value toString(value expr) {
  switch (expr.type) {
  case LAMBDA: {
    ssize_t buffer_size = snprintf(NULL, 0, "<procedure %ld %ld>",
                                   (long)expr.actual_value.lambda.fun,
                                   (long)expr.actual_value.lambda.ctx);
    char *return_string = (char *)malloc(buffer_size + 1);
    sprintf(return_string, "<procedure %ld %ld>",
            (long)expr.actual_value.lambda.fun,
            (long)expr.actual_value.lambda.ctx);
    return makeString(return_string);
  }
  case UNIT: {
    return makeString("<>");
  }
  case TAGGED_VALUE: {
    value tagged_val;
    tagged_val.actual_value = expr.actual_value.tagged_value.val->actual_value;
    tagged_val.type = expr.actual_value.tagged_value.val->type;
    return makeString(sdscat(
        sdscat(sdscat(sdscat(sdsnew("("), expr.actual_value.tagged_value.tag),
                      " "),
               toString(tagged_val).actual_value.string),
        ")"));
  }
  case U8: {
    // Allocates storage
    ssize_t buffer_size = snprintf(NULL, 0, "%u", expr.actual_value.u8);
    char *return_string = (char *)malloc(buffer_size + 1);
    // Prints "Hello world!" on hello_world
    snprintf(return_string, buffer_size + 1, "%u", expr.actual_value.u8);
    return makeString(return_string);
  }
  case STRING: {
    return makeString(
        sdscat(sdscat(sdsnew("\""), expr.actual_value.string), "\""));
  }
  case VECTOR: {
    sds acc = "";

    uint32_t length = rrb_count(expr.actual_value.vector);
    int i;
    for (i = 0; i < length; i++) {
      value *current_value = rrb_nth(expr.actual_value.vector, i);
      char *spacer = " ";
      sds current = sdsnew(toString(*current_value).actual_value.string);
      acc = sdscat(sdscat(current, " "), acc);
    }
    sdsrange(acc, 0, -2);
    acc = sdscat(sdsnew("["), acc);
    acc = sdscat(acc, "]");
    return makeString(acc);
  }
  case DICT: {
    sds acc = "{";
    return makeString(acc);
  }
  case BOOL: {
    return makeString(expr.actual_value.b ? "True" : "False");
  }
  case ENUM: {
    printf("Bad! toString got something it does not recognize, %d. \n",
           expr.type);
    puts("Error in the compiler lol n00b :o!\n");
    exit(1337);
  }
  }
}

void print(struct value v) { printf("%s", v.actual_value.string); }
