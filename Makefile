.PHONY: clean toplevel test

toplevel: util.cma codegen.cma parse.cma unify.cma platoc.cma
	ocaml -nopromptcont $^

clean:
	rm -r *.cma *.cmx *.a *.cmt *.annot ./out/* *.o *.cmo *.cmi _build

test: out/platoc
	out/platoc --test-results

state.cma: state.ml
	ocamlc -o $@ -a $^

unify.cmx: parse.cmx unify.ml
	ocamlopt -c $^

unify.a: unify.ml
	ocamlc -o unify.a -a $^

unify.cma: unify.ml
	ocamlc -o $@ -a $^

util.a: util.ml
	ocamlc -o $@ -a $^

util.cma: util.ml
	ocamlc -o $@ -a $^

util.cmx: util.ml
	ocamlopt -bin-annot -c $^

util.cmt: util.cmx

codegen.cmx: codegen.ml # util.cmx
	ocamlopt -bin-annot -c $^

codegen.cma: codegen.ml util.cma
	ocamlc -o $@ -a $^

parse.cmx: util.cmx parse.ml
	ocamlopt -bin-annot -c $^

parse.cma: util.cma parse.ml
	ocamlc -o $@ -a $^

platoc.cmx: platoc.ml codegen.cmx parse.cmx util.cmx
	ocamlopt -bin-annot -c $^

platoc.cma: platoc.ml util.cma codegen.cma parse.cma
	ocamlc -o $@ -a $^

test.cmx: test.ml util.cmx unify.cmx platoc.cmx codegen.cmx parse.cmx
	ocamlopt -bin-annot -c $^

out/platoc: *.ml
	@@echo Begin $@
	ocamlbuild -no-hygiene platoc.native && mv platoc.native out/platoc
	@@echo End $@

out/codegenned: out/platoc
	echo "(Log (((λ first (λ second first)) \"Hello, Combinators!\") \"disregarded\") )" > out/codegenned.plato
	out/platoc -oc out/codegenned.c out/codegenned.plato
	cc -o out/codegenned out/codegenned.c && ./out/codegenned

out/example-program.c: out/platoc
	./out/platoc -oc ./out/example-program.c example-program.plato

out/example-program: out/example-program.c
	cc -o out/example-program out/example-program.c

out/example/option.c: example/option.plato
	./out/platoc -oc ./out/example/option.plato.c ./example/option.plato

out/example/option: out/example/option.c
	cc -o out/example/option out/example/option.c
