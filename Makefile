.PHONY=install

install: bin/ lib/
	echo "Installing into $(PREFIX)/platoc" && dune build bin/platoc.exe && mv -f _build/default/bin/platoc.exe $(PREFIX)/platoc

shelltest.diff.md: shelltest.md
	ocaml-mdx test -v shelltest.md && diff shelltest.md shelltest.md.corrected > shelltest.diff.md
