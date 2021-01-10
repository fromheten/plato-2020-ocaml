shelltest.diff.md: shelltest.md
	ocaml-mdx test -v shelltest.md && diff shelltest.md shelltest.md.corrected > shelltest.diff.md
