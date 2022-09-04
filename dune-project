(lang dune 2.8)
(name platoc-2020)
(version 0)
(authors "Martin Josefsson")
(homepage "https://github.com/fromheten/plato-2020-ocaml")
(generate_opam_files true)

(package
 (name platoc-2020)
 (depends
  (cryptokit (>= 1.0.0))
  (yojson (= 1.7.0))
  (ppx_deriving_yojson (= 3.6.1))))
