(lang dune 2.7.1)
(name platoc-2020)
(generate_opam_files true)

(package
 (name platoc-2020)
 (depends
  (cryptokit (>= 1.0.0))
  (ounit2 (>= 2.2.4))
  (alcotest (>= 1.2.3))
  (yojson (= 1.7.0))
  (ppx_deriving_yojson (= 3.6.1))))
