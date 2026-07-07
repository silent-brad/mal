(lang dune 3.21)

(name ml_clj)

(generate_opam_files true)

(source
 (github silent-brad/ml_clj))

(authors "Brad White")

(license LICENSE)

(package
 (name ml_clj)
 (synopsis "Simple Clojure interpreter in OCaml")
 (depends ocaml lwt ml_clj))
