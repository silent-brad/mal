(lang dune 3.21)

(name clj-in-ml)

(generate_opam_files true)

(source
 (github silent-brad/clj-in-ml))

(authors "Brad White")

(license LICENSE)

(package
 (name clj-in-ml)
 (synopsis "Simple Clojure interpreter in OCaml")
 (depends ocaml lwt clj-in-ml))
