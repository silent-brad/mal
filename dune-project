(lang dune 3.21)

(name cljml)

(generate_opam_files true)

(source
 (github silent-brad/cljml))

(authors "Brad White")

(license LICENSE)

(package
 (name cljml)
 (synopsis "Simple Clojure interpreter in OCaml")
 (depends ocaml lwt cljml))
