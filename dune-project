(lang dune 3.20)

(name monad-spec)

(generate_opam_files true)

(package
 (name monad-spec)
 (depends
    (ocaml (>= 5.3))
    utop
    (zarith (>= 1.14))
    (lens (>= 1.2.5))
    (digestif (>= 1.3.0))
    (alcotest (>= 1.9.0))
    (qcheck-core (>= 0.26))
    (qcheck-alcotest (>= 0.26))))
