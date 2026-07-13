(lang dune 3.20)

(name monad-spec)

(generate_opam_files true)

(package
 (name monad-spec)
 (depends
    (ocaml (= 5.4.0))
    ocaml-option-flambda
    (zarith (= 1.14))
    cryptokit
    (secp256k1-internal (= 0.4.0))
    (alcotest (= 1.9.1))
    (qcheck-core (= 0.27))
    (qcheck-alcotest (= 0.27))
    (yojson (= 3.0.0))
    (ctypes (= 0.24.0))
    (ctypes-foreign (= 0.24.0))))
