(lang dune 3.21)

(using rocq 0.11)

(name verified-metaprogramming)

(generate_opam_files true)

(package
 (name verified-metaprogramming)
 (maintainers "Mathis Bouverot-Dupuis (mathis.bouverot@ens.psl.eu)")
 (authors "Mathis Bouverot-Dupuis")
 (synopsis "Verified meta-programming framework for Rocq")
 (depends
   (rocq-prover (= 9.0.0))
   rocq-equations))