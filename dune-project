(lang dune 3.21)

(using rocq 0.11)

(name phantom-names-rocqshop)

(generate_opam_files true)

(package
 (name phantom-names-rocqshop)
 (maintainers "Mathis Bouverot-Dupuis (mathis.bouverot@ens.psl.eu)")
 (authors "Mathis Bouverot-Dupuis")
 (synopsis
  "Supplementary material for the Rocqshop presentation on phantom names")
 (depends
  (rocq-core
   (= 9.1.0))
  rocq-equations
  rocq-stdpp))
