# Introduction

This repository contains supplementary material (examples and case studies) for the Rocqshop paper "Phantom Names: a Named Interface for de Bruijn Syntax".

# Building and running

You need a working Rocq installation (version 9.1) to run the code. I recommend using the `opam` package manager and creating a local switch:
```
opam switch create . 4.14.2 --repos=default,rocq-released='https://rocq-prover.org/opam/released'
```
The above command takes a few minutes and will install Rocq version 9.1 and the necessary libraries (Equations and stdpp).

You can then build the code using:
```
dune build && dune install
```
After which you should be able to step through the code interactively, e.g. using VsRocq (in VS Code).

# Dependencies

The code depends on the following libraries:
- `rocq-equations` makes dependent pattern matching easier. It is mainly used in `sec5-cc-meta-theory`.
- `rocq-stdpp` provides finite sets which we use in `sec4-stack-reduction` to reason about locally nameless.

# Overview of the code

The code is split into folders which mirror the sections of the extended abstract:
- `sec2-phantom-names` contains the basic machinery needed for phantom names:
  1. Tags and scopes.
  2. Typeclasses for scope membership and inclusion.
  3. (Well-scoped) de Bruijn indices and thinnings.
  The code from this folder is imported in other folders (using `From PhantomNames Import ...`).
- `sec3-translations` contains various translations written using phantom names:
  1. A CPS translation for the lambda calculus with let-in bindings.
  2. A unary parametricity translation for a dependently-typed calculus.
  3. A translation from the lambda calculus with explicity substitutions to the pi calculus.
- `sec4-stack-reduction` proves the correctness of a basic stack reduction machine for the lambda calculus,
  using several binder representations.
  1. `DeBruijn.v` uses (unscoped) de Bruijn indices.
  2. `PhantomNames.v` uses phantom names, and is very similar to the de Bruijn version.
  3. `LocallyNamelessCofinite.v` is a FAILED attempt using locally nameless and cofinite quantification,
      which shows exactly why cofinite quantification is insufficient.
  4. `LocallyNameless.v` uses locally nameless.
- `sec5-cc-meta-theory` formalizes the meta-theory of a variant of the calculus of constructions with evars,
  using phantom names.

We tried to ensure the code is readable and well commented: read the individual files
for more details.