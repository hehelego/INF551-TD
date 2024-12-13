# My solution to INF551 TDs

About the course

- the website: [Samuel Mimram — CSC_51051_EP -- Computational logic: from Artificial intelligence to Zero bugs](https://www.lix.polytechnique.fr/Labo/Samuel.Mimram/teaching/INF551/)
- the nice course notes: [Program = Proof](https://www.lix.polytechnique.fr/Labo/Samuel.Mimram/teaching/INF551/course.pdf)

Progress

- TD1: One optional task left: _5.3 implement functions for the tiny programming language_.
- TD2: Complete
- TD3: Complete
- TD4: 4 optional tasks to be finished.
- TD5: Complete
- TD6: Complete
- TD7: Complete
- TD8: Complete

Further extensions beyond the optional tasks:

For the SAT solver

- Conflict driver clause learning (CDCL)
- Basic SMT solving

For the simple typed programming language

- build a virtual machine
- compile to byte code and run on the virtual machine

For the proof assistant

- bidirectional type checking
- implicit parameters
- module system
- proof searching

For the agda formalization of programming languages

- confluence of the non-deterministic beta reduction
- strong normalization of STLC
- normalization by evaluation (NbE)

## TD1 a simple typed programming language

Encode programs of a simple programming language in OCaml.
Implement the typing rules and the reduction rules.

- program formation
  - literals: booleans and natural numbers
  - basic arithmetics
  - if branchings
  - pairs and projections
  - unit values
  - functions **TODO**
- type inference and type checking
- single step reduction, parallel reduction, and normalization

## TD2 boolean satisfiability solving

Implement a DPLL SAT solver in OCaml.

- brute force depth-first searching to exhaust the space of assignments
- DPLL: unit clause propagation, pure clause elimination, picking decision variable with heuristics
- encoding and solving sudoku problems using the DPLL SAT solver
- transform arbitrary formula into a equi-satisfiable CNF with Tesytin transformation

## TD3 untyped lambda calculus

- encoding terms of lambda calculus
- encoding products, natural numbers, booleans in untyped lambda calculus
- encoding recursive function using the fixed point combinator
- capture-avoiding substitution
- single step beta reduction
- alpha-beta-eta equivalence
- de Bruijn indices representation

## TD4 proof assistances based on type theories

- type checking and type inference of simply typed lambda calculus (STLC)
- interactively constructing proofs and proof terms with tactics
- naive implementation of dependent type theory
  - dependent products (dependent type functions)
  - natural numbers
  - homogeneous equality
  - W-types for defining inductive type **WIP**
  - layered type universes **WIP**
- another proof assistance based on dependent type theory
- proving associativity and commutativity of natural number addition
- proving associativity and commutativity of natural number multiplication
- exploring paradoxes in the proof assistance **WIP**
- de Bruijn indices representation **TODO**
- normalization by evaluation (NbE) **TODO**

## TD5 propositional logic in Agda

- encoding and proving tautologies of propositional logic using Agda
- exploring the interplay of negation and other connectives
- proving the equivalence among
  - the law of excluded middle
  - the Pierce law
  - the double negation elimination rule
- exploring the 4 de-Morgan rules in first order logic

## TD6 inductive types in Agda

- booleans, natural numbers, equalities, lists
- proving the formula of the sum of 1st power of natural numbers
- formalizing the Euclidean division algorithm with intrinsic/extrinsic approaches

## TD7 sorting algorithms in Agda

- formalizing the insertion sort algorithm
- proving the correctness of insertion sort
- formalizing the insertion sort algorithm with intrinsic approach (embedding invariants into type signatures)
- proving the insertion sort algorithm outputs a permutation of the input
- proving the termination of non-structural inductions with well-founded induction
- defining the merge sort algorithm using well-founded induction

## TD8 formalizing a simple programming language in Agda

- encoding Plotkin's Programming Computable Functions (PCF) in Agda
- typing context insertion and free variable lifting
- free variable substitution for de Bruijn indices representation
- defining the typing rules, the reduction rules, and the canonical forms
- proving the progress property for well-typed closed terms
- proving the subject-reduction property for well-typed reducible terms
