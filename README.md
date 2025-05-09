HOL-Light definition of real numbers in Coq using N
---------------------------------------------------

This library provides a translation in Coq of the definition of real numbers in HOL-Light, using the Coq type N for natural numbers (it is an adaptation of [coq-hol-light-real-with-nat](https://github.com/Deducteam/coq-hol-light-real-with-nat/)).

It has been automatically generated from HOL-Light using [hol2dk](https://github.com/Deducteam/hol2dk) and [lambdapi](https://github.com/Deducteam/lambdapi).

Proofs are not included but can be regenerated and rechecked by running [reproduce](https://github.com/Deducteam/coq-hol-light-real/blob/main/reproduce) (it takes about 7 minutes on a machine with 32 processors Intel Core i9-13950HX and 64 Gb RAM).

As HOL-Light is based on higher-order logic, this library assumes classical logic, Hilbert's ε operator, functional and propositional extensionnality:

```
Axiom classic : forall P:Prop, P \/ ~ P.
Axiom constructive_indefinite_description : forall (A : Type) (P : A->Prop), (exists x, P x) -> { x : A | P x }.
Axiom fun_ext : forall {A B : Type} {f g : A -> B}, (forall x, (f x) = (g x)) -> f = g.
Axiom prop_ext : forall {P Q : Prop}, (P -> Q) -> (Q -> P) -> P = Q.
Axiom proof_irrelevance : forall (P:Prop) (p1 p2:P), p1 = p2.
```

**Installation using [opam](https://opam.ocaml.org/)**

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-hol-light-real-with-N
```

**Usage in a Coq file**

```
Require Import HOLLight_Real_With_N.theorems.
Check thm_REAL_COMPLETE.
```

**Bibliography**

- [Translating HOL-Light proofs to Coq](https://doi.org/10.29007/6k4x), Frédéric Blanqui, 25th International Conference on Logic for Programming, Artificial Intelligence and Reasoning (LPAR), 2024.
