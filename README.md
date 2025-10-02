HOL-Light definition of real numbers in Rocq using N
----------------------------------------------------

This [Rocq](https://rocq-prover.org/) library contains an automatic translation of a subset of the [HOL-Light](https://github.com/jrh13/hol-light) base library [lib_hol.ml](https://github.com/jrh13/hol-light/blob/master/lib_hol.ml) up to the definition of real numbers in the file [real.ml](https://github.com/jrh13/hol-light/blob/master/real.ml), with various HOL-Light types and functions [mapped](https://github.com/Deducteam/coq-hol-light-real-with-N/blob/main/mappings.lp) to the corresponding types and functions of the Rocq standard library so that, for instance, a HOL-Light theorem on HOL-Light natural numbers is translated to a Rocq theorem on the Rocq type N of natural numbers in base 2. The provided theorems can therefore be readily used within other Rocq developments based on the Rocq standard library. The translation has been done using [hol2dk](https://github.com/Deducteam/hol2dk) to extract and translate HOL-Light proofs to Lambdapi files, and [lambdapi](https://github.com/Deducteam/lambdapi) to translate Lambdapi files to Rocq files.

This library is used as a basis for the alignment of real numbers in the much larger library [coq-hol-light](https://github.com/Deducteam/coq-hol-light) which contains a translation of more than 20,000 HOL-Light theorems on arithmetic, wellfounded relations, lists, real numbers, integers, basic set theory, permutations, group theory, matroids, metric spaces, homology, vectors, determinants, topology, convex sets and functions, paths, polytopes, Brouwer degree, derivatives, Clifford algebra, integration, measure theory, complex numbers and analysis, transcendental numbers, real analysis, complex line integrals, etc.

The translated theorems are provided as axioms in order to have a fast Require because the proofs currently extracted from HOL-Light may be big and not very informative for they are low level (the translation is done at the kernel level, not at the source level). If you are skeptical, you can however generate and check them again by using the script [reproduce](https://github.com/Deducteam/hol2dk/blob/main/reproduce). It takes about 50 minutes with 32 processors Intel Core i9-13950HX and 64 Gb RAM. If every thing works well, the proofs are available in the directory `tmp/output`.

The types and functions currently [aligned](https://github.com/Deducteam/coq-hol-light-real-with-N/blob/main/mappings.lp) are:
- types: unit, prod, list, option, sum, ascii, N
- functions on N: pred, add, mul, pow, le, lt, ge, gt, max, min, sub, div, modulo, even, odd, factorial
- functions on list: app, rev, map, fold_right, removelast, combine, In, hd, tl, last, Forall, Forall2, Exists, nth*, length*, repeat*, filter**\
\* modulo correspondance between N and nat with N.of_nat and N.to_nat\
** modulo truth value Prop -> bool with excluded middle and choice

More types and functions are aligned in [coq-hol-light](https://github.com/Deducteam/coq-hol-light).

**How to contribute?**

You can easily contribute by proving the correctness of more mappings in Rocq:

- Look in [terms.v](https://github.com/Deducteam/coq-hol-light-real-with-N/blob/main/terms.v) for the definition of a function symbol, say f, that you want to replace; note that it is followed by a lemma f_def stating what f is equal to.

- Copy and paste in [mappings.v](https://github.com/Deducteam/coq-hol-light-real-with-N/blob/main/mappings.v) the lemma f_def, and try to prove it if f is replaced by your own function.

- Create a [pull request](https://github.com/Deducteam/coq-hol-light-real-with-N/pulls).

You can also propose to change the mapping of some type in [mappings.v](https://github.com/Deducteam/coq-hol-light-real-with-N/blob/main/mappings.v). Every HOL-Light type `A` is axiomatized as being isomorphic to the subset of elements `x` of some already defined type `B` that satisfies some property `p:B->Prop`. `A` can always be mapped to the Rocq type `{x:B|p(x)}` (see [mappings.v](https://github.com/Deducteam/coq-hol-light-real-with-nat/blob/main/mappings.v)) but it is possible to map it to some more convenient type `A'` by defining two functions:

- `mk:B->A'`

- `dest:A'->B`

and proving two lemmas:

- `mk_dest x: mk (dest x) = x`

- `dest_mk x: P x = (dest (mk x) = x)`

showing that `A'` is isomorphic to `{x:B|p(x)}`.

**Axioms used**

As HOL-Light is based on classical higher-order logic with choice, this library uses the following standard set of axioms in Rocq:

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

**Usage in a Rocq file**

```
Require Import HOLLight_Real_With_N.theorems.
Check thm_DIV_DIV.
```

**Bibliography**

- [Translating HOL-Light proofs to Coq](https://doi.org/10.29007/6k4x), Frédéric Blanqui, 25th International Conference on Logic for Programming, Artificial Intelligence and Reasoning (LPAR), 2024.
