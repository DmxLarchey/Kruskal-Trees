```
(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL B FREE SOFTWARE LICENSE AGREEMENT           *)
(**************************************************************)
```
[comment]: # ( ∀ → ∃ ⋀ ⋁ ⇒ )

# What is this library?

This library formalizes in `Coq 8.14+` the notion of _rose tree_
via purely inductive characterizations and provides implementations of
proper (nested) induction principles and tools to manipulate those
trees. 

It is was extracted from a complete rework of the proof of Kruskal's
tree theorem based on dependent vectors instead of lists, but can be
used independently, as requested by @jjhughes.

This `README` file provides an introduction to the main definitions.

# Overview of the definitions 

Some remarks about notations below:

* we follow Coq syntax mostly, with some relaxations in that
  we may confuse a binary relation (eg. `le : nat → nat → Prop`) and its 
  infix notation `≤` and then write `af ≤` (which Coq would not accept);
* _implicit parameters_ are denoted between `{...}` as in Coq (eg `{X : Type}`)
  and we do not specify them afterwards except when terms are preceded 
  with an `@` which locally disables implicit parameters. Eg we can write
  `@af X R` or `af R` -- they are the same, -- provided the type of `R` is 
  guessably `X`;
* we write `_` for arguments that Coq can guess by unification from
  other arguments, eg `@af _ R` is _the same_ as `af R`, and
  `vec _ n` gives the length of vectors without giving the base type;
  btw (IMHO), maximum usage of unification and notations is critical 
  to write readable code.

## Data structures for lists, indices `idx n` and vectors `vec X n`:

Let us continue with the usual data-structures:

* type of natural numbers `nat`;
* type of lists `list X` over base type `X : Type`;
* type of indices [`idx n`](theories/vec/idx.v) from `[0,n[` (_identical_ to `Fin.t`); 
* dependent (uniform) vectors [`vec X n`](theories/vec/vec.v) with `X : Type` and `n : nat` (_identical_ to `Vector.t`);
* access to components of vectors via `v⦃i⦄` with `v : vec _ n` and `i : idx n`.

```
Inductive nat : Type :=
  | O : nat
  | S : nat → nat.
(* Decimal notations 0, 1, 2, ... are accepted *)

Inductive list (X : Type) : Type :=
  | nil : list X
  | cons : X → list X → list X
where "[]" := (@nil _)
 and  "x :: l" := (@cons _ x l).

Fixpoint In {X} (x : X) (l : list X) : Prop :=
  match l with
    | []   ⇒ False
    | y::l ⇒ y = x ⋁ x ∊ l
  end
where "x ∊ l" := (@In _ x l). 

Inductive idx n : Type :=
  | idx_fst : idx (S n)
  | idx_nxt : idx n → idx (S n)
where "𝕆" := idx_fst
 and  "𝕊" := idx_nxt.

Inductive vec X : nat → Type :=
  | vec_nil  : vec X 0
  | vec_cons : ∀n, X → vec X n → vec X (S n).
where "∅" := vec_nil.
 and  "x ## v" := (@vec_cons _ x v).

Fixpoint vec_prj X n (v : vec X n) : idx n → X := 
  match v with 
    ...  (* a bit complicated but critical piece of code *)
  end
where "v⦃i⦄" := (@vec_prj _ _ v i).

(* Verifies the fixpoint equations by *reduction*
       (x##_)⦃𝕆⦄ = x
       (_##v)⦃𝕊 p⦄ = v⦃p⦄  *)
```

## Data structure for trees

Now we come to variations around rose trees (finitely branching finite trees), 
ie direct sub-trees are collected in `list` or `vec _ n`:

* uniform trees [`ltree X`](theories/tree/ltree.v) as lists of trees with nodes of type `X : Type`;
* dependent trees [`dtree X`](theories/tree/dtree.v) where each arity `n` as nodes of type `X n : Type`;
* dependent uniform trees [`vtree X`](theories/tree/vtree.v) as vectors of trees with nodes of type `X : Type`.

Notice that the arity/breadth can be bounded at `k : nat` in `dtree X` by forcing `X n` to be an
`void` type for `n ≥ k`, ie a type without inhabitants; this is a requirement in Higman's theorem.

```
Inductive ltree (X : Type) : Type :=
  | in_ltree : X → list (ltree X) → ltree X
where "⟨x|l⟩ₗ" := (@in_ltree _ x l).

Inductive dtree (X : nat → Type) : Type :=
  | in_dtree k : X k → vec (dtree X) k → dtree X
where "⟨x|v⟩" := (@in_dtree _ _ x v).

Notation "vtree X" := (dtree (λ _, X)).
```

