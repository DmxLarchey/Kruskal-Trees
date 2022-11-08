(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL B FREE SOFTWARE LICENSE AGREEMENT           *)
(**************************************************************)

Set Implicit Arguments.

#[local] Reserved Notation "'⟨' x '⟩₀'" (at level 0, x at level 200, format "⟨ x ⟩₀").
#[local] Reserved Notation "'⟨' y | t '⟩₁'" (at level 0, t at level 200, format "⟨ y | t ⟩₁").

(** Unary trees *)
Inductive utree (X Y : Type) :=
  | utree_leaf : X -> utree X Y
  | utree_node : Y -> utree X Y -> utree X Y.

Arguments utree_leaf {X Y}.
Arguments utree_node {X Y}.

Module utree_notations.

  Notation "⟨ x ⟩₀" := (utree_leaf x).
  Notation "⟨ y | t ⟩₁" := (utree_node y t).

End utree_notations.

Import utree_notations.
