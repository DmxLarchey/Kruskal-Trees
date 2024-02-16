(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From KruskalTrees
  Require Import list_utils idx ltree.

Import ltree_notations.

Set Implicit Arguments.

#[local] Reserved Notation "'⌊' t '⌋ₙ'" (at level 0, t at level 200, format "⌊ t ⌋ₙ").

Unset Elimination Schemes.

(* Finitely branching trees labeled in idx n ~~ {1,...,n} *)

Definition ntree n := ltree (idx n).

Definition ntree_size {n} : ntree n -> nat := ltree_weight (fun _ : idx n => 1).

Module ntree_notations.

  Notation "⌊ t ⌋ₙ" := (ntree_size t).

End ntree_notations.

Import ntree_notations.

Fact ntree_size_fix n p l : @ntree_size n ⟨p|l⟩ₗ = 1+list_sum (fun t => ⌊t⌋ₙ) l.
Proof. apply ltree_weight_fix. Qed.
