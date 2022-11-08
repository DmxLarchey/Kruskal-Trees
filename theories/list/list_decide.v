(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL B FREE SOFTWARE LICENSE AGREEMENT           *)
(**************************************************************)

From Coq
  Require Import List.

From KruskalTrees
  Require Import notations.

Set Implicit Arguments.

#[local] Hint Resolve in_eq in_cons : core.

Fact list_eq_dect X (l m : list X) :
       (forall x y, x ∈ l -> y ∈ m -> { x = y } + { x <> y })
    -> { l = m } + { l <> m }.
Proof.
  revert m; induction l as [ | x l IHl ]; intros [ | y m ] H; auto.
  1,2: now right.
  destruct (H x y) as [ <- | H1 ]; auto.
  2: now right; contradict H1; inversion H1.
  destruct (IHl m) as [ <- | H2 ]; auto.
  now right; contradict H2; inversion H2.
Qed.

