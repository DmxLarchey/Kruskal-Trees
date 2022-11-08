(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL B FREE SOFTWARE LICENSE AGREEMENT           *)
(**************************************************************)

From Coq
  Require Import Arith List.

From KruskalTrees
  Require Import notations.

Import ListNotations.

Set Implicit Arguments.

Section list_sum.

  Variables (X : Type) (f : X -> nat).

  Fixpoint list_sum l :=
    match l with
      | []   => 0
      | x::l => f x + list_sum l
    end.

  Fact list_sum_app l m : list_sum (l++m) = list_sum l + list_sum m.
  Proof.
    induction l as [ | x l IHl ]; simpl; auto.
    now rewrite IHl, plus_assoc.
  Qed.

  Hint Resolve le_trans le_plus_l le_plus_r : core.

  Fact list_sum_in x l : x ∈ l -> f x <= list_sum l.
  Proof.
    induction l as [ | y l IHl ].
    + intros [].
    + intros [ <- | Hl%IHl ]; simpl; eauto.
  Qed.

End list_sum.
