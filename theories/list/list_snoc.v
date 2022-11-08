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

Import ListNotations.

Set Implicit Arguments.

Section snoc_lists.

  (* snoc is cons reversed !! *)

  Variable X : Type.

  Implicit Type l : list X.

  Theorem list_snoc_rect P :
            P []
        -> (forall l x, P l -> P (l++[x]))
        ->  forall l, P l.
  Proof.
    intros H1 H2 l; revert P H1 H2.
    induction l as [ | x l IHl ]; intros ? ? Hsnoc; trivial.
    apply IHl with (P := fun l => P (x::l)).
    + now apply (Hsnoc []).
    + now intros; apply (Hsnoc (_::_)).
  Qed.

  Fact list_snoc_inv l : ( l = [] ) + { m : _ & { x | l = m++[x] } }.
  Proof. destruct l using list_snoc_rect; eauto. Qed.

  Fact list_snoc_inj l m x y : l++[x] = m++[y] -> l = m /\ x = y.
  Proof.
    intros H.
    apply f_equal with (f := @rev _) in H.
    rewrite !rev_app_distr in H; simpl in H.
    inversion H; split; auto.
    now rewrite <- (rev_involutive l), <- (rev_involutive m); f_equal.
  Qed.

End snoc_lists.
