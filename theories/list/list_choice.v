(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import List.

From KruskalTrees
  Require Import notations.

Import ListNotations.

Set Implicit Arguments.

Fact list_choice X (P Q : X -> Prop) (l : list X) :
        (forall x, x ∈ l -> P x \/ Q x)
     -> (forall x, x ∈ l -> P x)
      \/ exists x, x ∈ l /\ Q x.
Proof.
  induction l as [ | x l IHl ]; intros Hl.
  + now left; simpl.
  + destruct IHl as [ H | (y & ? & ?) ].
    * intros; apply Hl; simpl; auto.
    * destruct (Hl x); simpl; eauto.
      left; intros ? [ [] | ]; auto.
    * right; exists y; simpl; auto.
Qed.

Fact list_choice_t X (P Q : X -> Prop) (l : list X) :
        (forall x, x ∈ l -> { P x } + { Q x })
     -> (forall x, x ∈ l -> P x)
      + { x | x ∈ l /\ Q x }.
Proof.
  induction l as [ | x l IHl ]; intros Hl.
  + left; simpl; tauto.
  + destruct IHl as [ H | (y & ? & ?) ].
    * intros; apply Hl; simpl; auto.
    * destruct (Hl x); simpl; eauto.
      left; intros ? [ [] | ]; auto.
    * right; exists y; simpl; auto.
Qed.
