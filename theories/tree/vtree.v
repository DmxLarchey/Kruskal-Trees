(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From KruskalTrees
  Require Import notations tactics idx vec.

From KruskalTrees
  Require Export dtree.

Import idx_notations vec_notations dtree_notations.

Set Implicit Arguments.

(** vectors tree with uniform type for nodes *)
Notation vtree := (fun X => dtree (fun _ => X)).

Module vtree_notations.

  Notation "⟨ x | v ⟩" := (dtree_cons x v).

End vtree_notations.

Section vtree.

  Variable A : Type.

  Implicit Types (X Y : nat -> A -> Prop).

  (** A predicate for well-formed vtrees: nodes of arity i satisfy X i 
      For instance, given a : X -> nat, then a x gives the unique arity 
      allowed for x, one could use X n x := n = a x *)
  Definition wft X : vtree A -> Prop := dtree_fall (fun n x _ => X n x).

  Fact wft_fix X n x (v : vec _ n) : wft X ⟨x|v⟩ <-> X n x /\ forall p, wft X v⦃p⦄.
  Proof. unfold wft at 1; rewrite dtree_fall_fix; apply and_equiv; tauto. Qed.

  Fact wft_mono X Y : X ⊆₂ Y -> wft X ⊆₁ wft Y.
  Proof. intro; apply dtree_fall_mono; eauto. Qed.

  Fact wft_dec X : (forall n x, { X n x } + { ~ X n x }) -> forall t, { wft X t } + { ~ wft X t }.
  Proof. intro; apply dtree_fall_dec; intros; auto. Qed.

  Section wft_rect.

    Variables (X : _ -> _ -> Prop)
              (P : _ -> Type)
              (HP : forall n x v, X n x -> (forall i : idx n, wft X v⦃i⦄) -> (forall i, P v⦃i⦄) -> P ⟨x|v⟩).

    Theorem wft_rect t : wft X t -> P t.
    Proof. induction 1 using dtree_fall_rect; auto. Qed.

  End wft_rect.

End vtree.

Section vtree_eq_dec.

  Variables (X : Type) (eqX_dec : forall x y : X, { x = y } + { x <> y }).

  Theorem vtree_eq_dec (r t : vtree X) : { r = t } + { r <> t }.
  Proof. apply dtree_eq_dec; auto. Qed.

End vtree_eq_dec.
