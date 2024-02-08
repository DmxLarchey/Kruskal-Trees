(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL B FREE SOFTWARE LICENSE AGREEMENT           *)
(**************************************************************)

From Coq
  Require Import Arith List Lia.

From KruskalTrees
  Require Import notations tactics list_utils ltree.

Import ListNotations ltree_notations.

Set Implicit Arguments.

#[local] Reserved Notation "'⟨' l '⟩ᵣ'" (at level 0, l at level 200, format "⟨ l ⟩ᵣ").
#[local] Reserved Notation "'⌊' t '⌋ᵣ'" (at level 0, t at level 200, format "⌊ t ⌋ᵣ").

(** Undecorated rose trees *)

Unset Elimination Schemes.
Inductive rtree := rt : list rtree -> rtree.
Set Elimination Schemes.

#[local] Notation "⟨ l ⟩ᵣ" := (rt l).

Section rtree_ind.

  Variables (P : rtree -> Prop)
            (HP : forall l, (forall t, t ∈ l -> P t) -> P ⟨l⟩ᵣ).

  Fixpoint rtree_ind t : P t.
  Proof.
    destruct t as [ l ].
    apply HP.
    induction l as [ | x l IHl ].
    + intros ? [].
    + intros ? [ <- | ].
      * apply rtree_ind.
      * now apply IHl.
  Qed.

End rtree_ind.

Section rtree_rect.

  Local Fact ist_wf : well_founded (fun s t => match t with ⟨l⟩ᵣ => s ∈ l end).
  Proof. intro t; induction t; now constructor. Qed.

  Variables (P : rtree -> Type)
            (HP : forall l, (forall t, t ∈ l -> P t) -> P ⟨l⟩ᵣ).

  Theorem rtree_rect t : P t.
  Proof.
    generalize (ist_wf t); revert t.
    refine (fix loop t d { struct d } := _).
    destruct t as [ l ]; apply HP.
    intros s Hs; apply loop.
    apply Acc_inv with (1 := d), Hs.
  Qed.

End rtree_rect.

Definition rtree_rec (P : _ -> Set) := @rtree_rect P.
(* Definition rtree_ind (P : _ -> Prop) := @rtree_rect P. *)

Fixpoint rtree_size (t : rtree) := 
  match t with 
  | ⟨l⟩ᵣ => 1+list_sum rtree_size l
  end.

Fact rtree_size_fix l : rtree_size ⟨l⟩ᵣ = 1+list_sum rtree_size l.
Proof. reflexivity. Qed.

Module rtree_notations.

  Notation "⟨ l ⟩ᵣ" := (rt l).
  Notation "⌊ t ⌋ᵣ" := (rtree_size t).

End rtree_notations.

Import rtree_notations.

Fact rtree_size_gt t : 0 < ⌊t⌋ᵣ.
Proof. destruct t; rewrite rtree_size_fix; lia. Qed.

Definition ltree_rtree : ltree unit -> rtree.
Proof. apply ltree_recursion; intros _ _; apply rt. Defined.

Fact ltree_rtee_surj (t : rtree) : { t' | ltree_rtree t' = t }.
Proof.
  induction t as [ l IHl ].
  Forall reif IHl as (m & Hm).
  exists ⟨tt|m⟩ₗ; simpl; f_equal.
  now rewrite Forall2_xchg, <- Forall2_map_left, Forall2_eq in Hm.
Qed.
