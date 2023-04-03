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

Section rtree_rect.

  Let is_subtree s t := s ∈ match t with ⟨l⟩ᵣ => l end.
  
  Let ist_wf : well_founded is_subtree.
  Proof.
    refine (fix loop t := _).
    destruct t as [ l ].
    constructor 1.
    induction l as [ | s l IHl ].
    + intros ? [].
    + intros x [ <- | Hx ].
      * apply loop.
      * apply IHl, Hx.
  Qed.

  Variables (P : rtree -> Type)
            (HP : forall l, (forall t, t ∈ l -> P t) -> P ⟨l⟩ᵣ).

  Let Fixpoint rtree_Acc_rect t (a : Acc is_subtree t) : P t :=
    match t return Acc is_subtree t -> P t with
      | ⟨l⟩ᵣ => fun a => HP _ (fun _ h => rtree_Acc_rect (Acc_inv a h))
    end a.

  Arguments rtree_Acc_rect : clear implicits.

  Definition rtree_rect t : P t := rtree_Acc_rect t (ist_wf t).

  Section rtree_rect_fix.

    Hypothesis HP_ext : forall l f g, (forall x Hx, f x Hx = g x Hx) -> HP l f = HP l g.

    (** The Acc based recursor is proof-irrelevant *)

    Let Fixpoint rtree_Acc_rect_eq t a a' : rtree_Acc_rect t a = rtree_Acc_rect t a'.
    Proof.
      destruct a; destruct a'; destruct t; simpl.
      apply HP_ext.
      intros; apply rtree_Acc_rect_eq.
    Qed.

    Lemma rtree_rect_fix l : rtree_rect ⟨l⟩ᵣ = HP l (fun t _ => rtree_rect t).
    Proof.
      unfold rtree_rect; destruct (ist_wf ⟨l⟩ᵣ); simpl.
      apply HP_ext.
      intros; apply rtree_Acc_rect_eq.
    Qed.

  End rtree_rect_fix.

End rtree_rect.

Definition rtree_rec (P : _ -> Set) := @rtree_rect P.
Definition rtree_ind (P : _ -> Prop) := @rtree_rect P.

Fixpoint rtree_size (r : rtree) : nat.
Proof.
  destruct r as [ l ].
  apply (plus 1).
  induction l as [ | t l IHl ].
  + exact 0.
  + apply (rtree_size t + IHl).
Defined.

Fact rtree_size_fix l : rtree_size ⟨l⟩ᵣ = 1+list_sum rtree_size l.
Proof. induction l; simpl; f_equal; auto. Qed.

Section rtree_recursion.

  (** A non-dependent recursor for trees, using a direct nested fixpoint,
      the nesting occurs with the external (list) map function *)

  Variable (Y : Type) (f : list rtree -> list Y -> Y).

  Fixpoint rtree_recursion (t : rtree) : Y :=
    match t with
      | ⟨l⟩ᵣ => f l (map rtree_recursion l)
    end.

End rtree_recursion.

Definition rtree_size_alt (r : rtree) : nat.
Proof.
  induction r as [ _ ls ] using rtree_recursion.
  exact (1+list_sum (fun x => x) ls).
Defined.

Fact rtree_size_alt_fix l :
      rtree_size_alt ⟨l⟩ᵣ = 1+list_sum (fun x => x) (map rtree_size_alt l).
Proof. reflexivity. Qed.

Fixpoint list_map_dep {X Y} l : (forall x : X, x ∈ l -> Y) -> list Y :=
  match l with 
    | nil  => fun _ => nil
    | x::l => fun f => f _ (or_introl eq_refl) :: list_map_dep l (fun y hy => f y (or_intror hy))
  end.

Fact list_map_dep_ext {X Y} l f g : (forall x hx, f x hx = g x hx) -> @list_map_dep X Y l f = list_map_dep l g.
Proof. revert f g; induction l; intros; simpl; f_equal; auto. Qed.

Definition rtree_size_rec (r : rtree) : nat.
Proof.
  induction r as [ l IHl ] using rtree_rec.
  exact (1+list_sum (fun x => x) (list_map_dep l IHl)).
Defined.

Fact rtree_size_rec_fix l : rtree_size_rec ⟨l⟩ᵣ = 1+list_sum (fun x => x) (list_map_dep l (fun t _ => rtree_size_rec t)).
Proof.
  unfold rtree_size_rec, rtree_rec.
  rewrite rtree_rect_fix; trivial.
  intros; do 2 f_equal.
  now apply list_map_dep_ext.
Qed.

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
