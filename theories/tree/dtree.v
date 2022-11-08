(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL B FREE SOFTWARE LICENSE AGREEMENT           *)
(**************************************************************)

From Coq
 Require Import Lia.

From KruskalTrees
  Require Import notations tactics idx vec.

From KruskalTrees
  Require list_choice.

Import idx_notations vec_notations
       list_choice (list_choice_t).

Set Implicit Arguments.

#[local] Reserved Notation "'⟨' x '|' v '⟩'" (at level 0, v at level 200, format "⟨ x | v ⟩").

(* ∈ ⟨|⟩ ≤ₑ ≤ₚ ≤ₕ ≤ₖ *)

Section dtree.

  (* The most general trees we have, ie dependent trees
     with a different type at each arity ... *)

  Variable (X : nat -> Type).

  Unset Elimination Schemes.

  Inductive dtree : Type :=
    | dtree_cons k : X k -> vec dtree k -> dtree.

  Set Elimination Schemes.

  Notation "⟨ x | v ⟩" := (dtree_cons x v).

  Section dtree_cons_inj.

    Local Definition dtree_arity t := match t with @dtree_cons k _ _ => k end.
    Local Definition dtree_root t : X (dtree_arity t) := match t with ⟨x|_⟩ => x end.
    Local Definition dtree_sons t : vec dtree (dtree_arity t) := match t with ⟨_|v⟩ => v end.

    Local Fact dtree_cons_injective n x (v : vec _ n) t :
          ⟨x|v⟩ = t -> exists e : n = dtree_arity t, x↺e = dtree_root t /\ v↺e = dtree_sons t.
    Proof. intros []; now exists eq_refl. Qed.

    Fact dtree_cons_inj n x (v : vec _ n) m y (w : vec _ m) :
          ⟨x|v⟩ = ⟨y|w⟩ <-> exists (e : n = m), x↺e = y /\ v↺e = w.
    Proof.
      split.
      + apply dtree_cons_injective.
      + intros (? & ? & ?); eq refl; subst; auto.
    Qed.

  End dtree_cons_inj.

  Section dtree_rect.

    Variable (P : dtree -> Type)
             (P_cons : forall k x (v : vec _ k), (forall p, P v⦃p⦄) -> P ⟨x|v⟩).

    Fixpoint dtree_rect t : P t :=
      match t with
        | dtree_cons x v => P_cons x v (fun p => dtree_rect v⦃p⦄)
      end.

    Fact dtree_rect_fix k x (v : vec _ k) : dtree_rect ⟨x|v⟩ = P_cons x v (fun p => dtree_rect v⦃p⦄).
    Proof. reflexivity. Qed.

  End dtree_rect.

  Definition dtree_rec (P : _ -> Set) := dtree_rect P.
  Definition dtree_ind (P : _ -> Prop) := dtree_rect P.

  Definition dtree_fall (P : forall k, X k -> vec dtree k -> Prop) : dtree -> Prop.
  Proof.
    induction 1 as [ k x v IH ].
    exact (P _ x v /\ forall p, IH p).
  Defined.

  Fact dtree_fall_fix P k x (v : vec _ k) : dtree_fall P ⟨x|v⟩ = (P _ x v /\ forall p, dtree_fall P v⦃p⦄).
  Proof. reflexivity. Qed.

  Definition dtree_exst (P : forall k, X k -> vec dtree k -> Prop) : dtree -> Prop.
  Proof.
    induction 1 as [ k x v IH ].
    exact (P _ x v \/ exists p, IH p).
  Defined.

  Fact dtree_exst_fix P k x (v : vec _ k) : dtree_exst P ⟨x|v⟩ = (P _ x v \/ exists p, dtree_exst P v⦃p⦄).
  Proof. reflexivity. Qed.

  Section dtree_fall_rect.

    Variables (P : forall k, X k -> vec dtree k -> Prop)
              (Q : dtree -> Type)
              (HQ : forall k x v, @P k x v -> (forall p : idx k, dtree_fall P v⦃p⦄) -> (forall p, Q v⦃p⦄) -> Q ⟨x|v⟩).

    Theorem dtree_fall_rect t : dtree_fall P t -> Q t.
    Proof.
      induction t as [ n x v IH ]; intros H.
      rewrite dtree_fall_fix in H; destruct H; auto.
    Qed.

  End dtree_fall_rect.

  Fact dtree_fall_mono (P Q : forall k, X k -> vec dtree k -> Prop) :
           (forall k, @P k ⊆₂ @Q k)
        -> dtree_fall P ⊆₁ dtree_fall Q.
  Proof. induction 2 using dtree_fall_rect; simpl; auto. Qed.

  Section dtree_fall_exst.

    Variables (P Q : forall k, X k -> vec dtree k -> Prop)
              (HPQ : forall k x v, { @P k x v } + { Q x v })
              (HPQnot : forall k x v, @P k x v -> Q x v -> False).

    Fact dtree_fall_exst t : { dtree_fall P t } + { dtree_exst Q t }.
    Proof.
      induction t as [ n x v IH ].
      destruct idx_finite_t with n as (l & Hl).
      destruct list_choice_t
        with (l := l)
             (P := fun p => dtree_fall P v⦃p⦄)
             (Q := fun p => dtree_exst Q v⦃p⦄)
        as [ H1 | (p & Hp1 & Hp2) ]; auto;
        [ destruct (HPQ x v) as [ H2 | H2 ] | ].
      1: left; simpl; auto.
      all: right; simpl; eauto.
    Qed.

    Fact dtree_fall_exst_absurd t : dtree_fall P t -> dtree_exst Q t -> False.
    Proof.
      induction 1 as [ k x v H1 H2 IH2 ] using dtree_fall_rect.
      intros [ | [] ]; eauto.
    Qed.

  End dtree_fall_exst.

  Fact dtree_fall_dec P :
           (forall n (x : X n) v, { P n x v } + { ~ P n x v })
         -> forall t, { dtree_fall P t } + { ~ dtree_fall P t }.
  Proof.
    intros H t.
    destruct dtree_fall_exst with (1 := H) (t := t) as [ H1 | H1 ]; auto.
    right.
    intros H2; revert H2 H1.
    apply dtree_fall_exst_absurd; auto.
  Qed.

End dtree.

Module dtree_notations.

  Notation "⟨ x | v ⟩" := (dtree_cons x v).

End dtree_notations.

Import dtree_notations.

Section dtree_map.

  Variables (X Y : nat -> Type) (f : forall n, X n -> Y n).

  Definition dtree_map : dtree X -> dtree Y.
  Proof.
    induction 1 as [ n x _ w ].
    exact ⟨f x|vec_set w⟩.
  Defined.

  Fact dtree_map_fix n x (v : vec (dtree X) n) : dtree_map ⟨x|v⟩ = ⟨f x|vec_map dtree_map v⟩.
  Proof. rewrite <- vec_set_map; auto. Qed.

End dtree_map.

Tactic Notation "dtree" "discr" hyp(H) :=
  (  (apply dtree_cons_inj in H as (? & _); lia)
  || (apply dtree_cons_inj in H as (? & ? & _); eq refl; easy) ).

Tactic Notation "dtree" "discr" :=
  try (repeat
    match goal with
      | H: _ = _ :> dtree _ |- _ => (dtree discr H || clear H)
    end; fail).

Tactic Notation "dtree" "inj" hyp(H) :=
  let e := fresh
  in  apply dtree_cons_inj in H as (e & H); eq refl;
      destruct H as [ H <- ]; try clear e.
