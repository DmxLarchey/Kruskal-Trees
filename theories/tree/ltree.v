(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import Arith List Lia.

From KruskalTrees
  Require Import notations tactics list_utils.

Import ListNotations.

Set Implicit Arguments.

#[local] Reserved Notation "'⟨' x '|' l '⟩ₗ'" (at level 0, l at level 200, format "⟨ x | l ⟩ₗ").

Section ltree.

  Variable (X : Type).

  Unset Elimination Schemes.

  Inductive ltree : Type :=
    | ltree_cons : X -> list ltree -> ltree.

  Set Elimination Schemes.

  Notation "⟨ x | l ⟩ₗ" := (ltree_cons x l).

  Definition ltree_node t := match t with ⟨x|_⟩ₗ => x end.
  Definition ltree_sons t := match t with ⟨_|l⟩ₗ => l end.

  Fact ltree_cons_inj x l y m : ⟨x|l⟩ₗ = ⟨y|m⟩ₗ -> x = y /\ l = m.
  Proof.
    intros H; split.
    + now apply f_equal with (f := ltree_node) in H.
    + now apply f_equal with (f := ltree_sons) in H.
  Qed.

  Section ltree_rect.

    (** The subtree relations between nodes and their sons *)

    Let is_subtree s t := s ∈ ltree_sons t.

    (* Same proof as below, but ltac style *)
    Local Fact is_subtree_wf_ltac : well_founded is_subtree.
    Proof.
      refine (fix is_subtree_wf_ltac t { struct t } := _).
      constructor; destruct t as [ x l ].
      cbn; clear x. 
      intros s Hs.
      induction l as [ | r l IHl ].
      + destruct Hs.                (* match Hs with end *)
      + destruct Hs as [ e | Hs ].  (* match Hs with or_intro ... end *)
        * (* Beware calling is_subtree_wf_ltac on r, sub-term of l, NOT on s *)
          subst s.                  (* match e with eq_refl => ... end *)
          exact (is_subtree_wf_ltac r).
        * exact (IHl Hs).           (* sons_wf _ _ Hs *)
    Qed.

    (** The is_subtree relation is well_founded.
        The proof critically uses a nested fixpoint *)
    Let is_subtree_wf : well_founded is_subtree :=
      fix is_subtree_wf t : Acc is_subtree t :=
        Acc_intro t ((fix sons_wf l :=
          match l return forall r, r ∈ l -> _ with
            | []   => fun _ Hs => match Hs with end
            | r::l => fun s Hs =>
            match Hs with
              | or_introl e    => match e with eq_refl => is_subtree_wf r end
              | or_intror Hs   => sons_wf _ _ Hs
            end
          end) (ltree_sons t)).

    Variable (P : ltree -> Type)
             (HP : forall x l, (forall t, t ∈ l -> P t) -> P ⟨x|l⟩ₗ).

    (** Now the recursor on tree, by well founded induction using <ist *)

    Let Fixpoint ltree_Acc_rect t (a : Acc is_subtree t) : P t :=
      match t return Acc is_subtree t -> P t with
        | ⟨x|l⟩ₗ => fun a => HP _ _ (fun _ h => ltree_Acc_rect (Acc_inv a h))
      end a.

    Arguments ltree_Acc_rect : clear implicits.

    (** And we combine the recursor with well-foundedness *)

    Definition ltree_rect t : P t := ltree_Acc_rect t (is_subtree_wf t).

    Section ltree_rect_fix.

      Hypothesis HP_ext : forall x l f g, (forall x Hx, f x Hx = g x Hx) -> HP x l f = HP x l g.

      (** The Acc based recursor is proof-irrelevant *)

      Local Fixpoint ltree_Acc_rect_eq t a a' : ltree_Acc_rect t a = ltree_Acc_rect t a'.
      Proof.
        destruct a; destruct a'; destruct t; simpl.
        apply HP_ext.
        intros; apply ltree_Acc_rect_eq.
      Qed.

      (** From which we deduce the fixpoint equation *)

      Lemma ltree_rect_fix x l : ltree_rect ⟨x|l⟩ₗ = HP x l (fun t _ => ltree_rect t).
      Proof.
        unfold ltree_rect; destruct (is_subtree_wf ⟨x|l⟩ₗ); simpl.
        apply HP_ext.
        intros; apply ltree_Acc_rect_eq.
      Qed.

    End ltree_rect_fix.

  End ltree_rect.

  Definition ltree_rec (P : _ -> Set) := ltree_rect P.
  Definition ltree_ind (P : _ -> Prop) := ltree_rect P.

  Section ltree_eq_dec.

    (** As an application of ltree_rect, the discreteness of
        ltree X follows from that of X *)

    Hypothesis eqX_dec : forall x y : X, { x = y } + { x <> y }.

    Theorem ltree_eq_dec (t₁ t₂ : ltree) : { t₁ = t₂ } + { t₁ <> t₂ }.
    Proof.
      revert t₂; induction t₁ as [ x ll IH ]; intros [ y mm ].
      destruct (eqX_dec x y) as [ <- | H1 ].
      2: now right; contradict H1; inversion H1.
      destruct (list_eq_dect ll mm) as [ <- | H2 ]; auto.
      now right; contradict H2; inversion H2.
    Qed.

  End ltree_eq_dec.

  Section ltree_recursion.

    (** A non-dependent recursor for trees, using a direct nested fixpoint,
        the nesting occurs with the external (list) map function *)

    Variable (Y : Type) (f : X -> list ltree -> list Y -> Y).

    Fixpoint ltree_recursion (t : ltree) : Y :=
      match t with
        | ⟨x|l⟩ₗ => f x l (map ltree_recursion l)
      end.

  End ltree_recursion.

  Section ltree_fall_exst.

    Variable (P Q : X -> list ltree -> Prop).

    Definition ltree_fall : ltree -> Prop.
    Proof.
      induction 1 as [ x l lP ] using ltree_recursion.
      exact (P x l /\ forall h, h ∈ lP -> h).
    Defined.

    Fact ltree_fall_fix x l : ltree_fall ⟨x|l⟩ₗ <-> P x l /\ forall t, t ∈ l -> ltree_fall t.
    Proof.
      clear Q.
      simpl; apply and_equiv; try tauto; split.
      + intros H t Hl.
        apply H, in_map_iff; exists t; auto.
      + intros H h; rewrite in_map_iff.
        intros (t & <- & ?); auto.
    Qed.

    Definition ltree_exst : ltree -> Prop.
    Proof.
      induction 1 as [ x l lQ ] using ltree_recursion.
      exact (Q x l \/ exists h, h ∈ lQ /\ h).
    Defined.

    Fact ltree_exst_fix x l : ltree_exst ⟨x|l⟩ₗ <-> Q x l \/ exists t, t ∈ l /\ ltree_exst t.
    Proof.
      clear P.
      simpl; apply or_equiv; try tauto; split.
      + intros (? & (? & <- & ?)%in_map_iff & ?); eauto.
      + intros (t & H1 & H2).
        exists (ltree_exst t); split; trivial.
        apply in_map_iff; eauto.
    Qed.

    Section ltree_fall_rect.

      Variables (K : ltree -> Type)
                (HK : forall x l, P x l
                               -> (forall t, t ∈ l -> ltree_fall t)
                               -> (forall t, t ∈ l -> K t)
                               -> K ⟨x|l⟩ₗ).

      Theorem ltree_fall_rect t : ltree_fall t -> K t.
      Proof.
        induction t as [ x l IH ]; intros H.
        rewrite ltree_fall_fix in H; destruct H; auto.
      Qed.

    End ltree_fall_rect.

    Section ltree_fall_exst.

      Hypothesis HPQ : forall x l, P x l \/ Q x l.

      Fact ltree_fall_exst t : ltree_fall t \/ ltree_exst t.
      Proof.
        induction t as [ x l IH ].
        apply list_choice in IH as [ Hl | (t & Ht & Hl) ];
          [ destruct (HPQ x l) as [ H | H ] | ].
        1: left; apply ltree_fall_fix; auto.
        all: right; apply ltree_exst_fix; eauto.
      Qed.

    End ltree_fall_exst.

    Section ltree_fall_exst_t.

      Hypothesis HPQ : forall x l, { P x l } + { Q x l }.

      Fact ltree_fall_exst_t t : { ltree_fall t } + { ltree_exst t }.
      Proof.
        induction t as [ x l IH ].
        apply list_choice_t in IH as [ Hl | (t & Ht & Hl) ];
          [ destruct (HPQ x l) as [ H | H ] | ].
        1: left; apply ltree_fall_fix; auto.
        all: right; apply ltree_exst_fix; eauto.
      Qed.

    End ltree_fall_exst_t.

    Section ltree_fall_exst_absurd.

      Hypothesis HPQ : forall x l, P x l -> Q x l -> False.

      Fact ltree_fall_exst_absurd t : ltree_fall t -> ltree_exst t -> False.
      Proof.
        induction 1 as [ x l Hx Hl IHl ] using ltree_fall_rect.
        intros [ | (? & ? & ?) ]%ltree_exst_fix; eauto.
      Qed.

    End ltree_fall_exst_absurd.

  End ltree_fall_exst.

  Section ltree_weight.

    Variable (w : X -> nat).

    Implicit Type l : list ltree.

    Definition ltree_weight : ltree -> nat.
    Proof.
      apply ltree_recursion.
      exact (fun x _ m => w x+list_sum (fun x => x) m).
    Defined.

    Fact ltree_weight_fix x l : ltree_weight ⟨x|l⟩ₗ = w x + list_sum ltree_weight l.
    Proof.
      unfold ltree_weight at 1; simpl; f_equal.
      clear x; induction l; simpl; auto.
    Qed.

    Fact ltree_weight_0_fall t : ltree_weight t = 0 -> ltree_fall (fun x _ => w x = 0) t.
    Proof.
      induction t as [ x l IHl ]; rewrite ltree_weight_fix, ltree_fall_fix; split; tlia.
      intros t Ht.
      apply IHl; auto.
      generalize (list_sum_in ltree_weight _ _ Ht); lia.
    Qed.

    Fact ltree_weight_0_exst t : ltree_weight t = 0 -> ltree_exst (fun x _ => w x = 0) t.
    Proof. induction t; rewrite ltree_weight_fix, ltree_exst_fix; lia. Qed.

    Hypothesis (Hw : forall x, 0 < w x).

    Fact ltree_weight_gt t : 0 < ltree_weight t.
    Proof.
      destruct t as [ x l ]; rewrite ltree_weight_fix.
      generalize (Hw x); lia.
    Qed.

  End ltree_weight.

End ltree.

Fact ltree_fall_dec X (P : X -> list (ltree X) -> Prop) :
        (forall x l, { P x l } + { ~ P x l })
     -> (forall t, { ltree_fall P t } + { ~ ltree_fall P t }).
Proof.
  intros H t.
  apply ltree_fall_exst_t with (t := t) in H.
  destruct H as [ H | H ]; auto.
  right; intros H1; revert H1 H.
  apply ltree_fall_exst_absurd; auto.
Qed.

Module ltree_notations.

  Notation "⟨ x | l ⟩ₗ" := (ltree_cons x l).

End ltree_notations.

Import ltree_notations.



