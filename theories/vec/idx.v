(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

#[warning="-warn-library-file-stdlib-vector"]
From Stdlib
  Require Import List Arith Fin Utf8.

From KruskalTrees
  Require Import notations.

Import ListNotations.

(* The type of indices [0,...,n-1] with a fixpoint compatible inversion lemma *)

Set Implicit Arguments.

(** We use the type Fin.t of the standard library but
    with another name and our own tools *)

Abbreviation idx := t.
Abbreviation idx_fst := F1.
Abbreviation idx_nxt := FS.

Abbreviation 𝕆 := idx_fst.
Abbreviation 𝕊 := idx_nxt.

(* 𝕆𝕊 ∀ → *)

Section idx_rect.

  (* This comes from an original idea of JF Monin
     on Smaller inversions (TYPES 2022) *)

  (* In Set to force not being automatically 
     transfered from Type to Prop *)
  Inductive idx_shape_O : idx 0 → Set := .

  Inductive idx_shape_S {n} : idx (S n) → Type :=
    | idx_shape_S_fst : idx_shape_S 𝕆
    | idx_shape_S_nxt i : idx_shape_S (𝕊 i).

  Let idx_invert_t n : idx n → Type :=
    match n with
    | O   => idx_shape_O
    | S n => idx_shape_S
    end.

  Definition idx_invert {n} (i : idx n) : idx_invert_t i :=
    match i with
    | 𝕆   => idx_shape_S_fst
    | 𝕊 i => idx_shape_S_nxt i
    end.

  Definition idx_O_rect X (i : idx 0) : X :=
    match idx_invert i with end.

  Variables (n : nat)
            (P : idx (S n) → Type)
            (P_0 : P 𝕆)
            (P_S : ∀i, P (𝕊 i)).

  Definition idx_S_rect i : P i :=
    match idx_invert i with
      | idx_shape_S_fst => P_0
      | idx_shape_S_nxt i => P_S i
    end.

End idx_rect.

Arguments idx_invert {_} _ /.
Arguments idx_S_rect {_ _} _ _ _ /.

Tactic Notation "idx" "invert" hyp(i) :=
  match type of i with
    | idx 0     => destruct (idx_invert i)
    | idx (S _) => destruct (idx_invert i) as [ | i ]
  end; simpl.

Tactic Notation "idx" "invert" "all" :=
  repeat match goal with
    | i : idx 0 |- _=> idx invert i
    | i : idx (S _) |- _ => idx invert i
  end.

Module idx_notations.

  Abbreviation idx₀ := 𝕆 (only parsing).
  Abbreviation idx₁ := (𝕊 idx₀) (only parsing).
  Abbreviation idx₂ := (𝕊 idx₁) (only parsing).

  Tactic Notation "invert" "idx" hyp(i) := idx invert i.

End idx_notations.

Import idx_notations.

Local Fact Some_inj X (x y : X) : Some x = Some y → x = y.
Proof. now inversion 1. Qed.

Section idx_nxt_inj.

  Variable (n : nat).

  Definition idx_S_inv : idx (S n) → option (idx n) := idx_S_rect None Some.

  Fact idx_S_inv_fst : idx_S_inv 𝕆 = None.            Proof. reflexivity. Qed.
  Fact idx_S_inv_nxt i : idx_S_inv (𝕊 i) = Some i.    Proof. reflexivity. Qed.

  Fact idx_nxt_inj (i j : idx n) (H : 𝕊 i = 𝕊 j) : i = j.
  Proof. now apply f_equal with (f := idx_S_inv), Some_inj in H. Qed.

End idx_nxt_inj.

Arguments idx_S_inv {_} i /.

(* 𝕆𝕊 ∀∃ → *)

(** That one works because we have finitely many choices *)

Fact idx_reif_dep n (X : idx n → Type) (R : ∀i, X i → Prop) : (∀i, ∃x, R i x) → ∃f, ∀i, R i (f i).
Proof.
  induction n as [ | n IHn ] in X, R |- *; intros HR.
  + exists (fun p => idx_O_rect (X p) p); intro; idx invert all.
  + destruct (IHn _ (fun p => R (𝕊 p))) as (f & Hf); eauto.
    destruct (HR idx₀) as (x & Hx).
    exists (idx_S_rect x f); intros p; idx invert p; auto.
Qed.

Fact reif_t_dep I (X : I → Type) (R : ∀i, X i → Prop) : (∀i, sig (R i)) → { f | ∀i, R i (f i) }.
Proof.
  intros H.
  exists (fun p => proj1_sig (H p)).
  apply (fun p => proj2_sig (H p)).
Qed.

Fact reif_tt_dep I (X : I → Type) (R : ∀i, X i → Type) : (∀i, sigT (R i)) → { f : _ & ∀i, R i (f i) }.
Proof.
  intros H.
  exists (fun p => projT1 (H p)).
  apply (fun p => projT2 (H p)).
Qed.

Fact idx_reif X n (R : idx n → X → Prop) : (∀i, ∃x, R i x) → ∃f, ∀i, R i (f i).      Proof. apply idx_reif_dep. Qed.
Fact reif_t I X (R : I → X → Prop) : (∀i, sig (R i)) → { f | ∀i, R i (f i) }.        Proof. apply reif_t_dep. Qed.
Fact reif_tt I X (R : I → X → Type) : (∀i, sigT (R i)) → { f : _ & ∀i, R i (f i) }.  Proof. apply reif_tt_dep. Qed.

Tactic Notation "idx" "reif" hyp(H) "as" simple_intropattern(P) :=
  match type of H with
    | forall _ : idx _, ex _   => apply idx_reif_dep in H as P
    | forall _ : idx _, sig _  => apply reif_t_dep   in H as P
    | forall _ : idx _, sigT _ => apply reif_tt_dep  in H as P
  end.

Section finite.

  Fixpoint idx_list n : list (idx n) :=
    match n with
      | 0   => []
      | S n => 𝕆 :: map 𝕊 (idx_list n)
    end.

  Fact idx_list_length n : length (idx_list n) = n.
  Proof. induction n; simpl; auto; f_equal; rewrite map_length; auto. Qed.

  Fact idx_list_In n p : p ∈ idx_list n.
  Proof.
    induction p as [ | n p ]; simpl; auto.
    right; apply in_map_iff; exists p; auto.
  Qed.

  Fact idx_finite_t n : { l : list (idx n) | ∀i, i ∈ l }.
  Proof. exists (idx_list n); apply idx_list_In. Qed.

  Fact idx_finite n : ∃l : list (idx n), ∀i, i ∈ l.
  Proof. exists (idx_list n); apply idx_list_In. Qed.

End finite.

Section decide.

  Hint Resolve idx_nxt_inj : core.

  Fact idx_eq_dec n (p q : idx n) : { p = q } + { p <> q }.
  Proof.
    induction p as [ | n p IHp ] in q |- *; idx invert all; auto; try (right; easy).
    destruct (IHp q); subst; auto.
  Qed.

End decide.

Fact forall_idx_Sn n (P : idx (S n) → Prop) :
        (∀i, P i) ↔ P 𝕆 ∧ ∀i, P (𝕊 i).
Proof.
  split.
  + intros H; split; auto.
  + intros [] p; idx invert p; auto.
Qed.

Section idx_left_right.

  (** The injections:
         idx_left  : idx n -> idx (n+m)
         idx_right : idx m -> idx (n+m)
      and the surjection
         idx_sum : idx (n+m) -> idx n + idx m

      together with the equations *)

  Fixpoint idx_left n m (i : idx n) : idx (n+m) :=
    match i with
      | 𝕆     => 𝕆
      | 𝕊 i => 𝕊 (@idx_left _ m i)
    end.

  Fixpoint idx_right n m (i : idx m) : idx (n+m) :=
    match n with
      | 0   => i
      | S n => 𝕊 (idx_right n i)
    end.

  Fixpoint idx_sum {n m} : idx (n+m) → (idx n + idx m)%type :=
    match n with
      | 0   => fun i => inr i
      | S n => fun i =>
        match idx_S_inv i with
          | None   => inl 𝕆
          | Some j =>
          match idx_sum j with
            | inl k => inl (𝕊 k)
            | inr k => inr k
          end
        end
    end.

  Fact idx_left_right_sum n m p :
    match @idx_sum n m p with
      | inl q => p = idx_left _ q
      | inr q => p = idx_right _ q
    end.
  Proof.
    induction n; simpl in *; auto; idx invert p; auto.
    specialize (IHn p); destruct (idx_sum p); subst; simpl; auto.
  Qed.

  Fact idx_sum_left n m p : idx_sum (@idx_left n m p) = inl p.
  Proof. induction p as [ | ? ? IH ]; simpl; auto; now rewrite IH. Qed.

  Fact idx_sum_right n m p : idx_sum (@idx_right n m p) = inr p.
  Proof. induction n as [ | ? IH ]; simpl; auto; now rewrite IH. Qed.

End idx_left_right.

Section idx2nat.

  (** The bijection idx <-> [0,n[ *)

  Fixpoint idx2nat {n} (i : idx n) : nat :=
    match i with
      | 𝕆 => 0
      | 𝕊 i => S (idx2nat i)
    end.

  Fact idx2nat_lt n (i : idx n) : idx2nat i < n.
  Proof.
    induction i; simpl.
    + apply lt_0_Sn.
    + now apply lt_n_S.
  Qed.

  Fact idx2nat_inj n : ∀ i j : idx n, idx2nat i = idx2nat j → i = j.
  Proof.
    induction n as [ | n IHn ]; intros; idx invert all; try easy.
    f_equal; apply IHn, eq_add_S; auto.
  Qed.

  Section nat2idx.

    Local Fact nat2idx_pwc n : ∀p, p < n → { q : idx n | p = idx2nat q }.
    Proof.
      induction n as [ | n IHn ].
      + intros ? H; exfalso; revert H; apply Nat.nlt_0_r.
      + intros [ | i ] Hi.
        * exists idx_fst; auto.
        * destruct (IHn _ (lt_S_n _ _ Hi)) as (q & ->).
          now exists (idx_nxt q).
    Qed.

    Context {n : nat}.

    Definition nat2idx {i} Hi := proj1_sig (@nat2idx_pwc n i Hi).

    Fact nat2idx_spec i Hi : i = idx2nat (@nat2idx i Hi).
    Proof. apply (proj2_sig (nat2idx_pwc _)). Qed.

    Fact idx2nat2idx i Hi : idx2nat (@nat2idx i Hi) = i.
    Proof. symmetry; apply nat2idx_spec. Qed.

    Fact nat2idx2nat (j : idx n) : nat2idx (idx2nat_lt j) = j.
    Proof. apply idx2nat_inj; rewrite idx2nat2idx; auto. Qed.

  End nat2idx.

End idx2nat.

Section idx_emb.

  (** The embedding idx n -> idx m with n <= m *)

  Context {n m : nat} (Hnm : n <= m).

  Let emb k : k < n -> k < m :=
    λ Hkn, lt_le_trans _ _ _ Hkn Hnm.

  Definition idx_emb (i : idx n) : idx m :=
    nat2idx (emb (idx2nat_lt i)).

  Fact idx2nat_emb i : idx2nat i = idx2nat (idx_emb i).
  Proof.
    unfold idx_emb.
    generalize (idx2nat i) (emb (idx2nat_lt i)).
    intros; rewrite idx2nat2idx; auto.
  Qed.

End idx_emb.





