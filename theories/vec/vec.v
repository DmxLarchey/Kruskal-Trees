(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Stdlib
  Require Import Arith List Lia Eqdep_dec Utf8.

From Stdlib
  Require Vector.

From KruskalTrees
  Require Import notations tactics idx.

Set Implicit Arguments.

Import idx_notations.

#[local] Reserved Notation "v ⦃ p ⦄" (at level 1, format "v ⦃ p ⦄").
#[local] Reserved Notation "x '##' y" (at level 60, right associativity).
#[local] Reserved Notation "x '∈ᵥ' v" (at level 70, format "x  ∈ᵥ  v").
#[local] Reserved Notation "'⦑' i ',' v '⦒'"  (at level 0, format "⦑ i , v ⦒").

Notation vec := Vector.t.
Notation vec_nil := Vector.nil.
Notation vec_cons := Vector.cons.

Arguments vec_nil {A}.
Arguments vec_cons {A} _ {n}.

#[local] Notation "∅" := vec_nil.
#[local] Infix "##" := vec_cons.

Create HintDb vec_db.

Section vec_invert.

  Variable X : Type.

  (** General induction principle for vec 0 and vec (S n).
      Following Smaller inversions by JF Monin (TYPES 2022)
    *)

  Inductive vec_shape_O : vec X 0 → Set :=
    | vec_shape_O_nil : vec_shape_O ∅.

  Inductive vec_shape_S {n} : vec X (S n) → Type :=
    | vec_shape_S_cons x v : vec_shape_S (x##v).

  Definition vec_invert_t {n} : vec X n → Type :=
    match n with
    | 0   => vec_shape_O
    | S n => vec_shape_S
    end.

  Definition vec_invert {n} v : @vec_invert_t n v :=
    match v return vec_invert_t v with
    | ∅    => vec_shape_O_nil
    | x##v => vec_shape_S_cons x v
    end.

  Definition vec_head n (v : vec X (S n)) :=
    match vec_invert v with
      | vec_shape_S_cons x _ => x
    end.

  Definition vec_tail n (v : vec X (S n)) :=
    match vec_invert v with
    | vec_shape_S_cons _ w => w
    end.

  Fact vec_head_tail n (v : vec X (S n)) : v = vec_head v##vec_tail v.
  Proof. now destruct (vec_invert v). Qed.

End vec_invert.

Arguments vec_head {_ _} _ /.
Arguments vec_tail {_ _} _ /.

Tactic Notation "vec" "invert" hyp(v) :=
  destruct (vec_invert v).

Tactic Notation "vec" "invert" hyp(v) "as" simple_intropattern(x) ident(w) :=
  destruct (vec_invert v) as [ x w ].

Section vec_in.

  Variable X : Type.

  (** vector membership, via an inductive definition, to allow for
      nesting in other induction definitions (strict positivity) *)

  Inductive vec_in x : ∀n, vec X n → Prop :=
    | vec_in_hd n (v : vec _ n)   :          x ∈ᵥ x##v
    | vec_in_tl n y (v : vec _ n) : x ∈ᵥ v → x ∈ᵥ y##v
  where "x ∈ᵥ v" := (vec_in x v).

  Hint Constructors vec_in : core.

  Fact vec_in_inv x n (v : vec _ n) :
         x ∈ᵥ v
       → match v with
         | ∅    => False
         | y##v => x = y \/ x ∈ᵥ v
         end.
  Proof. induction 1; auto. Qed.

  Fact vec_in_nil_inv x (v : vec X 0) : x ∈ᵥ v ↔ False.
  Proof. split; inversion 1. Qed.

  Fact vec_in_cons_inv x y n (v : vec _ n) : x ∈ᵥ y##v ↔ x = y ∨ vec_in x v.
  Proof.
    split.
    + apply vec_in_inv.
    + intros [ <- | ]; constructor; auto.
  Qed.

End vec_in.

Arguments vec_in {_} _ {_} _.

#[local] Notation "x ∈ᵥ v" := (vec_in x v).
#[global] Hint Constructors vec_in : vec_db.

(* 𝕆𝕊 λ ∀∃ → ↔ ∧ ∨ *)

Section vec_prj.

  Variable (X : Type).

  (** A nice implementation is *critical* here when using nested defs
      Notice that idx_O_rect is implemented with

                   match _ : Empty_set with end

      which allows vec_prj v p to be recognized as a sub-term of v *)

  Fixpoint vec_prj n (v : vec _ n) : idx n → X :=
    match v with
    | ∅    => idx_O_rect _
    | x##v => λ i,
      match idx_S_inv i with
      | None   => x
      | Some j => v⦃j⦄
      end
    end
  where "v ⦃ i ⦄" := (@vec_prj _ v i).

  (** The following fixpoint equations hold *by reduction*
      and v⦃i⦄ is effectivelly recognised as a sub-term of v
      by the guardness checker of Coq, so you can implement
      recursive fixpoint calls on these, for instance
      using vec in trees. *)

  Goal ∀n x (v : vec _ n),   (x##v)⦃𝕆⦄   = x.   Proof. reflexivity. Qed.
  Goal ∀n x (v : vec _ n) i, (x##v)⦃𝕊 i⦄ = v⦃i⦄. Proof. reflexivity. Qed.

  (** unlike idx n → X, vectors in vec X n are equal
      iff there components are *)

  Fact vec_prj_ext n (v w : vec X n) : (∀p, v⦃p⦄ = w⦃p⦄) → v = w.
  Proof.
    revert v w; induction n as [ | n IHn ]; intros v w.
    + vec invert v; vec invert w; trivial.
    + vec invert v as x v.
      vec invert w as y w.
      intros H; f_equal.
      * apply (H 𝕆).
      * apply IHn; intros; apply (H (𝕊 _)).
  Qed.

  Variable (n : nat).

  Fact vec_prj_fix_1 (v : vec X (S n)) : v⦃𝕆⦄ = vec_head v.
  Proof. now vec invert v as ? v. Qed.

  Fact vec_prj_fix_2 (v : vec X (S n)) p : v⦃𝕊 p⦄ = (vec_tail v)⦃p⦄.
  Proof. now vec invert v as ? v. Qed.

  Definition vec_nxt := vec_prj_fix_2.

  Fact vec_in_iff_prj x v : @vec_in X x n v ↔ ∃p, x = v⦃p⦄.
  Proof.
    split.
    + induction 1 as [ n v | n y v _ (p & Hp) ].
      * now exists 𝕆.
      * now exists (𝕊 p).
    + intros (p & ->).
      revert v p; induction n; intros v p;
        idx invert p; vec invert v as ? v; simpl; eauto with vec_db.
  Qed.

End vec_prj.

Arguments vec_prj {X n}.
#[local] Notation "v ⦃ i ⦄" := (vec_prj v i).

Tactic Notation "vec" "ext" "with" ident(p) :=
  apply vec_prj_ext; intros p.

Tactic Notation "vec" "ext" :=
  apply vec_prj_ext; intro.

Section vec_basics.

  Variable X : Type.

  (** Inversion lemmas for v _ 0 and vec _ (S n)

      Beware that the vec invert tactic is the preferred choice
   *)

  Fact vec_0_inv (v : vec X 0) : v = ∅.
  Proof. now vec invert v. Qed.

  Fact vec_S_inv n (v : vec X (S n)) : { x : _ & { w | v = x##w } }.
  Proof. now vec invert v as x w; eauto. Qed.

  (** vec_cons is injective *)

  Fact vec_cons_inj n x y (v w : vec X n) : x##v = y##w → x = y ∧ v = w.
  Proof.
     intros H; split.
     + now apply f_equal with (f := vec_head) in H.
     + now apply f_equal with (f := vec_tail) in H.
  Qed.

  (**    vec_prj : vec X n → (idx n → X)
     and vec_set : (idx n → X) → vec X n *)

  Fixpoint vec_set n : (idx n → X) → vec X n :=
    match n return (idx n → _) → vec _ n with
      | 0   => λ _, ∅
      | S n => λ f, f 𝕆##vec_set (fun p => f (𝕊 p))
    end.

  Fact vec_prj_set n (f : idx n → X) p : (vec_set f)⦃p⦄  = f p.
  Proof.
    revert f p; induction n as [ | n IHn ]; intros g p; idx invert p; auto.
    apply IHn.
  Qed.

  Fact vec_set_prj n v : @vec_set n (vec_prj v) = v.
  Proof. now vec ext; rewrite vec_prj_set. Qed.

  (** From vectors to lists *)

  Fixpoint vec_list n (v : vec X n) : list X :=
    match v with
      | ∅    => nil
      | x##v => x::vec_list v
    end.

  Fact vec_list_length n v : length (@vec_list n v) = n.
  Proof. induction v; simpl; f_equal; auto. Qed.

  Fact vec_list_idx n (v : vec X n) : vec_list v = map (vec_prj v) (idx_list n).
  Proof. induction v; simpl; f_equal; rewrite map_map; auto. Qed.

  Fact in_vec_list n v x : In x (@vec_list n v) ↔ ∃i, v⦃i⦄ = x.
  Proof.
    induction v as [ | n y v IH ]; simpl.
    * split; try tauto; intros (p & _); idx invert p.
    * split.
      + intros [ H | H ].
        - exists idx_fst; auto.
        - rewrite IH in H.
          destruct H as (p & Hp); exists (idx_nxt p); auto.
      + intros (p & Hp); idx invert p; auto.
        rewrite IH; firstorder.
  Qed.

  Fixpoint list_vec l : vec X ⌊l⌋ :=
    match l return vec X ⌊l⌋ with
      | nil  => ∅
      | x::l => x##list_vec l
    end.

  Fact vec_list_vec l : vec_list (list_vec l) = l.
  Proof. induction l; simpl; f_equal; auto. Qed.

  Fact list_vec_sig l : { n : nat & { v : vec _ n | vec_list v = l } }.
  Proof. exists (length l), (list_vec l); apply vec_list_vec. Qed.

  Fact list_vec_list n v : ∃e, v↺e = list_vec (@vec_list n v).
  Proof.
    induction v as [ | n x v (e & IHv) ]; simpl.
    + exists eq_refl; auto.
    + revert e IHv.
      generalize (vec_list v).
      intros l ->; simpl; intros ->.
      exists eq_refl; auto.
  Qed.

  Fact vec_list_split_inv n v l x r :
        @vec_list n v = l++x::r → { i | v⦃i⦄ = x /\ idx2nat i = ⌊l⌋ }.
  Proof.
    revert l x r.
    induction v as [ | n x v IHv ].
    + now intros [] ? ?.
    + intros [ | y l ] z r; simpl.
      * inversion 1; exists idx_fst; auto.
      * intros H; injection H; clear H; intros H1 <-.
        apply IHv in H1 as (p & H1 & H2).
        exists (idx_nxt p); split; simpl; auto.
  Qed.

  (** vector append *)

  Fixpoint vec_app n (v : vec X n) m (w : vec X m) : vec X (n+m) :=
    match v with
      | ∅    => w
      | x##v => x##vec_app v w
    end.

  Fact vec_app_idx_left n v m w p : (@vec_app n v m w)⦃idx_left _ p⦄ = v⦃p⦄.
  Proof. induction v; idx invert p; auto. Qed.

  Fact vec_app_idx_right n v m w p : (@vec_app n v m w)⦃idx_right _ p⦄ = w⦃p⦄.
  Proof. induction v; simpl; auto. Qed.

End vec_basics.

#[export] Hint Rewrite vec_prj_set vec_app_idx_left vec_app_idx_right : vec_db.

Tactic Notation "vec" "rew" := autorewrite with vec_db.

(* 𝕆𝕊 λ ∀∃ → ↔ ∧ ∨ *)

Section vec_map.

  Variables (X Y : Type) (f : X → Y).

  Fixpoint vec_map n (v : vec X n) : vec Y n :=
    match v with
      | ∅    => ∅
      | x##v => f x##vec_map v
    end.

  Fact vec_prj_map n v : ∀i : idx n, (vec_map v)⦃i⦄ = f v⦃i⦄.
  Proof. induction v; intro; idx invert all; auto. Qed.

  Fact vec_list_map n v : vec_list (@vec_map n v) = map f (vec_list v).
  Proof. induction v; simpl; f_equal; auto. Qed.

End vec_map.

#[export] Hint Rewrite vec_prj_map : vec_db.

Arguments vec_map {_ _} _ {_} _.

Fact vec_set_map X Y f n v : vec_set (fun i => f v⦃i⦄) = @vec_map X Y f n v.
Proof. now vec ext; vec rew. Qed.

Fact vec_map_map X Y Z (f : X -> Y) (g : Y -> Z) n (v : vec X n) :
    vec_map g (vec_map f v) = vec_map (fun x => g (f x)) v.
Proof. induction v; simpl; f_equal; auto. Qed.

Section lvec_hvec.

  Variable X : Type.

  (* isomorphic to list X but with length pre-computed *)

  Inductive lvec : Type :=
    | lvec_pack n : vec X n → lvec.

  Definition lvec_len l :=
    match l with
      | @lvec_pack n _ => n
    end.

  Definition lvec_vec l : vec _ (lvec_len l) :=
    match l with
      | lvec_pack v => v
    end.

  Fact lvec_pair_eq l : l = @lvec_pack (lvec_len l) (lvec_vec l).
  Proof. destruct l; auto. Qed.

  Definition hvec := vec lvec.

  Fixpoint hvec_size n (w : hvec n) :=
    match w with
      | ∅ => 0
      | v##w => 1+(lvec_len v+hvec_size w)
    end.

  Fact hvec_size_ge n w : n <= @hvec_size n w.
  Proof. induction w as [  | [] ]; simpl; tlia. Qed.

End lvec_hvec.

Arguments lvec_pack {X} n v.

Module vec_notations.

  Notation "∅" := vec_nil.
  Notation "x ## v" := (vec_cons x v).
  Notation "v ⦃ p ⦄" := (vec_prj v p).
  Notation "x ∈ᵥ v" := (@vec_in _ x _ v).
  Notation "⦑ i , v ⦒" := (lvec_pack i v).

End vec_notations.

Import vec_notations.

Theorem vec_eq_dec_ext X n (u v : vec X n) :
       (forall i, { u⦃i⦄ = v⦃i⦄ } + { u⦃i⦄ <> v⦃i⦄ })
    -> { u = v } + { u <> v }.
Proof.
  induction u as [ | x n u IH ] in v |- *.
  + vec invert v; eauto.
  + vec invert v as y v; intros H.
    destruct (H 𝕆) as [ C | C ]; simpl in C; subst.
    2: now right; contradict C; apply vec_cons_inj in C.
    specialize (fun i => H (𝕊 i)); simpl in H.
    apply IH in H as [ <- | C ]; auto.
    now right; contradict C; apply vec_cons_inj in C.
Qed.

Definition lvec_map {X Y} f v := match v with ⦑n,v⦒ => ⦑n,@vec_map X Y f n v⦒ end.

Section vec_reif.

  (** Finitary choice functions *)

  Variable (n : nat) (X : Type) (R : idx n → X → Prop).

  Fact vec_reif : (∀p, ∃x, R p x) → ∃v, ∀p, R p v⦃p⦄.
  Proof.
    intros H; idx reif H as (f & Hf).
    exists (vec_set f).
    now intro; vec rew.
  Qed.

  Fact vec_reif_t : (∀p, { x | R p x }) → { v | ∀p, R p v⦃p⦄ }.
  Proof.
    intros H; idx reif H as (f & Hf).
    exists (vec_set f).
    now intro; vec rew.
  Qed.

  Definition vec_reif_tt : (∀p, { x : _ & R p x }) → { v | ∀p, R p v⦃p⦄ }.
  Proof. intro; apply vec_reif_t; firstorder. Qed.

End vec_reif.

Tactic Notation "vec" "reif" hyp(H) "as" simple_intropattern(P) :=
  match type of H with
  | ∀_ : idx _, ex _ => apply vec_reif in H as P
  | ∀_ : idx _, sig _ => apply vec_reif_t in H as P
  | ∀_ : idx _, sigT _ => apply vec_reif_tt in H as P
  end.

Section vec_cond_reif.

  Variable (X Y : Type) (P : Y → Prop) (f : X → Y)
           (P_inv : ∀y, P y → { x | f x = y}).

  Fact vec_cond_reif n (w : vec _ n) :
      (∀i, P w⦃i⦄) → { v | vec_map f v = w }.
  Proof.
    intros H.
    generalize (fun i => P_inv (H i)); intros H'.
    vec reif H' as (v & Hv).
    exists v.
    now vec ext; vec rew.
  Qed.

End vec_cond_reif.

Section vec_fall.

  Variable (X : Type) (P : X → Prop).

  Definition vec_fall n (v : vec _ n) := ∀i, P v⦃i⦄.

  Fact vec_fall_nil : vec_fall ∅.
  Proof. intro; idx invert all. Qed.

  Fact vec_fall_cons n x (v : vec _ n) : P x → vec_fall v → vec_fall (x##v).
  Proof. intros H1 H2 p; idx invert p; auto. Qed.

  Hint Resolve vec_fall_nil vec_fall_cons : core.

  Fact vec_fall_nil_iff (v : vec _ 0) : vec_fall v ↔ True.
  Proof. vec invert v; split; auto. Qed.

  Fact vec_fall_cons_iff n x (v : vec _ n) : vec_fall (x##v) ↔ P x ∧ vec_fall v.
  Proof. unfold vec_fall; rewrite forall_idx_Sn; simpl; tauto. Qed.

  Section vec_fall_rect.

    Variables (Q : ∀n, vec _ n → Type)
              (Qnil : Q ∅)
              (Qcons : ∀n x (v : vec _ n), vec_fall v → Q v → Q (x##v)).

    Theorem vec_fall_rect n (v : vec _ n) : vec_fall v -> Q v.
    Proof.
      induction v as [ | n x v IH ]; intros H; auto.
      apply vec_fall_cons_iff in H as []; auto.
    Qed.

  End vec_fall_rect.

End vec_fall.

#[global] Hint Resolve vec_fall_nil vec_fall_cons : vec_db.

Section vec_fall2.

  Variables (X Y : Type) (R : X → Y → Prop).

  Definition vec_fall2 n (u : vec _ n) v := ∀i, R u⦃i⦄ v⦃i⦄.

  Fact vec_fall2_nil (v w : vec _ 0) : vec_fall2 v w.
  Proof. intro; idx invert all. Qed.

  Fact vec_fall2_cons n x (v : vec _ n) y w :
        R x y → vec_fall2 v w → vec_fall2 (x##v) (y##w).
  Proof. intros ? ? p; idx invert p; auto. Qed.

  Hint Resolve vec_fall2_nil vec_fall2_cons : core.

  Fact vec_fall2_cons_inv n x (v : vec _ n) y w :
         vec_fall2 (x##v) (y##w) ↔ R x y ∧ vec_fall2 v w.
  Proof.
    split.
    + intros H; split.
      * apply (H idx_fst).
      * intro; apply (H (idx_nxt _)).
    + intros []; apply vec_fall2_cons; auto.
  Qed.

  Section vec_fall2_rect.

    Variable (P : ∀n, vec X n → vec Y n → Type)
             (HP0 : P ∅ ∅)
             (HP1 : ∀ n x y v w, R x y → vec_fall2 v w → @P n v w → P (x##v) (y##w)).

    Fact vec_fall2_rect n : ∀ v w : vec _ n, vec_fall2 v w → P v w.
    Proof.
      induction n as [ | n IHn ]; intros v w.
      + vec invert v; vec invert w; auto.
      + vec invert v as x v; vec invert w as y w; intros Hw.
        apply vec_fall2_cons_inv in Hw as []; auto.
    Qed.

  End vec_fall2_rect.

End vec_fall2.

#[global] Hint Resolve vec_fall2_nil vec_fall2_cons : vec_db.

Fact vec_fall2_swap X Y R n u v :
     @vec_fall2 X Y R n u v → vec_fall2 (λ x y, R y x) v u.
Proof. induction 1 using vec_fall2_rect; auto with vec_db. Qed.






