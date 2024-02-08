(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL B FREE SOFTWARE LICENSE AGREEMENT           *)
(**************************************************************)

(* Following a discussion on Coq-Zulip

    https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/Problem.20with.20nested.20fixpoints/near/309498019

   we implement the nested short lex(icographic) order on list based rose-trees
   and show that it is a (strongly) total strict order on those trees, but
   however it is NOT well-founded as we expose a strictly decreasing sequence *)

From Coq
  Require Import Arith List Lia Wellfounded Utf8.

From KruskalTrees
  Require Import notations tactics list_utils rtree.

Import ListNotations rtree_notations.

Set Implicit Arguments.

#[local] Reserved Notation "l '<lex' m " (at level 70, no associativity, format "l  <lex  m").
#[local] Reserved Notation "l '<slex' m " (at level 70, no associativity, format "l  <slex  m").
#[local] Reserved Notation "l '<rlex' m " (at level 70, no associativity, format "l  <rlex  m").

Section measure_rect.

  Variable (X : Type) (m : X → nat) (P : X → Type).

  Hypothesis F : ∀x, (∀y, m y < m x → P y) → P x.

  Definition measure_rect x : P x.
  Proof.
    cut (Acc (fun x y => m x < m y) x); [ revert x | ].
    + refine (
        fix loop x Dx := @F x (fun y Dy => loop y _)
      ).
      apply (Acc_inv Dx), Dy.
    + apply wf_inverse_image with (f := m), lt_wf.
  Qed.

End measure_rect.

Tactic Notation "induction" "on" hyp(x) "as" ident(IH) "with" "measure" uconstr(f) :=
  pattern x; revert x; apply measure_rect with (m := fun x => f); intros x IH.

Definition order_stotal {X} (R : X → X → Prop) :=
     (∀ x y, { R x y } + { x = y } + { R y x }).

Section order.

  Context {X : Type}.

  Implicit Type (l m : list X).

  Definition list_shorter l m := ⌊l⌋ < ⌊m⌋.

  Fact list_shorter_wf : well_founded list_shorter.
  Proof. unfold list_shorter; apply wf_inverse_image, lt_wf. Qed.

  Variable (R : X → X → Prop).

  Inductive list_lex : list X -> list X -> Prop :=
    | list_lex_init x y l m : R x y → ⌊l⌋ = ⌊m⌋ → x::l <lex y::m
    | list_lex_cons x l m : l <lex m → x::l <lex x::m
  where "l <lex m" := (list_lex l m).

  Fact list_lex_length l m : l <lex m → ⌊l⌋ = ⌊m⌋.
  Proof. induction 1; simpl; f_equal; auto. Qed.

  Fact list_lex_inv l m :
        l <lex m 
      → match m with 
        | []   => False
        | y::m =>
          match l with
          | []   => False
          | x::l => R x y ∧ ⌊l⌋ = ⌊m⌋ 
                  ∨ x = y ∧ l <lex m
          end
        end.
  Proof. destruct 1; eauto. Qed.

  Section list_lex_irrefl.

    Local Fact list_lex_irrefl_rec l m : l <lex m → l = m → ∃x, x ∈ l ∧ R x x.
    Proof.
      induction 1 as [ x y l m H1 H2 | x l m H IH ].
      + inversion 1; subst; simpl; eauto.
      + inversion 1; subst.
        destruct IH as (? & ? & ?); simpl; eauto.
    Qed.

    Fact list_lex_irrefl l : l <lex l → ∃x, x ∈ l ∧ R x x.
    Proof. intros H; apply list_lex_irrefl_rec with (1 := H); auto. Qed.

  End list_lex_irrefl.

  Lemma list_lex_trans l m k :
          (∀ x y z, x ∈ l → y ∈ m → z ∈ k → R x y → R y z → R x z)
        → l <lex m → m <lex k → l <lex k.
  Proof.
    intros H1 H2; revert H2 k H1.
    induction 1 as [ x y l m H1 H2 | x l m H IH ]; intros k HR Hk.
    + apply list_lex_inv in Hk.
      destruct k as [ | z k ]; try easy.
      destruct Hk as [ [H3 H4] | [[] H4]].
      * constructor 1; eauto; try lia.
        revert H1 H3; apply HR; simpl; auto.
      * constructor 1; auto.
        apply list_lex_length in H4; lia.
    + apply list_lex_inv in Hk.
      destruct k as [ | z k ]; try easy.
      destruct Hk as [ [H3 H4] | [[] H4]].
      * constructor 1; auto.
        apply list_lex_length in H; lia.
      * constructor 2.
        apply IH; auto.
        intros ? ? ? ? ? ?; apply HR; simpl; auto.
  Qed.

  Lemma list_lex_stotal l m : 
          ⌊l⌋ = ⌊m⌋
        → (∀ x y, x ∈ l → y ∈ m → { R x y } + { x = y } + { R y x })
        → { l <lex m } + { l = m } + { m <lex l }.
  Proof.
    revert m; induction l as [ | x l IHl ]; intros [ | y m ]; try discriminate; simpl; intros E H; auto.
    apply f_equal with (f := pred) in E; simpl in E.
    destruct (H x y) as [ [ Hxy | <- ] | Hxy ]; auto.
    + do 2 left; constructor 1; auto.
    + destruct (IHl _ E) as [ [ H1 | <- ] | H1 ].
      * intros; apply H; auto.
      * do 2 left; constructor 2; auto.
      * left; right; auto.
      * right; constructor 2; auto.
    + right; constructor 1; auto.
  Qed.

  Hypothesis (Rwf : well_founded R). 

  Lemma list_lex_wf : well_founded list_lex.
  Proof.
    intros m; induction on m as IHm with measure (length m).
    destruct m as [ | y m ].
    + constructor; intros l Hl; apply list_lex_inv  in Hl; easy.
    + induction y as [ y IHy' ] using (well_founded_induction Rwf) in m, IHm |- *.
      assert (Acc list_lex m) as Hm by (apply IHm; simpl; auto).
      assert (forall x l, R x y -> length l = length m -> Acc list_lex (x::l)) as IHy.
      1: { intros x l Hx Hl; apply IHy'; auto.
           intros; apply IHm.
           simpl in *; rewrite <- Hl; auto. }
      clear IHy' IHm.
      induction Hm as [ m Hm IHm ] in IHy |- *.
      constructor; intros l Hl. 
      apply list_lex_inv in Hl; destruct l as [ | x l ]; try tauto.
      destruct Hl as [ (Hx & Hlm) | (-> & Hl) ].
      * apply IHy; auto.
      * apply IHm; auto.
        apply list_lex_length in Hl as ->; auto.
  Qed.

  Definition list_short_lex l m := ⌊l⌋ < ⌊m⌋ ∨ l <lex m.

  Infix "<slex" := list_short_lex.

  Lemma list_short_lex_irrefl l : l <slex l → ∃x, x ∈ l ∧ R x x.
  Proof.
    intros [ H | H ]; try lia.
    revert H; apply list_lex_irrefl.
  Qed.

  Lemma list_short_lex_trans l m k : 
        (∀ x y z, x ∈ l → y ∈ m → z ∈ k → R x y → R y z → R x z)
      → l <slex m -> m <slex k -> l <slex k.
  Proof.
    intros H0 [H1|H1] [H2|H2].
    + constructor 1; lia.
    + apply list_lex_length in H2; constructor 1; lia.
    + apply list_lex_length in H1; constructor 1; lia.
    + constructor 2; eapply list_lex_trans; eauto.
  Qed.

  Lemma list_short_lex_stotal l m :
       (∀ x y, x ∈ l → y ∈ m → { R x y } + { x = y } + { R y x })
     → { list_short_lex l m } + { l = m } + { list_short_lex m l }.
  Proof.
    intros Hlm.
    destruct (lt_eq_lt_dec (length l) (length m)) as [ [| E] |].
    + do 2 left; constructor 1; auto.
    + destruct list_lex_stotal with (1 := E) as [[|[]]|]; auto.
      * do 2 left; constructor 2; auto.
      * right; constructor 2; auto.
    + right; constructor 1; auto.
  Qed.

  Lemma list_short_lex_wf : well_founded list_short_lex.
  Proof.
    intros m.
    induction on m as IH with measure (length m).
    induction m as [ m IHm ] using (well_founded_induction list_lex_wf).
    constructor; intros l [ Hl | Hl ]; auto.
    apply IHm; auto.
    apply list_lex_length in Hl as ->; eauto.
  Qed.

End order.

#[local] Hint Constructors list_lex : core.

(** This is the nested list short lex order *)

Unset Elimination Schemes.

Inductive rtree_slex : rtree → rtree → Prop :=
  | rtree_slex_intro l m : l <slex m → ⟨l⟩ᵣ <rlex ⟨m⟩ᵣ
where "r <rlex s" := (rtree_slex r s)
and "l <slex m" := (list_short_lex rtree_slex l m).

Set Elimination Schemes.

#[local] Hint Constructors rtree_slex : core.

(** A versatile non-dependent induction principle for rtree_slex 
    but we do ot use it below *)

Section rtree_slex_ind.

  Variables (P : rtree → rtree → Prop)
            (HP : ∀ l m, l <slex m → list_short_lex P l m → P ⟨l⟩ᵣ ⟨m⟩ᵣ).

  Fixpoint rtree_slex_ind l m (H : l <rlex m) { struct H } : P l m.
  Proof.
    destruct H as [ l m H ]; apply HP; destruct H as [ H | H ].
    + constructor 1; trivial.
    + right; induction H; eauto.
    + constructor 1; trivial.
    + constructor 2; induction H.
      * constructor 1; trivial. 
        apply rtree_slex_ind, H.
      * constructor 2; trivial.
  Qed.

End rtree_slex_ind.

(* However we use the inversion lemma below *)
Fact rtree_slex_inv r t : 
        rtree_slex r t
      → match r, t with
          | ⟨l⟩ᵣ, ⟨m⟩ᵣ => l <slex m
        end.
Proof. now destruct 1. Qed.

(** rtree_slex is a strongly total strict order:
     - it is irreflexive and transitive
     - one can computationally decide r <rlex t or r = t or t <rlex r *)

Theorem rtree_slex_irrefl t : ¬ t <rlex t.
Proof. red; induction t; intros (? & ? & ?)%rtree_slex_inv%list_short_lex_irrefl; eauto. Qed.

Theorem rtree_slex_trans r s t : r <rlex s → s <rlex t → r <rlex t.
Proof.
  revert s t; induction r as [ l IHl ]; intros [m] [p] H1%rtree_slex_inv H2%rtree_slex_inv.
  constructor.
  revert H1 H2; apply list_short_lex_trans; eauto.
Qed.

Theorem rtree_slex_stotal : order_stotal rtree_slex.
Proof.
  intros r.
  induction r as [ l IH ]; intros [ m ].
  destruct (list_short_lex_stotal rtree_slex l m) as [ [|[]] | ];auto.
Qed.

(** However rtree_slex is NOT well-founded because [x,y] > [[x,y]] > [[[x,y]] ... *)

Fixpoint rtree_decr_seq n :=
  match n with
    | 0 => ⟨[⟨[]⟩ᵣ;⟨[]⟩ᵣ]⟩ᵣ
    | S n => ⟨[rtree_decr_seq n]⟩ᵣ
  end.

Fact rtree_decr_seq_spec n : rtree_decr_seq (S n) <rlex rtree_decr_seq n.
Proof.
  induction n as [ | n IHn ]; simpl.
  + simpl; constructor; constructor 1; simpl; auto.
  + simpl; constructor; constructor 2; auto.
Qed.
