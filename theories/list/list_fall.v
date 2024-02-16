(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import List Arith.

From KruskalTrees
  Require Import notations.

Import ListNotations.

Set Implicit Arguments.

Fact Forall_cons_inv X (P : X -> Prop) (x : X) l : 
       Forall P (x::l) <-> P x /\ Forall P l.
Proof.
  split.
  + inversion 1; eauto.
  + constructor; tauto.
Qed.

Arguments Forall2_nil {_ _ _}.
Arguments Forall2_cons {_ _ _ _ _ _ _}.

Section Forall2.

  Variables (X Y : Type).

  Implicit Types (P Q : X -> Y -> Prop).

  (** A explicit term here is better for nested fixpoints like ltree_product_embed_ind in tree/ltree.v *)

  Definition Forall2_mono {P Q} (HPQ : P ⊆₂ Q) : Forall2 P ⊆₂ Forall2 Q :=
    fix loop l m Hlm :=
      match Hlm return Forall2 Q _ _ with
        | Forall2_nil        => Forall2_nil
        | Forall2_cons H1 H2 => Forall2_cons (HPQ _ _ H1) (loop _ _ H2)
      end.

  Fact Forall2_length P l m : Forall2 P l m -> ⌊l⌋ = ⌊m⌋.
  Proof. induction 1; simpl; auto. Qed.

  Fact Forall2_in_left_inv P l m :
       Forall2 P l m -> forall x, x ∈ l -> exists y, y ∈ m /\ P x y.
  Proof.
    induction 1 as [ | x y l m H1 H2 IH2 ]; simpl; try tauto.
    intros z [ <- | Hz ]; eauto.
    apply IH2 in Hz as (k & ? & ?); eauto.
  Qed.

  Fact Forall2_cons_inv P x l y m : Forall2 P (x::l) (y::m) <-> P x y /\ Forall2 P l m.
  Proof.
    split.
    + inversion 1; tauto.
    + intros []; constructor; auto.
  Qed.

  Local Fact Forall2_rev_rec P l m : Forall2 P l m -> Forall2 P (rev l) (rev m).
  Proof.
    induction 1; simpl; auto.
    apply Forall2_app; simpl; auto.
  Qed.

  Fact Forall2_rev P l m : Forall2 P (rev l) (rev m) <-> Forall2 P l m.
  Proof.
    split.
    + intros H; apply Forall2_rev_rec in H; revert H.
      rewrite !rev_involutive; auto.
    + apply Forall2_rev_rec.
  Qed.

End Forall2.

Fact Forall2_Forall X (R : X -> X -> Prop) l :
      Forall2 R l l <-> Forall (fun x => R x x) l.
Proof.
  induction l.
  + split; constructor.
  + rewrite Forall2_cons_inv, Forall_cons_inv; tauto.
Qed.

Fact Forall2_conj X Y (R T : X -> Y -> Prop) l m :
      Forall2 (R∩₂T) l m <-> Forall2 R l m /\ Forall2 T l m.
Proof.
  split.
  + induction 1; split; constructor; tauto.
  + intros (H1 & H2); revert H1 H2.
    induction 1; inversion 1; auto.
Qed.

Fact Forall2_xchg X Y (R : X -> Y -> Prop) l m :
      Forall2 R l m <-> Forall2 (fun x y => R y x) m l.
Proof. split; induction 1; auto. Qed.

Fact Forall2_in_right_inv X Y (P : X -> Y -> Prop) l m :
      Forall2 P l m -> forall y, y ∈ m -> exists x, x ∈ l /\ P x y.
Proof.
  rewrite Forall2_xchg; intros H y Hy.
  now apply Forall2_in_left_inv with (2 := Hy) in H.
Qed.

Fact Forall2_eq X l m : Forall2 (@eq X) l m <-> l = m.
Proof.
  split.
  + induction 1; subst; auto.
  + intros []; induction l; simpl; auto.
Qed.

Fact Forall2_map_right X Y Z (R : X -> Z -> Prop) (f : Y -> Z) l m :
      Forall2 R l (map f m) <-> Forall2 (fun x y => R x (f y)) l m.
Proof.
  split.
  + revert m; induction l as [ | x l IHl ]; intros [ | y m ]; intros H; try (inversion H; fail); auto.
    simpl in H; apply Forall2_cons_inv in H as []; constructor; auto.
  + induction 1; simpl; auto.
Qed.

Fact Forall2_map_left X Y Z (R : Y -> Z -> Prop) (f : X -> Y) l m :
      Forall2 R (map f l) m <-> Forall2 (fun x z => R (f x) z) l m.
Proof. rewrite Forall2_xchg, Forall2_map_right, Forall2_xchg; tauto. Qed.

Fact Forall2_comp X Y Z (P : X -> Y -> Prop) (Q : Y -> Z -> Prop) l m k :
      Forall2 P l m -> Forall2 Q m k -> Forall2 Q∘P l k.
Proof.
  intros H; revert H k.
  induction 1; auto; inversion 1; subst; eauto.
Qed.

Fact Forall2_equiv X Y (R T : X -> Y -> Prop) l m :
       (forall x y, R x y <-> T x y)
    -> Forall2 R l m <-> Forall2 T l m.
Proof. intros E; split; apply Forall2_mono; intros ? ?; apply E. Qed.

Fact forall_ex_Forall2 X Y (R : X -> Y -> Prop) l :
       (forall x, x ∈ l -> ex (R x))
    -> ex (Forall2 R l).
Proof.
  induction l as [ | x l IHl ]; intros Hl.
  + exists nil; auto.
  + destruct (Hl x) as (y & Hy); simpl; auto.
    destruct IHl as (m & Hm).
    * intros; apply Hl; simpl; auto.
    * exists (y::m); auto.
Qed.

Fact Forall2_Forall_left X Y (P : Y -> Prop) l m :
      Forall2 (fun _ : X => P) l m -> Forall P m.
Proof. induction 1; eauto. Qed.

Fact forall_sig_Forall2 X Y (R : X -> Y -> Prop) l :
      (forall x, x ∈ l -> sig (R x)) -> sig (Forall2 R l).
Proof.
  induction l as [ | x l IHl ]; intros Hl.
  + exists nil; auto.
  + destruct (Hl x) as (y & Hy); simpl; auto.
    destruct IHl as (m & Hm).
    * intros; apply Hl; simpl; auto.
    * exists (y::m); auto.
Qed.

Fact forall_sigT_Forall2 X Y (R : X -> Y -> Prop) l :
      (forall x, x ∈ l -> sigT (R x)) -> sig (Forall2 R l).
Proof.
  intros H; apply forall_sig_Forall2.
  intros x Hx; destruct (H _ Hx); eauto.
Qed.

Fact Forall_sig X (P : X -> Prop) l :
      Forall P l -> { m : list (sig P) | l = map (@proj1_sig _ _) m }.
Proof.
  induction l as [ | x l IHl ].
  + exists nil; auto.
  + intros H.
    destruct IHl as (m & Hm).
    * inversion H; auto.
    * apply Forall_cons_inv in H as [ Hx ? ].
      exists (exist _ x Hx::m); subst; auto.
Qed.

Tactic Notation "Forall" "reif" hyp(H) "as" simple_intropattern(P) :=
  match type of H with
    | forall _, _ ∈ _ -> ex _ => apply forall_ex_Forall2 in H as P
    | forall _, _ ∈ _ -> sig _ => apply forall_sig_Forall2 in H as P
    | forall _, _ ∈ _ -> sigT _ => apply forall_sigT_Forall2 in H as P
  end.
