(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL B FREE SOFTWARE LICENSE AGREEMENT           *)
(**************************************************************)

From Coq
  Require Import Arith List Lia Eqdep_dec.

From KruskalTrees
  Require Import notations.

Set Implicit Arguments.

(** Utilities *)

(* Try lia *)

Ltac tlia := try abstract lia.

(* split a goal A1 /\ ... /\ An with rsplit n *)

Ltac rsplit n :=
  match n with
    | 0 => idtac
    | S ?n => split; [ | rsplit n ]
  end.

(* with a goal ..., H : A, ... |- B, replace it with ... |- A = B *)

Ltac replace_with H :=
  match goal with [ G : ?h |- ?c ] => match H with G => cutrewrite (c = h); [ exact H | f_equal ] end end.

Tactic Notation "eq" "goal" hyp(H) :=
  match goal with
    |- ?b => match type of H with ?t => replace b with t; auto end
  end.

Tactic Notation "equiv" "with" uconstr(equiv) :=
  match goal with
    | |- _ -> _ => let H := fresh in intro H; try apply equiv in H; try apply equiv; revert H
  end.

(* dealing with casts on nat *)

Fact eq_refl_nat (x : nat) (H : x = x) : H = eq_refl.
Proof. apply UIP_dec, eq_nat_dec. Qed.

#[global] Notation "v ↺ e" := (eq_rect _ _ v _ e) (at level 1, format "v ↺ e").

Tactic Notation "eq" "refl" :=
  repeat match goal with
    | e: ?x = ?x, H: context[_↺?t] |- _ =>
    match e with t => rewrite (eq_refl_nat e) in H; simpl in H end
    | e: ?x = ?y, H: context[_↺?t] |- _ =>
    match e with t => (subst x || subst y); simpl in H end
    | e: ?x = ?x |- context[_↺?t] =>
    match e with t => rewrite (eq_refl_nat e); simpl end
    | e: ?x = ?y |- context[_↺?t] =>
    match e with t => (subst x || subst y); simpl end
  end.

Fact eq_sigT_inj (X : nat -> Type) i (x : X i) j (y : X j) :
        existT _ i x = existT _ j y -> exists e : i = j, x↺e = y.
Proof.
  inversion 1; subst j.
  apply inj_pair2_eq_dec in H; subst.
  + exists eq_refl; auto.
  + apply eq_nat_dec.
Qed.

(* logical equivalences are congruences *)

Fact and_equiv A A' B B' : A <-> A' -> B <-> B' -> A /\ B <-> A' /\ B'.
Proof. tauto. Qed.

Fact or_equiv A A' B B' : A <-> A' -> B <-> B' -> A \/ B <-> A' \/ B'.
Proof. tauto. Qed.

