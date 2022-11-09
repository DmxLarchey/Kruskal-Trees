(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL B FREE SOFTWARE LICENSE AGREEMENT           *)
(**************************************************************)

From Coq
  Require Import Arith List.

(** For lists *)

Arguments In {_}.
Arguments app {_}.

#[global] Infix "∈" := In (at level 70, no associativity).
#[global] Notation "⌊ l ⌋" := (length l) (at level 0, l at level 200, format "⌊ l ⌋").

#[global] Notation "P '⊆₁' Q" := (forall x, P x -> Q x) (at level 70, no associativity, format "P  ⊆₁  Q").
#[global] Notation "P '⊆₂' Q" := (forall x y, P x y -> Q x y) (at level 70, no associativity, format "P  ⊆₂  Q").

#[global] Notation "P '∪₁' Q" := (fun x => P x \/ Q x) (at level 1, no associativity, format "P ∪₁ Q").
#[global] Notation "P '∪₂' Q" := (fun x y => P x y \/ Q x y) (at level 1, no associativity, format "P ∪₂ Q").
#[global] Notation "P '∩₁' Q" := (fun x => P x /\ Q x) (at level 1, no associativity, format "P ∩₁ Q").
#[global] Notation "P '∩₂' Q" := (fun x y => P x y /\ Q x y) (at level 1, no associativity, format "P ∩₂ Q").

#[global] Notation "Q '∘' P" := (fun x z => exists y, P x y /\ Q y z) (at level 1, left associativity, format "Q ∘ P").

#[global] Notation plus_assoc := Nat.add_assoc.
#[global] Notation le_plus_l := Nat.le_add_l.
#[global] Notation le_plus_r := Nat.le_add_r.

#[global] Notation le_trans := Nat.le_trans.
#[global] Notation lt_le_trans := Nat.lt_le_trans.
#[global] Notation lt_0_Sn := Nat.lt_0_succ.
#[global] Notation lt_n_S := (fun n m => proj1 (Nat.succ_lt_mono n m)).
#[global] Notation lt_S_n := (fun n m => proj2 (Nat.succ_lt_mono n m)).


