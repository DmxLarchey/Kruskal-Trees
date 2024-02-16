(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Coq
  Require Import Arith Lia List.

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

(** We use lia to avoid incompatibilities between Coq <= 8.15.2 and Coq >= 8.16 
    DLW: I know this is a like a tank to crush a fly but it is more compatible
         than the other options *)
Definition plus_assoc n m p : n + (m + p) = n + m + p.      Proof. lia. Qed.
Definition le_plus_l n m : n <= n + m.                      Proof. lia. Qed.
Definition le_plus_r n m : m <= n + m.                      Proof. lia. Qed.
Definition le_trans n m p : n <= m -> m <= p -> n <= p.     Proof. lia. Qed.
Definition lt_le_trans n m p : n <= m -> m <= p -> n <= p.  Proof. lia. Qed.
Definition lt_0_Sn n : 0 < S n.                             Proof. lia. Qed.
Definition lt_n_S n m : n < m -> S n < S m.                 Proof. lia. Qed.
Definition lt_S_n n m : S n < S m -> n < m.                 Proof. lia. Qed.


