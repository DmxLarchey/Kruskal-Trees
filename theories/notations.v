(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List.

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

