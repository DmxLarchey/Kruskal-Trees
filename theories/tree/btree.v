(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL B FREE SOFTWARE LICENSE AGREEMENT           *)
(**************************************************************)

From KruskalTrees
  Require Import idx vec.

Import idx_notations vec_notations.

Set Implicit Arguments.

Section btree.

  Variable (k : nat).

  (* Undecorated trees of width bounded by k *)

  Unset Elimination Schemes.

  Inductive btree := btree_cons n : vec btree n -> n < k -> btree.

  Set Elimination Schemes.

  Section btree_rect.

    Variable (P : btree -> Type)
             (HP : forall n v h, (forall i, P v⦃i⦄) -> P (@btree_cons n v h)).

    Fixpoint btree_rect t : P t :=
      match t with
        | btree_cons v h => HP v h (fun p => btree_rect v⦃p⦄)
      end.

  End btree_rect.

  Definition btree_ind (P : _ -> Prop) := btree_rect P.

End btree.
