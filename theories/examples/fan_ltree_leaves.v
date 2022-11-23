(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL B FREE SOFTWARE LICENSE AGREEMENT           *)
(**************************************************************)

From Coq
  Require Import List Utf8.

From KruskalTrees
  Require Import notations tactics list_utils ltree.

Import ListNotations ltree_notations.

Set Implicit Arguments.

Definition list_is_nil {X} (l : list X) : { l = [] } + { l ≠ [] }.
Proof. now destruct l; [ left | right ]. Qed.

Fact list_cons_inj {X} (x : X) l y m : x::l = y::m ↔ x = y /\ l = m.
Proof. 
  split. 
  + now inversion 1.
  + now intros (-> & ->). 
Qed.

Fact Forall2_right_Forall X Y (P : Y -> Prop) (l : list X) m : 
     Forall2 (λ _ y, P y) l m ↔ ⌊l⌋ = ⌊m⌋ ∧ Forall P m.
Proof.
  split.
  + split.
    * eapply Forall2_length; eauto.
    * induction H; eauto.
  + intros (H1 & H2); revert H2 l H1.
    induction 1 as [ | y m IH ]; intros [ | x l ]; try easy; simpl; intros H.
    constructor; auto.
Qed.

#[local] Hint Resolve in_eq in_cons : core.

Arguments ltree_node {_}.
Arguments ltree_sons {_}.

Section filter.

  Context {X : Type} (b : X → list (ltree X) → bool).

  (* The list of nodes of a ltree X in prefix order, filtered by 
     the Boolean test b *)
  Fixpoint ltree_filter (t : ltree X) : list X :=
    match t with
      | ⟨x|l⟩ₗ => let m := flat_map ltree_filter l
                  in if b x l then x :: m else m
    end.

End filter.

Section leaves_nodes.

  Context {X : Type}.

  Let f (_ : X) (l : list (ltree X)) := match l with [] => true | _ => false end.

  (* This collects the leaves in a tree, left to right *)
  Definition ltree_leaves := ltree_filter f.

  Fact ltree_leaves_nil x : ltree_leaves ⟨x|[]⟩ₗ = [x].
  Proof. reflexivity. Qed.
  
  Fact ltree_leaves_not_nil x l : 
      l ≠ [] → ltree_leaves ⟨x|l⟩ₗ = flat_map ltree_leaves l.
  Proof. simpl; unfold f; now destruct l. Qed.

  Let g (x : X) (_ : list (ltree X)) := true.

  (* This collects all the nodes in a tree, prefix order *)
  Definition ltree_nodes := ltree_filter g.

  Fact ltree_nodes_fix x l : ltree_nodes ⟨x|l⟩ₗ = x :: flat_map ltree_nodes l.
  Proof. reflexivity. Qed.

  Fact ltree_node_nodes t : ltree_node t ∈ ltree_nodes t.
  Proof. destruct t; simpl; auto. Qed.

End leaves_nodes.

#[local] Hint Resolve ltree_node_nodes : core.

Section build_fan.

  (** Below f : X → list X described a finitary FAN
      which generates a process of (eg reduction). This
      process terminates for the nodes x which
      are accessible for the relation R := λ u v, u ∈ f v

      a) on those nodes we compute the a rose-tree in ltree X
         collecting all the reduction process upto irreducibles
         (ie f x = [])
      b) then we collect the leaves of this ltree X to
         get the list of irreducibles.

      c) assuming R is well founded, we define
         the list of all irreducible values generated
         by the reduction of x as irred x
      d) we characterize irred with the fixpoint equations:
         - f x = [] → irred x = [x]
         - f x ≠ [] → irred x = flat_map irred (f x). *)

  Variables (X : Type) (f : X → list X).

  Let R := λ u v, u ∈ f v.

  Definition fan := ltree_fall (λ x l, f x = map ltree_node l).

  (* A fan for f is a ltree X such that at every node ⟨x|l⟩ₗ 
     the list of label of each son (ie map ltree_node l) is
     exactly f x *) 
  Fact fan_fix x l : 
       fan ⟨x|l⟩ₗ ↔ f x = map ltree_node l ∧ Forall fan l.
  Proof. unfold fan at 1; rewrite ltree_fall_fix, Forall_forall; split; auto. Qed.

  Fact fan_spec_nil t : fan t → f (ltree_node t) = [] → ltree_leaves t = [ltree_node t].
  Proof.
    induction 1 as [ x l Hx Hl _ ] using ltree_fall_rect; intros H.
    simpl in H; rewrite Hx in H; destruct l; easy.
  Qed.

  Fact fan_spec_not_nil t : fan t → f (ltree_node t) ≠ [] → ltree_leaves t = flat_map ltree_leaves (ltree_sons t).
  Proof.
    induction 1 as [ x l Hx Hl _ ] using ltree_fall_rect; intros H.
    destruct (list_is_nil l) as [ -> | Hl' ].
    1: exfalso; apply H; auto.
    simpl in H.
    rewrite ltree_leaves_not_nil; auto.
  Qed.

  (* Notice that a fan may not exists, but if it exists, all its nodes are in (Acc R) *)
  Fact fan_Acc t : fan t → ∀ x, x ∈ ltree_nodes t → Acc R x.
  Proof.
    induction 1 as [ x l Hx Hl IH ] using ltree_fall_rect; simpl; intros y Hy.
    destruct Hy as [ <- | Hy ].
    + constructor; intros y Hyx; red in Hyx.
      rewrite Hx, in_map_iff in Hyx.
      destruct Hyx as (t & <- & Ht).
      apply (IH t); auto.
    + apply in_flat_map in Hy as (t & H1 & H2).
      apply (IH t); auto.
  Qed.

  (* The fan is a unique characterization *)
  Fact fan_uniq t1 t2 : fan t1 → fan t2 → ltree_node t1 = ltree_node t2 → t1 = t2.
  Proof.
    intros H1 H2; revert H1 t2 H2.
    induction 1 as [ x l1 Hx Hl1 IH ] using ltree_fall_rect; intros [ y l2 ].
    fold fan in Hl1; apply Forall_forall in Hl1.
    rewrite fan_fix; simpl; intros [ H1 H2 ] <-; f_equal.
    rewrite Hx, <- Forall2_eq, Forall2_map_right, Forall2_map_left in H1.
    clear x Hx Hl1; revert l1 l2 H1 IH H2.
    induction 1 as [ | x y l1 l2 H1 H2 IH2 ]; auto. 
    intros H3 [H4 H5]%Forall_cons_iff; f_equal.
    + apply H3; auto.
    + apply IH2; auto.
  Qed.

  (* A fan at x is a fan with root node labeled by x *)
  Definition fan_at x t := ltree_node t = x ∧ fan t.

  (* The fan_at x is unique *)
  Fact fan_at_uniq x t1 t2 : fan_at x t1 → fan_at x t2 → t1 = t2.
  Proof.
    intros (H1 & H2) (<- & H4).
    revert H2 H4 H1; apply fan_uniq.
  Qed.

  (* It is sufficient for x to be accessible so that we can build 
     a fan_at x.

     We build the fan_at by Acc_rect induction, knowing that
     f x contains only R-smaller values (this is f_R) *)
  Theorem build_fan_at x : Acc R x → { t | fan_at x t }.
  Proof.
    induction 1 as [ x _ IHx ] using Acc_rect.
    apply forall_sig_Forall2 in IHx as (m & Hm).
    destruct (list_is_nil (f x)) as [ Hfx | Hfx ].
    + exists ⟨x|[]⟩ₗ; split; simpl; split; tauto.
    + exists ⟨x|m⟩ₗ; split; auto.
      rewrite fan_fix.
      apply Forall2_conj in Hm as [ H1 H2 ].
      split.
      * rewrite <- Forall2_eq, Forall2_map_right.
        revert H1; apply Forall2_mono; eauto.
      * apply Forall2_right_Forall in H2; tauto.
  Qed.

  (* A fan_at x exists iff x is R-accessible *)
  Corollary fan_at_iff x : ex (fan_at x) ↔ Acc R x.
  Proof.
    split.
    + intros (t & <- & ?); apply fan_Acc with t; auto. 
    + intros Hx; destruct (build_fan_at Hx); eauto.
  Qed.

  (* Now we assume R is well-founded so a fan can always be computed *)
  Hypothesis hf : well_founded R.

  Let FAN x : sig (fan_at x).
  Proof. apply build_fan_at, hf. Qed.

  (* The irreductible elements generated by x as collected
     in the leaves of a fan_at x *)
  Definition irred x := ltree_leaves (proj1_sig (FAN x)).

  Lemma irred_nil x : f x = [] → irred x = [x].
  Proof.
    unfold irred.
    destruct (FAN x) as (t & <- & H2); simpl.
    now apply fan_spec_nil.
  Qed.

  Lemma irred_not_nil x : f x ≠ [] → irred x = flat_map irred (f x).
  Proof.
    unfold irred at 1.
    destruct (FAN x) as (t & <- & H2); simpl; intros H.
    rewrite fan_spec_not_nil, !flat_map_concat_map; auto.
    f_equal.
    destruct t as [ x l ]; simpl in H |- *.
    apply fan_fix in H2 as (-> & H2).
    rewrite Forall_forall in H2.
    rewrite map_map.
    apply map_ext_in_iff.
    unfold irred.
    intros t Ht.
    destruct (FAN (ltree_node t)) as (t' & H'); simpl.
    f_equal.
    apply fan_at_uniq with (ltree_node t); auto.
    split; auto.
  Qed.

End build_fan.

Check irred.
Check irred_nil.
Check irred_not_nil.

