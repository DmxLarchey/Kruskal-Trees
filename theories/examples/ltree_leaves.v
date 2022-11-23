(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL B FREE SOFTWARE LICENSE AGREEMENT           *)
(**************************************************************)

From Coq
  Require Import Arith List Lia.

From KruskalTrees
  Require Import notations tactics list_utils ltree.

Import ListNotations ltree_notations.

Set Implicit Arguments.

Section filter.

  Context {X : Type} (f : X -> list (ltree X) -> bool).

  Fixpoint ltree_filter (t : ltree X) : list X :=
    match t with
      | ⟨x|l⟩ₗ => let m := flat_map ltree_filter l
                  in if f x l then x :: m else m
    end.

End filter.

Section leaves.

  Context {X : Type}.

  Let f (_ : X) (l : list (ltree X)) := match l with [] => true | _ => false end.

  (* This collects the leaves in a tree *)
  Definition ltree_leaves := ltree_filter f.

  Fact ltree_leaves_nil x : ltree_leaves ⟨x|[]⟩ₗ = [x].
  Proof. reflexivity. Qed.
  
  Fact ltree_leaves_not_nil x l : 
      l <> [] -> ltree_leaves ⟨x|l⟩ₗ = flat_map ltree_leaves l.
  Proof. simpl; unfold f; now destruct l. Qed.

End leaves.

Arguments ltree_node {_}.

Definition list_is_nil {X} (l : list X) : { l = [] } + { l <> [] }.
Proof. now destruct l; [ left | right ]. Qed.

Fact Forall2_right_Forall X Y (P : Y -> Prop) l m : 
        Forall2 (fun (_ : X) y => P y) l m <-> length l = length m /\ Forall P m.
Proof.
  split.
  + split.
    * eapply Forall2_length; eauto.
    * induction H; eauto.
  + intros (H1 & H2); revert H2 l H1.
    induction 1 as [ | y m IH ]; intros [ | x l ]; try easy; simpl; intros H.
    constructor; auto.
Qed.

Fact list_cons_inj {X} (x : X) l y m : x::l = y::m <-> x = y /\ l = m.
Proof. 
  split. 
  + now inversion 1.
  + now intros (-> & ->). 
Qed.

Section build_fan.

  Variables (X : Type) 
            (R : X -> X -> Prop) 
            (Rwf : well_founded R) 
            (f : X -> list X)
            (f_R : forall x y, y ∈ f x -> R y x).

  Definition fan := ltree_fall (fun x l => f x = map ltree_node l).

  (* A fan for f is a ltree X such that at every node ⟨x|l⟩ₗ 
     the list of label of each son (ie map ltree_node l) is
     exactly f x *) 
  Fact fan_fix x l : 
       fan ⟨x|l⟩ₗ <-> f x = map ltree_node l /\ Forall fan l.
  Proof. unfold fan at 1; rewrite ltree_fall_fix, Forall_forall; split; auto. Qed.

  (* The fan is a unique characterization, by wf induction on the root *)
  Fact fan_uniq x t1 t2 : fan t1 -> fan t2 -> ltree_node t1 = x -> ltree_node t2 = x -> t1 = t2.
  Proof.
    revert t1 t2;
    induction x as [ x IHx ] using (well_founded_induction_type Rwf); intros [ x1 l1 ] [ x2 l2 ].
    rewrite !fan_fix; intros [H1 H2] [H3 H4]; simpl; intros -> ->; f_equal.
    assert (IH : forall y, y ∈ f x 
         -> forall t1 t2, fan t1 -> fan t2 -> ltree_node t1 = y -> ltree_node t2 = y -> t1 = t2).
    1:{ intros y Hy; apply IHx; eauto. }
    clear IHx.
    revert l1 l2 H1 H3 H2 H4 IH; generalize (f x); clear x; intro l.
    induction l as [ | x l IHl ].
    + now intros [] [].
    + intros [ | t1 l1 ] [ | t2 l2 ]; try easy; simpl.
      rewrite !list_cons_inj, !Forall_cons_iff.
      intros (H1 & H2) (H3 & H4) (H5 & H6) (H7 & H8) H9.
      specialize (IHl _ _ H2 H4 H6 H8).
      split.
      * apply H9 with x; auto.
      * apply IHl; eauto.
  Qed.

  (* A fan at x is a fan with root node labeled by x *)
  Definition fan_at x (t : ltree X) := ltree_node t = x /\ fan t.

  Fact fan_at_uniq x t1 t2 : fan_at x t1 -> fan_at x t2 -> t1 = t2.
  Proof.
    intros (H1 & H2) (H3 & H4).
    revert H2 H4 H1 H3; apply fan_uniq.
  Qed.

  (* We build a fan by well-founded induction, know that
     f x contains only R-smaller values (this is f_R) *)
  Definition build_fan_at x : { t | fan_at x t }.
  Proof.
    induction x as [ x IHx ] using (well_founded_induction_type Rwf).
    specialize (fun y Hy => IHx y (f_R _ _ Hy)).
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

  Check ltree_leaves.

  Fact fan_prop t : 
         fan t 
      -> match t with 
           | ⟨x|l⟩ₗ => (f x = []  -> ltree_leaves t = [x])
                    /\ (f x <> [] -> ltree_leaves t = flat_map ltree_leaves l)
         end.
  Proof. Admitted.

  Definition irred x := ltree_leaves (proj1_sig (build_fan_at x)).

  Theorem irred_fix_nil x : f x = [] -> irred x = [x].
  Proof.
    unfold irred.
    destruct (build_fan_at x) as (t & Ht); simpl.
    destruct t as (y & l).
    destruct Ht as (H1 & H2); simpl in H1; subst y.
    apply fan_fix in H2 as (H2 & H3).
    intros E; rewrite E in H2.
    now destruct l.
  Qed.

  Theorem irred_fix_not_nil x : f x <> [] -> irred x = flat_map irred (f x).
  Proof.
    unfold irred at 1.
    destruct (build_fan_at x) as (t & Ht); simpl; intros D.
    destruct t as (y & l).
    destruct Ht as (H1 & H2); simpl in H1; subst y.
    apply fan_fix in H2 as (H2 & H3).
    assert (l <> []) as Hl by now destruct l.
    rewrite ltree_leaves_not_nil; auto.
    rewrite H2.
    rewrite !flat_map_concat_map, map_map.
    f_equal.
    apply map_ext_in_iff, Forall_forall.
    clear x H2 D Hl; revert H3.
    induction 1 as [ | x l Hx Hl IHl ]; constructor; auto.
  Admitted.

End build_fan.

Check irred_fix_not_nil.

