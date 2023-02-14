(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2.1 FREE SOFTWARE LICENSE AGREEMENT        *)
(**************************************************************)

(* Following a question by Frederic Soufflet from Haapie
  
   ...
   J'ai une question technique au sujet de certaines preuves concernant des
   arbres 'rooted unlabelled', et pas forcément binaires, montrant que la
   cardinalité d'un ensemble de tels arbres ayant un nombre fixé de noeuds
   est finie.

   Est-ce que tu pourrais me dire si je peux trouver ce genre de preuves
   dans l'environnement Coq ?
*)

(* Réponse: ici !! 

   En fait c'est un exercice très intéressant de montrer la finitude des
   rose tree lorsque l'on borne pex la taille. J'ai déjà eu besoin de
   faire qqch de similaire par rapport avec la fonction TREE(n) de 
   Harvey Friedman.

   J'ai importé dans ce fichier du code qui vient d'une libraire personnelle 
   pas encore publique: une refonte de ma preuve en Coq du théorème de Kruskal. 
   La partie Import sur les ltree a déjà été publiée sur opam parce que
   Jérôme Hugues en avait besoin donc elle vit sa propre vie dans Kruskal-Trees. 

   Après quelques résultats de clôture sur les prédicats finis: par union,
   intersection decidable, produit, composition, on travaille sur la
   décomposition d'un entier n sous la forme n = f x1 + ... + f xk où
   [x1,...,xk] : list X est une liste arbitraire et f : X -> nat et
   telle que f _ > 0. On montre qu'il n'y a qu'un nombre fini de
   telles listes.

   Puis on passe aux Roses trees, càd les arbres orientés avec des
   labels dans un type fini.

   Bonne lecture,

   Dominique

*)

From Coq
  Require Import Arith List Lia.

From KruskalTrees
  Require Import notations tactics list_utils ltree.

Import ListNotations ltree_notations.

Set Implicit Arguments.

(* Finiteness for unary predicates *)
Definition fin {X} (P : X -> Prop) := { l : list X | forall x, P x <-> x ∈ l }.

Fact fin_equiv X P Q : (forall x : X, P x <-> Q x) -> fin P -> fin Q.
Proof. intros H (l & Hl); exists l; intros; rewrite <- H; auto. Qed.

Fact fin_union X P Q : fin P -> fin Q -> fin (fun x : X => P x \/ Q x).
Proof.
  intros (l & Hl) (m & Hm); exists (l++m).
  intros x; rewrite in_app_iff, Hl, Hm; tauto.
Qed.

Fact fin_prod X Y P Q : @fin X P -> @fin Y Q -> fin (fun '(x,y) => P x /\ Q y).
Proof.
  intros (lx & Hx) (ly & Hy).
  exists (list_prod lx ly).
  intros (x,y); rewrite in_prod_iff, Hx, Hy; tauto.
Qed.

Fact fin_sg X (x : X) : fin (fun y => y = x).
Proof. exists [x]; simpl; firstorder. Qed.

Fact fin_inter_dec X P Q : (forall x : X, { P x } + { ~ P x }) -> fin Q -> fin (fun x => P x /\ Q x).
Proof.
  intros Pdec (l & Hl).
  exists (filter (fun x => if Pdec x then true else false) l).
  intros x; rewrite filter_In, <- Hl.
  destruct (Pdec x); split; tauto || easy.
Qed.

Fact fin_lt n : fin (fun x => x < n).
Proof.
  induction n as [ | n (l & Hl) ].
  + exists []; intros; simpl; split; tlia.
  + exists (n::l).
    intros x; simpl; rewrite <- Hl; tlia.
Qed.

Fact fin_le n : fin (fun x => x <= n).
Proof.
  apply fin_equiv with (P := fun x => x < S n).
  + intros; tlia.
  + apply fin_lt.
Qed.

Section fin_compose.

  Variable (X Y : Type) (R : X -> Y -> Prop) (P : Y -> Prop).

  (** A very useful lemma to compose finitary relations *)

  Lemma fin_compose :
             (forall y, P y -> fin (fun x => R x y))
          -> fin P
          -> fin (fun x => exists y, R x y /\ P y).
  Proof.
    intros H (lP & HP).
    apply fin_equiv with (P := fun x => exists y, R x y /\ In y lP).
    + intros x; split; intros (y & Hy); exists y; revert Hy; rewrite HP; auto.
    + cut (forall y, In y lP -> fin (fun x => R x y)).
      2: intros; apply H, HP; auto.
      clear P HP H.
      induction lP as [ | y lP IHlP ]; intros H.
      * exists nil; intros k; split.
        - intros (? & _ & []).
        - intros [].
      * destruct IHlP as (ll & Hll).
        - intros; apply H; simpl; auto.
        - destruct (H y) as (l & Hl); simpl; auto.
          exists (l++ll); intros x; rewrite in_app_iff, <- Hl, <- Hll.
          split.
          ++ intros (y' & H1 & [ <- | H2 ]); auto.
             right; exists y'; auto.
          ++ intros [ | (y' & ? & ?) ].
             ** exists y; auto.
             ** exists y'; auto.
  Qed.

End fin_compose.

Fact fin_plus_eq n : fin (fun '(a,b) => n = a + b).
Proof.
  induction n as [ | n (l & Hl) ].
  + exists [(0,0)]; intros (x,y); split.
    * destruct x; destruct y; tlia; left; auto.
    * intros [ E | [] ]; now inversion E.
  + exists ((S n,0)::map (fun '(x,y) => (x,S y)) l).
    intros (x,[|y]); split.
    * left; f_equal; tlia.
    * intros [ H | ((u,v) & H & _)%in_map_iff ]; now inversion H.
    * intros E; right; apply in_map_iff; exists (x,y); rewrite <- Hl; split; auto; tlia.
    * intros [ H | ((u,v) & H & H2%Hl)%in_map_iff ].
      - now inversion H.
      - inversion H; subst; tlia.
Qed.

Fact fin_plus_eq_strict n : fin (fun '(a,b) => 0 < a /\ n = a + b).
Proof.
  apply fin_equiv with (P := fun c : nat * nat => (let (a,b) := c in 0 < a) /\ let (a,b) := c in n = a + b).
  + intros []; tauto.
  + apply fin_inter_dec.
    * intros []; apply lt_dec.
    * apply fin_plus_eq.
Qed.

Fact fin_plus_le n : fin (fun '(a,b) => a + b <= n).
Proof.
  apply fin_equiv with (P := fun c : nat * nat => exists i, (let (a,b) := c in i = a+b) /\ i <= n).
  + intros []; firstorder; tlia.
  + apply fin_compose.
    * intros; apply fin_plus_eq.
    * apply fin_le.
Qed.

Fact fin_plus_le_strict n : fin (fun '(a,b) => 0 < a /\ a + b <= n).
Proof.
  apply fin_equiv with (P := fun c : nat * nat => (let (a,b) := c in 0 < a) /\ let (a,b) := c in a + b <= n).
  + intros []; tauto.
  + apply fin_inter_dec.
    * intros []; apply lt_dec.
    * apply fin_plus_le.
Qed.

Section fin_sum.

  Variables (X : Type) (f : X -> nat) (Hf : forall x, 0 < f x)
            (Y : Type) (g : Y -> nat).

  Theorem fin_sum n : 
         fin (fun x => f x <= n) 
      -> fin (fun y => g y < n)
      -> fin (fun '(x,y) => f x + g y <= n).
  Proof.
    intros H1 H2.
    apply fin_equiv with (P := fun c : X*Y => exists k : nat*nat, (let (x,y) := c in let (a,b) := k in f x <= a /\ g y <= b) /\ (let (a,b) := k in 0 < a /\ a + b <= n)).
    + intros (x,y); split.
      * intros ((a,b) & H3 & H4); tlia.
      * intros Hxy; exists (f x,g y); repeat split; tlia; apply Hf.
    + apply fin_compose.
      * intros (a,b) []; apply fin_prod.
        - apply fin_equiv with (fun x => f x <= a /\ f x <= n).
          1: split; tlia.
          apply fin_inter_dec; auto.
          intro; apply le_dec.
        - apply fin_equiv with (fun y => g y <= b /\ g y < n).
          1: split; tlia.
          apply fin_inter_dec; auto.
          intro; apply le_dec.
      * apply fin_plus_le_strict.
  Qed.

End fin_sum.

Section list_sum_finite.

  Variables (X : Type) (f : X -> nat) (Hf : forall x, 0 < f x).

  Lemma list_sum_le_fin n : (forall j, j <= n -> fin (fun x => f x <= j)) -> fin (fun l => list_sum f l <= n).
  Proof.
    induction n as [ n IHn ] using (well_founded_induction_type lt_wf); intros Hn.
    apply fin_equiv with (P := fun l => l = [] 
                                     \/ exists c : nat*nat, (let (a,b) := c in exists x m, f x <= a /\ list_sum f m <= b /\ l = x::m) /\ let (a,b) := c in 0 < a /\ n = a+b).
    + intros l; simpl; split.
      * intros [ -> | ((a,b) & (x & m & H1 & H2 & ->) & H3 & H4) ]; simpl; tlia.
      * destruct l as [ | x m ]; [ left | right ]; simpl; auto.
        exists (f x, n - f x);  split; simpl in *.
        - exists x, m; repeat split; auto; tlia.
        - repeat split; tlia; auto.
    + apply fin_union.
      1: apply fin_sg.
      apply fin_compose with (2 := fin_plus_eq_strict _).
      intros (a,b) (Ha & Hab).
      destruct (Hn a) as (la & Hla); tlia.
      destruct (IHn b) as (lb & Hlb); tlia.
      1: intros; apply Hn; tlia.
      exists (map (fun '(x,l) => x::l) (list_prod la lb)).
      intros l; rewrite in_map_iff; split.
      * intros (x & m & H1%Hla & H2%Hlb & H3).
        exists (x,m); split; auto.
        apply in_prod_iff; auto.
      * intros ((x,m) & H1 & (H2%Hla & H3%Hlb)%in_prod_iff).
        exists x, m; auto.
  Qed.

  Lemma list_sum_eq_fin n : (forall j, j <= n -> fin (fun x => f x <= j)) -> fin (fun l => list_sum f l = n).
  Proof.
    intros Hn.
    apply fin_equiv with (P := fun l => list_sum f l = n /\ list_sum f l <= n).
    + intros; tlia.
    + apply fin_inter_dec.
      * intro; apply eq_nat_dec.
      * apply list_sum_le_fin; auto.
  Qed.

End list_sum_finite.

Section fin_ltree_weight.

  Variables (X : Type) (f : X -> nat) (Hf : forall x, 0 < f x).

  Theorem fin_ltree_weight_le n : (forall i, i <= n -> fin (fun x => f x <= i)) -> fin (fun t => ltree_weight f t <= n).
  Proof.
    induction n as [ n IHn ] using (well_founded_induction_type lt_wf); intros Hn.
    apply fin_equiv with (P := fun t => exists c : X * list (ltree X), (let (x,l) := c in t = ⟨x|l⟩ₗ) /\ (let (x,l) := c in f x + list_sum (ltree_weight f) l <= n)).
    + intros t; split.
      * intros ((x,l) & -> & H); now rewrite ltree_weight_fix.
      * destruct t as [ x l ]; exists (x,l); now rewrite ltree_weight_fix in H.
    + apply fin_compose.
      * intros (x,l) _; apply fin_sg.
      * apply fin_sum; auto.
        apply fin_equiv with (P := fun l => exists k, list_sum (ltree_weight f) l = k /\ k < n).
        - intros l; split.
          ++ intros (k & <- & ?); auto.
          ++ exists (list_sum (ltree_weight f) l); tlia.
        - apply fin_compose.
          ++ intros y Hy; apply list_sum_eq_fin; auto.
             ** apply ltree_weight_gt; auto.
             ** intros; apply IHn; tlia.
                intros; apply Hn; tlia.
          ++ apply fin_lt.
  Qed.

End fin_ltree_weight.

Definition lsum := fold_right plus 0.

Fact list_sum_lsum X (f : X -> nat) l : list_sum f l = lsum (map f l).
Proof. induction l; simpl; f_equal; auto. Qed.

Section fin_ltree_size.

  Variable (X : Type) (Xfin : { lX | forall x : X, x ∈ lX }). 

  Definition ltree_size := ltree_weight (fun _ : X => 1).

  Fact ltree_size_fix x l : ltree_size ⟨x|l⟩ₗ = 1 + lsum (map ltree_size l).
  Proof.
    unfold ltree_size.
    rewrite ltree_weight_fix; f_equal.
    apply list_sum_lsum.
  Qed.

  Theorem fin_ltree_size_le n : fin (fun t => ltree_size t <= n).
  Proof.
    apply fin_ltree_weight_le.
    + tlia.
    + destruct Xfin as (lX & HlX).
      intros [ | i ] _.
      * exists []; simpl; tlia.
      * exists lX; split; auto; tlia.
  Qed.

  Corollary fin_ltree_size_eq n : { lt : list (ltree X) | forall t, ltree_size t = n <-> t ∈ lt }.
  Proof.
    apply fin_equiv with (P := fun t => ltree_size t = n /\ ltree_size t <= n).
    + intros; tlia.
    + apply fin_inter_dec.
      * intros; apply eq_nat_dec.
      * apply fin_ltree_size_le.
  Qed.

End fin_ltree_size.

Print lsum.
Check ltree_size.
Check ltree_size_fix.
Check fin_ltree_size_eq.
