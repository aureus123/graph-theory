
(* Formalization of resolution of the Upper Weighted Irredundant Problem
 * via the Maximum Weighted Stable Set Problem
 *
 * Contributors: Ricardo Katz, Daniel Severin, Mauricio Salichs *)

From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import preliminaries digraph sgraph dom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


(**********************************************************************************)
Section Preliminaries.

(* This is an adapted version of partition_disjoint_bigcup in finset.v
 * where we force the index in the bigcup to satisfy P.
 * Could be more general for all bigops, not just sum. *)
Lemma partition_disjoint_bigcup_P (T I : finType) (F : I -> {set T}) (P : pred I)
    E : (forall i j, P i -> P j -> i != j -> [disjoint F i & F j]) ->
  \sum_(x in \bigcup_(i | P i) F i) E x =
    \sum_(i | P i) \sum_(x in F i) E x.
Proof.
move=> disjF. pose P' := [set F i | i in I & P i && (F i != set0)].
have trivP: trivIset P'.
  apply/trivIsetP=> _ _ /imsetP[i iP' ->] /imsetP[j jP' ->] neqFij.
  apply: disjF; have/setId2P [_ iP _] := iP'. exact: iP.
  have/setId2P [_ jP _] := jP'. exact: jP. by apply: contraNneq neqFij => ->.
have ->: \bigcup_(i | P i) F i = cover P'.
  apply/esym. rewrite cover_imset. 
  under eq_bigl=> x. rewrite inE andbA [in X in X && _]andbC -andbA. over.
  rewrite big_mkcondr; apply: eq_bigr => i _. by rewrite inE; case: eqP.
rewrite big_trivIset // big_imset => [|i j Pi' /setIdP[_ /andP [Pj notFj0]] eqFij].
  under eq_bigl=> x. rewrite inE andbA [in X in X && _]andbC -andbA. over.
  rewrite big_mkcondr; apply: eq_bigr => i _; rewrite inE.
  by case: eqP => //= ->; rewrite big_set0. have/setId2P [_ Pi _] := Pi'.
  by apply: contraNeq (disjF _ _ Pi Pj) _; by rewrite -setI_eq0 eqFij setIid.
Qed.

Lemma sub_diff_sum (T : finType) (A B : {set T}) (F : T -> nat) :
 B \subset A -> \sum_(i in A :\: B) F i = \sum_(i in A) F i - \sum_(i in B) F i.
Proof.
  move/setIidPr=> BsubA.
  rewrite [in X in _ = X - _](big_setID B) /=.
  under [in X in _ = X + _ - _]eq_bigl do rewrite BsubA.
  rewrite addnC -addnBA. by rewrite subnn addn0. auto.
Qed.

Lemma sub_leq_sum (T : finType) (A B : {set T}) (F : T -> nat) :
 A \subset B -> \sum_(i in A) F i <= \sum_(i in B) F i.
Proof.
  move/setIidPr=> AsubB.
  rewrite [in X in _ <= X](big_setID A) /=.
  under [in X in _ <= X + _]eq_bigl do rewrite AsubB.
  by rewrite leq_addr.
Qed.

(* give_sg generate the sedge relation from a function f such that:
     f u v (with 0 <= u < v < n) is true iff (u,v) is an edge of G *)
Definition give_sg (f : nat -> nat -> bool) (n : nat) (i j : 'I_n) :=
  let u := nat_of_ord i in
    let v := nat_of_ord j in
      if (u == v) then false else
        if (u < v) then f u v else f v u.

Fact give_sg_sym (f : nat -> nat -> bool) (n : nat) : symmetric (give_sg f (n:=n)).
Proof.
  rewrite /symmetric /give_sg => u v.
  case: (boolP (u == v))=> [ | uneqv] ; first by move/eqP->.
  rewrite (ifN _ _ uneqv).
  rewrite eq_sym in uneqv.
  rewrite (ifN _ _ uneqv).
  rewrite neq_ltn in uneqv.
  by case: (orP uneqv) => ultv;
    move: (ltnW ultv) ; rewrite leqNgt => nvltu; rewrite (ifN _ _ nvltu) ultv.
Qed.

Fact give_sg_irrefl (f : nat -> nat -> bool) (n : nat) : irreflexive (give_sg f (n:=n)).
Proof. by rewrite /irreflexive /give_sg => ? ; rewrite eq_refl. Qed.

End Preliminaries.


(**********************************************************************************)
Section Basic_Facts_Induced_Homomorphism_Isomorphism.

Definition induced_hom (G1 G2 : sgraph) (h : G1 -> G2) :=
          forall x y : G1, x -- y <-> h x -- h y.

Lemma induced_hom_comp (G1 G2 G3 : sgraph) (h : G1 -> G2) (h' : G2 -> G3) :
  induced_hom h -> induced_hom h' -> induced_hom (h' \o h).
Proof.
  move => hom_h hom_h' x y.
  by rewrite (hom_h x y) (hom_h' (h x) (h y)).
Qed.

Definition induced_subgraph (G1 G2 : sgraph) :=
          exists2 h : G1 -> G2, injective h & induced_hom h.

Lemma induced_S_is_sub (G : sgraph) (S : {set G}) : induced_subgraph (induced S) G.
Proof. rewrite /induced_subgraph /induced_hom. exists val => // ; exact: val_inj. Qed.

Definition isomorphic (G1 G2 : sgraph) := 
          exists2 f : G1 -> G2, (exists2 g : G2 -> G1, cancel f g & cancel g f) & induced_hom f.

Variables G1 G2 : sgraph.
Hypothesis iso_G1_G2 : isomorphic G1 G2.

Lemma sub_G1_G2 : induced_subgraph G1 G2.
Proof.
  move: iso_G1_G2 => [f [g can_f_g can_g_f hom_f]].
  rewrite /induced_subgraph ; exists f => // ; exact: (can_inj can_f_g).
Qed.

Lemma iso_G2_G1 : isomorphic G2 G1.
Proof.
  move: iso_G1_G2 => [f [g can_f_g can_g_f hom_f]].
  rewrite /isomorphic ; exists g ; first by exists f => //.
  rewrite /induced_hom => x y. set x' := g x. set y' := g y.
  by rewrite -(can_g_f x) -(can_g_f y) -/x' -/y' hom_f.
Qed.

Lemma induced_hom_bijective : exists h : G1 -> G2, bijective h.
Proof. by move: iso_G1_G2 => [h [invh ? ? _]] ; exists h ; exists invh. Qed.

End Basic_Facts_Induced_Homomorphism_Isomorphism.

Lemma sub_G2_G1 (G1 G2 : sgraph) : isomorphic G1 G2 -> induced_subgraph G2 G1.
Proof. move/iso_G2_G1 ; exact: sub_G1_G2. Qed.

Lemma subgraph_trans (G1 G2 G3 : sgraph) :
  induced_subgraph G1 G2 ->
  induced_subgraph G2 G3 -> induced_subgraph G1 G3.
Proof.
  rewrite /induced_subgraph => [[h inj_h hom_h] [h' inj_h' hom_h']].
  by exists (h' \o h); [apply: inj_comp | apply: induced_hom_comp].
Qed.

Notation "A \subgraph B" := (induced_subgraph A B) (at level 70, no associativity).


(**********************************************************************************)
Section Graph_definitions.

(* 'K_n,m : complete bipartite graph K_{n,m} *)
Section complete_bipartite.
  Variables n m : nat.

  Let Knm_vert := 'I_(n+m).
  Let Knm_adj (u v : nat) := (u < n) && (n <= v).

  Let Knm_rel := [ rel u v : Knm_vert | give_sg Knm_adj u v ].
  Let Knm_sym : symmetric Knm_rel. Proof. exact: give_sg_sym. Qed.
  Let Knm_irrefl : irreflexive Knm_rel. Proof. exact: give_sg_irrefl. Qed.
  Definition Knm := SGraph Knm_sym Knm_irrefl.
End complete_bipartite.

(* claw: a complete bipartite K_{1,3} *)
Definition claw := Knm 1 3.

(* 'P_n : path of n vertices P_n *)
Section path_graph.
  Variable n : nat.

  Let Pn_vert := 'I_n.
  Let Pn_adj (u v : nat) := (u == v-1).

  Let Pn_rel := [ rel u v : Pn_vert | give_sg Pn_adj u v ].
  Let Pn_sym : symmetric Pn_rel. Proof. exact: give_sg_sym. Qed.
  Let Pn_irrefl : irreflexive Pn_rel. Proof. exact: give_sg_irrefl. Qed.
  Definition Pn := SGraph Pn_sym Pn_irrefl.
End path_graph.

Notation "''K_' n" := (complete n)
  (at level 8, n at level 2, format "''K_' n").

(* 'C_n : circuit of n vertices C_n *)
Section circuit_graph.
  Variables n : nat.

  Let Cn_vert := 'I_n.
  Let Cn_adj (u v : nat) := (u == v-1) || ((u == 0) && (v == n-1)).

  Let Cn_rel := [ rel u v : Cn_vert | give_sg Cn_adj u v ].
  Let Cn_sym : symmetric Cn_rel. Proof. exact: give_sg_sym. Qed.
  Let Cn_irrefl : irreflexive Cn_rel. Proof. exact: give_sg_irrefl. Qed.
  Definition Cn := SGraph Cn_sym Cn_irrefl.
End circuit_graph.

(* 'CC_n : complement of circuit of n vertices *)
Section circuit_graph.
  Variables n : nat.

  Let CCn_vert := 'I_n.
  Let CCn_adj (u v : nat) := ~~ ((u == v-1) || ((u == 0) && (v == n-1))).

  Let CCn_rel := [ rel u v : CCn_vert | give_sg CCn_adj u v ].
  Let CCn_sym : symmetric CCn_rel. Proof. exact: give_sg_sym. Qed.
  Let CCn_irrefl : irreflexive CCn_rel. Proof. exact: give_sg_irrefl. Qed.
  Definition CCn := SGraph CCn_sym CCn_irrefl.
End circuit_graph.

(* co-paw graph (a path of 3 vertices + an isolated vertex *)
Section copaw_graph.

  Let copaw_vert := 'I_4.
  Let copaw_adj(u v : nat) :=
    match u, v with
    | 0, 1 => true
    | 1, 2 => true
    | _, _ => false
  end.

  Let copaw_rel := [ rel u v : copaw_vert | give_sg copaw_adj u v ].
  Let copaw_sym : symmetric copaw_rel. Proof. exact: give_sg_sym. Qed.
  Let copaw_irrefl : irreflexive copaw_rel. Proof. exact: give_sg_irrefl. Qed.
  Definition copaw := SGraph copaw_sym copaw_irrefl.
End copaw_graph.

(* Bull graph (a triangle with two appended vertices) *)
Section bull_graph.

  Let bull_vert := 'I_5.
  Let bull_adj(u v : nat) :=
    match u, v with
    | 0, 2 => true
    | 1, 3 => true
    | 2, 3 => true
    | 2, 4 => true
    | 3, 4 => true
    | _, _ => false
  end.

  Let bull_rel := [ rel u v : bull_vert | give_sg bull_adj u v ].
  Let bull_sym : symmetric bull_rel. Proof. exact: give_sg_sym. Qed.
  Let bull_irrefl : irreflexive bull_rel. Proof. exact: give_sg_irrefl. Qed.
  Definition bull := SGraph bull_sym bull_irrefl.
End bull_graph.

(* G7_1 (a certain graph with 7 vertices and 13 edges) *)
Section G7_1_graph.

  Let G7_1_vert := 'I_7.
  Let G7_1_adj(u v : nat) :=
    match u, v with
    | 0, 2 => true
    | 0, 3 => true
    | 0, 4 => true
    | 0, 6 => true
    | 1, 3 => true
    | 1, 4 => true
    | 1, 5 => true
    | 1, 6 => true
    | 2, 4 => true
    | 2, 5 => true
    | 3, 5 => true
    | 3, 6 => true
    | 4, 6 => true
    | _, _ => false
  end.

  Let G7_1_rel := [ rel u v : G7_1_vert | give_sg G7_1_adj u v ].
  Let G7_1_sym : symmetric G7_1_rel. Proof. exact: give_sg_sym. Qed.
  Let G7_1_irrefl : irreflexive G7_1_rel. Proof. exact: give_sg_irrefl. Qed.
  Definition G7_1 := SGraph G7_1_sym G7_1_irrefl.
End G7_1_graph.

(* G7_2 = G7_1 + an extra edge (2,6) *)
Section G7_2_graph.

  Let G7_2_vert := 'I_7.
  Let G7_2_adj(u v : nat) :=
    match u, v with
    | 0, 2 => true
    | 0, 3 => true
    | 0, 4 => true
    | 0, 6 => true
    | 1, 3 => true
    | 1, 4 => true
    | 1, 5 => true
    | 1, 6 => true
    | 2, 4 => true
    | 2, 5 => true
    | 2, 6 => true
    | 3, 5 => true
    | 3, 6 => true
    | 4, 6 => true
    | _, _ => false
  end.

  Let G7_2_rel := [ rel u v : G7_2_vert | give_sg G7_2_adj u v ].
  Let G7_2_sym : symmetric G7_2_rel. Proof. exact: give_sg_sym. Qed.
  Let G7_2_irrefl : irreflexive G7_2_rel. Proof. exact: give_sg_irrefl. Qed.
  Definition G7_2 := SGraph G7_2_sym G7_2_irrefl.
End G7_2_graph.

End Graph_definitions.

Notation "''K_' n , m" := (Knm n m)
  (at level 8, n at level 2, m at level 2, format "''K_' n , m").

Notation "''P_' n" := (Pn n)
  (at level 8, n at level 2, format "''P_' n").

Notation "''C_' n" := (Cn n)
  (at level 8, n at level 2, format "''C_' n").

Notation "''CC_' n" := (CCn n)
  (at level 8, n at level 2, format "''CC_' n").

