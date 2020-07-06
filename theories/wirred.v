
(* Resolution of the Upper Weighted Irredundant Problem *)

From mathcomp Require Import all_ssreflect.
Require Import preliminaries digraph sgraph dom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(** * Alternative versions of private_set for irredundant sets *)
Section alternative_private_set.

Variable G : sgraph.

Variable D : {set G}.

(* This alternative definition of private_set contemplates cases where v \notin D.
 * If v belongs to D, it returns the set of private vertices; otherwise, it returns an empty set. *)
Definition private_set' (v : G) := NS[D :&: [set v]] :\: NS[D :\: [set v]].

Lemma eq_prvs_prvs' (v : G) : v \in D -> private_set' v == private_set D v.
Proof.
  move=> vinD ; rewrite /private_set /private_set'.
  suff: N[v] = NS[D :&: [set v]] by move->.
  rewrite (setIidPr _) ?sub1set //.
  apply/eqP ; rewrite eqEsubset ; apply/andP ; split.
  - apply: cln_sub_clns. by rewrite in_set1.
  - apply/subsetP => x. move/bigcupP. elim=> z ; rewrite in_set1. by move/eqP->.
Qed.

Lemma eq0prvs' (v : G) : v \notinD -> (private_set' v == set0).
Proof.
  move=> vnotinD ; rewrite /private_set' disjoint_setI0 1?disjoint_sym ?disjoints1 //.
  by rewrite clns0 set0D.
Qed.

End alternative_private_set.


(** * Homomorphisms, isomorphisms and subgraphs. All "induced"! *)
Section Basic_Facts_Induced_Homomorphism_Isomorphism.

Definition induced_hom (G1 G2 : sgraph) (h : G1 -> G2) :=
          forall x y : G1, x -- y <-> h x -- h y.

Lemma induced_hom_comp (G1 G2 G3 : sgraph) (h : G1 -> G2) (h' : G2 -> G3) :
  induced_hom h -> induced_hom h' -> induced_hom (h' \o h).
Proof.
  rewrite /induced_hom => hom_h hom_h' x y ; rewrite /comp /iff ; split.
  all: by rewrite (hom_h x y) (hom_h' (h x) (h y)).
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
  elim: iso_G1_G2 => f [g can_f_g can_g_f hom_f].
  rewrite /induced_subgraph ; exists f => // ; exact: (can_inj can_f_g).
Qed.

Lemma iso_G2_G1 : isomorphic G2 G1.
Proof.
  elim: iso_G1_G2 => f [g can_f_g can_g_f hom_f].
  rewrite /isomorphic ; exists g ; first by exists f => //.
  rewrite /induced_hom => x y. set x' := g x. set y' := g y.
  by rewrite -(can_g_f x) -(can_g_f y) -/x' -/y' hom_f.
Qed.

Lemma induced_hom_bijective : exists h : G1 -> G2, bijective h.
Proof. by elim: iso_G1_G2 => h [invh ? ? _] ; exists h ; exists invh. Qed.

End Basic_Facts_Induced_Homomorphism_Isomorphism.

Lemma sub_G2_G1 (G1 G2 : sgraph) : isomorphic G1 G2 -> induced_subgraph G2 G1.
Proof. move/iso_G2_G1 ; exact: sub_G1_G2. Qed.

Lemma subgraph_trans (G1 G2 G3 : sgraph) :
  induced_subgraph G1 G2 ->
  induced_subgraph G2 G3 -> induced_subgraph G1 G3.
Proof.
  rewrite /induced_subgraph => [[h inj_h hom_h] [h' inj_h' hom_h']].
  exists (h' \o h) ; [ by apply: inj_comp | by apply: induced_hom_comp ].
Qed.

Notation "A \subgraph B" := (induced_subgraph A B) (at level 70, no associativity).


(**********************************************************************************)
Section Newgraph_construction.

Variable G : sgraph.

Definition V' := [set x : G * G | x.1 -*- x.2].

Definition newgraph_type := sig [eta mem V'].

Definition newgraph_rel := [rel x y : newgraph_type | (val x != val y)
                                                   && (((val y).1 -*- (val x).2)
                                                   || ((val y).2 -*- (val x).1))].

Lemma newgraph_sym : symmetric newgraph_rel.
Proof.
  rewrite /symmetric /newgraph_rel /= => x y.
  rewrite eq_sym ; apply: andb_id2l => _ ; rewrite cl_sg_sym orbC ; apply: orb_id2r => _.
  by rewrite cl_sg_sym.
Qed.

Lemma newgraph_irrefl : irreflexive newgraph_rel.
Proof. rewrite /irreflexive /newgraph_rel /= ; move=> x ; rewrite eq_refl //. Qed.

Definition newgraph := SGraph newgraph_sym newgraph_irrefl.

End Newgraph_construction.


(**********************************************************************************)
Section Upper_Weighted_Irredundant_Problem.

Variable G : sgraph.
Variable weight : G -> nat.
Hypothesis positive_weights : forall v : G, weight v > 0.

Let G' := newgraph G.
Let weight' := fun x : G' => weight (val x).1.
Let W := weight_set weight.
Let W' := weight_set weight'.

Lemma positive_weights' : forall v : G', weight' v > 0.
Proof. by rewrite /weight'. Qed.



(* Function h_vv maps a vertex v in G to its counterpart vv in G' *)
Section h_counterpart_definition.
  Variable v : G.

  Let vv_in_V' : (v, v) \in V' G.
  Proof. by rewrite /V' in_set /fst /snd dominates_refl. Qed.

  Definition h_vv := Sub (v, v) vv_in_V' : G'.

  Fact h_vv1 : (val h_vv).1 = v.
  Proof. by rewrite /=. Qed.

  Fact h_vv2 : (val h_vv).2 = v.
  Proof. by rewrite /=. Qed.
End h_counterpart_definition.


(* Function h_vw maps a vertex v in D (an irredundant set) to (v,w) where w is one of its
 * private vertices, while h_vw' maps any vertex to a set of G', where it returns {(v,w)} if
 * v belongs to D, and an empty set otherwise.
 * Function h_Dw gives the set {(v,w) : v \in D, w is a private set of v}. *)
Section set_h_vertex_and_its_private_definition.
  Variable D : {set G}.

  Hypothesis Dirr : irredundant D.

  Section h_vertex_and_its_private_definition.
    Variable v: G.

    Section h_vertex_in_D_and_its_private_definition.
      Hypothesis vinD: v \in D.

      Let w_exists : exists w : G, w \in private_set D v.
      Proof. by move/irredundantP: Dirr => /(_ v vinD) ; move/set0Pn. Qed.

      Let w : G := xchoose w_exists.
      Let w_is_private : w \in private_set D v := xchooseP w_exists.

      Let vw_in_V' : (v, w) \in V' G.
      Proof. by rewrite /V' in_set /= ; move/privateP: w_is_private => [? _]. Qed.

      Definition h_vw := Sub (v, w) vw_in_V' : G'.

      Fact h_vw1 : (val h_vw).1 = v.
      Proof. by rewrite /=. Qed.

      Fact h_vw2 : (val h_vw).2 \in private_set D v.
      Proof. by rewrite /=. Qed.
    End h_vertex_in_D_and_its_private_definition.

    Definition h_vw' := if @idP (v \in D) is ReflectT p then set1 (h_vw p) else set0.

    Fact h_vw'0 : v \notin D -> h_vw' = set0.
    Proof.
      move=> vnotinD.
      rewrite /h_vw'; case: {-}_ / idP => [// | ] ; last by rewrite /=.
      move=> vinD; apply/eqP ; apply contraT=> _; by move/negP in vnotinD.
    Qed.

    Fact h_vw'1 (vD : v \in D) : h_vw' = set1 (h_vw vD).
    Proof. rewrite /h_vw'; case: {-}_ / idP => [vD'|//]; by rewrite (bool_irrelevance vD' vD). Qed.
  End h_vertex_and_its_private_definition.

  Definition h_Dw := \bigcup_(v in D) (h_vw' v).

  Fact h_Dw1 (x : G') : x \in h_Dw -> (val x).1 \in D.
  Proof.
    rewrite /h_Dw ; move/bigcupP=> [v vinD].
    by rewrite (h_vw'1 vinD) in_set1 ; move/eqP-> ; rewrite h_vw1.
  Qed.

  Fact h_Dw2 (x : G') : x \in h_Dw -> (val x).2 \in private_set D (val x).1.
  Proof.
    rewrite /h_Dw ; move/bigcupP=> [v vinD].
    by rewrite (h_vw'1 vinD) in_set1 ; move/eqP-> ; rewrite h_vw2.
  Qed.

  Lemma weight_D_eq_h_Dw : W D = W' h_Dw.
  Proof.
    (* we shape the statement and prove by induction on the cardinality of D *)
    suff: forall (n : nat), #|D| = n -> W D = W' h_Dw by move=> /(_ #|D| erefl).
    move=> n ; elim/nat_ind: n => [| m IH].
    - move/cards0_eq/eqP => D0.
      move: (D0) ; rewrite /W (wset0 positive_weights D) ; move/eqP->.
      rewrite /W' ; apply/eqP ; rewrite eq_sym -(wset0 positive_weights' h_Dw).
      move: D0 ; apply: contraLR.
      move/set0Pn => [x xinhDw] ; apply/set0Pn ; exists (val x).1 ; exact: h_Dw1.
    - 
  (* La idea es, con el #|D| = m.+1, probar que #|D|>0 y así sacar un elemento v de D con el set0Pn.
     Luego sacamos el elemento x := (h_vw v) de h_Dw. Deberíamos llegar a algo como:
        W ((D :\: v) :|: v) = W' ((h_Dw :\: x) :|: x).
     Luego, usando big_setID y setIidPr, lo convertimos en:
        W (D :\: v) + W (set1 v) = W' (h_Dw :\: x) + W' (set1 x).
     pero el h_Dw está ligado a D, hay que trabajar un poco para ligarlo a D :\: v.
     Luego, con la hipótesis inductiva cancelamos los términos izquierdos y nos queda:
        W (set1 v) = W' (set1 x).
     que son cuentitas. *)
  Admitted.

End set_h_vertex_and_its_private_definition.


Theorem subgraph_G_G' : G \subgraph G'.
Proof.
  rewrite /induced_subgraph.
  exists h_vv.
  (* h_vv is injective *)
  - rewrite /injective=> x y H1.
    by move: (h_vv1 x) <- ; move: (h_vv1 y) <- ; rewrite H1.
  (* h_vv is an induced homomorphism *)
  - rewrite /induced_hom=> x y ; set x' := h_vv x ; set y' := h_vv y.
    rewrite /iff ; split.
    (* case x -- y -> x' -- y' *)
    + move=> adjxy.
      suff: ((x, x) != (y, y)) && (y -*- x || y -*- x) by rewrite /=.
      apply/andP ; split.
      * move: (negbT (sg_edgeNeq adjxy)) ; apply: contra => /eqP.
        by rewrite pair_equal_spec => [[xeqy _]] ; move: xeqy->.
      * by rewrite orbb cl_sg_sym /dominates adjxy orbT.
    (* case x' -- y' -> x -- y *)
    + move=> adjx'y'.
      have H2: ((x, x) != (y, y)) && (y -*- x || y -*- x) by exact: adjx'y'.
      move/andP: H2 => [/negP x'neqy'].
      rewrite orbb cl_sg_sym /dominates ; move/orP ; case ; last by [].
      move/eqP=> xeqy.
      have x'eqy': (x, x) == (y, y) by apply/eqP ; rewrite pair_equal_spec ; split=> //.
      contradiction.
Qed.

(* For a given irredundant set D of G, there exists a stable set S of G' such that w(D) = w'(S) *)
Theorem irred_G_to_stable_G' (D : {set G}) (Dirr : irredundant D) :
  exists2 S : {set G'}, stable S & W D = W' S.
Admitted.

(* For a given stable set S of G', there exists an irredundant set D of G such that w(D) = w'(G') *)
Theorem stable_G'_to_irred_G (S : {set G'}) (stS : stable S) :
  exists2 D : {set G}, irredundant D & W D = W' S.
Admitted.

(* Main theorem *)
Theorem IR_w_G_is_alpha_w_G' : IR_w G weight = alpha_w G' weight'.
Proof.
  apply/eqP; rewrite eqn_leq ; apply/andP ; split.
  - have [D Dirr] := IR_witness weight.
    move<- ; rewrite -/W.
    have [S Sst] := irred_G_to_stable_G' Dirr.
    by move-> ; apply: alpha_max.
  - have [S Sst] := alpha_witness weight'.
    move<- ; rewrite -/W'.
    have [D Dirr] := stable_G'_to_irred_G Sst.
    by move<- ; apply: IR_max.
Qed.

End Upper_Weighted_Irredundant_Problem.


(**********************************************************************************)
Section Graph_definitions.

(* give_sg generate the sedge relation from a function f such that:
     f u v (with 0 <= u < v < n) is true iff (u,v) is an edge of G *)
Definition give_sg (f : nat -> nat -> bool) (n : nat) (i j : ordinal_finType n) :=
  let u := nat_of_ord i in
    let v := nat_of_ord j in
      if (u == v) then false else
        if (u < v) then f u v else f v u.

Fact give_sg_sym (f : nat -> nat -> bool) (n : nat) : symmetric (give_sg f (n:=n)).
Proof.
  rewrite /symmetric /give_sg => u v.
  case: (boolP (u == v)) ; first by move/eqP->.
  move=> uneqv ; move: (uneqv) ; rewrite neq_ltn => uneqv'.
  rewrite (ifN _ _ uneqv).
  rewrite eq_sym in uneqv.
  rewrite (ifN _ _ uneqv).
  move/orP: uneqv' ; case.
  all : move=> ultv ; move: (ltnW ultv) ; rewrite leqNgt => nvltu ; by rewrite (ifN _ _ nvltu) ultv.
Qed.

Fact give_sg_irrefl (f : nat -> nat -> bool) (n : nat) : irreflexive (give_sg f (n:=n)).
Proof. by rewrite /irreflexive /give_sg => ? ; rewrite eq_refl. Qed.

(* 'K_n,m : complete bipartite graph K_{n,m} *)
Section complete_bipartite.
  Variables n m : nat.

  Let Knm_adj (u v : nat) := (u < n) && (n <= v).

  Definition Knm : sgraph.
  Proof.
    refine {| svertex := ordinal_finType (n+m) ;
              sedge := give_sg Knm_adj (n:=n+m) |}.
    - exact: give_sg_sym. - exact: give_sg_irrefl.
  Qed.
End complete_bipartite.

(* 'P_n : path of n vertices P_n *)
Section path_graph.
  Variables n : nat.

  Let Pn_adj (u v : nat) := (u == v-1).

  Definition Pn : sgraph.
  Proof.
    refine {| svertex := ordinal_finType n ;
              sedge := give_sg Pn_adj (n:=n) |}.
    - exact: give_sg_sym. - exact: give_sg_irrefl.
  Qed.
End path_graph.

(* 'C_n : circuit of n vertices C_n *)
Section circuit_graph.
  Variables n : nat.

  Let Cn_adj (u v : nat) := (u == v-1) || ((u == 0) && (v == n-1)).

  Definition Cn : sgraph.
  Proof.
    refine {| svertex := ordinal_finType n ;
              sedge := give_sg Cn_adj (n:=n) |}.
    - exact: give_sg_sym. - exact: give_sg_irrefl.
  Qed.
End circuit_graph.

(* 'CC_n : complement of circuit of n vertices *)
Section circuit_graph.
  Variables n : nat.

  Let CCn_adj (u v : nat) := ~~ ((u == v-1) || ((u == 0) && (v == n-1))).

  Definition CCn : sgraph.
  Proof.
    refine {| svertex := ordinal_finType n ;
              sedge := give_sg CCn_adj (n:=n) |}.
    - exact: give_sg_sym. - exact: give_sg_irrefl.
  Qed.
End circuit_graph.

(* Claw *)
Let claw_adj(u v : nat) :=
  match u, v with
  | 0, 1 => true
  | 0, 2 => true
  | 0, 3 => true
  | _, _ => false
end.

Definition claw : sgraph.
Proof.
  refine {| svertex := ordinal_finType 4 ;
            sedge := give_sg claw_adj (n:=4) |}.
  - exact: give_sg_sym. - exact: give_sg_irrefl.
Qed.

(* Bull *)
Let bull_adj(u v : nat) :=
  match u, v with
  | 0, 1 => true
  | 0, 2 => true
  | 1, 2 => true
  | 1, 3 => true
  | 2, 4 => true
  | _, _ => false
end.

Definition bull : sgraph.
Proof.
  refine {| svertex := ordinal_finType 5 ;
            sedge := give_sg claw_adj (n:=5) |}.
  - exact: give_sg_sym. - exact: give_sg_irrefl.
Qed.

End Graph_definitions.

Notation "''K_' n , m" := (Knm n m)
  (at level 8, n at level 2, m at level 2, format "''K_' n , m").

Notation "''P_' n" := (Pn n)
  (at level 8, n at level 2, format "''P_' n").

Notation "''C_' n" := (Cn n)
  (at level 8, n at level 2, format "''C_' n").

Notation "''CC_' n" := (Cn n)
  (at level 8, n at level 2, format "''CC_' n").


(**********************************************************************************)
Section Upper_Weighted_Irredundant_Properties.

Variable G : sgraph.
Let G' := newgraph G.

(* Some vertex numbering *)
Definition v0_4 := @Ordinal 4 0 isT : 'I_4.
Definition v1_4 := @Ordinal 4 1 isT : 'I_4.
Definition v2_4 := @Ordinal 4 2 isT : 'I_4.
Definition v3_4 := @Ordinal 4 3 isT : 'I_4.

Definition v0_5 := @Ordinal 5 0 isT : 'I_5.
Definition v1_5 := @Ordinal 5 1 isT : 'I_5.
Definition v2_5 := @Ordinal 5 2 isT : 'I_5.
Definition v3_5 := @Ordinal 5 3 isT : 'I_5.
Definition v4_5 := @Ordinal 5 4 isT : 'I_5.

Definition v0_6 := @Ordinal 6 0 isT : 'I_6.
Definition v1_6 := @Ordinal 6 1 isT : 'I_6.
Definition v2_6 := @Ordinal 6 2 isT : 'I_6.
Definition v3_6 := @Ordinal 6 3 isT : 'I_6.
Definition v4_6 := @Ordinal 6 4 isT : 'I_6.
Definition v5_6 := @Ordinal 6 5 isT : 'I_6.

(* To prove G' P4-free => G {P4,K23}-free we do the following:
     If G has P4 as an induced subgraph, then G' does too.
     If G has K23 as an induced subgraph, then G' has a P4. *)

Theorem G'P4free : 'P_4 \subgraph G \/ 'K_2,3 \subgraph G -> 'P_4 \subgraph G'.
Proof.
  case.
  - move=> P4subG ; move: (subgraph_G_G' G) ; rewrite -/G' => GsubG'.
    exact: subgraph_trans P4subG GsubG'.
  - (* Hay que ver la prueba escrita y trabajar un poquito *)
Admitted.

Variables GP4 GK23 : sgraph.
Hypothesis G_is_P4 : isomorphic GP4 'P_4.
Hypothesis G_is_K23 : isomorphic GK23 'K_2,3.

Corollary G'P4free' : GP4 \subgraph G \/ GK23 \subgraph G -> GP4 \subgraph G'.
Proof.
  case.
  - move=> P4subG ; apply: (subgraph_trans (sub_G1_G2 G_is_P4)).
    apply: G'P4free ; left.
    by apply: (subgraph_trans (sub_G2_G1 G_is_P4)).
  - move=> K23subG ; apply: (subgraph_trans (sub_G1_G2 G_is_P4)).
    apply: G'P4free ; right.
    by apply: (subgraph_trans (sub_G2_G1 G_is_K23)).
Qed.

(* To prove G' claw-free => G {claw,bull,P6,CC6}-free we do the following:
     If G has claw as an induced subgraph, then G' does too.
     If G has bull as an induced subgraph, then G' has a claw.
     If G has P6 as an induced subgraph, then G' has a claw.
     If G has a complement of C6 as an induced subgraph, then G' has a claw. *)

Theorem G'clawfree : claw \subgraph G \/ bull \subgraph G \/
                     'P_6 \subgraph G \/ 'CC_6 \subgraph G -> claw \subgraph G'.
Proof.
  case.
  { move=> clawsubG ; move: (subgraph_G_G' G) ; rewrite -/G' => GsubG'.
    exact: subgraph_trans clawsubG GsubG'. }
  case.
Admitted.

Variables Gclaw Gbull GP6 GCC6 : sgraph.
Hypothesis G_is_claw : isomorphic Gclaw claw.
Hypothesis G_is_bull : isomorphic Gbull bull.
Hypothesis G_is_P6 : isomorphic GP6 'P_6.
Hypothesis G_is_CC6 : isomorphic GCC6 'CC_6.

Corollary G'clawfree' : Gclaw \subgraph G \/ Gbull \subgraph G \/
                          GP6 \subgraph G \/ GCC6 \subgraph G -> Gclaw \subgraph G'.
Proof.
  case.
  { move=> clawsubG ; apply: (subgraph_trans (sub_G1_G2 G_is_claw)).
    apply: G'clawfree ; left.
    by apply: (subgraph_trans (sub_G2_G1 G_is_claw)). }
  case.
  { move=> bullsubG ; apply: (subgraph_trans (sub_G1_G2 G_is_claw)).
    apply: G'clawfree ; right ; left.
    by apply: (subgraph_trans (sub_G2_G1 G_is_bull)). }
  case.
  - move=> P6subG ; apply: (subgraph_trans (sub_G1_G2 G_is_claw)).
    apply: G'clawfree ; right ; right ; left.
    by apply: (subgraph_trans (sub_G2_G1 G_is_P6)).
  - move=> CC6subG ; apply: (subgraph_trans (sub_G1_G2 G_is_claw)).
    apply: G'clawfree ; right ; right ; right.
    by apply: (subgraph_trans (sub_G2_G1 G_is_CC6)).
Qed.

End Upper_Weighted_Irredundant_Properties.

















(* A PARTIR DE ACA ES LO VIEJO!! *)















Lemma G'_vertex_def : forall x : G', (exists u v : G, u -*- v).
Proof.
  move=> /= [x xinV'].
  exists x.1.
  exists x.2.
  move: xinV'.
  by rewrite in_set.
Qed.

Lemma G'_edge_def : forall x y : G', x -- y -> (exists u v w r : G,
          ([set u; v] != [set w; r]) /\ ((v -*- w) \/ (r -*- u))).
Proof.
  move=> [x xinV'] [y yinV'] /andP /= [x_neq_y /orP cond2_newgraph_rel].
  have pair_neq: (x.1 != y.1) \/ (x.2 != y.2).
  apply/orP; move: x_neq_y; apply/contraR.
  rewrite negb_or => /andP [/negPn/eqP x1_eq /negPn/eqP x2_eq].
  by apply/eqP/injective_projections.
  case: (boolP ((x.1 == y.2) && (x.2 == y.1))) => [/andP [/eqP x1_eq /eqP x2_eq] | neg_perm].
  - exists x.1.
    exists y.2.
    exists y.1.
    exists x.2.
    split.
    + case: pair_neq => [x1_neq | x2_neq].
      * rewrite -x1_eq x2_eq !setUid.
        move: x1_neq; apply: contra_neq => set_eq.
        by apply/set1P; rewrite -set_eq in_set1.
      * rewrite x1_eq -x2_eq !setUid.
        move: x2_neq; apply: contra_neq => set_eq.
        by apply/set1P; rewrite set_eq in_set1.
    + by left; rewrite /= in_set cl_sg_sym in yinV'.
  - exists x.1.
    exists x.2.
    exists y.1.
    exists y.2.
    split.
    + apply/contraT => doubleton_eq.
      move/doubleton_eq_iff: (eqP (negPn doubleton_eq)) => doubleton_eq_equiv.
      case: doubleton_eq_equiv => [[x1_eq x2_eq] | [x1_eq x2_eq]].
      * by case: pair_neq => [x1_neq | x2_neq]; [rewrite x1_eq eq_refl in x1_neq | rewrite x2_eq eq_refl in x2_neq].
      * by rewrite x1_eq x2_eq !eq_refl in neg_perm.
    + by case: cond2_newgraph_rel => [? | ?]; [left; rewrite cl_sg_sym | right].
Qed.

Lemma G'_vertex_def' : forall x : G', (val x).1 -*- (val x).2.
Proof.
  move=> /= [x xinV'] /=.
  move: xinV'.
  by rewrite in_set.
Qed.

Lemma G'_edge_def' : forall x y : G', x -- y -> (val x != val y) /\
          ((val y).1 -*- (val x).2 \/ (val y).2 -*- (val x).1).
Proof. by move=> [x _] [y _] /andP /= [x_neq_y /orP cond2_newgraph_rel]. Qed.


(* Function h_vw maps a vertex v in D (an irredundant set) to (v,w) where w is one of its
 * private vertices *)
Section h_vertex_and_its_private_definition.

  Variable D : {set G}.

  Hypothesis Dirr : irredundant D.

  Variable v: G.

  Hypothesis vinD: v \in D.

(*  Alternative (that uses "pick"):

  Let w_opt := [pick u | private D v u].
  Let w := if w_opt is Some u then u else v.

  Local Lemma w_is_private : private D v w.
  Proof.
    rewrite /w /w_opt.
    case: pickP => [? ? | private_eq_pred0]; first by done.
    move/irredundantP: Dirr => /(_ v vinD) /(private_set_not_empty vinD).
    elim => u.
    by rewrite private_eq_pred0.
  Qed. *)

  Local Lemma w_exists : exists w : G, private D v w.
  Proof. by  move/irredundantP: Dirr => /(_ v vinD) /(private_set_not_empty vinD). Qed.

  Let w : G := xchoose w_exists.
  Let w_is_private : private D v w := xchooseP w_exists.

  Lemma vw_in_V' : (v, w) \in V' G.
  Proof.
    rewrite /V' in_set /=.
    move: w_is_private.
    rewrite /private.
    by move/andP=> [ ? _ ].
  Qed.

  Definition h_vw := Sub (v, w) vw_in_V' : G'. (* i.e. {x : G * G | x \in V' G} *)
  Definition set_h_vw := set1 h_vw.

  Lemma h_vw1 : (val h_vw).1 = v.
  Proof. by rewrite /=. Qed.

  Lemma h_vw2 : private D v (val h_vw).2.
  Proof. by rewrite /= w_is_private. Qed.

End h_vertex_and_its_private_definition.

Definition h_vw' (D : {set G}) (Dirr : irredundant D) (v : G) :=
          if @idP (v \in D) is ReflectT p then set_h_vw Dirr p else set0.

Lemma h_vw'P1 (D : {set G}) (Dirr : irredundant D) (v : G) (vD : v \in D) : h_vw' Dirr v = set_h_vw Dirr vD.
Proof. rewrite /h_vw'; case: {-}_ / idP => [vD'|//]; by rewrite (bool_irrelevance vD' vD). Qed.

Lemma h_vw'P0 (D : {set G}) (Dirr : irredundant D) (v : G) (vnD: v \notin D) : h_vw' Dirr v = set0.
Proof.
  rewrite /h_vw'; case: {-}_ / idP => [//|vnD'] ; last by rewrite /=.
  move=> vinD; apply/eqP ; apply contraT=> _; by move/negP in vnD.
Qed.

Lemma h_vw'_not_empty (D : {set G}) (Dirr : irredundant D) (v : G) (x : G') : x \in h_vw' Dirr v -> v \in D.
Proof.
  move=> H; apply contraT=> vnotinD.
  by rewrite (h_vw'P0 Dirr vnotinD) in_set0 in H.
Qed.

(* For a given irredundant set D of G, there exists a stable set S of G' such that w(D) = w'(S) *)
Theorem irred_G_to_stable_G' (D : {set G}) (Dirr : irredundant D) : exists2 S : {set G'}, stable S & weight_set weight D = weight_set weight' S.
Proof.
  set S := \bigcup_(v in G) (h_vw' Dirr v).
  exists S.
  rewrite /stable.
  apply/forallP=> x ; apply/forallP=> y.
  apply/implyP=> xinS ; apply/implyP=> yinS.
(*  move/bigcupP in xinS; move/bigcupP in yinS.*)
  (* x = (v1,w1) *)
  move/bigcupP: xinS ; elim=> [v1 v1inG] xinh_vw'v1.
  move: (xinh_vw'v1)=> /h_vw'_not_empty v1inD.
  rewrite (h_vw'P1 Dirr v1inD) in_set1 in xinh_vw'v1.
  move/eqP in xinh_vw'v1.
  (* y = (v2,w2) *)
  move/bigcupP: yinS; elim=> [v2 v2inG] yinh_vw'v2.
  move: (yinh_vw'v2)=> /h_vw'_not_empty v2inD.
  rewrite (h_vw'P1 Dirr v2inD) in_set1 in yinh_vw'v2.
  move/eqP in yinh_vw'v2.
  (* stable *)
  rewrite xinh_vw'v1 yinh_vw'v2.
  suff H: ~~ (newgraph_rel (h_vw Dirr v1inD) (h_vw Dirr v2inD)) by rewrite /=.
  rewrite /newgraph_rel.
  rewrite negb_and.
  case: (boolP (v2 == v1)) ; last first.
  (* case v1 != v2 *)
  move/eqP=> v1neqv2.
  apply/orP/or_intror.
  rewrite negb_or; apply/andP ; split.
  rewrite h_vw1.
  have privateV1: private D v1 (val (h_vw Dirr v1inD)).2 by exact: (h_vw2 Dirr v1inD).
  move/privateP: privateV1=> [_ v1domw]; move: (v1domw v2 v2inD)=> v1eqv2.
  apply contraT; rewrite negbK; move=> v2domw.
  by move: (v1eqv2 v2domw).
  rewrite h_vw1.
  have privateV2: private D v2 (val (h_vw Dirr v2inD)).2 by exact: (h_vw2 Dirr v2inD).
  move/privateP: privateV2=> [_ v2domw]; move: (v2domw v1 v1inD)=> v1eqv2.
  apply contraT; rewrite negbK; move=> v1domw; rewrite cl_sg_sym in v1domw.
  move: (v1eqv2 v1domw).
  by move/eqP in v1neqv2; rewrite eq_sym in v1neqv2; move/eqP in v1neqv2.
  (* case v1 == v2 *)
  move/eqP=> v1eqv2.
  apply/orP ; left.
  rewrite negbK /= xpair_eqE; apply/andP; split ; first by rewrite v1eqv2.
  apply/eqP.
  have samePrivateVertex: private D v1 =1 private D v2 by rewrite v1eqv2.
  exact: eq_xchoose (w_exists Dirr v1inD) (w_exists Dirr v2inD) samePrivateVertex.
  (* same weight *)
  rewrite /weight_set.
  (* si podemos probar que la función h_vw es biyectiva para todo v en D,
   * ¿podría ser suficiente probar "weight v = weight' (h_vw v)" ? *)
Admitted.

