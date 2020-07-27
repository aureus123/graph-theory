
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

Section Newgraph_Subgraph.

Variable G H : sgraph.
Let G' := newgraph G.
Let H' := newgraph H.
Variable h : G -> H.
Hypothesis inj_h : injective h.
Hypothesis ind_hom_h : induced_hom h.
Variable v : G'.

Let hv1_hv2_in_H' : (h (val v).1, h (val v).2) \in V' H.
Proof.
  rewrite inE /=. move: (valP v); rewrite !inE.
  rewrite [(val v).1 -*- (val v).2]/dominates; case/orP.
  - move/eqP ->; exact: dominates_refl.
  - by rewrite ind_hom_h=> dom; apply/orP/or_intror.
Qed.

Lemma h_eq (w : G') : ((val v).1 == (val w).2) = (h (val v).1 == h (val w).2).
Proof.
  case (boolP ((val v).1 == (val w).2)).
    - by move/eqP=> eq; rewrite eq !eq_refl.
    - apply/contraNeq; rewrite negbK; move/eqP. by move=> hip; move: (inj_h hip); move ->.
Qed.

Lemma h_adj (w : G') : ((val v).1 -- (val w).2) = (h (val v).1 -- h (val w).2).
Proof.
  case (boolP ((val v).1 -- (val w).2)); last first.
  apply/contraNeq; rewrite negbK. all: by rewrite ind_hom_h.
Qed.

Definition hv := Sub (h (val v).1, h (val v).2) hv1_hv2_in_H' : H'.

End Newgraph_Subgraph.

Lemma newgraph_subgraph (G H : sgraph) : G \subgraph H -> newgraph G \subgraph newgraph H.
Proof.
  elim=> [h inj_h ind_hom_h].
  exists (hv ind_hom_h).
  - move=> x y /eqP/andP [/eqP ? /eqP ?].
    by apply/val_inj/eqP/andP; split; apply/eqP/inj_h.
  - move=> x y.
    suff: newgraph_rel x y <-> newgraph_rel (hv ind_hom_h x) (hv ind_hom_h y) by [].
    rewrite /newgraph_rel /dominates /=.
    have eq1 : (sval x != sval y) = ((h (sval x).1, h (sval x).2) != (h (sval y).1, h (sval y).2)).
    { case (boolP (sval x != sval y)).
      + apply/contraNeq; rewrite negbK; move/eqP; rewrite pair_equal_spec=> [[h1 h2]].
        have ? := inj_h (sval x).1 (sval y).1 h1; have ? := inj_h (sval x).2 (sval y).2 h2.
        rewrite [val x]surjective_pairing [val y]surjective_pairing xpair_eqE; apply/andP.
        split; by apply/eqP.
      + rewrite negbK [val x]surjective_pairing [val y]surjective_pairing xpair_eqE=>/andP [/eqP h1 /eqP h2].
        by rewrite h1 h2 /= eq_refl.
    }
    move: (h_eq inj_h x y); rewrite eq_sym [(h (val x).1 == h (val y).2)]eq_sym; move ->.
    move: (h_adj ind_hom_h x y); rewrite sg_sym [(h (val x).1 -- h (val y).2)]sg_sym; move ->.
    by rewrite eq1 (h_eq inj_h y x) (h_adj ind_hom_h y x).
Qed.

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
  Proof. by rewrite /V' in_set /= dominates_refl. Qed.

  Definition h_vv := Sub (v, v) vv_in_V' : G'.

  Fact h_vv1 : (val h_vv).1 = v.
  Proof. by rewrite /=. Qed.

  Fact h_vv2 : (val h_vv).2 = v.
  Proof. by rewrite /=. Qed.
End h_counterpart_definition.

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

  Fact h_DwP (x : G') : x \in h_Dw -> (val x).1 \in D /\ (val x).2 \in private_set D (val x).1.
  Proof. move=> H; split. by exact: h_Dw1. by exact: h_Dw2. Qed.

  Fact h_Dw_unique (u v : G') : u \in h_Dw -> v \in h_Dw ->
          sval u != sval v -> (sval u).1 != (sval v).1.
  Proof.
    move=> uDw vDw; apply/contra=> u1eqv1.
    suff: ((sval u).1 == (sval v).1) && ((sval u).2 == (sval v).2) by auto.
    apply/andP; split; first by []. move/eqP in u1eqv1.
    have/bigcupP [a aD] := uDw; rewrite h_vw'1; move/set1P=>uprva.
    have/bigcupP [b bD] := vDw; rewrite h_vw'1; move/set1P=>vprvb.
    rewrite uprva vprvb !h_vw1 in u1eqv1.
    have H : (fun x => x \in private_set D a) =1 (fun x => x \in private_set D b) by rewrite u1eqv1.
    rewrite uprva vprvb /h_vw /=; apply/eqP.
    exact: eq_xchoose (elimTF (set0Pn (private_set D a))
     (elimTF (irredundantP D) Dirr a aD)) (elimTF (set0Pn (private_set D b))
     (elimTF (irredundantP D) Dirr b bD)) H.
  Qed.

  Lemma h_Dw_stable : @stable G' h_Dw.
  Proof.
    apply/stableP=> [u v uh_Dw vh_Dw].
    have/h_DwP [u1D u2prvu1] := uh_Dw. have/h_DwP [v1D v2prvv1] := vh_Dw.
    suff: ~~ (newgraph_rel u v) by rewrite /=.
    apply/contraT; move/negPn; rewrite /newgraph_rel /=.
    move/andP=> [uneqv /orP H]; elim H.
    - move=> v1domu2; move/privateP: (u2prvu1)=> [_ prvu2].
      move: (prvu2 (sval v).1 v1D v1domu2)=> v1equ1.
      move/negP: (h_Dw_unique uh_Dw vh_Dw uneqv). by rewrite v1equ1 eq_refl.
    - rewrite cl_sg_sym=> u1domv2; move/privateP: (v2prvv1)=> [_ prvu2].
      move: (prvu2 (sval u).1 u1D u1domv2)=> v1equ1.
      move/negP: (h_Dw_unique uh_Dw vh_Dw uneqv). by rewrite v1equ1 eq_refl.
  Qed.

  (* Proof not using induction. Needs lemma from preliminaries. *)
  Lemma weight_D_eq_h_Dw : W D = W' h_Dw.
  Proof.
    rewrite /W' /weight_set (partition_disjoint_bigcup_P weight').
    - by under eq_bigr=> v vD do rewrite (h_vw'1 vD) big_set1 /weight' h_vw1.
    - move=> i j iD jD ineqj; apply/disjointP=> x.
      rewrite (h_vw'1 iD) (h_vw'1 jD) !in_set1=> /eqP xprvi.
      rewrite xprvi => /eqP H.
      have: val (h_vw iD) == val (h_vw jD) by rewrite H.
      by rewrite xpair_eqE ; move/nandP/orP ; rewrite ineqj.
  Qed.
End set_h_vertex_and_its_private_definition.

(* Function h_inv takes a stable set S of G' and gives the set {v : (v,w) \in S} *)
Section set_h_inverse.
  Variable S : {set G'}.
  Hypothesis Sst : stable S.

  Definition h_inv := \bigcup_(x in S) [set (val x).1].

  Lemma h_inv_irr : @irredundant G h_inv.
  Proof.
    apply/forallP=> v. apply/implyP; move/bigcupP.
    elim=> [v' v'S v'1v]; rewrite inE in v'1v; move/eqP in v'1v. apply/set0Pn.
    exists (val v').2; apply/privateP; split. by move: (valP v'); rewrite v'1v !inE.
    move=> u /bigcupP [u' u'S u'1v]. rewrite inE in u'1v; move/eqP in u'1v.
    move/stableP: Sst=> /(_ u' v' u'S v'S)=> u'nadjv'.
    have: ~~ newgraph_rel u' v' by []; move/nandP; case.
    - move/negbNE/eqP; rewrite [val u']surjective_pairing [val v']surjective_pairing.
      by rewrite pair_equal_spec=> [[H _] _]; rewrite u'1v v'1v.
    - move/norP=> [_ H]; rewrite u'1v cl_sg_sym. by apply/contraTeq.
  Qed.

  Lemma weight_S_eq_h_inv : W h_inv = W' S.
  Proof.
    rewrite /W /W' /weight_set (partition_disjoint_bigcup_P weight).
    by under eq_bigr=> v' v'S do rewrite big_set1.
    move=> i j iS jS ineqj. rewrite disjoints1 in_set1.
    move/stableP: Sst=> /(_ i j iS jS). apply/contra=>/eqP i1eqj1.
    suff: newgraph_rel i j by []; rewrite /newgraph_rel /=.
    apply/andP; split. exact: ineqj.
    apply/orP/or_introl. rewrite -i1eqj1. by move: (valP i); rewrite !inE.
  Qed.
End set_h_inverse.


(* For a given irredundant set D of G, there exists a stable set S of G' such that w(D) = w'(S) *)
Lemma irred_G_to_stable_G' (D : {set G}) (Dirr : irredundant D) :
  exists2 S : {set G'}, stable S & W D = W' S.
Proof. exists (h_Dw Dirr) ; [ exact: h_Dw_stable | exact: weight_D_eq_h_Dw ]. Qed.

(* For a given stable set S of G', there exists an irredundant set D of G such that w(D) = w'(G') *)
Lemma stable_G'_to_irred_G (S : {set G'}) (Sst : stable S) :
  exists2 D : {set G}, irredundant D & W D = W' S.
Proof. exists (h_inv S) ; [ exact: h_inv_irr | exact: weight_S_eq_h_inv]. Qed.

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
Definition give_sg (f : nat -> nat -> bool) (n : nat) (i j : 'I_n) :=
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

End Graph_definitions.

Notation "''K_' n , m" := (Knm n m)
  (at level 8, n at level 2, m at level 2, format "''K_' n , m").

Notation "''P_' n" := (Pn n)
  (at level 8, n at level 2, format "''P_' n").

Notation "''C_' n" := (Cn n)
  (at level 8, n at level 2, format "''C_' n").

Notation "''CC_' n" := (CCn n)
  (at level 8, n at level 2, format "''CC_' n").


(**********************************************************************************)
Section Upper_Weighted_Irredundant_Properties.

Variable G : sgraph.
Let G' := newgraph G.

(* vn@m refers to the nth. vertex of a graph of m vertices, with 0 <= n < m *)
Notation "''v' n @ m" := (@Ordinal m n isT) (at level 0, m, n at level 8, format "''v' n @ m").

Ltac subgraph_proof Hi Hj := try (by rewrite (bool_irrelevance Hi Hj)); by rewrite /=.

Section Construction_of_Induced_Subgraphs.

(* ¿Hay una manera de dar el objeto de la prueba 'rewrite inE' en cada una de las
   siguientes construcciones de Sub para ahorrarme de escribir todas estas lineas
   de pruebas idénticas? *)

Lemma P4subK23' : 'P_4 \subgraph newgraph 'K_2,3.
Proof.
  have K23'_v1 : ('v3@5, 'v0@5) \in V' 'K_2,3 by rewrite inE.
  have K23'_v2 : ('v2@5, 'v0@5) \in V' 'K_2,3 by rewrite inE.
  have K23'_v3 : ('v1@5, 'v2@5) \in V' 'K_2,3 by rewrite inE.
  have K23'_v4 : ('v1@5, 'v4@5) \in V' 'K_2,3 by rewrite inE.
  pose h (v : 'P_4) : newgraph 'K_2,3 :=
    match v with
    | Ordinal 0 _ => Sub ('v3@5, 'v0@5) K23'_v1
    | Ordinal 1 _ => Sub ('v2@5, 'v0@5) K23'_v2
    | Ordinal 2 _ => Sub ('v1@5, 'v2@5) K23'_v3
    | Ordinal _ _ => Sub ('v1@5, 'v4@5) K23'_v4
    end.
  exists h. all: case => [[|[|[|[|i]]]] Hi]; case => [[|[|[|[|j]]]] Hj]; subgraph_proof Hi Hj.
Qed.

Lemma claw_sub_bull' : claw \subgraph newgraph bull.
Proof.
  have bull'_v1 : ('v2@5, 'v3@5) \in V' bull by rewrite inE.
  have bull'_v2 : ('v0@5, 'v0@5) \in V' bull by rewrite inE.
  have bull'_v3 : ('v1@5, 'v1@5) \in V' bull by rewrite inE.
  have bull'_v4 : ('v4@5, 'v4@5) \in V' bull by rewrite inE.
  pose h (v : claw) : newgraph bull :=
    match v with
    | Ordinal 0 _ => Sub ('v2@5, 'v3@5) bull'_v1
    | Ordinal 1 _ => Sub ('v0@5, 'v0@5) bull'_v2
    | Ordinal 2 _ => Sub ('v1@5, 'v1@5) bull'_v3
    | Ordinal _ _ => Sub ('v4@5, 'v4@5) bull'_v4
    end.
  exists h. all: case => [[|[|[|[|i]]]] Hi]; case => [[|[|[|[|j]]]] Hj]; subgraph_proof Hi Hj.
Qed.

Lemma claw_sub_P6' : claw \subgraph newgraph 'P_6.
Proof.
  have P6'_v1 : ('v3@6, 'v2@6) \in V' 'P_6 by rewrite inE.
  have P6'_v2 : ('v1@6, 'v0@6) \in V' 'P_6 by rewrite inE.
  have P6'_v3 : ('v5@6, 'v4@6) \in V' 'P_6 by rewrite inE.
  have P6'_v4 : ('v2@6, 'v3@6) \in V' 'P_6 by rewrite inE.
  pose h (v : claw) : newgraph 'P_6 :=
    match v with
    | Ordinal 0 _ => Sub ('v3@6, 'v2@6) P6'_v1
    | Ordinal 1 _ => Sub ('v1@6, 'v0@6) P6'_v2
    | Ordinal 2 _ => Sub ('v5@6, 'v4@6) P6'_v3
    | Ordinal _ _ => Sub ('v2@6, 'v3@6) P6'_v4
    end.
  exists h. all: case => [[|[|[|[|i]]]] Hi]; case => [[|[|[|[|j]]]] Hj]; subgraph_proof Hi Hj.
Qed.

Lemma claw_sub_CC6' : claw \subgraph newgraph 'CC_6.
Proof.
  have CC6'_v1 : ('v5@6, 'v5@6) \in V' 'CC_6 by rewrite inE.
  have CC6'_v2 : ('v1@6, 'v4@6) \in V' 'CC_6 by rewrite inE.
  have CC6'_v3 : ('v3@6, 'v0@6) \in V' 'CC_6 by rewrite inE.
  have CC6'_v4 : ('v5@6, 'v2@6) \in V' 'CC_6 by rewrite inE.
  pose h (v : claw) : newgraph 'CC_6 :=
    match v with
    | Ordinal 0 _ => Sub ('v5@6, 'v5@6) CC6'_v1
    | Ordinal 1 _ => Sub ('v1@6, 'v4@6) CC6'_v2
    | Ordinal 2 _ => Sub ('v3@6, 'v0@6) CC6'_v3
    | Ordinal _ _ => Sub ('v5@6, 'v2@6) CC6'_v4
    end.
  exists h. all: case => [[|[|[|[|i]]]] Hi]; case => [[|[|[|[|j]]]] Hj]; subgraph_proof Hi Hj.
Qed.

End Construction_of_Induced_Subgraphs.

(* To prove G' P4-free => G {P4,K23}-free we do the following:
     If G has P4 as an induced subgraph, then G' does too.
     If G has K23 as an induced subgraph, then G' has a P4. *)

Theorem G'P4free : 'P_4 \subgraph G \/ 'K_2,3 \subgraph G -> 'P_4 \subgraph G'.
Proof.
  case.
  - move=> P4subG ; move: (subgraph_G_G' G) ; rewrite -/G' => GsubG'.
    exact: subgraph_trans P4subG GsubG'.
  - move/newgraph_subgraph=> K23'subG'. by move: (subgraph_trans P4subK23' K23'subG').
Qed.

Variables GP4 GK23 : sgraph.
Hypothesis G_is_P4 : isomorphic GP4 'P_4.
Hypothesis G_is_K23 : isomorphic GK23 'K_2,3.

Corollary G'P4free' : GP4 \subgraph G \/ GK23 \subgraph G -> GP4 \subgraph G'.
Proof.
  case.
  - move=> /(subgraph_trans (sub_G2_G1 G_is_P4)) P4subG.
    apply: (subgraph_trans (sub_G1_G2 G_is_P4)).
    by apply: G'P4free ; left.
  - move=> /(subgraph_trans (sub_G2_G1 G_is_K23)) K23subG.
    apply: (subgraph_trans (sub_G1_G2 G_is_P4)).
    by apply: G'P4free ; right.
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
  case. by move/newgraph_subgraph=> bull'subG'; move: (subgraph_trans claw_sub_bull' bull'subG').
  case. by move/newgraph_subgraph=> P6'subG'; move: (subgraph_trans claw_sub_P6' P6'subG').
  by move/newgraph_subgraph=> CC6'subG'; move: (subgraph_trans claw_sub_CC6' CC6'subG').
Qed.

Variables Gclaw Gbull GP6 GCC6 : sgraph.
Hypothesis G_is_claw : isomorphic Gclaw claw.
Hypothesis G_is_bull : isomorphic Gbull bull.
Hypothesis G_is_P6 : isomorphic GP6 'P_6.
Hypothesis G_is_CC6 : isomorphic GCC6 'CC_6.

Corollary G'clawfree' : Gclaw \subgraph G \/ Gbull \subgraph G \/
                          GP6 \subgraph G \/ GCC6 \subgraph G -> Gclaw \subgraph G'.
Proof.
  case.
  { move=> /(subgraph_trans (sub_G2_G1 G_is_claw)) clawsubG.
    apply: (subgraph_trans (sub_G1_G2 G_is_claw)).
    by apply: G'clawfree ; left. }
  case.
  { move=> /(subgraph_trans (sub_G2_G1 G_is_bull)) bullsubG.
    apply: (subgraph_trans (sub_G1_G2 G_is_claw)).
    by apply: G'clawfree ; right ; left. }
  case.
  - move=> /(subgraph_trans (sub_G2_G1 G_is_P6)) P6subG.
    apply: (subgraph_trans (sub_G1_G2 G_is_claw)).
    by apply: G'clawfree ; right ; right ; left.
  - move=> /(subgraph_trans (sub_G2_G1 G_is_CC6)) CC6subG.
    apply: (subgraph_trans (sub_G1_G2 G_is_claw)).
    by apply: G'clawfree ; right ; right ; right.
Qed.

Lemma forallOrdinalP4 (p : 'P_4 -> Prop) :
  (forall v : 'P_4, p v) <-> (p 'v0@4 /\ p 'v1@4 /\ p 'v2@4 /\ p 'v3@4).
Proof.
  split.
  - move=> H ; do 3 try split.
    + by move: (H 'v0@4).
    + by move: (H 'v1@4).
    + by move: (H 'v2@4).
    + by move: (H 'v3@4).
  - move=> [pv0 [pv1 [pv2 pv3]]] [v vlt4].
    do 4 try destruct v.
    all : try by rewrite (bool_irrelevance vlt4 isT).
    suff: ~ (v.+4 < 4) by contradiction.
    by apply/negP ; rewrite /=.
Qed.

Ltac t_x1x2 x1 x2 :=
  (suff : (x1, x2) \in V' G by rewrite /V' in_set /=) ;
  rewrite /x1 /x2 -surjective_pairing ; apply/valP.

Ltac t_v1v2 v1 v2 h h_hom := 
  (have : (h v2) -- (h v1) by rewrite -h_hom /edge_rel /= /give_sg /=) ;
  rewrite /edge_rel /= => /andP [_] ; rewrite /dominates orbA.

Ltac t_x1x2y1y2 x1 x2 y1 y2 v1 v2 h h_inj := 
  rewrite -[(x1 != y1) || (x2 != y2)]negbK negb_or !negbK -xpair_eqE ;
  (have : h v1 != h v2 by apply/negP ; move/eqP/h_inj) ;
  rewrite -!surjective_pairing ; apply: contra ; move/eqP/val_inj/eqP.

Ltac t_x1y2x2y1 x1 x2 y1 y2 v1 v2 h h_hom := 
  (have : ~~ (h v2) -- (h v1) by apply/negP ; rewrite -h_hom /edge_rel /= /give_sg /=) ;
  rewrite /edge_rel /= negb_and negbK -/x1 -/x2 -/y1 -/y2 ;
  (have : (sval (h v2) == sval (h v1) = false) by apply/negP ; move/eqP/val_inj/h_inj) ;
  move-> ; rewrite orFb /dominates !negb_or andbA.

Theorem G'P4free_rev : 'P_4 \subgraph G' -> 'P_4 \subgraph G \/ 'K_2,3 \subgraph G.
Proof.
  rewrite /induced_subgraph.
  move=> [h h_inj h_hom].

  (* in G', we have the path (a1,a2) - (b1,b2) - (c1,c2) - (d1,d2) *)
  set a1 := (val (h 'v0@4)).1.
  set a2 := (val (h 'v0@4)).2.
  set b1 := (val (h 'v1@4)).1.
  set b2 := (val (h 'v1@4)).2.
  set c1 := (val (h 'v2@4)).1.
  set c2 := (val (h 'v2@4)).2.
  set d1 := (val (h 'v3@4)).1.
  set d2 := (val (h 'v3@4)).2.

  (* The following comes from the fact that x1x2 are vertices of G' *)
  have a1a2 : (a1 == a2) || a1 -- a2 by t_x1x2 a1 a2.
  have b1b2 : (b1 == b2) || b1 -- b2 by t_x1x2 b1 b2.
  have c1c2 : (c1 == c2) || c1 -- c2 by t_x1x2 c1 c2.
  have d1d2 : (d1 == d2) || d1 -- d2 by t_x1x2 d1 d2.

  (* The following comes from the edges of the path P_4 in G' *)
  have a1b2a2b1 : (a1 == b2) || a1 -- b2 || (a2 == b1) || (a2 -- b1)
    by t_v1v2 'v0@4 'v1@4 h h_hom.
  have b1c2b2c1 : (b1 == c2) || b1 -- c2 || (b2 == c1) || (b2 -- c1)
    by t_v1v2 'v1@4 'v2@4 h h_hom.
  have c1d2c2d1 : (c1 == d2) || c1 -- d2 || (c2 == d1) || (c2 -- d1)
    by t_v1v2 'v2@4 'v3@4 h h_hom.

  (* The following comes from the fact that vertices of P_4 are different *)
  have a1a2b1b2 : (a1 != b1) || (a2 != b2)
    by t_x1x2y1y2 a1 a2 b1 b2 'v0@4 'v1@4 h h_inj.
  have a1a2c1c2 : (a1 != c1) || (a2 != c2)
    by t_x1x2y1y2 a1 a2 c1 c2 'v0@4 'v2@4 h h_inj.
  have a1a2d1d2 : (a1 != d1) || (a2 != d2)
    by t_x1x2y1y2 a1 a2 d1 d2 'v0@4 'v3@4 h h_inj.
  have b1b2c1c2 : (b1 != c1) || (b2 != c2)
    by t_x1x2y1y2 b1 b2 c1 c2 'v1@4 'v2@4 h h_inj.
  have b1b2d1d2 : (b1 != d1) || (b2 != d2)
    by t_x1x2y1y2 b1 b2 d1 d2 'v1@4 'v3@4 h h_inj.
  have c1c2d1d2 : (c1 != d1) || (c2 != d2)
    by t_x1x2y1y2 c1 c2 d1 d2 'v2@4 'v3@4 h h_inj.

  (* The following comes from the no-edges of P_4 in G' *)
  have a1c2a2c1 : (a1 != c2) && (~~ a1 -- c2) && (a2 != c1) && (~~ a2 -- c1)
    by t_x1y2x2y1 a1 a2 c1 c2 'v0@4 'v2@4 h h_hom.
  have a1d2a2d1 : (a1 != d2) && (~~ a1 -- d2) && (a2 != d1) && (~~ a2 -- d1)
    by t_x1y2x2y1 a1 a2 d1 d2 'v0@4 'v3@4 h h_hom.
  have b1d2b2d1 : (b1 != d2) && (~~ b1 -- d2) && (b2 != d1) && (~~ b2 -- d1)
    by t_x1y2x2y1 b1 b2 d1 d2 'v1@4 'v3@4 h h_hom.

  (* Here is a proof of injectivity of a given function, by giving proofs of
     inequalities among their vertices *)
  have h'_inj (h' : 'P_4 -> G)
    (v0v1 : h' 'v0@4 != h' 'v1@4) (v0v2 : h' 'v0@4 != h' 'v2@4)
    (v0v3 : h' 'v0@4 != h' 'v3@4) (v1v2 : h' 'v1@4 != h' 'v2@4)
    (v1v3 : h' 'v1@4 != h' 'v3@4) (v2v3 : h' 'v2@4 != h' 'v3@4)
       : forall x1 x2 : 'P_4, h' x1 = h' x2 -> x1 = x2.
  { move: (negP v0v1) => ?. move: (negP v0v2) => ?. move: (negP v0v3) => ?.
    move: (negP v1v2) => ?. move: (negP v1v3) => ?. move: (negP v2v3) => ?.
    rewrite !forallOrdinalP4 ; do 6 try split.
    all : try by [].
    all : try by move/eqP ; contradiction.
    all : try by move/eqP ; rewrite eq_sym ; contradiction.
  }

  (* Here is a proof of the homomorphism of a given function, by giving proofs
     of the edges and non-edges of the P_4 *)
  have h'_hom (h' : 'P_4 -> G)
    (e_v0v1 : h' 'v0@4 -- h' 'v1@4) (e_v1v2 : h' 'v1@4 -- h' 'v2@4)
    (e_v2v3 : h' 'v2@4 -- h' 'v3@4) (n_v0v2 : ~~ h' 'v0@4 -- h' 'v2@4)
    (n_v0v3 : ~~ h' 'v0@4 -- h' 'v3@4) (n_v1v3 : ~~ h' 'v1@4 -- h' 'v3@4)
       : forall x1 x2 : 'P_4, x1 -- x2 <-> h' x1 -- h' x2.
  { rewrite !forallOrdinalP4 ; do 7 try split.
    all : try by [].
    all : try by rewrite !sg_irrefl ; apply/implyP.
    all : try by rewrite [in X in _ -> X]sg_sym.
    all : try by apply: contraLR.
    all : try by rewrite [in X in X -> _]sg_sym ; apply: contraLR.
  }

  (* Start separation in cases... *)
  case/orP: a1a2 => [ a1eqa2 | a1neqa2 ].
  - case/orP: b1b2 => [ b1eqb2 | b1neqb2 ].
    + case/orP: c1c2 => [ c1eqc2 | c1neqc2 ].
      * case/orP: d1d2 => [ d1eqd2 | d1neqd2 ].
        (* a a --- b b --- c c --- d d *)
        -- left ; pose h' (v : 'P_4) :=
                  match v with
                  | Ordinal 0 _ => a1
                  | Ordinal 1 _ => b1
                  | Ordinal 2 _ => c1
                  | Ordinal _ _ => d1
                  end.
           exists h'.
           ++ apply: h'_inj ; rewrite /=.
              ** by move: a1a2b1b2 ; rewrite (eqP a1eqa2) (eqP b1eqb2) orbb.
              ** by move: a1a2c1c2 ; rewrite (eqP a1eqa2) (eqP c1eqc2) orbb.
              ** by move: a1a2d1d2 ; rewrite (eqP a1eqa2) (eqP d1eqd2) orbb.
              ** by move: b1b2c1c2 ; rewrite (eqP b1eqb2) (eqP c1eqc2) orbb.
              ** by move: b1b2d1d2 ; rewrite (eqP b1eqb2) (eqP d1eqd2) orbb.
              ** by move: c1c2d1d2 ; rewrite (eqP c1eqc2) (eqP d1eqd2) orbb.
           ++ apply: h'_hom ; rewrite /=.
              ** move: a1a2b1b2 ; rewrite (eqP a1eqa2) (eqP b1eqb2) orbb.
                 move: a1b2a2b1 ; rewrite (eqP a1eqa2) (eqP b1eqb2) -orbA orbb.
                 case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by []].
              ** move: b1b2c1c2 ; rewrite (eqP b1eqb2) (eqP c1eqc2) orbb.
                 move: b1c2b2c1 ; rewrite (eqP b1eqb2) (eqP c1eqc2) -orbA orbb.
                 case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by []].
              ** move: c1c2d1d2 ; rewrite (eqP c1eqc2) (eqP d1eqd2) orbb.
                 move: c1d2c2d1 ; rewrite (eqP c1eqc2) (eqP d1eqd2) -orbA orbb.
                 case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by []].
              ** by move: a1c2a2c1 => /andP [_] ; rewrite (eqP a1eqa2).
              ** by move: a1d2a2d1 => /andP [_] ; rewrite (eqP a1eqa2).
              ** by move: b1d2b2d1 => /andP [_] ; rewrite (eqP b1eqb2).
        (* a a --- b b --- c c --- c d2 *)
        -- left ; pose h' (v : 'P_4) :=
                  match v with
                  | Ordinal 0 _ => a1
                  | Ordinal 1 _ => b1
                  | Ordinal 2 _ => c1
                  | Ordinal _ _ => if (c1 -- d1) then d1 else d2
                  end.
           exists h'.
           ++ apply: h'_inj ; rewrite /=.
              ** by move: a1a2b1b2 ; rewrite (eqP a1eqa2) (eqP b1eqb2) orbb.
              ** by move: a1a2c1c2 ; rewrite (eqP a1eqa2) (eqP c1eqc2) orbb.
              ** rewrite (fun_if (fun d => a1 != d)) ; case: (boolP (c1 -- d1)).
                 --- by move: a1d2a2d1 => /andP [/andP [_ ?]] ; rewrite (eqP a1eqa2).
                 --- by move: a1d2a2d1 => /andP [/andP [ /andP [? _]]].
              ** by move: b1b2c1c2 ; rewrite (eqP b1eqb2) (eqP c1eqc2) orbb.
              ** rewrite (fun_if (fun d => b1 != d)) ; case: (boolP (c1 -- d1)).
                 --- by move: b1d2b2d1 => /andP [/andP [_ ?]] ; rewrite (eqP b1eqb2).
                 --- by move: b1d2b2d1 => /andP [/andP [ /andP [? _]]].
              ** rewrite (fun_if (fun d => c1 != d)) ; case: (boolP (c1 -- d1)).
                 --- by apply: contraL ; move/eqP-> ; rewrite sg_irrefl.
                 --- by apply: contra ; move/eqP-> ; rewrite sg_sym.
           ++ apply: h'_hom ; rewrite /=.
              ** move: a1a2b1b2 ; rewrite (eqP a1eqa2) (eqP b1eqb2) orbb.
                 move: a1b2a2b1 ; rewrite (eqP a1eqa2) (eqP b1eqb2) -orbA orbb.
                 case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by []].
              ** move: b1b2c1c2 ; rewrite (eqP b1eqb2) (eqP c1eqc2) orbb.
                 move: b1c2b2c1 ; rewrite (eqP b1eqb2) (eqP c1eqc2) -orbA orbb.
                 case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by []].
              ** rewrite (fun_if (fun d => c1 -- d)) ; case: (boolP (c1 -- d1)).
                 --- by move=> _.
                 --- move: c1d2c2d1 ; rewrite (eqP c1eqc2) ; case/orP ; last
                       by move=> ? /negP ; contradiction.
                     case/orP ; last by move/eqP->.
                     case/orP ; last by [].
                     by move/eqP-> ; apply: contraR ; rewrite sg_sym.
              ** by move: a1c2a2c1 => /andP [_] ; rewrite (eqP a1eqa2).
              ** rewrite (fun_if (fun d => a1 -- d)) ; case: (boolP (c1 -- d1)).
                 --- by move: a1d2a2d1 => /andP [/andP [_ ?]] ; rewrite (eqP a1eqa2).
                 --- by move: a1d2a2d1 => /andP [/andP [ /andP [_ ?]]].
              ** rewrite (fun_if (fun d => b1 -- d)) ; case: (boolP (c1 -- d1)).
                 --- by move: b1d2b2d1 => /andP [/andP [_ ?]] ; rewrite (eqP b1eqb2).
                 --- by move: b1d2b2d1 => /andP [/andP [ /andP [_ ?]]].
      * admit.
    + admit.
  - admit.
Admitted.

Corollary G'P4free'_rev : GP4 \subgraph G' -> GP4 \subgraph G \/ GK23 \subgraph G.
Proof.
  move=> /(subgraph_trans (sub_G2_G1 G_is_P4)) P4subG'.
  move: (G'P4free_rev P4subG') ; case.
  - by left ; apply: (subgraph_trans (sub_G1_G2 G_is_P4)).
  - by right ; apply: (subgraph_trans (sub_G1_G2 G_is_K23)).
Qed.

End Upper_Weighted_Irredundant_Properties.
