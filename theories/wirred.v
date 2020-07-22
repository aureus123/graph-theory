
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

Lemma newgraph_subgraph (G H : sgraph) : G \subgraph H -> newgraph G \subgraph newgraph H.
Proof.
  rewrite /induced_subgraph; elim=> [h inj_h ind_hom_h].
  have refine_img : forall v : newgraph G, h (val v).1 -*- h (val v).2. {
    move=> v; move: (valP v); rewrite !inE.
    rewrite [(val v).1 -*- (val v).2]/dominates; case/orP.
    - move/eqP ->; exact: dominates_refl.
    - by rewrite ind_hom_h=> dom; apply/orP/or_intror. }
  pose h' := fun x : newgraph G => (h (val x).1, h (val x).2).
  (*exists h'.*)
Admitted.

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

(* claw: a complete bipartite K_{1,3} *)
Definition claw := Knm 1 3.

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
            sedge := give_sg bull_adj (n:=5) |}.
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

(*
Let h (g : 'P_4) :=
   1 -> (4,1)
   2 -> (3,1)
   3 -> (2,3)
   4 -> (2,5)
*)

Lemma P4subK23' : 'P_4 \subgraph newgraph 'K_2,3.
Admitted.

(* To prove G' P4-free => G {P4,K23}-free we do the following:
     If G has P4 as an induced subgraph, then G' does too.
     If G has K23 as an induced subgraph, then G' has a P4. *)

Theorem G'P4free : 'P_4 \subgraph G \/ 'K_2,3 \subgraph G -> 'P_4 \subgraph G'.
Proof.
  case.
  - move=> P4subG ; move: (subgraph_G_G' G) ; rewrite -/G' => GsubG'.
    exact: subgraph_trans P4subG GsubG'.
  - by move/newgraph_subgraph=> K23'subG; move: (subgraph_trans P4subK23' K23'subG).
   (* Hay que ver la prueba escrita y trabajar un poquito *)
Qed.

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
