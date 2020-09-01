
(* Resolution of the Upper Weighted Irredundant Problem *)

From mathcomp Require Import all_ssreflect.
Require Import preliminaries digraph sgraph dom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


(** * Homomorphisms, isomorphisms and subgraphs. All "induced"! *)
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
Section TrfGraph_construction.

Variable G : sgraph.

Inductive trfgraph_vert_type := TrfGraphVert (x : G * G) of (x.1 -*- x.2).
Coercion of_trfgraph_vert_type x := let: TrfGraphVert s _ := x in s.
Canonical trfgraph_vert_subType := [subType for of_trfgraph_vert_type].
Definition trfgraph_vert_eqMixin := Eval hnf in [eqMixin of trfgraph_vert_type by <:].
Canonical trfgraph_vert_eqType := Eval hnf in EqType trfgraph_vert_type trfgraph_vert_eqMixin.
Definition trfgraph_vert_choiceMixin := [choiceMixin of trfgraph_vert_type by <:].
Canonical trfgraph_vert_choiceType := Eval hnf in ChoiceType trfgraph_vert_type trfgraph_vert_choiceMixin.
Definition trfgraph_vert_countMixin := [countMixin of trfgraph_vert_type by <:].
Canonical trfgraph_vert_countType := Eval hnf in CountType trfgraph_vert_type trfgraph_vert_countMixin.
Canonical trfgraph_vert_subCountType := [subCountType of trfgraph_vert_type].

Definition trfgraph_vert_enum : seq trfgraph_vert_type :=
  pmap insub (enum [set x : G * G | (x.1 -*- x.2)]).

Fact trfgraph_vert_enum_uniq : uniq trfgraph_vert_enum.
Proof.
by apply: pmap_sub_uniq; apply: enum_uniq.
Qed.

Fact mem_trfgraph_vert_enum x : x \in trfgraph_vert_enum.
Proof.
rewrite mem_pmap_sub mem_enum in_set.
by move: (valP x).
Qed.

Definition trfgraph_vert_finMixin :=
  Eval hnf in UniqFinMixin trfgraph_vert_enum_uniq mem_trfgraph_vert_enum.
Canonical trfgraph_vert_finType := Eval hnf in FinType trfgraph_vert_type trfgraph_vert_finMixin.
Canonical trfgraph_vert_subFinType := Eval hnf in [subFinType of trfgraph_vert_type].

Definition trfgraph_rel := [rel x y : trfgraph_vert_type | (x != y)
                                                   && ((y.1 -*- x.2)
                                                   || (y.2 -*- x.1))].

Lemma trfgraph_sym : symmetric trfgraph_rel.
Proof.
  move => ? ? /=.
  rewrite eq_sym ; apply: andb_id2l => _ ; rewrite cl_sg_sym orbC ; apply: orb_id2r => _.
  by rewrite cl_sg_sym.
Qed.

Lemma trfgraph_irrefl : irreflexive trfgraph_rel.
Proof.
  by move=> ?; rewrite /= eq_refl.
Qed.

Definition trfgraph := SGraph trfgraph_sym trfgraph_irrefl.

End TrfGraph_construction.

Section TrfGraph_Subgraph.

Variable G H : sgraph.
Let G' := trfgraph G.
Let H' := trfgraph H.
Variable h : G -> H.
Hypothesis inj_h : injective h.
Hypothesis ind_hom_h : induced_hom h.
Variable v : G'.

Let hv1_hv2_in_H' : (h v.1, h v.2).1 -*- (h v.1, h v.2).2.
Proof.
by case/orP: (valP v) => [/eqP -> | /ind_hom_h ?];
  [exact: dominates_refl | apply/orP; right].
Qed.

Lemma h_eq (w : G') : (v.1 == w.2) = (h v.1 == h w.2).
Proof.
  case (boolP (v.1 == w.2)).
    - by move/eqP=> ->; rewrite !eq_refl.
    - apply/contraNeq; rewrite negbK; move/eqP.
      by move=> hip; move: (inj_h hip); move ->.
Qed.

Lemma h_adj (w : G') : (v.1 -- w.2) = (h v.1 -- h w.2).
Proof.
by case: (boolP (v.1 -- w.2));
  [ | apply/contraNeq; rewrite negbK]; rewrite ind_hom_h.
Qed.

(*Definition hv := Sub (h (val v).1, h (val v).2) hv1_hv2_in_H' : H'.*)
Definition hv := TrfGraphVert hv1_hv2_in_H'.

End TrfGraph_Subgraph.

Lemma trfgraph_subgraph (G H : sgraph) : G \subgraph H -> trfgraph G \subgraph trfgraph H.
Proof.
  move=> [h inj_h ind_hom_h].
  exists (hv ind_hom_h).
  - move=> x y /eqP/andP [/eqP ? /eqP ?].
    by apply/val_inj/eqP/andP; split; apply/eqP/inj_h.
  - move=> x y.
    suff: trfgraph_rel x y <-> trfgraph_rel (hv ind_hom_h x) (hv ind_hom_h y) by [].
    rewrite /trfgraph_rel /dominates /=.
    have eq1 : (x != y) = ((h x.1, h x.2) != (h y.1, h y.2)).
    { case (boolP (x != y)).
      + apply/contraNeq; rewrite negbK; move/eqP; rewrite pair_equal_spec=> [[h1 h2]].
        have ? := inj_h x.1 y.1 h1; have ? := inj_h x.2 y.2 h2.
        apply/eqP/val_inj; rewrite [val x]surjective_pairing [val y]surjective_pairing.
        apply/eqP; rewrite xpair_eqE; apply/andP.
        split; by apply/eqP.
      + rewrite negbK [val x]surjective_pairing [val y]surjective_pairing xpair_eqE=>/andP [/eqP h1 /eqP h2].
        by rewrite h1 h2 //= !eq_refl.
    }
    move: (h_eq inj_h x y); rewrite eq_sym [(h x.1 == h y.2)]eq_sym; move ->.
    move: (h_adj ind_hom_h x y); rewrite sg_sym [(h x.1 -- h y.2)]sg_sym; move ->.
    by rewrite eq1 (h_eq inj_h y x) (h_adj ind_hom_h y x).
Qed.

(**********************************************************************************)
Section Upper_Weighted_Irredundant_Problem.

Variable G : sgraph.
Variable weight : G -> nat.
Hypothesis positive_weights : forall v : G, weight v > 0.

Let G' := trfgraph G.
Let weight' := fun x : G' => weight x.1.
Let W := weight_set weight.
Let W' := weight_set weight'.

Lemma positive_weights' : forall v : G', weight' v > 0.
Proof. by rewrite /weight'. Qed.

(* Function h_vv maps a vertex v in G to its counterpart vv in G' *)
Section h_counterpart_definition.
  Variable v : G.

  Let vv_in_V' : (v, v).1 -*- (v, v).2.
  Proof. exact: dominates_refl. Qed.

  Definition h_vv := TrfGraphVert vv_in_V' : G'.
End h_counterpart_definition.

Theorem subgraph_G_G' : G \subgraph G'.
Proof.
  rewrite /induced_subgraph.
  exists h_vv.
  (* h_vv is injective *)
  - by move=> ? ? [_ ?].
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

      Let vw_in_V' : (v, w).1 -*- (v, w).2.
      Proof. by move/privateP: w_is_private => [? _]. Qed.

      (*Definition h_vw := Sub (v, w) vw_in_V' : G'.*)
      Definition h_vw := TrfGraphVert vw_in_V'.

      Fact h_vw1 : h_vw.1 = v.
      Proof. by rewrite /=. Qed.

      Fact h_vw2 : h_vw.2 \in private_set D v.
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

  Fact h_Dw1 (x : G') : x \in h_Dw -> x.1 \in D.
  Proof.
    rewrite /h_Dw ; move/bigcupP=> [v vinD].
    by rewrite (h_vw'1 vinD) in_set1 ; move/eqP->.
  Qed.

  Fact h_Dw2 (x : G') : x \in h_Dw -> x.2 \in private_set D x.1.
  Proof.
    rewrite /h_Dw ; move/bigcupP=> [v vinD].
    by rewrite (h_vw'1 vinD) in_set1 ; move/eqP->; rewrite h_vw2.
  Qed.

  Fact h_DwP (x : G') : x \in h_Dw -> x.1 \in D /\ x.2 \in private_set D x.1.
  Proof. by  move=> ?; split; [exact: h_Dw1 | exact: h_Dw2]. Qed.

  Fact fst_inj_on_h_Dw (u v : G') : u \in h_Dw -> v \in h_Dw ->
            u.1 = v.1 -> u = v.
  Proof.
    move=> /bigcupP [? ?]; rewrite h_vw'1 => /set1P uprva.
    move=> /bigcupP [? ?]; rewrite h_vw'1 => /set1P vprvb u1eqv1.
    apply/eqP/andP; split; apply/eqP; first exact: u1eqv1.
    rewrite uprva vprvb /= in u1eqv1.
    rewrite uprva vprvb.
    apply/eq_xchoose.
    by rewrite u1eqv1.
  Qed.

  Lemma h_Dw_stable : @stable G' h_Dw.
  Proof.
    apply/stableP=> [u v uh_Dw vh_Dw].
    have/h_DwP [u1D u2prvu1] := uh_Dw; have/h_DwP [v1D v2prvv1] := vh_Dw.
    apply/contraT; move/negPn.
    move/andP=> [uneqv /orP H].
    case: H => [v1domu2 | ].
    - move/privateP: (u2prvu1)=> [_ prvu2].
      by rewrite (fst_inj_on_h_Dw vh_Dw uh_Dw (prvu2 v.1 v1D v1domu2)) eq_refl in uneqv.
    - rewrite cl_sg_sym=> u1domv2; move/privateP: (v2prvv1)=> [_ prvu2].
      by rewrite (fst_inj_on_h_Dw uh_Dw vh_Dw (prvu2 u.1 u1D u1domv2)) eq_refl in uneqv.
  Qed.

  (* Proof not using induction. Needs lemma from preliminaries. *)
  Lemma weight_D_eq_h_Dw : W D = W' h_Dw.
  Proof.
    rewrite /W' /weight_set (partition_disjoint_bigcup_P weight').
    - by under eq_bigr=> v vD do rewrite (h_vw'1 vD) big_set1 /weight' /=.
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

(*  Definition h_inv := \bigcup_(x in S) [set (val x).1].*)
  Definition h_inv := \bigcup_(x in S) [set x.1].

  Lemma h_inv_irr : @irredundant G h_inv.
  Proof.
    apply/forallP=> v; apply/implyP; move/bigcupP.
    move=> [v' v'S /set1P v'1v].
    apply/set0Pn; exists v'.2.
    apply/privateP; split; first by move: (valP v'); rewrite v'1v.
    move=> u /bigcupP [u' u'S /set1P u'1v].
    move/stableP: Sst=> /(_ u' v' u'S v'S)=> u'nadjv'.
    have: ~~ trfgraph_rel u' v' by []; move/nandP; case.
    - by move/negbNE/andP => [/eqP ? _] _; rewrite u'1v v'1v.
    - by move/norP=> [_ ?]; rewrite u'1v cl_sg_sym; apply/contraTeq.
  Qed.

  Lemma weight_S_eq_h_inv : W h_inv = W' S.
  Proof.
    rewrite /W /W' /weight_set (partition_disjoint_bigcup_P weight).
    by under eq_bigr=> v' v'S do rewrite big_set1.
    move=> i j iS jS ineqj. rewrite disjoints1 in_set1.
    move/stableP: Sst=> /(_ i j iS jS); apply/contra=>/eqP i1eqj1.
    suff: trfgraph_rel i j by [].
    apply/andP; split; first exact: ineqj.
    apply/orP/or_introl; rewrite -i1eqj1.
    exact: (valP i).
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

(**********************************************************************************)
Section IR_w_upper_bound.

Let M (n : nat) := ([set: G] == set0) || [exists v, [exists u, (u \in N[v]) && (W(N[v] :\ u) == n)]].

Local Fact exM : exists n : nat, M n.
Proof.
rewrite /M.
case: (boolP ([set: G] == set0)) => [_ |/set0Pn [x _]].
- by exists 0; apply/orP; left.
- exists (W N(x)).
  apply/orP; right.
  do 2 (apply/existsP; exists x).
  rewrite setU1K; last exact: v_notin_opneigh.
  by apply/andP; split; [exact: v_in_clneigh | done].
Qed.

Definition delta_w' := ex_minn exM.

Fact delta_w'_min (u v : G) : (u \in N[v]) -> delta_w' <= W (N[v] :\ u).
Proof.
move => ?; rewrite /delta_w'.
move: (ex_minnP exM) => [n _ n_min].
apply/n_min.
rewrite /M; apply/orP; right.
apply/existsP; exists v; apply/existsP; exists u.
by apply/andP.
Qed.

Lemma bound_weight_irredundant S :
  (irredundant S) -> W S <= W [set: G] - delta_w'.
Proof.
move/irredundantP=> irrS.
case: (boolP (S == set0)) => [/eqP-> | /set0Pn [u u_in_S]];
  first by rewrite /W /weight_set big_set0.
move/set0Pn: (irrS _ u_in_S)=> [v /privateP [udomv H]].
rewrite cl_sg_sym -in_cln in udomv.
apply/(@leq_trans ((\sum_(i in [set: G]) weight i) - W (N[v] :\ u)));
  last exact: (leq_sub2l (\sum_(i in [set: G]) weight i) (delta_w'_min udomv)).
rewrite -sub_diff_sum; last by done.
apply/sub_leq_sum/subsetDP; split; first by done.
apply/disjointP=> w w_in_S.
move/setD1P=> [wnequ w_in_Nv]; rewrite in_cln cl_sg_sym in w_in_Nv.
by move/negP: wnequ; rewrite (H w w_in_S w_in_Nv).
Qed.

Theorem IR_w_leq_V_minus_delta_w' : IR_w G weight <= W [set: G] - delta_w'.
Proof.
move: (IR_witness weight) => [?] ? <-.
by apply: bound_weight_irredundant.
Qed.

End IR_w_upper_bound.

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


(**********************************************************************************)
Section Upper_Weighted_Irredundant_Properties.

Variable G : sgraph.
Let G' := trfgraph G.

(* vn@m refers to the nth. vertex of a graph of m vertices, with 0 <= n < m *)
Notation "''v' n @ m" := (@Ordinal m n isT) (at level 0, m, n at level 8, format "''v' n @ m").

Ltac subgraph_proof Hi Hj := try (by rewrite (bool_irrelevance Hi Hj)); by rewrite /=.

Section Construction_of_Induced_Subgraphs.

  Lemma copaw_sub_copaw' : copaw \subgraph trfgraph copaw.
  Proof. exact: subgraph_G_G'. Qed.

  Lemma copaw_sub_G7_1' : copaw \subgraph trfgraph G7_1.
  Proof.
    have G7_1'_v1 : @dominates G7_1 ('v0@7, 'v3@7).1 ('v0@7, 'v3@7).2 by done.
    have G7_1'_v2 : @dominates G7_1 ('v6@7, 'v1@7).1 ('v6@7, 'v1@7).2 by done.
    have G7_1'_v3 : @dominates G7_1 ('v4@7, 'v1@7).1 ('v4@7, 'v1@7).2 by done.
    have G7_1'_v4 : @dominates G7_1 ('v2@7, 'v5@7).1 ('v2@7, 'v5@7).2 by done.
    pose h (v : copaw) : trfgraph G7_1 :=
      match v with
      | Ordinal 0 _ => TrfGraphVert G7_1'_v1
      | Ordinal 1 _ => TrfGraphVert G7_1'_v2
      | Ordinal 2 _ => TrfGraphVert G7_1'_v3
      | Ordinal _ _ => TrfGraphVert G7_1'_v4
      end.
    exists h. all: case => [[|[|[|[|i]]]] Hi];
      case => [[|[|[|[|j]]]] Hj]; subgraph_proof Hi Hj.
  Qed.

  Lemma copaw_sub_G7_2' : copaw \subgraph trfgraph G7_2.
  Proof.
    have G7_2'_v1 : @dominates G7_2 ('v0@7, 'v3@7).1 ('v0@7, 'v3@7).2 by done.
    have G7_2'_v2 : @dominates G7_2 ('v6@7, 'v1@7).1 ('v6@7, 'v1@7).2 by done.
    have G7_2'_v3 : @dominates G7_2 ('v4@7, 'v1@7).1 ('v4@7, 'v1@7).2 by done.
    have G7_2'_v4 : @dominates G7_2 ('v2@7, 'v5@7).1 ('v2@7, 'v5@7).2 by done.
    pose h (v : copaw) : trfgraph G7_2 :=
      match v with
      | Ordinal 0 _ => TrfGraphVert G7_2'_v1
      | Ordinal 1 _ => TrfGraphVert G7_2'_v2
      | Ordinal 2 _ => TrfGraphVert G7_2'_v3
      | Ordinal _ _ => TrfGraphVert G7_2'_v4
      end.
    exists h. all: case => [[|[|[|[|i]]]] Hi];
      case => [[|[|[|[|j]]]] Hj]; subgraph_proof Hi Hj.
  Qed.

  Lemma claw_sub_claw' : claw \subgraph trfgraph claw.
  Proof. exact: subgraph_G_G'. Qed.

  Lemma claw_sub_bull' : claw \subgraph trfgraph bull.
  Proof.
    have bull'_v1 : @dominates bull ('v2@5, 'v3@5).1 ('v2@5, 'v3@5).2 by done.
    have bull'_v2 : @dominates bull ('v0@5, 'v0@5).1 ('v0@5, 'v0@5).2 by done.
    have bull'_v3 : @dominates bull ('v1@5, 'v1@5).1 ('v1@5, 'v1@5).2 by done.
    have bull'_v4 : @dominates bull ('v4@5, 'v4@5).1 ('v4@5, 'v4@5).2 by done.
    pose h (v : claw) : trfgraph bull :=
      match v with
      | Ordinal 0 _ => TrfGraphVert bull'_v1
      | Ordinal 1 _ => TrfGraphVert bull'_v2
      | Ordinal 2 _ => TrfGraphVert bull'_v3
      | Ordinal _ _ => TrfGraphVert bull'_v4
      end.
    exists h. all: case => [[|[|[|[|i]]]] Hi];
      case => [[|[|[|[|j]]]] Hj]; subgraph_proof Hi Hj.
  Qed.

  Lemma claw_sub_P6' : claw \subgraph trfgraph 'P_6.
  Proof.
    have P6'_v1 : @dominates 'P_6 ('v3@6, 'v2@6).1 ('v3@6, 'v2@6).2 by done.
    have P6'_v2 : @dominates 'P_6 ('v1@6, 'v0@6).1 ('v1@6, 'v0@6).2 by done.
    have P6'_v3 : @dominates 'P_6 ('v5@6, 'v4@6).1 ('v5@6, 'v4@6).2 by done.
    have P6'_v4 : @dominates 'P_6 ('v2@6, 'v3@6).1 ('v2@6, 'v3@6).2 by done.
    pose h (v : claw) : trfgraph 'P_6 :=
      match v with
      | Ordinal 0 _ => TrfGraphVert P6'_v1
      | Ordinal 1 _ => TrfGraphVert P6'_v2
      | Ordinal 2 _ => TrfGraphVert P6'_v3
      | Ordinal _ _ => TrfGraphVert P6'_v4
      end.
    exists h. all: case => [[|[|[|[|i]]]] Hi];
      case => [[|[|[|[|j]]]] Hj]; subgraph_proof Hi Hj.
  Qed.

  Lemma claw_sub_CC6' : claw \subgraph trfgraph 'CC_6.
  Proof.
    have CC6'_v1 : @dominates 'CC_6 ('v5@6, 'v5@6).1 ('v5@6, 'v5@6).2 by done.
    have CC6'_v2 : @dominates 'CC_6 ('v1@6, 'v4@6).1 ('v1@6, 'v4@6).2 by done.
    have CC6'_v3 : @dominates 'CC_6 ('v3@6, 'v0@6).1 ('v3@6, 'v0@6).2 by done.
    have CC6'_v4 : @dominates 'CC_6 ('v5@6, 'v2@6).1 ('v5@6, 'v2@6).2 by done.
    pose h (v : claw) : trfgraph 'CC_6 :=
      match v with
      | Ordinal 0 _ => TrfGraphVert CC6'_v1
      | Ordinal 1 _ => TrfGraphVert CC6'_v2
      | Ordinal 2 _ => TrfGraphVert CC6'_v3
      | Ordinal _ _ => TrfGraphVert CC6'_v4
      end.
    exists h. all: case => [[|[|[|[|i]]]] Hi];
      case => [[|[|[|[|j]]]] Hj]; subgraph_proof Hi Hj.
  Qed.

End Construction_of_Induced_Subgraphs.

(* To prove G' co-paw-free => G {co-paw,G7_1,G7_2}-free we do the following:
     If G has a co-paw as an induced subgraph, then G' does too.
     If G has G7_1 or G7_2 as an induced subgraph, then G' has a co-paw. *)

Theorem G'copawfree : copaw \subgraph G \/ G7_1 \subgraph G \/
                      G7_2 \subgraph G -> copaw \subgraph G'.
Proof.
  case.
  { move/trfgraph_subgraph=> copaw'subG' ;
    by move: (subgraph_trans copaw_sub_copaw' copaw'subG'). }
  case.
  - move/trfgraph_subgraph=> G7_1'subG' ;
    by move: (subgraph_trans copaw_sub_G7_1' G7_1'subG').
  - move/trfgraph_subgraph=> G7_2'subG' ;
    by move: (subgraph_trans copaw_sub_G7_2' G7_2'subG').
Qed.

Variables Gcopaw GG7_1 GG7_2 : sgraph.
Hypothesis G_is_copaw : isomorphic Gcopaw copaw.
Hypothesis G_is_G7_1 : isomorphic GG7_1 G7_1.
Hypothesis G_is_G7_2 : isomorphic GG7_2 G7_2.

Corollary G'copawfree' : Gcopaw \subgraph G \/ GG7_1 \subgraph G \/
                         GG7_2 \subgraph G -> Gcopaw \subgraph G'.
Proof.
  case.
  { move=> /(subgraph_trans (sub_G2_G1 G_is_copaw)) copawsubG.
    apply: (subgraph_trans (sub_G1_G2 G_is_copaw)).
    by apply: G'copawfree ; left. }
  case.
  - move=> /(subgraph_trans (sub_G2_G1 G_is_G7_1)) G7_1subG.
    apply: (subgraph_trans (sub_G1_G2 G_is_copaw)).
    by apply: G'copawfree ; right ; left.
  - move=> /(subgraph_trans (sub_G2_G1 G_is_G7_2)) G7_2subG.
    apply: (subgraph_trans (sub_G1_G2 G_is_copaw)).
    by apply: G'copawfree ; right ; right.
Qed.

(* To prove G' claw-free => G {claw,bull,P6,CC6}-free we do the following:
     If G has claw as an induced subgraph, then G' does too.
     If G has a bull, P6 or a complement of C6 as an induced subgraph, then G' has a claw. *)

Theorem G'clawfree : claw \subgraph G \/ bull \subgraph G \/
                     'P_6 \subgraph G \/ 'CC_6 \subgraph G -> claw \subgraph G'.
Proof.
  case.
  { move/trfgraph_subgraph=> claw'subG' ;
    by move: (subgraph_trans claw_sub_claw' claw'subG'). }
  case.
  { move/trfgraph_subgraph=> bull'subG' ;
    by move: (subgraph_trans claw_sub_bull' bull'subG'). }
  case. 
  - move/trfgraph_subgraph=> P6'subG' ;
    by move: (subgraph_trans claw_sub_P6' P6'subG'). 
  - move/trfgraph_subgraph=> CC6'subG' ;
    by move: (subgraph_trans claw_sub_CC6' CC6'subG'). 
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

(* converse results *)

Lemma forallOrdinalI4 (p : 'I_4 -> Prop) :
  (forall v : 'I_4, p v) <-> (p 'v0@4 /\ p 'v1@4 /\ p 'v2@4 /\ p 'v3@4).
Proof.
  split.
  - by move=> H; do 3 try split; apply: H.
  - move=> [pv0 [pv1 [pv2 pv3]]] [v vlt4].
    do 4 try destruct v.
    all : try by rewrite (bool_irrelevance vlt4 isT).
    suff: ~ (v.+4 < 4) by contradiction.
    by apply/negP ; rewrite /=.
Qed.
(*RK
Ltac t_x1x2 x1 x2 :=
  (suff : (x1, x2) \in V' G by rewrite /V' in_set /=) ;
  rewrite /x1 /x2 -surjective_pairing ; apply/valP.
RK*)
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
  (have : ((h v2) == (h v1) = false) by apply/negP ; move/eqP/h_inj) ;
  by move-> ; rewrite orFb !negb_or andbA eq_sym sg_sym' [x1 -- y2]sg_sym' [x2 == y1]eq_sym => /andP [/andP [/andP [-> ->] ->] ->].

  (* Here is a proof of injectivity of a given function, by giving proofs of
     inequalities among their vertices *)
Lemma h'_inj (h' : copaw -> G)
    (v0v1 : h' 'v0@4 != h' 'v1@4) (v0v2 : h' 'v0@4 != h' 'v2@4)
    (v0v3 : h' 'v0@4 != h' 'v3@4) (v1v2 : h' 'v1@4 != h' 'v2@4)
    (v1v3 : h' 'v1@4 != h' 'v3@4) (v2v3 : h' 'v2@4 != h' 'v3@4)
       : forall x1 x2 : copaw, h' x1 = h' x2 -> x1 = x2.
Proof.
  move: (negP v0v1) => ?; move: (negP v0v2) => ?; move: (negP v0v3) => ?;
  move: (negP v1v2) => ?; move: (negP v1v3) => ?; move: (negP v2v3) => ?.
  rewrite !forallOrdinalI4 ; do 6 try split.
  all : try by [].
  all : try by move/eqP ; contradiction.
  all : try by move/eqP ; rewrite eq_sym ; contradiction.
Qed.

  (* Here is a proof of the homomorphism of a given function, by giving proofs
     of the edges and non-edges of the co-paw *)
Lemma h'_hom (h' : copaw -> G)
    (e_v0v1 : h' 'v0@4 -- h' 'v1@4) (e_v1v2 : h' 'v1@4 -- h' 'v2@4)
    (n_v0v2 : ~~ h' 'v0@4 -- h' 'v2@4) (n_v0v3 : ~~ h' 'v0@4 -- h' 'v3@4)
    (n_v1v3 : ~~ h' 'v1@4 -- h' 'v3@4) (n_v2v3 : ~~ h' 'v2@4 -- h' 'v3@4)
       : forall x1 x2 : copaw, x1 -- x2 <-> h' x1 -- h' x2.
Proof.
  rewrite !forallOrdinalI4 ; do 7 try split.
  all : try by [].
  all : try by rewrite !sg_irrefl ; apply/implyP.
  all : try by rewrite [in X in _ -> X]sg_sym.
  all : try by apply: contraLR.
  all : try by rewrite [in X in X -> _]sg_sym ; apply: contraLR.
Qed.

Theorem G'copawfree_rev : copaw \subgraph G' -> copaw \subgraph G \/
                                                G7_1 \subgraph G \/ G7_2 \subgraph G.
Proof.
  rewrite /induced_subgraph.
  move=> [h h_inj h_hom].

  (* in G', we have the path (a1,a2) - (b1,b2) - (c1,c2) and the isolate vert. (d1,d2) *)
  set a1 := (h 'v0@4).1.
  set a2 := (h 'v0@4).2.
  set b1 := (h 'v1@4).1.
  set b2 := (h 'v1@4).2.
  set c1 := (h 'v2@4).1.
  set c2 := (h 'v2@4).2.
  set d1 := (h 'v3@4).1.
  set d2 := (h 'v3@4).2.

  (* The following comes from the fact that x1x2 are vertices of G' *)
  have a1a2 : (a1 == a2) || a1 -- a2 by exact: (valP (h 'v0@4)).
  have b1b2 : (b1 == b2) || b1 -- b2 by exact: (valP (h 'v1@4)).
  have c1c2 : (c1 == c2) || c1 -- c2 by exact: (valP (h 'v2@4)).
  have d1d2 : (d1 == d2) || d1 -- d2 by exact: (valP (h 'v3@4)).

  (* The following comes from the edges of the path in G' *)
  have a1b2a2b1 : (a1 == b2) || a1 -- b2 || (a2 == b1) || (a2 -- b1)
    by t_v1v2 'v0@4 'v1@4 h h_hom.
  have b1c2b2c1 : (b1 == c2) || b1 -- c2 || (b2 == c1) || (b2 -- c1)
    by t_v1v2 'v1@4 'v2@4 h h_hom.

  (* The following comes from the fact that vertices of the co-paw are different *)
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

  (* The following comes from the no-edges of the co-paw in G' *)
  have a1c2a2c1 : (a1 != c2) && (~~ a1 -- c2) && (a2 != c1) && (~~ a2 -- c1).
    by t_x1y2x2y1 a1 a2 c1 c2 'v0@4 'v2@4 h h_hom.
  move: a1c2a2c1 => /andP [/andP [/andP [a1_neq_c2 a1_nadj_c2] a2_neq_c1] a2_nadj_c1].
  have a1d2a2d1 : (a1 != d2) && (~~ a1 -- d2) && (a2 != d1) && (~~ a2 -- d1).
    by t_x1y2x2y1 a1 a2 d1 d2 'v0@4 'v3@4 h h_hom.
  move: a1d2a2d1 => /andP [/andP [/andP [a1_neq_d2 a1_nadj_d2] a2_neq_d1] a2_nadj_d1].
  have b1d2b2d1 : (b1 != d2) && (~~ b1 -- d2) && (b2 != d1) && (~~ b2 -- d1).
    by t_x1y2x2y1 b1 b2 d1 d2 'v1@4 'v3@4 h h_hom.
  move: b1d2b2d1 => /andP [/andP [/andP [b1_neq_d2 b1_nadj_d2] b2_neq_d1] b2_nadj_d1].
  have c1d2c2d1 : (c1 != d2) && (~~ c1 -- d2) && (c2 != d1) && (~~ c2 -- d1).
    by t_x1y2x2y1 c1 c2 d1 d2 'v2@4 'v3@4 h h_hom.
  move: c1d2c2d1 => /andP [/andP [/andP [c1_neq_d2 c1_nadj_d2] c2_neq_d1] c2_nadj_d1].

  (* Start separation in cases... *)
  case/orP: a1a2 => [/eqP a1_eq_a2 | a1_adj_a2 ].
  - case/orP: b1b2 => [/eqP b1_eq_b2 | b1_adj_b2 ].
    + case/orP: c1c2 => [/eqP c1_eq_c2 | c1_adj_c2 ].
      (* a a --- b b --- c c *)
      * left; pose h' (v : copaw) :=
        match v with
        | Ordinal 0 _ => a1
        | Ordinal 1 _ => b1
        | Ordinal 2 _ => c1
        | Ordinal _ _ => d1
        end.
        exists h'.
        -- apply: h'_inj ; rewrite /=.
           ++ by move: a1a2b1b2 ; rewrite a1_eq_a2 b1_eq_b2 orbb.
           ++ by move: a1a2c1c2 ; rewrite a1_eq_a2 c1_eq_c2 orbb.
           ++ by rewrite a1_eq_a2.
           ++ by move: b1b2c1c2 ; rewrite b1_eq_b2 c1_eq_c2 orbb.
           ++ by rewrite b1_eq_b2.
           ++ by rewrite c1_eq_c2.
        -- apply: h'_hom ; rewrite /=.
           ++ move: a1a2b1b2 ; rewrite a1_eq_a2 b1_eq_b2 orbb.
              move: a1b2a2b1 ; rewrite a1_eq_a2 b1_eq_b2 -orbA orbb.
              case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by []].
           ++ move: b1b2c1c2 ; rewrite b1_eq_b2 c1_eq_c2 orbb.
              move: b1c2b2c1 ; rewrite b1_eq_b2 c1_eq_c2 -orbA orbb.
              case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by []].
           ++ by rewrite a1_eq_a2.
           ++ by rewrite a1_eq_a2.
           ++ by rewrite b1_eq_b2.
           ++ by rewrite c1_eq_c2.
      (* a a --- b b --- c1 c2 *)
        * case/orP: d1d2 => [/eqP d1_eq_d2 | d1_adj_d2 ].
          -- left.
             case: (orP b1c2b2c1)=> [b1c2b2c1' | b2_adj_c1].
             ++ case: (orP b1c2b2c1')=> [b1_dom_c2 |/eqP b2_eq_c1].
                ** case: (orP b1_dom_c2)=> [/eqP b1_eq_c2 | a1_adj_b2].
                   --- pose h' (v : copaw) :=
                       match v with
                       | Ordinal 0 _ => a1
                       | Ordinal 1 _ => b1
                       | Ordinal 2 _ => c1
                       | Ordinal _ _ => d1
                       end.
                       exists h'.
                       +++ apply: h'_inj ; rewrite /=.
                           *** by move: a1a2b1b2 ; rewrite a1_eq_a2 b1_eq_b2 orbb.
                           *** by rewrite a1_eq_a2.
                           *** by rewrite a1_eq_a2.
                           *** by rewrite b1_eq_c2 eq_sym (sg_edgeNeq c1_adj_c2).
                           *** by rewrite b1_eq_b2.
                           *** by rewrite d1_eq_d2.
                       +++ apply: h'_hom ; rewrite /=.
                           *** move: a1a2b1b2 ; rewrite a1_eq_a2 b1_eq_b2 orbb.
                               move: a1b2a2b1 ; rewrite a1_eq_a2 b1_eq_b2 -orbA orbb.
                               case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by []].
                           *** by rewrite b1_eq_c2 sg_sym.
                           *** by rewrite a1_eq_a2.
                           *** by rewrite a1_eq_a2.
                           *** by rewrite b1_eq_b2.
                           *** by rewrite d1_eq_d2.
                   --- pose h' (v : copaw) :=
                       match v with
                       | Ordinal 0 _ => a1
                       | Ordinal 1 _ => b1
                       | Ordinal 2 _ => c2
                       | Ordinal _ _ => d1
                       end.
                       exists h'.
                       +++ apply: h'_inj ; rewrite /=.
                           *** by move: a1a2b1b2 ; rewrite a1_eq_a2 b1_eq_b2 orbb.
                           *** by done.
                           *** by rewrite a1_eq_a2.
                           *** by rewrite (sg_edgeNeq a1_adj_b2).
                           *** by rewrite b1_eq_b2.
                           *** by done.
                       +++ apply: h'_hom ; rewrite /=.
                           *** move: a1a2b1b2 ; rewrite a1_eq_a2 b1_eq_b2 orbb.
                               move: a1b2a2b1 ; rewrite a1_eq_a2 b1_eq_b2 -orbA orbb.
                               case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by []].
                           *** by done.
                           *** by done.
                           *** by rewrite a1_eq_a2.
                           *** by rewrite b1_eq_b2.
                           *** by done.
                ** pose h' (v : copaw) :=
                   match v with
                   | Ordinal 0 _ => a1
                   | Ordinal 1 _ => b1
                   | Ordinal 2 _ => c2
                   | Ordinal _ _ => d1
                   end.
                   exists h'.
                   --- apply: h'_inj ; rewrite /=.
                       +++ by move: a1a2b1b2 ; rewrite a1_eq_a2 b1_eq_b2 orbb.
                       +++ by done.
                       +++ by rewrite a1_eq_a2.
                       +++ by rewrite b1_eq_b2 b2_eq_c1 (sg_edgeNeq c1_adj_c2).
                       +++ by rewrite b1_eq_b2.
                       +++ by done.
                   --- apply: h'_hom ; rewrite /=.
                       +++ move: a1a2b1b2 ; rewrite a1_eq_a2 b1_eq_b2 orbb.
                           move: a1b2a2b1 ; rewrite a1_eq_a2 b1_eq_b2 -orbA orbb.
                           case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by []].
                       +++ by rewrite b1_eq_b2 b2_eq_c1.
                       +++ by done.
                       +++ by rewrite a1_eq_a2.
                       +++ by rewrite b1_eq_b2.
                       +++ by done.
           ++ pose h' (v : copaw) :=
              match v with
              | Ordinal 0 _ => a1
              | Ordinal 1 _ => b1
              | Ordinal 2 _ => c1
              | Ordinal _ _ => d1
                       end.
              exists h'.
              ** apply: h'_inj ; rewrite /=.
                 --- by move: a1a2b1b2 ; rewrite a1_eq_a2 b1_eq_b2 orbb.
                 --- by rewrite a1_eq_a2.
                 --- by rewrite a1_eq_a2.
                 --- by rewrite b1_eq_b2 (sg_edgeNeq b2_adj_c1).
                 --- by rewrite b1_eq_b2.
                 --- by rewrite d1_eq_d2.
              ** apply: h'_hom ; rewrite /=.
                 --- move: a1a2b1b2 ; rewrite a1_eq_a2 b1_eq_b2 orbb.
                     move: a1b2a2b1 ; rewrite a1_eq_a2 b1_eq_b2 -orbA orbb.
                     case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by []].
                 --- by rewrite b1_eq_b2.
                 --- by rewrite a1_eq_a2.
                 --- by rewrite a1_eq_a2.
                 --- by rewrite b1_eq_b2.
                 --- by rewrite d1_eq_d2.
          -- left.
             case: (orP b1c2b2c1)=> [b1c2b2c1' | b2_adj_c1].
             ++ case: (orP b1c2b2c1')=> [b1_dom_c2 |/eqP b2_eq_c1].
                ** case: (orP b1_dom_c2)=> [/eqP b1_eq_c2 | b1_adj_c2].
                   --- pose h' (v : copaw) :=
                       match v with
                       | Ordinal 0 _ => a1
                       | Ordinal 1 _ => b1
                       | Ordinal 2 _ => c1
                       | Ordinal _ _ => d2
                       end.
                       exists h'.
                       +++ apply: h'_inj ; rewrite /=.
                           *** by move: a1a2b1b2 ; rewrite a1_eq_a2 b1_eq_b2 orbb.
                           *** by rewrite a1_eq_a2.
                           *** by done.
                           *** by rewrite b1_eq_c2 eq_sym (sg_edgeNeq c1_adj_c2).
                           *** by done.
                           *** by done.
                       +++ apply: h'_hom ; rewrite /=.
                           *** move: a1a2b1b2 ; rewrite a1_eq_a2 b1_eq_b2 orbb.
                               move: a1b2a2b1 ; rewrite a1_eq_a2 b1_eq_b2 -orbA orbb.
                               case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by []].
                           *** by rewrite b1_eq_c2 sg_sym.
                           *** by rewrite a1_eq_a2.
                           *** by done.
                           *** by done.
                           *** by done.
                   --- pose h' (v : copaw) :=
                       match v with
                       | Ordinal 0 _ => a1
                       | Ordinal 1 _ => b1
                       | Ordinal 2 _ => c2
                       | Ordinal _ _ => d1
                       end.
                       exists h'.
                       +++ apply: h'_inj ; rewrite /=.
                           *** by move: a1a2b1b2 ; rewrite a1_eq_a2 b1_eq_b2 orbb.
                           *** by done.
                           *** by rewrite a1_eq_a2.
                           *** by rewrite (sg_edgeNeq b1_adj_c2).
                           *** by rewrite b1_eq_b2.
                           *** by done.
                       +++ apply: h'_hom ; rewrite /=.
                           *** move: a1a2b1b2 ; rewrite a1_eq_a2 b1_eq_b2 orbb.
                               move: a1b2a2b1 ; rewrite a1_eq_a2 b1_eq_b2 -orbA orbb.
                               case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by []].
                           *** by done.
                           *** by done.
                           *** by rewrite a1_eq_a2.
                           *** by rewrite b1_eq_b2.
                           *** by done.
                ** pose h' (v : copaw) :=
                   match v with
                   | Ordinal 0 _ => a1
                   | Ordinal 1 _ => b1
                   | Ordinal 2 _ => c2
                   | Ordinal _ _ => d1
                   end.
                   exists h'.
                   --- apply: h'_inj ; rewrite /=.
                       +++ by move: a1a2b1b2 ; rewrite a1_eq_a2 b1_eq_b2 orbb.
                       +++ by done.
                       +++ by rewrite a1_eq_a2.
                       +++ by rewrite b1_eq_b2 b2_eq_c1 (sg_edgeNeq c1_adj_c2).
                       +++ by rewrite b1_eq_b2.
                       +++ by done.
                   --- apply: h'_hom ; rewrite /=.
                       +++ move: a1a2b1b2 ; rewrite a1_eq_a2 b1_eq_b2 orbb.
                           move: a1b2a2b1 ; rewrite a1_eq_a2 b1_eq_b2 -orbA orbb.
                           case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by []].
                       +++ by rewrite b1_eq_b2 b2_eq_c1.
                       +++ by done.
                       +++ by rewrite a1_eq_a2.
                       +++ by rewrite b1_eq_b2.
                       +++ by done.
           ++ pose h' (v : copaw) :=
              match v with
              | Ordinal 0 _ => a1
              | Ordinal 1 _ => b1
              | Ordinal 2 _ => c1
              | Ordinal _ _ => d2
              end.
              exists h'.
              ** apply: h'_inj ; rewrite /=.
                 --- by move: a1a2b1b2 ; rewrite a1_eq_a2 b1_eq_b2 orbb.
                 --- by rewrite a1_eq_a2.
                 --- by done.
                 --- by rewrite b1_eq_b2 (sg_edgeNeq b2_adj_c1).
                 --- by done.
                 --- by done.
              ** apply: h'_hom ; rewrite /=.
                 --- move: a1a2b1b2 ; rewrite a1_eq_a2 b1_eq_b2 orbb.
                     move: a1b2a2b1 ; rewrite a1_eq_a2 b1_eq_b2 -orbA orbb.
                     case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by []].
                 --- by rewrite b1_eq_b2.
                 --- by rewrite a1_eq_a2.
                 --- by done.
                 --- by done.
                 --- by done.
    + case/orP: c1c2 => [/eqP c1_eq_c2 | c1_adj_c2 ].
      (* a a --- b1 b2 --- c c *)
        -- left.
           case: (orP a1b2a2b1)=> [a1b2a2b1' | a2_adj_b1].
             ++ case: (orP a1b2a2b1')=> [a1_dom_b2 |/eqP a2_eq_b1].
                ** case: (orP a1_dom_b2)=> [/eqP a1_eq_b2 | a1_adj_b2].
                   --- case: (orP b1c2b2c1)=> [b1c2b2c1' | b2_adj_c1]; 
                        last by rewrite -a1_eq_b2 c1_eq_c2 in b2_adj_c1; rewrite b2_adj_c1 in a1_nadj_c2.
                       case: (orP b1c2b2c1')=> [b1_dom_c2 |/eqP b2_eq_c1];
                        last by rewrite a1_eq_b2 b2_eq_c1 c1_eq_c2 eq_refl in a1_neq_c2.
                       case: (orP b1_dom_c2)=> [/eqP b1_eq_c2 | b1_adj_c2];
                        first by rewrite a1_eq_b2 -b1_eq_c2 sg_sym b1_adj_b2 in a1_nadj_c2.
                       pose h' (v : copaw) :=
                        match v with
                        | Ordinal 0 _ => b2
                        | Ordinal 1 _ => b1
                        | Ordinal 2 _ => c2
                        | Ordinal _ _ => d2
                        end.
                       exists h'.
                       +++ apply: h'_inj ; rewrite /=.
                           *** apply/contraT; rewrite negbK => /eqP b2_eq_b1.
                               rewrite -b2_eq_b1 -a1_eq_b2 in b1_adj_c2.
                               by rewrite b1_adj_c2 in a1_nadj_c2.
                           *** by rewrite -a1_eq_b2.
                           *** by rewrite -a1_eq_b2.
                           *** by move: b1_adj_c2; apply/contraTneq => ->; rewrite sg_irrefl.
                           *** by done.
                           *** apply/contraT; rewrite negbK => /eqP c2_eq_d2.
                               by rewrite -c2_eq_d2 b1_adj_c2 in b1_nadj_d2.
                       +++ apply: h'_hom ; rewrite /=.
                           *** by rewrite sg_sym.
                           *** by done.
                           *** by rewrite -a1_eq_b2.
                           *** by rewrite -a1_eq_b2.
                           *** by done.
                           *** by rewrite -c1_eq_c2.
                   --- case: (orP b1c2b2c1)=> [b1c2b2c1' | b2_adj_c1].
                       +++ case: (orP b1c2b2c1')=> [b1_dom_c2 |/eqP b2_eq_c1];
                             last by rewrite -c1_eq_c2 -b2_eq_c1 a1_adj_b2 in a1_nadj_c2.
                           case: (orP b1_dom_c2)=> [/eqP b1_eq_c2 | b1_adj_c2].
                           *** pose h' (v : copaw) :=
                                 match v with
                                 | Ordinal 0 _ => a1
                                 | Ordinal 1 _ => b2
                                 | Ordinal 2 _ => b1
                                 | Ordinal _ _ => d1
                                 end.
                               exists h'.
                               ---- apply: h'_inj ; rewrite /=.
                                    ++++ by move: a1_adj_b2; apply/contraTneq => ->; rewrite sg_irrefl.
                                    ++++ by rewrite b1_eq_c2.
                                    ++++ by rewrite a1_eq_a2.
                                    ++++ by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_irrefl.
                                    ++++ by done.
                                    ++++ by rewrite b1_eq_c2.
                               ---- apply: h'_hom ; rewrite /=.
                                    ++++ by done.
                                    ++++ by rewrite sg_sym.
                                    ++++ by rewrite b1_eq_c2.
                                    ++++ by rewrite a1_eq_a2.
                                    ++++ by done.
                                    ++++ by rewrite b1_eq_c2.
                           *** case: (boolP (c1 -- b2))=> [c1_adj_b2 | c1_nadj_b2].
                               ---- pose h' (v : copaw) :=
                                      match v with
                                      | Ordinal 0 _ => c1
                                      | Ordinal 1 _ => b2
                                      | Ordinal 2 _ => a1
                                      | Ordinal _ _ => d1
                                      end.
                                    exists h'.
                                    ++++ apply: h'_inj ; rewrite /=.
                                         **** by move: c1_adj_b2; apply/contraTneq => ->; rewrite sg_irrefl.
                                         **** by rewrite a1_eq_a2 eq_sym.
                                         **** by rewrite c1_eq_c2.
                                         **** by move: a1_adj_b2; apply/contraTneq => ->; rewrite sg_irrefl.
                                         **** by done.
                                         **** by rewrite a1_eq_a2.
                                    ++++ apply: h'_hom ; rewrite /=.
                                         **** by done.
                                         **** by rewrite sg_sym.
                                         **** by rewrite a1_eq_a2 sg_sym.
                                         **** by rewrite c1_eq_c2.
                                         **** by done.
                                         **** by rewrite a1_eq_a2.
                               ---- case: (boolP (b2 -- d2))=> [b2_adj_d2 | b2_nadj_d2].
                                    ++++ pose h' (v : copaw) :=
                                           match v with
                                           | Ordinal 0 _ => d2
                                           | Ordinal 1 _ => b2
                                           | Ordinal 2 _ => a2
                                           | Ordinal _ _ => c1
                                           end.
                                         exists h'.
                                         **** apply: h'_inj ; rewrite /=.
                                              ----- by move: b2_adj_d2; apply/contraTneq => ->; rewrite sg_irrefl.
                                              ----- by rewrite -a1_eq_a2 eq_sym.
                                              ----- by rewrite eq_sym.
                                              ----- by move: a1_adj_b2; apply/contraTneq => ->; rewrite a1_eq_a2 sg_irrefl.
                                              ----- by move: a1_adj_b2; apply/contraTneq => ->; rewrite c1_eq_c2.
                                              ----- by done.
                                         **** apply: h'_hom ; rewrite /=.
                                              ----- by rewrite sg_sym.
                                              ----- by rewrite -a1_eq_a2 sg_sym.
                                              ----- by rewrite -a1_eq_a2 sg_sym.
                                              ----- by rewrite sg_sym.
                                              ----- by rewrite sg_sym.
                                              ----- by done.
                                    ++++ pose h' (v : copaw) :=
                                           match v with
                                           | Ordinal 0 _ => c2
                                           | Ordinal 1 _ => b1
                                           | Ordinal 2 _ => b2
                                           | Ordinal _ _ => d2
                                           end.
                                         exists h'.
                                         **** apply: h'_inj ; rewrite /=.
                                              ----- by move: b1_adj_c2; apply/contraTneq => ->; rewrite sg_irrefl.
                                              ----- by move: a1_adj_b2; apply/contraTneq => <-.
                                              ----- by rewrite -c1_eq_c2.
                                              ----- by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_irrefl.
                                              ----- by done.
                                              ----- by move: b1_adj_b2; apply/contraTneq => ->.
                                         **** apply: h'_hom ; rewrite /=.
                                              ----- by rewrite sg_sym.
                                              ----- by done.
                                              ----- by rewrite -c1_eq_c2.
                                              ----- by rewrite -c1_eq_c2.
                                              ----- by done.
                                              ----- by done.
                      +++ pose h' (v : copaw) :=
                            match v with
                            | Ordinal 0 _ => a1
                            | Ordinal 1 _ => b2
                            | Ordinal 2 _ => c1
                            | Ordinal _ _ => d1
                            end.
                          exists h'.
                          *** apply: h'_inj ; rewrite /=.
                              ---- by move: a1_adj_b2; apply/contraTneq => ->; rewrite sg_irrefl.
                              ---- by rewrite a1_eq_a2.
                              ---- by rewrite a1_eq_a2.
                              ---- by move: b2_adj_c1; apply/contraTneq => ->; rewrite sg_irrefl.
                              ---- by done.
                              ---- by rewrite c1_eq_c2.
                          *** apply: h'_hom ; rewrite /=.
                              ---- by done.
                              ---- by done.
                              ---- by rewrite a1_eq_a2.
                              ---- by rewrite a1_eq_a2.
                              ---- by done.
                              ---- by rewrite c1_eq_c2.
                ** case: (orP b1c2b2c1)=> [b1c2b2c1' | b2_adj_c1].
                   --- case: (orP b1c2b2c1')=> [b1_dom_c2 |/eqP b2_eq_c1];
                         last by move: a2_nadj_c1; rewrite -b2_eq_c1 a2_eq_b1 b1_adj_b2.
                       by case: (orP b1_dom_c2)=> [/eqP b1_eq_c2 | b1_adj_c2];
                            [move: a1a2c1c2; rewrite a1_eq_a2 c1_eq_c2 a2_eq_b1 b1_eq_c2 eq_refl
                               | move: a1_nadj_c2; rewrite a1_eq_a2 a2_eq_b1 b1_adj_c2].
                   --- pose h' (v : copaw) := 
                         match v with
                         | Ordinal 0 _ => b1
                         | Ordinal 1 _ => b2
                         | Ordinal 2 _ => c1
                         | Ordinal _ _ => d1
                         end.
                       exists h'.
                       +++ apply: h'_inj ; rewrite /=.
                           *** by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_irrefl.
                           *** by rewrite -a2_eq_b1.
                           *** by rewrite -a2_eq_b1.
                           *** by move: b2_adj_c1; apply/contraTneq => ->; rewrite sg_irrefl.
                           *** by done.
                           *** by rewrite c1_eq_c2.
                       +++ apply: h'_hom ; rewrite /=.
                           *** by done.
                           *** by done.
                           *** by rewrite -a2_eq_b1.
                           *** by rewrite -a2_eq_b1.
                           *** by done.
                           *** by rewrite c1_eq_c2.
             ++ case: (orP b1c2b2c1)=> [b1c2b2c1' | b2_adj_c1].
                   ** case: (orP b1c2b2c1')=> [b1_dom_c2 |/eqP b2_eq_c1].
                      --- case: (orP b1_dom_c2)=> [/eqP b1_eq_c2 | b1_adj_c2];
                            first by move: a2_nadj_c1; rewrite c1_eq_c2 -b1_eq_c2 a2_adj_b1.
                          pose h' (v : copaw) :=
                            match v with
                            | Ordinal 0 _ => a2
                            | Ordinal 1 _ => b1
                            | Ordinal 2 _ => c2
                            | Ordinal _ _ => d2
                            end.
                          exists h'.
                          +++ apply: h'_inj ; rewrite /=.
                              *** by move: a2_adj_b1; apply/contraTneq => ->; rewrite sg_irrefl.
                              *** by rewrite -a1_eq_a2.
                              *** by rewrite -a1_eq_a2.
                              *** by move: b1_adj_c2; apply/contraTneq => ->; rewrite sg_irrefl.
                              *** by done.
                              *** by rewrite -c1_eq_c2.
                          +++ apply: h'_hom ; rewrite /=.
                              *** by done.
                              *** by done.
                              *** by rewrite -a1_eq_a2.
                              *** by rewrite -a1_eq_a2.
                              *** by done.
                              *** by rewrite -c1_eq_c2.
                      --- pose h' (v : copaw) :=
                            match v with
                            | Ordinal 0 _ => a2
                            | Ordinal 1 _ => b1
                            | Ordinal 2 _ => c2
                            | Ordinal _ _ => d2
                            end.
                          exists h'.
                          +++ apply: h'_inj ; rewrite /=.
                              *** by move: a2_adj_b1; apply/contraTneq => ->; rewrite sg_irrefl.
                              *** by rewrite -a1_eq_a2.
                              *** by rewrite -a1_eq_a2.
                              *** by move: b1_adj_b2; apply/contraTneq => ->; rewrite -c1_eq_c2 -b2_eq_c1 sg_irrefl.
                              *** by done.
                              *** by rewrite -c1_eq_c2.
                          +++ apply: h'_hom ; rewrite /=.
                              *** by done.
                              *** by rewrite -c1_eq_c2 -b2_eq_c1.
                              *** by rewrite -a1_eq_a2.
                              *** by rewrite -a1_eq_a2.
                              *** by done.
                              *** by rewrite -c1_eq_c2.
                   ** case: (boolP (a1 -- b2))=> [a1_adj_b2 | a1_nadj_b2].
                      --- pose h' (v : copaw) :=
                            match v with
                            | Ordinal 0 _ => a1
                            | Ordinal 1 _ => b2
                            | Ordinal 2 _ => c1
                            | Ordinal _ _ => d1
                            end.
                          exists h'.
                          +++ apply: h'_inj ; rewrite /=.
                              *** by move: a1_adj_b2; apply/contraTneq => <-; rewrite sg_irrefl.
                              *** by rewrite a1_eq_a2.
                              *** by rewrite a1_eq_a2.
                              *** by move: b2_adj_c1; apply/contraTneq => ->; rewrite sg_irrefl.
                              *** by done.
                              *** by rewrite c1_eq_c2.
                          +++ apply: h'_hom ; rewrite /=.
                              *** by done.
                              *** by done.
                              *** by rewrite a1_eq_a2.
                              *** by rewrite a1_eq_a2.
                              *** by done.
                              *** by rewrite c1_eq_c2.
                      --- case: (boolP (b2 -- d2))=> [b2_adj_d2 | b2_nadj_d2].
                          +++ pose h' (v : copaw) :=
                                match v with
                                | Ordinal 0 _ => d2
                                | Ordinal 1 _ => b2
                                | Ordinal 2 _ => c1
                                | Ordinal _ _ => a1
                                end.
                              exists h'.
                              *** apply: h'_inj ; rewrite /=.
                                  ---- by move: b2_adj_d2; apply/contraTneq => ->; rewrite sg_irrefl.
                                  ---- by rewrite eq_sym.
                                  ---- by rewrite eq_sym.
                                  ---- by move: b2_adj_c1; apply/contraTneq => ->; rewrite sg_irrefl.
                                  ---- by move: b2_adj_c1; apply/contraTneq => ->; rewrite a1_eq_a2.
                                  ---- by rewrite c1_eq_c2 eq_sym.
                              *** apply: h'_hom ; rewrite /=.
                                  ---- by rewrite sg_sym.
                                  ---- by done.
                                  ---- by rewrite sg_sym.
                                  ---- by rewrite sg_sym.
                                  ---- by rewrite sg_sym.
                                  ---- by rewrite a1_eq_a2 sg_sym.
                          +++ pose h' (v : copaw) :=
                                match v with
                                | Ordinal 0 _ => a1
                                | Ordinal 1 _ => b1
                                | Ordinal 2 _ => b2
                                | Ordinal _ _ => d2
                                end.
                              exists h'.
                              *** apply: h'_inj ; rewrite /=.
                                  ---- by move: a2_adj_b1; apply/contraTneq => <-; rewrite a1_eq_a2 sg_irrefl.
                                  ---- by move: b2_adj_c1; apply/contraTneq => <-; rewrite a1_eq_a2.
                                  ---- by done.
                                  ---- by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_irrefl.
                                  ---- by done.
                                  ---- by move: b1_adj_b2; apply/contraTneq => ->.
                              *** apply: h'_hom ; rewrite /=.
                                  ---- by rewrite a1_eq_a2.
                                  ---- by done.
                                  ---- by done.
                                  ---- by done.
                                  ---- by done.
                                  ---- by done.
        -- (* a a --- b1 b2 --- c1 c2 *)
           case: (orP d1d2)=> [/eqP d1_eq_d2 | d1_adj_d2]. 
           ++ (* a a --- b1 b2 --- c1 c2 *)
              (*          d d            *)
              left.
              case: (boolP (a1 -- b1))=> [a1_adj_b1 | a1_nadj_b1].
              ** case: (boolP (a1 -- b2))=> [a1_adj_b2 | a1_nadj_b2].
                 --- case: (boolP (c1 -- b2))=> [c1_adj_b2 | c1_nadj_b2].
                     +++ pose h' (v : copaw) :=
                           match v with
                           | Ordinal 0 _ => a2
                           | Ordinal 1 _ => b2
                           | Ordinal 2 _ => c1
                           | Ordinal _ _ => d2
                           end.
                         exists h'.
                         *** apply: h'_inj ; rewrite /=.
                             ---- by move: a1_adj_b2; apply/contraTneq => <-; rewrite a1_eq_a2 sg_irrefl.
                             ---- by done.
                             ---- by rewrite -d1_eq_d2.
                             ---- by move: c1_adj_b2; apply/contraTneq => <-; rewrite sg_irrefl.
                             ---- by rewrite -d1_eq_d2.
                             ---- by done.
                         *** apply: h'_hom ; rewrite /=.
                             ---- by rewrite -a1_eq_a2.
                             ---- by rewrite sg_sym.
                             ---- by done.
                             ---- by rewrite -d1_eq_d2.
                             ---- by rewrite -d1_eq_d2.
                             ---- by done.
                     +++ pose h' (v : copaw) :=
                           match v with
                           | Ordinal 0 _ => a1
                           | Ordinal 1 _ => b1
                           | Ordinal 2 _ => c2
                           | Ordinal _ _ => d2
                           end.
                         exists h'.
                         *** apply: h'_inj ; rewrite /=.
                             ---- by move: a1_adj_b1; apply/contraTneq => <-; rewrite sg_irrefl.
                             ---- by done.
                             ---- by done.
                             ---- by move: a1_adj_b1; apply/contraTneq => ->.
                             ---- by done.
                             ---- by rewrite -d1_eq_d2.
                         *** apply: h'_hom ; rewrite /=.
                             ---- by done.
                             ---- have b1_neq_c2: b1 != c2 by move: a1_adj_b1; apply/contraTneq => ->.
                                  have b2_neq_c1: b2 != c1 by move: a1_adj_b2; apply/contraTneq => ->; rewrite a1_eq_a2.
                                  rewrite sg_sym in c1_nadj_b2.
                                  rewrite (negbTE b1_neq_c2) (negbTE b2_neq_c1) (negbTE c1_nadj_b2) //= in b1c2b2c1.
                                  by case: (orP b1c2b2c1) => // H; case: (orP H).
                             ---- by done.
                             ---- by done.
                             ---- by done.
                             ---- by rewrite -d1_eq_d2.
                 --- case: (boolP (a1 == b2))=> [/eqP a1_eq_b2 | a1_neq_b2].
                     +++ (* c1 -- c2 -- b1 -- b2 = a1 = a2 *)
                         (*           d1 = d2              *)
                         pose h' (v : copaw) :=
                           match v with
                           | Ordinal 0 _ => b2
                           | Ordinal 1 _ => b1
                           | Ordinal 2 _ => c2
                           | Ordinal _ _ => d1
                           end.
                         exists h'.
                         *** apply: h'_inj ; rewrite /=.
                             ---- by move: b1_adj_b2; apply/contraTneq => <-; rewrite sg_irrefl.
                             ---- by rewrite -a1_eq_b2.
                             ---- by done.
                             ---- by move: a1_adj_b1; apply/contraTneq => ->.
                             ---- by rewrite d1_eq_d2.
                             ---- by done.
                         *** apply: h'_hom ; rewrite /=.
                             ---- by rewrite sg_sym.
                             ---- have b1_neq_c2: b1 != c2 by move: a1_adj_b1; apply/contraTneq => ->.
                                  have b2_neq_c1: b2 != c1 by rewrite -a1_eq_b2 a1_eq_a2.
                                  have b2_nadj_c1: ~~ b2 -- c1 by rewrite -a1_eq_b2 a1_eq_a2.
                                  rewrite (negbTE b1_neq_c2) (negbTE b2_neq_c1) (negbTE b2_nadj_c1) //= in b1c2b2c1.
                                  by case: (orP b1c2b2c1) => // H; case: (orP H).
                             ---- by rewrite -a1_eq_b2.
                             ---- by done.
                             ---- by rewrite d1_eq_d2.
                             ---- by done.
                     +++ pose h' (v : copaw) :=
                           match v with
                           | Ordinal 0 _ => a1
                           | Ordinal 1 _ => b1
                           | Ordinal 2 _ => b2
                           | Ordinal _ _ => d1
                           end.
                         exists h'.
                         *** apply: h'_inj ; rewrite /=.
                             ---- by move: a1_adj_b1; apply/contraTneq => <-; rewrite a1_eq_a2 sg_irrefl.
                             ---- by done.
                             ---- by rewrite d1_eq_d2.
                             ---- by move: b1_adj_b2; apply/contraTneq => <-; rewrite sg_irrefl.
                             ---- by rewrite d1_eq_d2.
                             ---- by done.
                         *** apply: h'_hom ; rewrite /=.
                             ---- by done.
                             ---- by done.
                             ---- by done.
                             ---- by rewrite d1_eq_d2.
                             ---- by rewrite d1_eq_d2.
                             ---- by done.
              ** case: (boolP (a1 == b2))=> [/eqP a1_eq_b2 | a1_neq_b2];
                   first by move: a1_nadj_b1; rewrite a1_eq_b2 sg_sym b1_adj_b2.
                 case: (boolP (a1 == b1))=> [/eqP a1_eq_b1 | a1_neq_b1].
                 --- pose h' (v : copaw) :=
                       match v with
                       | Ordinal 0 _ => a1
                       | Ordinal 1 _ => b2
                       | Ordinal 2 _ => c1
                       | Ordinal _ _ => d2
                       end.
                     exists h'.
                     +++ apply: h'_inj ; rewrite /=.
                         *** by done.
                         *** by rewrite a1_eq_a2.
                         *** by done.
                         *** by move: b1_adj_b2; apply/contraTneq => ->; rewrite -a1_eq_b1 a1_eq_a2.
                         *** by rewrite -d1_eq_d2.
                         *** by done.
                     +++ apply: h'_hom ; rewrite /=.
                         *** by rewrite a1_eq_b1.
                         *** have b1_neq_c2: b1 != c2 by rewrite -a1_eq_b1.
                             have b2_neq_c1: b2 != c1 by move: b1_adj_b2; apply/contraTneq => ->; rewrite -a1_eq_b1 a1_eq_a2.
                             have b1_nadj_c2: ~~ b1 -- c2 by rewrite -a1_eq_b1.
                             by rewrite (negbTE b1_neq_c2) (negbTE b2_neq_c1) (negbTE b1_nadj_c2) //= in b1c2b2c1.
                         *** by rewrite a1_eq_a2.
                         *** by done.
                         *** by rewrite -d1_eq_d2.
                         *** by done.
                 --- pose h' (v : copaw) :=
                       match v with
                       | Ordinal 0 _ => a1
                       | Ordinal 1 _ => b2
                       | Ordinal 2 _ => b1
                       | Ordinal _ _ => d2
                       end.
                     exists h'.
                     +++ apply: h'_inj ; rewrite /=.
                         *** by done.
                         *** by done.
                         *** by done.
                         *** by move: b1_adj_b2; apply/contraTneq => <-; rewrite sg_irrefl.
                         *** by rewrite -d1_eq_d2.
                         *** by done.
                     +++ apply: h'_hom ; rewrite /=.
                         *** rewrite a1_eq_a2 in a1_nadj_b1.
                             rewrite a1_eq_a2 in a1_neq_b1.
                             rewrite (negbTE a1_neq_b2) (negbTE a1_neq_b1) (negbTE a1_nadj_b1) //= in a1b2a2b1.
                             by case: (orP a1b2a2b1) => // H; case: (orP H).
                         *** by rewrite sg_sym.
                         *** by done.
                         *** by done.
                         *** by rewrite -d1_eq_d2.
                         *** by done.
           ++ case: (boolP (c1 -- d1))=> [c1_adj_d1 | c1_nadj_d1].
              ** pose h' (v : copaw) :=
                   match v with
                   | Ordinal 0 _ => c1
                   | Ordinal 1 _ => d1
                   | Ordinal 2 _ => d2
                   | Ordinal _ _ => a2
                   end.
                 left; exists h'.
                 --- apply: h'_inj ; rewrite /=.
                     +++ by move: c1_adj_d1; apply/contraTneq => <-; rewrite sg_irrefl.
                     +++ by done.
                     +++ by rewrite eq_sym.
                     +++ by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_irrefl.
                     +++ by rewrite eq_sym.
                     +++ by rewrite -a1_eq_a2 eq_sym.
                 --- apply: h'_hom ; rewrite /=.
                     +++ by done.
                     +++ by done.
                     +++ by done.
                     +++ by rewrite sg_sym.
                     +++ by rewrite sg_sym.
                     +++ by rewrite  -a1_eq_a2 sg_sym.
              ** case: (boolP (c2 -- d2))=> [c2_adj_d2 | c2_nadj_d2].
                 --- pose h' (v : copaw) :=
                       match v with
                       | Ordinal 0 _ => c1
                       | Ordinal 1 _ => c2
                       | Ordinal 2 _ => d2
                       | Ordinal _ _ => a1
                       end.
                     left; exists h'.
                     +++ apply: h'_inj ; rewrite /=.
                         *** by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_irrefl.
                         *** by done.
                         *** by rewrite a1_eq_a2 eq_sym.
                         *** by move: c2_adj_d2; apply/contraTneq => <-; rewrite sg_irrefl.
                         *** by rewrite eq_sym.
                         *** by rewrite eq_sym.
                     +++ apply: h'_hom ; rewrite /=.
                         *** by done.
                         *** by done.
                         *** by done.
                         *** by rewrite a1_eq_a2 sg_sym.
                         *** by rewrite sg_sym.
                         *** by rewrite sg_sym.
                 --- case: (boolP (a2 -- b1))=> [a2_adj_b1 | a2_nadj_b1].
                     +++ case: (boolP (b1 -- c2))=> [b1_adj_c2 | b1_nadj_c2].
                         *** pose h' (v : copaw) :=
                               match v with
                               | Ordinal 0 _ => a2
                               | Ordinal 1 _ => b1
                               | Ordinal 2 _ => c2
                               | Ordinal _ _ => d2
                               end.
                             left; exists h'.
                             ---- apply: h'_inj ; rewrite /=.
                                  ++++ by move: a2_adj_b1; apply/contraTneq => <-; rewrite sg_irrefl.
                                  ++++ by rewrite -a1_eq_a2.
                                  ++++ by rewrite -a1_eq_a2.
                                  ++++ by move: b1_adj_c2; apply/contraTneq => <-; rewrite sg_irrefl.
                                  ++++ by done.
                                  ++++ by move: c1_nadj_d2; apply/contraTneq => <-; rewrite c1_adj_c2.
                             ---- apply: h'_hom ; rewrite /=.
                                  ++++ by done.
                                  ++++ by done.
                                  ++++ by rewrite -a1_eq_a2.
                                  ++++ by rewrite -a1_eq_a2.
                                  ++++ by done.
                                  ++++ by done.
                         *** case: (boolP (b1 -- c1))=> [b1_adj_c1 | b1_nadj_c1].
                             ---- pose h' (v : copaw) :=
                                    match v with
                                    | Ordinal 0 _ => b1
                                    | Ordinal 1 _ => c1
                                    | Ordinal 2 _ => c2
                                    | Ordinal _ _ => d2
                                    end.
                                  left; exists h'.
                                  ++++ apply: h'_inj ; rewrite /=.
                                       **** by move: b1_adj_c1; apply/contraTneq => <-; rewrite sg_irrefl.
                                       **** by move: a2_adj_b1; apply/contraTneq => ->; rewrite -a1_eq_a2.
                                       **** by done.
                                       **** by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_irrefl.
                                       **** by done.
                                       **** by move: c1_nadj_d2; apply/contraTneq => <-; rewrite c1_adj_c2.
                                  ++++ apply: h'_hom ; rewrite /=.
                                       **** by done.
                                       **** by done.
                                       **** by done.
                                       **** by done.
                                       **** by done.
                                       **** by done.
                             ---- case: (boolP (b2 -- c2))=> [b2_adj_c2 | b2_nadj_c2].
                                  ++++ case: (boolP (b1 -- d1))=> [b1_adj_d1 | b1_nadj_d1].
                                       **** pose h' (v : copaw) :=
                                              match v with
                                              | Ordinal 0 _ => a2
                                              | Ordinal 1 _ => b1
                                              | Ordinal 2 _ => d1
                                              | Ordinal _ _ => c2
                                              end.
                                            left; exists h'.
                                            ----- apply: h'_inj ; rewrite /=.
                                                  +++++ by move: a2_adj_b1 ; apply/contraTneq => ->; rewrite sg_irrefl.
                                                  +++++ by done.
                                                  +++++ by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                                                  +++++ by move: b1_adj_d1; apply/contraTneq => ->; rewrite sg_irrefl.
                                                  +++++ by move: b1_adj_d1; apply/contraTneq => ->.
                                                  +++++ by move: b2_adj_c2; apply/contraTneq => <-.
                                            ----- apply: h'_hom ; rewrite /=.
                                                  +++++ by done.
                                                  +++++ by done.
                                                  +++++ by done.
                                                  +++++ by rewrite -a1_eq_a2.
                                                  +++++ by done.
                                                  +++++ by rewrite sg_sym.
                                       **** case: (boolP (a1 -- b2))=> [a1_adj_b2 | a1_nadj_b2].
                                            ----- pose h' (v : copaw) :=
                                                    match v with
                                                    | Ordinal 0 _ => a1
                                                    | Ordinal 1 _ => b2
                                                    | Ordinal 2 _ => c2
                                                    | Ordinal _ _ => d1
                                                    end.
                                                  left; exists h'.
                                                  +++++ apply: h'_inj ; rewrite /=.
                                                        ***** by move: a1_adj_b2 ; apply/contraTneq => ->; rewrite sg_irrefl.
                                                        ***** by done.
                                                        ***** by rewrite a1_eq_a2.
                                                        ***** by move: b2_adj_c2 ; apply/contraTneq => ->; rewrite sg_irrefl.
                                                        ***** by move: b1_nadj_d1; apply/contraTneq => <-; rewrite b1_adj_b2.
                                                        ***** by done.
                                                  +++++ apply: h'_hom ; rewrite /=.
                                                        ***** by done.
                                                        ***** by done.
                                                        ***** by done.
                                                        ***** by rewrite a1_eq_a2.
                                                        ***** by done.
                                                        ***** by done.
                                            ----- pose h' (v : copaw) :=
                                                    match v with
                                                    | Ordinal 0 _ => a2
                                                    | Ordinal 1 _ => b1
                                                    | Ordinal 2 _ => b2
                                                    | Ordinal _ _ => d1
                                                    end.
                                                  left; exists h'.
                                                  +++++ apply: h'_inj ; rewrite /=.
                                                        ***** by move: a2_adj_b1; apply/contraTneq => ->; rewrite sg_irrefl.
                                                        ***** by move: b2_adj_c2; apply/contraTneq => <-; rewrite -a1_eq_a2.
                                                        ***** by done.
                                                        ***** by move: b1_adj_b2 ; apply/contraTneq => ->; rewrite sg_irrefl.
                                                        ***** by move: b2_nadj_d1; apply/contraTneq => <-; rewrite sg_sym b1_adj_b2.
                                                        ***** by done.
                                                  +++++ apply: h'_hom ; rewrite /=.
                                                        ***** by done.
                                                        ***** by done.
                                                        ***** by rewrite -a1_eq_a2.
                                                        ***** by done.
                                                        ***** by done.
                                                        ***** by done.
                                  ++++ pose h' (v : copaw) :=
                                         match v with
                                         | Ordinal 0 _ => b2
                                         | Ordinal 1 _ => c1
                                         | Ordinal 2 _ => c2
                                         | Ordinal _ _ => d1
                                         end.
                                       left; exists h'.
                                       **** apply: h'_inj ; rewrite /=.
                                            ----- by move: b2_nadj_c2; apply/contraTneq => ->; rewrite c1_adj_c2.
                                            ----- by move: b1_nadj_c2; apply/contraTneq => <-; rewrite b1_adj_b2.
                                            ----- by done.
                                            ----- by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_irrefl.
                                            ----- by move: c2_nadj_d1; apply/contraTneq => <-; rewrite sg_sym c1_adj_c2.
                                            ----- by move: d1_adj_d2; apply/contraTneq => <-.
                                       **** apply: h'_hom ; rewrite /=.
                                            ----- have b2_neq_c1: b2 != c1 by move: b2_nadj_c2; apply/contraTneq => ->; rewrite c1_adj_c2.
                                                  have b1_neq_c2: b1 != c2 by move: b1_nadj_c1; apply/contraTneq => ->; rewrite sg_sym c1_adj_c2.
                                                  move: b1c2b2c1.
                                                  by rewrite (negbTE b2_neq_c1) (negbTE b1_neq_c2) (negbTE b1_nadj_c2) /=.
                                            ----- by done.
                                            ----- by done.
                                            ----- by done.
                                            ----- by done.
                                            ----- by done.
                     +++ admit.

  - case/orP: b1b2 => [/eqP b1_eq_b2 | b1_adj_b2 ].
    + case/orP: c1c2 => [/eqP c1_eq_c2 | c1_adj_c2 ].
      (* a1 a2 --- b b --- c c *)
      *  case/orP: d1d2 => [/eqP d1_eq_d2 | d1_adj_d2 ].
          -- left.
             case: (orP a1b2a2b1)=> [a1b2a2b1' | a2_adj_b1].
             ++ case: (orP a1b2a2b1')=> [b1_dom_c2 |/eqP a2_eq_b1].
                ** case: (orP b1_dom_c2)=> [/eqP a1_eq_b2 | a1_adj_b2].
                   --- pose h' (v : copaw) :=
                       match v with
                       | Ordinal 0 _ => a2
                       | Ordinal 1 _ => b2
                       | Ordinal 2 _ => c2
                       | Ordinal _ _ => d2
                       end.
                       exists h'.
                       +++ apply: h'_inj ; rewrite /=.
                           *** by rewrite -a1_eq_b2 eq_sym (sg_edgeNeq a1_adj_a2).
                           *** by rewrite -c1_eq_c2.
                           *** by rewrite -d1_eq_d2.
                           *** by rewrite -a1_eq_b2.
                           *** by rewrite -d1_eq_d2.
                           *** by rewrite -d1_eq_d2.
                       +++ apply: h'_hom ; rewrite /=.
                           *** by rewrite -a1_eq_b2 sg_sym.
                           *** move: b1b2c1c2 ; rewrite c1_eq_c2 b1_eq_b2 orbb.
                               move: b1c2b2c1 ; rewrite c1_eq_c2 b1_eq_b2 -orbA orbb.
                               case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by []].
                           *** by rewrite -c1_eq_c2.
                           *** by rewrite -d1_eq_d2.
                           *** by rewrite -b1_eq_b2.
                           *** by rewrite -c1_eq_c2.
                   --- pose h' (v : copaw) :=
                       match v with
                       | Ordinal 0 _ => c2
                       | Ordinal 1 _ => b2
                       | Ordinal 2 _ => a1
                       | Ordinal _ _ => d2
                       end.
                       exists h'.
                       +++ apply: h'_inj ; rewrite /=.
                           *** by move: b1b2c1c2 ; rewrite c1_eq_c2 b1_eq_b2 orbb eq_sym.
                           *** by rewrite eq_sym.
                           *** by rewrite -d1_eq_d2.
                           *** by rewrite eq_sym (sg_edgeNeq a1_adj_b2).
                           *** by rewrite -d1_eq_d2.
                           *** by done.
                       +++ apply: h'_hom ; rewrite /=.
                           *** move: b1b2c1c2 ; rewrite c1_eq_c2 b1_eq_b2 orbb.
                               move: b1c2b2c1 ; rewrite c1_eq_c2 b1_eq_b2 -orbA orbb sg_sym.
                               case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by []].
                           *** by rewrite sg_sym.
                           *** by rewrite sg_sym.
                           *** by rewrite -c1_eq_c2.
                           *** by rewrite -b1_eq_b2.
                           *** by done.
                ** pose h' (v : copaw) :=
                   match v with
                   | Ordinal 0 _ => c2
                   | Ordinal 1 _ => b2
                   | Ordinal 2 _ => a1
                   | Ordinal _ _ => d2
                   end.
                   exists h'.
                   --- apply: h'_inj ; rewrite /=.
                       +++ by move: b1b2c1c2 ; rewrite c1_eq_c2 b1_eq_b2 orbb eq_sym.
                       +++ by rewrite eq_sym.
                       +++ by rewrite -c1_eq_c2.
                       +++ by rewrite -b1_eq_b2 -a2_eq_b1 eq_sym (sg_edgeNeq a1_adj_a2).
                       +++ by rewrite -b1_eq_b2.
                       +++ by done.
                   --- apply: h'_hom ; rewrite /=.
                       +++ move: b1b2c1c2 ; rewrite c1_eq_c2 b1_eq_b2 orbb.
                           move: b1c2b2c1 ; rewrite c1_eq_c2 b1_eq_b2 -orbA orbb sg_sym.
                           case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by []].
                       +++ by rewrite -b1_eq_b2 -a2_eq_b1 sg_sym.
                       +++ by rewrite sg_sym.
                       +++ by rewrite -c1_eq_c2.
                       +++ by rewrite -b1_eq_b2.
                       +++ by done.
           ++ pose h' (v : copaw) :=
              match v with
              | Ordinal 0 _ => c2
              | Ordinal 1 _ => b2
              | Ordinal 2 _ => a2
              | Ordinal _ _ => d2
                       end.
              exists h'.
              ** apply: h'_inj ; rewrite /=.
                 --- by move: b1b2c1c2 ; rewrite c1_eq_c2 b1_eq_b2 orbb eq_sym.
                 --- by rewrite -c1_eq_c2 eq_sym.
                 --- by rewrite -c1_eq_c2.
                 --- by rewrite -b1_eq_b2 eq_sym (sg_edgeNeq a2_adj_b1).
                 --- by rewrite -b1_eq_b2.
                 --- by rewrite -d1_eq_d2.
              ** apply: h'_hom ; rewrite /=.
                 --- move: b1b2c1c2 ; rewrite c1_eq_c2 b1_eq_b2 orbb.
                     move: b1c2b2c1 ; rewrite c1_eq_c2 b1_eq_b2 -orbA orbb sg_sym.
                     case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by []].
                 --- by rewrite -b1_eq_b2 sg_sym.
                 --- by rewrite -c1_eq_c2 sg_sym.
                 --- by rewrite -c1_eq_c2.
                 --- by rewrite -b1_eq_b2.
                 --- by rewrite -d1_eq_d2.
          -- left.
             case: (orP a1b2a2b1)=> [a1b2a2b1' | a2_adj_b1].
             ++ case: (orP a1b2a2b1')=> [a1_dom_b2 |/eqP a2_eq_b1].
                ** case: (orP a1_dom_b2)=> [/eqP a1_eq_b2 | a1_adj_b2].
                   --- pose h' (v : copaw) :=
                       match v with
                       | Ordinal 0 _ => c2
                       | Ordinal 1 _ => b2
                       | Ordinal 2 _ => a2
                       | Ordinal _ _ => d1
                       end.
                       exists h'.
                       +++ apply: h'_inj ; rewrite /=.
                           *** by move: b1b2c1c2 ; rewrite c1_eq_c2 b1_eq_b2 orbb eq_sym.
                           *** by rewrite -c1_eq_c2 eq_sym.
                           *** by done.
                           *** by rewrite -a1_eq_b2 (sg_edgeNeq a1_adj_a2).
                           *** by done.
                           *** by done.
                       +++ apply: h'_hom ; rewrite /=.
                           *** move: b1b2c1c2 ; rewrite c1_eq_c2 b1_eq_b2 orbb.
                               move: b1c2b2c1 ; rewrite c1_eq_c2 b1_eq_b2 -orbA orbb sg_sym.
                               by case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | done].
                           *** by rewrite -a1_eq_b2.
                           *** by rewrite -c1_eq_c2 sg_sym.
                           *** by done.
                           *** by done.
                           *** by done.
                   --- pose h' (v : copaw) :=
                       match v with
                       | Ordinal 0 _ => c2
                       | Ordinal 1 _ => b2
                       | Ordinal 2 _ => a1
                       | Ordinal _ _ => d2
                       end.
                       exists h'.
                       +++ apply: h'_inj ; rewrite /=.
                           *** by move: b1b2c1c2 ; rewrite c1_eq_c2 b1_eq_b2 orbb eq_sym.
                           *** by rewrite eq_sym.
                           *** by rewrite -c1_eq_c2.
                           *** by rewrite eq_sym(sg_edgeNeq a1_adj_b2).
                           *** by rewrite -b1_eq_b2.
                           *** by done.
                       +++ apply: h'_hom ; rewrite /=.
                           *** move: b1b2c1c2 ; rewrite c1_eq_c2 b1_eq_b2 orbb.
                               move: b1c2b2c1 ; rewrite c1_eq_c2 b1_eq_b2 -orbA orbb sg_sym.
                               by case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | done].
                           *** by rewrite sg_sym.
                           *** by rewrite sg_sym.
                           *** by rewrite -c1_eq_c2.
                           *** by rewrite -b1_eq_b2.
                           *** by done.
                ** pose h' (v : copaw) :=
                   match v with
                   | Ordinal 0 _ => c2
                   | Ordinal 1 _ => b2
                   | Ordinal 2 _ => a1
                   | Ordinal _ _ => d2
                   end.
                   exists h'.
                   --- apply: h'_inj ; rewrite /=.
                       +++ by move: b1b2c1c2 ; rewrite c1_eq_c2 b1_eq_b2 orbb eq_sym.
                       +++ by rewrite eq_sym.
                       +++ by rewrite -c1_eq_c2.
                       +++ by rewrite -b1_eq_b2 -a2_eq_b1 eq_sym (sg_edgeNeq a1_adj_a2).
                       +++ by rewrite -b1_eq_b2.
                       +++ by done.
                   --- apply: h'_hom ; rewrite /=.
                       +++ move: b1b2c1c2 ; rewrite c1_eq_c2 b1_eq_b2 orbb.
                           move: b1c2b2c1 ; rewrite c1_eq_c2 b1_eq_b2 -orbA orbb sg_sym.
                           by case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | done].
                       +++ by rewrite -b1_eq_b2 -a2_eq_b1 sg_sym.
                       +++ by rewrite sg_sym.
                       +++ by rewrite -c1_eq_c2.
                       +++ by rewrite -b1_eq_b2.
                       +++ by done.
           ++ pose h' (v : copaw) :=
              match v with
              | Ordinal 0 _ => c2
              | Ordinal 1 _ => b2
              | Ordinal 2 _ => a2
              | Ordinal _ _ => d1
              end.
              exists h'.
              ** apply: h'_inj ; rewrite /=.
                 --- by move: b1b2c1c2 ; rewrite c1_eq_c2 b1_eq_b2 orbb eq_sym.
                 --- by rewrite -c1_eq_c2 eq_sym.
                 --- by done.
                 --- by rewrite -b1_eq_b2 eq_sym (sg_edgeNeq a2_adj_b1).
                 --- by done.
                 --- by done.
              ** apply: h'_hom ; rewrite /=.
                 --- move: b1b2c1c2 ; rewrite c1_eq_c2 b1_eq_b2 orbb.
                     move: b1c2b2c1 ; rewrite c1_eq_c2 b1_eq_b2 -orbA orbb sg_sym.
                     by case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | done].
                 --- by rewrite -b1_eq_b2 sg_sym.
                 --- by rewrite -c1_eq_c2 sg_sym.
                 --- by done.
                 --- by done.
                 --- by done.
* admit.
+ admit.
Admitted.

Corollary G'copawfree'_rev : Gcopaw \subgraph G' -> Gcopaw \subgraph G \/
                                                    GG7_1 \subgraph G \/ GG7_2 \subgraph G.
Proof.
  move=> /(subgraph_trans (sub_G2_G1 G_is_copaw)) copawsubG'.
  move: (G'copawfree_rev copawsubG') ; case.
  { by left ; apply: (subgraph_trans (sub_G1_G2 G_is_copaw)). }
  case.
  - by right ; left ; apply: (subgraph_trans (sub_G1_G2 G_is_G7_1)).
  - by right ; right ; apply: (subgraph_trans (sub_G1_G2 G_is_G7_2)).
Qed.

Theorem G'clawfree_rev : claw \subgraph G' -> claw \subgraph G \/ bull \subgraph G \/
                                             'P_6 \subgraph G \/ 'CC_6 \subgraph G.
Proof.
  rewrite /induced_subgraph.
  move=> [h h_inj h_hom].

  (* in G', we have the claw (b1,b2) - (a1,a2) - (c1,c2) *)
  (*                                   (d1,d2)           *)
  set a1 := (h 'v0@4).1.
  set a2 := (h 'v0@4).2.
  set b1 := (h 'v1@4).1.
  set b2 := (h 'v1@4).2.
  set c1 := (h 'v2@4).1.
  set c2 := (h 'v2@4).2.
  set d1 := (h 'v3@4).1.
  set d2 := (h 'v3@4).2.

  (* The following comes from the fact that x1x2 are vertices of G' *)
  have a1a2 : (a1 == a2) || a1 -- a2 by exact: (valP (h 'v0@4)). 
  have b1b2 : (b1 == b2) || b1 -- b2 by exact: (valP (h 'v1@4)).
  have c1c2 : (c1 == c2) || c1 -- c2 by exact: (valP (h 'v2@4)).
  have d1d2 : (d1 == d2) || d1 -- d2 by exact: (valP (h 'v3@4)).

  (* The following comes from the edges of the claw in G' *)
  have a1b2a2b1 : (a1 == b2) || a1 -- b2 || (a2 == b1) || (a2 -- b1)
    by t_v1v2 'v0@4 'v1@4 h h_hom.
  have a1c2a2c1 : (a1 == c2) || a1 -- c2 || (a2 == c1) || (a2 -- c1)
    by t_v1v2 'v0@4 'v2@4 h h_hom.
  have a1d2a2d1 : (a1 == d2) || a1 -- d2 || (a2 == d1) || (a2 -- d1)
    by t_v1v2 'v0@4 'v3@4 h h_hom.

  (* The following comes from the fact that vertices of the claw are different *)
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

  (* The following comes from the no-edges of the claw in G' *)
  have b1c2b2c1 : (b1 != c2) && (~~ b1 -- c2) && (b2 != c1) && (~~ b2 -- c1)
    by t_x1y2x2y1 b1 b2 c1 c2 'v1@4 'v2@4 h h_hom.
  have b1d2b2d1 : (b1 != d2) && (~~ b1 -- d2) && (b2 != d1) && (~~ b2 -- d1)
    by t_x1y2x2y1 b1 b2 d1 d2 'v1@4 'v3@4 h h_hom.
  have c1d2c2d1 : (c1 != d2) && (~~ c1 -- d2) && (c2 != d1) && (~~ c2 -- d1)
    by t_x1y2x2y1 c1 c2 d1 d2 'v2@4 'v3@4 h h_hom.

  (* Here is a proof of injectivity of a given function, by giving proofs of
     inequalities among their vertices *)
  have h'_inj (h' : claw -> G)
    (v0v1 : h' 'v0@4 != h' 'v1@4) (v0v2 : h' 'v0@4 != h' 'v2@4)
    (v0v3 : h' 'v0@4 != h' 'v3@4) (v1v2 : h' 'v1@4 != h' 'v2@4)
    (v1v3 : h' 'v1@4 != h' 'v3@4) (v2v3 : h' 'v2@4 != h' 'v3@4)
       : forall x1 x2 : claw, h' x1 = h' x2 -> x1 = x2.
  { move: (negP v0v1) => ?. move: (negP v0v2) => ?. move: (negP v0v3) => ?.
    move: (negP v1v2) => ?. move: (negP v1v3) => ?. move: (negP v2v3) => ?.
    rewrite !forallOrdinalI4 ; do 6 try split.
    all : try by [].
    all : try by move/eqP ; contradiction.
    all : try by move/eqP ; rewrite eq_sym ; contradiction.
  }

  (* Here is a proof of the homomorphism of a given function, by giving proofs
     of the edges and non-edges of the claw *)
  have h'_hom (h' : claw -> G)
    (e_v0v1 : h' 'v0@4 -- h' 'v1@4) (e_v0v2 : h' 'v0@4 -- h' 'v2@4)
    (e_v0v3 : h' 'v0@4 -- h' 'v3@4) (n_v1v2 : ~~ h' 'v1@4 -- h' 'v2@4)
    (n_v1v3 : ~~ h' 'v1@4 -- h' 'v3@4) (n_v2v3 : ~~ h' 'v2@4 -- h' 'v3@4)
       : forall x1 x2 : claw, x1 -- x2 <-> h' x1 -- h' x2.
  { rewrite !forallOrdinalI4 ; do 7 try split.
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
        (* b b --- a a --- c c *)
        (*         d d         *)
        -- left ; pose h' (v : claw) :=
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
              ** move: a1a2c1c2 ; rewrite (eqP a1eqa2) (eqP c1eqc2) orbb.
                 move: a1c2a2c1 ; rewrite (eqP a1eqa2) (eqP c1eqc2) -orbA orbb.
                 case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by []].
              ** move: a1a2d1d2 ; rewrite (eqP a1eqa2) (eqP d1eqd2) orbb.
                 move: a1d2a2d1 ; rewrite (eqP a1eqa2) (eqP d1eqd2) -orbA orbb.
                 case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by []].
              ** by move: b1c2b2c1 => /andP [_] ; rewrite (eqP b1eqb2).
              ** by move: b1d2b2d1 => /andP [_] ; rewrite (eqP b1eqb2).
              ** by move: c1d2c2d1 => /andP [_] ; rewrite (eqP c1eqc2).
        (* b b --- a a --- c c *)
        (*        d1 d2        *)
        -- left ; pose h' (v : claw) :=
                  match v with
                  | Ordinal 0 _ => a1
                  | Ordinal 1 _ => b1
                  | Ordinal 2 _ => c1
                  | Ordinal _ _ => if (a1 -- d1) then d1 else d2
                  end.
           exists h'.
           ++ apply: h'_inj ; rewrite /=.
              ** by move: a1a2b1b2 ; rewrite (eqP a1eqa2) (eqP b1eqb2) orbb.
              ** by move: a1a2c1c2 ; rewrite (eqP a1eqa2) (eqP c1eqc2) orbb.
              ** rewrite (fun_if (fun d => a1 != d)) ; case: (boolP (a1 -- d1)).
                 --- by apply: contraL ; move/eqP-> ; rewrite sg_irrefl.
                 --- by apply: contra ; move/eqP-> ; rewrite sg_sym.
              ** by move: b1b2c1c2 ; rewrite (eqP b1eqb2) (eqP c1eqc2) orbb.
              ** rewrite (fun_if (fun d => b1 != d)) ; case: (boolP (a1 -- d1)).
                 --- by move: b1d2b2d1 => /andP [/andP [_ ?]] ; rewrite (eqP b1eqb2).
                 --- by move: b1d2b2d1 => /andP [/andP [ /andP [? _]]].
              ** rewrite (fun_if (fun d => c1 != d)) ; case: (boolP (a1 -- d1)).
                 --- by move: c1d2c2d1 => /andP [/andP [_ ?]] ; rewrite (eqP c1eqc2).
                 --- by move: c1d2c2d1 => /andP [/andP [ /andP [? _]]].
           ++ apply: h'_hom ; rewrite /=.
              ** move: a1a2b1b2 ; rewrite (eqP a1eqa2) (eqP b1eqb2) orbb.
                 move: a1b2a2b1 ; rewrite (eqP a1eqa2) (eqP b1eqb2) -orbA orbb.
                 case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by []].
              ** move: a1a2c1c2 ; rewrite (eqP a1eqa2) (eqP c1eqc2) orbb.
                 move: a1c2a2c1 ; rewrite (eqP a1eqa2) (eqP c1eqc2) -orbA orbb.
                 case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by []].
              ** rewrite (fun_if (fun d => a1 -- d)) ; case: (boolP (a1 -- d1)).
                 --- by move=> _.
                 --- move: a1d2a2d1 ; rewrite (eqP a1eqa2) ; case/orP ; last
                       by move=> ? /negP ; contradiction.
                     case/orP ; last by move/eqP->.
                     case/orP ; last by [].
                     by move/eqP-> ; apply: contraR ; rewrite sg_sym.
              ** by move: b1c2b2c1 => /andP [_] ; rewrite (eqP b1eqb2).
              ** rewrite (fun_if (fun d => b1 -- d)) ; case: (boolP (a1 -- d1)).
                 --- by move: b1d2b2d1 => /andP [/andP [_ ?]] ; rewrite (eqP b1eqb2).
                 --- by move: b1d2b2d1 => /andP [/andP [ /andP [_ ?]]].
              ** rewrite (fun_if (fun d => c1 -- d)) ; case: (boolP (a1 -- d1)).
                 --- by move: c1d2c2d1 => /andP [/andP [_ ?]] ; rewrite (eqP c1eqc2).
                 --- by move: c1d2c2d1 => /andP [/andP [ /andP [_ ?]]].
      * admit.
    + admit.
  - admit.
Admitted.

Corollary G'clawfree'_rev : Gclaw \subgraph G' -> Gclaw \subgraph G \/ Gbull \subgraph G \/
                                                    GP6 \subgraph G \/ GCC6 \subgraph G.
Proof.
  move=> /(subgraph_trans (sub_G2_G1 G_is_claw)) clawsubG'.
  move: (G'clawfree_rev clawsubG') ; case.
  { by left ; apply: (subgraph_trans (sub_G1_G2 G_is_claw)). }
  case.
  { by right ; left ; apply: (subgraph_trans (sub_G1_G2 G_is_bull)). }
  case.
  - by right ; right ; left ; apply: (subgraph_trans (sub_G1_G2 G_is_P6)).
  - by right ; right ; right ; apply: (subgraph_trans (sub_G1_G2 G_is_CC6)).
Qed.

(*End Upper_Weighted_Irredundant_Properties.*)









































(* ************************ ATENCION! **************************)

(* DEJE ACA TODO LO QUE CREO QUE NO VA A ENTRAR EN LA VERSION FINAL
   De momento lo de G {P4, K23}-free <==> G' P4-free *)

Lemma P4_sub_P4' : 'P_4 \subgraph trfgraph 'P_4.
Proof. exact: subgraph_G_G'. Qed.

Lemma P4_sub_K23' : 'P_4 \subgraph trfgraph 'K_2,3.
Proof.
  have K23'_v1 : @dominates 'K_2,3 ('v3@5, 'v0@5).1 ('v3@5, 'v0@5).2 by done.
  have K23'_v2 : @dominates 'K_2,3 ('v2@5, 'v0@5).1 ('v2@5, 'v0@5).2 by done.
  have K23'_v3 : @dominates 'K_2,3 ('v1@5, 'v2@5).1 ('v1@5, 'v2@5).2 by done.
  have K23'_v4 : @dominates 'K_2,3 ('v1@5, 'v4@5).1 ('v1@5, 'v4@5).2 by done.
  pose h (v : 'P_4) : trfgraph 'K_2,3 :=
    match v with
    | Ordinal 0 _ => TrfGraphVert K23'_v1
    | Ordinal 1 _ => TrfGraphVert K23'_v2
    | Ordinal 2 _ => TrfGraphVert K23'_v3
    | Ordinal _ _ => TrfGraphVert K23'_v4
    end.
  exists h. all: case => [[|[|[|[|i]]]] Hi]; case => [[|[|[|[|j]]]] Hj]; subgraph_proof Hi Hj.
Qed.

(* To prove G' P4-free => G {P4,K23}-free we do the following:
     If G has P4 as an induced subgraph, then G' does too.
     If G has K23 as an induced subgraph, then G' has a P4. *)

Theorem G'P4free : 'P_4 \subgraph G \/ 'K_2,3 \subgraph G -> 'P_4 \subgraph G'.
Proof.
  case.
  - move/trfgraph_subgraph=> P4'subG' ;
    by move: (subgraph_trans P4_sub_P4' P4'subG').
  - move/trfgraph_subgraph=> K23'subG' ;
    by move: (subgraph_trans P4_sub_K23' K23'subG').
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

Theorem G'P4free_rev : 'P_4 \subgraph G' -> 'P_4 \subgraph G \/ 'K_2,3 \subgraph G.
Proof.
  rewrite /induced_subgraph.
  move=> [h h_inj h_hom].

  (* in G', we have the path (a1,a2) - (b1,b2) - (c1,c2) - (d1,d2) *)
  set a1 := (h 'v0@4).1.
  set a2 := (h 'v0@4).2.
  set b1 := (h 'v1@4).1.
  set b2 := (h 'v1@4).2.
  set c1 := (h 'v2@4).1.
  set c2 := (h 'v2@4).2.
  set d1 := (h 'v3@4).1.
  set d2 := (h 'v3@4).2.

  (* The following comes from the fact that x1x2 are vertices of G' *)
  have a1a2 : (a1 == a2) || a1 -- a2 by exact: (valP (h 'v0@4)).
  have b1b2 : (b1 == b2) || b1 -- b2 by exact: (valP (h 'v1@4)).
  have c1c2 : (c1 == c2) || c1 -- c2 by exact: (valP (h 'v2@4)).
  have d1d2 : (d1 == d2) || d1 -- d2 by exact: (valP (h 'v3@4)).

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
  have a1c2a2c1 : (a1 != c2) && (~~ a1 -- c2) && (a2 != c1) && (~~ a2 -- c1).
    by t_x1y2x2y1 a1 a2 c1 c2 'v0@4 'v2@4 h h_hom.
  have a1d2a2d1 : (a1 != d2) && (~~ a1 -- d2) && (a2 != d1) && (~~ a2 -- d1).
    by t_x1y2x2y1 a1 a2 d1 d2 'v0@4 'v3@4 h h_hom.
  have b1d2b2d1 : (b1 != d2) && (~~ b1 -- d2) && (b2 != d1) && (~~ b2 -- d1).
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
    rewrite !forallOrdinalI4 ; do 6 try split.
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
  { rewrite !forallOrdinalI4 ; do 7 try split.
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


(** * Alternative versions of private_set for irredundant sets *)
Section alternative_private_set.

Variable G : sgraph.

Variable D : {set G}.

(* This alternative definition of private_set contemplates cases where v \notin D.
 * If v belongs to D, it returns the set of private vertices; otherwise, it returns an empty set. *)
Definition private_set' (v : G) := NS[D :&: [set v]] :\: NS[D :\: [set v]].

Lemma eq_prvs_prvs' (v : G) : v \in D -> private_set' v == private_set D v.
Proof.
  move=> ?; rewrite /private_set /private_set'.
  suff: N[v] = NS[D :&: [set v]] by move->.
  rewrite (setIidPr _) ?sub1set //.
  apply/eqP ; rewrite eqEsubset ; apply/andP ; split.
  - by apply/cln_sub_clns/set1P.
  - by apply/subsetP => x; move/bigcupP => [?]; move/set1P ->.
Qed.

Lemma eq0prvs' (v : G) : v \notinD -> (private_set' v == set0).
Proof.
  move=> vnotinD ; rewrite /private_set' disjoint_setI0 1?disjoint_sym ?disjoints1 //.
  by rewrite clns0 set0D.
Qed.

End alternative_private_set.


