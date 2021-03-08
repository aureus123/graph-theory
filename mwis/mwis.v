
(* Formalization of resolution of the Upper Weighted Irredundant Problem
 * via the Maximum Weighted Stable Set Problem
 *
 * Contributors: Ricardo Katz, Daniel Severin, Mauricio Salichs *)

From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import preliminaries digraph sgraph dom.
Require Import prelim.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


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
Section Upper_Weighted_Irredundant_Problem_Transformation.

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

End Upper_Weighted_Irredundant_Problem_Transformation.


(**********************************************************************************)
Section IR_w_upper_bound.

Variable G : sgraph.
Variable weight : G -> nat.

Let G' := trfgraph G.
Let W := weight_set weight.

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

