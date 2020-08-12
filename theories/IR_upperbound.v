
(* Definitions of max/min degree and the proof that IR <= |V| - delta *)

From mathcomp Require Import all_ssreflect.
Require Import preliminaries digraph sgraph connectivity dom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


(**********************************************************************************)
(** * Minimum and maximum (weighted and unweighted) degrees of a graph *)

Section Weighted_degree.

Variable G : sgraph.
Variable weight : G -> nat.
Hypothesis positive_weights : forall v : G, weight v > 0.

Let W := weight_set weight.

Definition deg_w (v : G) := W N(v).

Lemma ltn_deg_w_subwsetT1 (v : G) : deg_w v <= W setT - 1.
Proof.
  suff: deg_w v < W setT by move=> H ; rewrite (pred_Sn (deg_w v)) -subn1 (leq_sub2r 1 H).
  rewrite /deg_w ; apply: (ltnwset positive_weights).
  rewrite properT ; apply/negP => /eqP H1.
  move: (in_setT v) ; rewrite -H1 ; move/negP: (v_notin_opneigh v) ; contradiction.
Qed.

(* Minimum and maximum weighted degree of a graph. *)

(* x is a vertex of G (i.e. G is a non-empty graph) *)
Hypothesis x : G.

Let some_vertex_with_neighborhood (S : {set G}) := [exists v, S == N(v)].

Local Fact Nx_is_neighborhood_x : some_vertex_with_neighborhood N(x).
Proof. by rewrite /some_vertex_with_neighborhood ; apply/existsP ; exists x. Qed.

Definition delta_w := W (arg_min N(x) some_vertex_with_neighborhood W).

Fact delta_w_min (v : G) : delta_w <= deg_w v.
Proof.
  rewrite /delta_w ; case: (arg_minP W Nx_is_neighborhood_x) => A _ ; apply.
  by rewrite /some_vertex_with_neighborhood ; apply/existsP ; exists v.
Qed.

Fact delta_w_witness : exists v, deg_w v = delta_w.
Proof.
  rewrite /delta_w ; case: (arg_minP W Nx_is_neighborhood_x) => S exS _.
  move/existsP: exS => [u] /eqP SeqNu ; exists u ; by rewrite /deg_w SeqNu.
Qed.

Definition Delta_w := W (arg_max N(x) some_vertex_with_neighborhood W).

Fact Delta_w_max (v : G) : deg_w v <= Delta_w.
Proof.
  rewrite /Delta_w ; case: (arg_maxP W Nx_is_neighborhood_x) => A _ ; apply.
  by rewrite /some_vertex_with_neighborhood ; apply/existsP ; exists v.
Qed.

Fact Delta_w_witness : exists v, deg_w v = Delta_w.
Proof.
  rewrite /Delta_w ; case: (arg_maxP W Nx_is_neighborhood_x) => S exS _.
  move/existsP: exS => [u] /eqP SeqNu ; exists u ; by rewrite /deg_w SeqNu.
Qed.

End Weighted_degree.


Section Degree_of_vertices.

Variable G : sgraph.

Definition deg (v : G) := #|N(v)|.

Fact eq_deg_deg1 (v : G) : deg v = deg_w (@ones G) v.
Proof. by rewrite /deg /deg_w -cardwset1. Qed.

Lemma ltn_deg_subn1 (v : G) : deg v <= #|G| - 1.
Proof. by rewrite eq_deg_deg1 -cardsT (cardwset1 setT) ; exact: ltn_deg_w_subwsetT1. Qed.

(* Minimum and maximum weighted degree of a graph. *)

(* x is a vertex of G (i.e. G is a non-empty graph) *)
Hypothesis somev : G.

Let some_vertex_with_degree (n : nat) := [exists v, deg v == n].

Local Fact degx_has_deg_x : exists (n : nat), some_vertex_with_degree n.
Proof. by rewrite /some_vertex_with_degree ; exists (deg somev) ; apply/existsP ; exists somev. Qed.

Local Fact ltn_someu_degu_subn1 (n : nat) : some_vertex_with_degree n -> n <= #|G| - 1.
Proof.
  rewrite /some_vertex_with_degree ; move/existsP => [u].
  move/eqP<- ; exact: ltn_deg_subn1.
Qed.

Definition delta := ex_minn degx_has_deg_x.

Lemma eq_delta_delta1 : delta = delta_w (@ones G) somev.
Proof.
  rewrite /delta.
  have [n some_n n_min] := ex_minnP.
  apply/eqP ; rewrite eqn_leq ; apply/andP ; split.
  - apply: n_min ; rewrite /some_vertex_with_degree.
    apply/existsP ; elim: (delta_w_witness (@ones G) somev) => u.
    move<- ; exists u ; apply/eqP.
    exact: eq_deg_deg1.
  - move: some_n.
    rewrite /some_vertex_with_degree.
    move/existsP => [u] /eqP <-.
    rewrite eq_deg_deg1.
    exact: delta_w_min.
Qed.

Fact delta_min (v : G) : delta <= deg v.
Proof. rewrite eq_delta_delta1 eq_deg_deg1; exact: delta_w_min. Qed.

Definition Delta := ex_maxn degx_has_deg_x ltn_someu_degu_subn1.

Lemma eq_Delta_Delta1 : Delta = Delta_w (@ones G) somev.
Proof.
  rewrite /Delta.
  have [n some_n n_max] := ex_maxnP.
  apply/eqP ; rewrite eqn_leq ; apply/andP ; split.
  - move: some_n.
    rewrite /some_vertex_with_degree.
    move/existsP => [u] /eqP <-.
    rewrite eq_deg_deg1.
    exact: Delta_w_max.
  - apply: n_max ; rewrite /some_vertex_with_degree.
    apply/existsP ; elim: (Delta_w_witness (@ones G) somev) => u.
    move<- ; exists u ; apply/eqP.
    exact: eq_deg_deg1.
Qed.

Fact Delta_min (v : G) : deg v <= Delta.
Proof. rewrite eq_Delta_Delta1 eq_deg_deg1; exact: Delta_w_max. Qed.

End Degree_of_vertices.

(**********************************************************************************)
(** * Proof of the upper bound of IR(G) *)

Section IR_upperbound.

Variable G : sgraph.

(* somev is a vertex of G (i.e. G is a non-empty graph) *)
Hypothesis somev : G.

Local Lemma bigcup_disj (A : {set G}) (F : G -> {set G}) :
  {in A, forall x, 0 < #|F x|} ->
  {in A&, forall x y, x != y -> [disjoint F x & F y]} ->
  #|\bigcup_(x in A) F x| = \sum_(x in A) #|F x|.
Proof.
  move=> Fn0 Fdisj; pose Fs := imset F (mem A).
  have trivFs: trivIset Fs.
  { apply/trivIsetP=> _ _ /imsetP[i iA ->] /imsetP[j jA ->] neqFij.
    apply/(Fdisj i j iA jA)/negP. move/eqP=> ieqj.
    rewrite ieqj in neqFij. by move/negP in neqFij. }
  rewrite -(big_imset id _) /=.
  rewrite -(big_imset (fun X : {set G} => card (mem X)) _) /=.
  apply/eqP; rewrite eq_sym; exact: trivFs.
  all: rewrite/injective=> [v w vA wA FvFw].
  all: apply/eqP/contraT=> vneqw.
  all: move: (Fdisj v w vA wA vneqw)=> Fw0.
  all: rewrite FvFw in Fw0; move/disjoint_setI0 in Fw0.
  all: rewrite setIid in Fw0; move: (Fn0 w wA)=> Fwn0.
  all: by rewrite Fw0 cards0 in Fwn0; move/negP in Fwn0.
Qed.

Lemma disjoint_prv (D : {set G}) :
  {in D&, forall v w, v != w -> [disjoint private_set D v & private_set D w]}.
Proof.
  move=> v w vD wD vneqw ; apply/disjointP=> x.
  move/privateP=> [vdomx _] ; move/privateP=> [_ prvw].
  by move: vneqw ; rewrite (prvw v vD vdomx) ; move/negP.
Qed.

(*  Prueba completa, pero demasiado larga.
    Voy a simplificarla lo mas posible usando las recomendaciones de Christian. *)
Theorem IR_leq_V_minus_delta : IR G <= #|[set: G]| - @delta G somev.
Proof.
  rewrite /IR.
  have [S irrS _] := arg_maxP (fun D : {set G} => #|D|) (irr0 G).
  case (boolP (S == set0)) ; first by move/eqP-> ; rewrite cards0 leq0n.
  move=> S0n. move: (S0n) ; move/set0Pn=> [v vS].
  have degV := delta_min somev v ; rewrite /deg in degV.
  have H : #|N(v)| <= #|[set: G] :\: S|.
  { have splitNv : N(v) :\: N(v) :&: S = N(v) :\: S by rewrite -[in X in _ = X](set0U (N(v) :\: S)) -(setDv N(v)); exact: setDIr.
    have NvsubV : N(v) :\: N(v) :&: S \subset [set: G] :\: S by rewrite splitNv setSD.
    case (boolP (N(v) :&: S == set0)).
    - move/eqP=> NvS0 ; move: NvsubV ; rewrite NvS0 setD0 ; exact: subset_leq_card.
    - move/set0Pn=> _.
      set prvSNv := \bigcup_(w in N(v) :&: S) private_set S w.
(* Probamos que el conjunto de los vertices privados elegidos de N(v) :&: S no están en S *)
      have prvSsubV : prvSNv \subset [set: G] :\: S.
      { apply/subsetP. move=> y; rewrite /prvSNv.
        move/bigcupP; elim=> y' y'NvS.
        move/privateP=> [y'domy prvy'].
        rewrite in_setD; apply/andP; split; last by []. apply/contraT. move/negPn=> yS.
        have yeqy' := (prvy' y yS (dominates_refl y)). rewrite -yeqy' in y'NvS.
        have/setIP [yNv _] := y'NvS. move: (yNv)=> yNv'; rewrite in_opn in yNv'; move/or_intror in yNv'.
        have/orP vdomy := yNv' (v == y). have veqy' := prvy' v vS vdomy. rewrite yeqy' -veqy' in yNv.
        by move: (v_notin_opneigh v)=> VnNv; move/negP in VnNv.
      }
(* Probamos que ela cardinalidad de N(v) :&: S es igual o menor que la de sus vertices privados elegidos  *)
      have leq_card_prvS_NvcapS : #|prvSNv| >= #|N(v) :&: S|. (*Check inj_card_leq.*)
      { rewrite /prvSNv.
        have prv_disj: forall x y : G, x \in N(v) :&: S -> y \in N(v) :&: S -> (x != y) -> [disjoint private_set S x & private_set S y].
        by move=> w w'; move/setIP=> [_ wS]; move/setIP=> [_ w'S]; exact: disjoint_prv wS w'S.
        have prv_NvS_n0 : (forall x : G, x \in N(v) :&: S -> 0 < #|private_set S x|).
        by move=> w /setIP [wNv wS]; rewrite card_gt0; move/irredundantP: irrS; move=> /(_ w wS).
        rewrite (bigcup_disj prv_NvS_n0 prv_disj) -sum1_card.
        apply/leq_sum/prv_NvS_n0.
      } rewrite -(leq_add2l (#|N(v)| - #|N(v) :&: S|)) in leq_card_prvS_NvcapS.
(* Probamos que ningún vertice en el conjunto de los privados de N(v) :&: S es vecino de v *)
      have disj_Nv_prvSNv : N(v) :&: prvSNv = set0.
      { apply/eqP; rewrite setIC setI_eq0 disjoints_subset. apply/subsetP=> w.
        rewrite in_setC in_opn /prvSNv.
        move/bigcupP; elim=> w' w'NvS. have/setIP [w'Nv _] := w'NvS.
        move/privateP=> [w'domw prvw'].
        apply/contraT. move/negPn=> vadjw. move/or_intror in vadjw.
        have/orP vdomw := vadjw (v == w). have veqw' := prvw' v vS vdomw.
        rewrite -veqw' in w'Nv. by move: (v_notin_opneigh v)=> VnNv; move/negP in VnNv.
      }
(* Fin de las pruebas *)
      move/subUsetP/subset_leq_card: (conj NvsubV prvSsubV)=> Nv'subV.
      have disj_full : (N(v) :\: N(v) :&: S) :&: prvSNv = set0 by rewrite setIDAC disj_Nv_prvSNv set0D.
      have NvgeqNvcupS : #|N(v)| >= #|N(v) :&: S| by rewrite -[in X in _ <= X](cardsID S) leq_addr.
      rewrite cardsU disj_full cardsDS in Nv'subV; last by exact: subsetIl. rewrite cards0 subn0 in Nv'subV.
      by move: (leq_trans leq_card_prvS_NvcapS Nv'subV); rewrite subnK.
  }
  rewrite cardsDS in H; last by auto.
  case (boolP (@delta G somev > 0)).
  + move=> deltagt0. rewrite -card_gt0 in S0n. rewrite leq_psubCr.
    exact: (leq_trans degV H). exact: S0n. exact: deltagt0.
  + rewrite -leqNgt leqn0; move/eqP=> delta0. rewrite delta0 subn0.
    exact: subset_leq_card.
Qed.

End IR_upperbound.

Arguments deg_w : clear implicits.
Arguments delta_w : clear implicits.
Arguments Delta_w : clear implicits.
Arguments deg : clear implicits.
Arguments delta : clear implicits.
Arguments Delta : clear implicits.


(**********************************************************************************)
(** * Example of value of IR(K_n) *)

Section IR_complete_graph.

Variable n : nat.
Hypothesis n_positive : 0 < n.

Let somev := @Ordinal n 0 n_positive : 'I_n.

Theorem min_degree_complete : @delta 'K_n somev = n - 1.
Proof.
  rewrite /delta ; have [d some_d _] := ex_minnP.
  suff: forall v : 'K_n, @deg 'K_n v = n - 1.
  { by move/existsP: some_d => [x] ; move/eqP<- ; move=> /(_ x). }
  move=> v ; rewrite /deg.
  suff: N(v) == [set~ v] by move/eqP-> ; rewrite cardsC1 card_ord subn1.
  rewrite /open_neigh ; rewrite eqEsubset ; apply/andP ; split.
  - apply/subsetP=> w ; rewrite in_set in_setC ; apply: contra.
    by rewrite in_set1 eq_sym.
  - apply/subsetP=> w ; rewrite in_set in_setC /edge_rel /=.
    by apply: contra ; rewrite in_set1 eq_sym.
Qed.

Lemma somev_irr : @irredundant 'K_n [set somev].
Proof.
  apply/irredundantP ; move=> v vinD ; apply/set0Pn ; exists v.
  apply/privateP ; split ; first by exact: dominates_refl.
  move=> u ; rewrite in_set1 ; move/eqP=> -> _.
  by move: vinD ; rewrite in_set1 ; move/eqP->.
Qed.

Theorem IR_complete_1 : IR 'K_n = 1.
Proof.
  apply/eqP ; rewrite eqn_leq ; apply/andP ; split.
  - have: IR 'K_n <= #|[set: 'K_n]| - @delta 'K_n somev by exact: IR_leq_V_minus_delta.
    by rewrite min_degree_complete cardsT card_ord (subKn n_positive).
  - have: #|[set somev]| = 1 by rewrite cards1.
    by move<- ; rewrite eq_IR_IR1 (@cardwset1 'K_n [set somev]) (IR_max _ somev_irr).
Qed.

End IR_complete_graph.
