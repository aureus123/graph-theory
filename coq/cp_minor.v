From mathcomp Require Import all_ssreflect.

Require Import edone finite_quotient preliminaries sgraph minor checkpoint.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs". 

(** * Combined Minor and Checkpoint Properties *)

(** This file is where we combine the theory of checkpoints and the theory of
minors and prove the lemmas underlying the correctness arguments for the term
extraction function. *)


Lemma linkNeq (G : sgraph) (x y : link_graph G) : x -- y -> x != y.
Proof. move => A. by rewrite sg_edgeNeq. Qed.

Arguments Path G x y : clear implicits.

Section CheckpointsAndMinors.
Variables (G : sgraph).
Hypothesis (conn_G : connected [set: G]).


Lemma ins (T : finType) (A : pred T) x : x \in A -> x \in [set z in A].
Proof. by rewrite inE. Qed.

(** ** K4 of link triangle *)

Lemma C3_of_triangle (x y z : link_graph G) : 
  x -- y -> y -- z -> z -- x -> exists2 phi : G -> option C3, 
  minor_map phi & [/\ phi x = Some ord0, phi y = Some ord1 & phi z = Some ord2].
Proof.
  move => xy yz zx.
  have/cpPn' [p irr_p av_z] : (z:G) \notin @cp G x y. 
  { apply: link_cpN => //; apply: linkNeq => //. by rewrite sg_sym. }
  have/cpPn' [q irr_q av_x] : (x:G) \notin @cp G z y.
  { apply: link_cpN => //; first (by rewrite sg_sym) ;apply: linkNeq => //. 
    by rewrite sg_sym. }
  have [Yq Yp] : y \in q /\ y \in p by split;apply: nodes_end.
  case: (split_at_first (G := G) (A := mem p) Yp Yq) => n1 [q1] [q2] [def_q Q1 Q2]. 
  have Hn : n1 != x.
  { apply: contraNN av_x => /eqP<-. by rewrite def_q mem_pcat nodes_end. }
  have {q irr_q av_x Yq def_q q2 Yp} irr_q1 : irred q1.
  { move:irr_q. rewrite def_q irred_cat. by case/and3P. }
  have/cpPn' [q irr_q av_n1] : n1 \notin @cp G z x. 
  { apply link_cpN => //. apply: contraNN av_z => /eqP?. by subst n1. }
  have [Xq Xp] : x \in q /\ x \in p by split; rewrite /= ?nodes_end ?nodes_start. 
  case: (split_at_first (G := G) (A := mem p) Xp Xq) => n2 [q2] [q2'] [def_q Q3 Q4].
  have N : n1 != n2. 
  { apply: contraNN av_n1 => /eqP->. by rewrite def_q mem_pcat nodes_end. }
  have {q irr_q av_n1 Xp Xq q2' def_q} irr_q2 : irred q2.
  { move:irr_q. rewrite def_q irred_cat. by case/and3P. }
  wlog before: n1 n2 q1 q2 irr_q1 irr_q2 Q1 Q2 Q3 Q4 N {Hn} / idx p n1 < idx p n2. 
  { move => W. 
    case: (ltngtP (idx p n1) (idx p n2)) => H.
    - by apply: (W n1 n2 q1 q2).
    - apply: (W n2 n1 q2 q1) => //. by rewrite eq_sym.
    - case:notF. apply: contraNT N => _. apply/eqP. exact: idx_inj H. }
  case: (splitR q1 _) => [|z1 [q1' [zn1 def_q1]]].
  { by apply: contraNN av_z => /eqP->. }
  case: (splitR q2 _) => [|z2 [q2' [zn2 def_q2]]].
  { by apply: contraNN av_z => /eqP->. }
  gen have D,D1 : z1 n1 q1 q1' zn1 irr_q1 def_q1  Q2 {Q1 N before} / 
     [disjoint p & q1'].
  { have A : n1 \notin q1'. 
    { move: irr_q1. rewrite def_q1 irred_cat /= => /and3P[_ _ A].
      by rewrite (disjointFl A _). }
    rewrite disjoint_subset; apply/subsetP => z' Hz'. rewrite !inE.
    apply: contraNN A => A. 
    by rewrite -[n1](Q2 _ Hz' _) // def_q1 mem_pcat A. }
  have {D} D2 : [disjoint p & q2'] by apply: (D z2 n2 q2 q2' zn2).
  case/(isplitP irr_p) def_p : p / Q1 => [p1 p2 _ irr_p2 D3].
  have N2 : n2 \in tail p2. { subst p. by rewrite -idxR in before. }
  have N1 : n1 != y. 
  { apply: contraTN before => /eqP->. by rewrite -leqNgt idx_end // idx_mem. }
  case: (splitL p2 N1) => n1' [n_edge] [p2'] [def_p2 tail_p2].
  have N2' : n2 \in p2' by rewrite tail_p2.
  
  pose pz := pcat (prev q1') q2'.
  pose phi u : option C3 := 
         if u \in p1  then Some ord0
    else if u \in p2' then Some ord1
    else if u \in pz  then Some ord2
                    else None.
  have D_aux : [disjoint p & pz].
  { (* ugly: exposes in_nodes *)
    rewrite ![[disjoint p & _]]disjoint_sym in D1 D2 *. 
    rewrite (eq_disjoint (A2 := [predU q1' & q2'])) ?disjointU ?D1 //.
    move => u. by rewrite !inE mem_pcat mem_prev. }
  have {D_aux} D : [disjoint3 p1 & p2' & pz].
  { subst p; apply/and3P. split.
    - apply: disjoint_transR D3. apply/subsetP => u. by rewrite tail_p2. 
    - apply: disjoint_transL D_aux. apply/subsetP => u. 
      by rewrite mem_pcatT tail_p2 => ->.
    - rewrite disjoint_sym. apply: disjoint_transL D_aux. apply/subsetP => u. 
      by rewrite mem_pcat => ->. }
  (* clean up assumptions that are no longer needed *)
  move => {Q2 Q3 Q4 av_z irr_p before D2 D1 D3 irr_q1 irr_q2 xy yz zx}.
  move => {def_q1 def_q2 N1 N2 def_p2 tail_p2 p def_p N q1 q2}.

  have [Px Py Pz] : [/\ x \in p1, y \in p2' & z \in pz]. 
  { by rewrite /= mem_pcat ?nodes_start ?nodes_end. }
  have phi_x : phi x = Some ord0. 
  { rewrite /phi. by case: (disjoint3P x D) Px. }
  have phi_y : phi y = Some ord1. 
  { rewrite /phi. by case: (disjoint3P y D) Py. }
  have phi_z : phi z = Some ord2. 
  { rewrite /phi. by case: (disjoint3P z D) Pz. }
  exists phi => //. split. 
    + case. move => [|[|[|//]]] Hc; [exists x|exists y|exists z]; 
        rewrite ?phi_x ?phi_y ?phi_z;exact/eqP.
    + move => c u v. rewrite !inE => /eqP E1 /eqP E2; move: E1 E2. 
      rewrite {1 2}/phi. 
      case: (disjoint3P u D) => [Hu|Hu|Hu|? ? ?];
      case: (disjoint3P v D) => [Hv|Hv|Hv|? ? ?] // <- // _.      
      * move: (connected_path (p := p1) (ins Hu) (ins Hv)).
        apply: connect_mono. apply: restrict_mono => {u v Hu Hv} u.
        rewrite !inE /phi. by case: (disjoint3P u D).
      * move: (connected_path (p := p2') (ins Hu) (ins Hv)).
        apply: connect_mono. apply: restrict_mono => {u v Hu Hv} u.
        rewrite !inE /phi. by case: (disjoint3P u D).
      * move: (connected_path (p := pz) (ins Hu) (ins Hv)).
        apply: connect_mono. apply: restrict_mono => {u v Hu Hv} u.
        rewrite !inE /phi. by case: (disjoint3P u D).
    + move => c1 c2.
      wlog: c1 c2 / c1 < c2.
      { move => W. case: (ltngtP c1 c2) => [|A B|A B]; first exact: W.
        - case: (W _ _ A _) => [|y0 [x0] [? ? ?]]; first by rewrite sgP. 
          exists x0; exists y0. by rewrite sgP.
        - case/ord_inj : A => ?. subst. by rewrite sgP in B. }
      case: c1 => [[|[|[|//]]]]; case: c2 => [[|[|[|//]]]] //= Hc2 Hc1 _ _. 
      * exists n1. exists n1'. rewrite !inE n_edge. split => //.
        -- rewrite /phi. by case: (disjoint3P n1 D) (nodes_end p1). 
        -- rewrite /phi. by case: (disjoint3P n1' D) (nodes_start p2'). 
      * exists n1. exists z1. rewrite !inE sg_sym zn1. split => //.
        -- rewrite /phi. by case: (disjoint3P n1 D) (nodes_end p1). 
        -- rewrite /phi. by case: (disjoint3P z1 D) (nodes_start pz). 
      * exists n2. exists z2. rewrite !inE sg_sym zn2. split => //.
        -- rewrite /phi. by case: (disjoint3P n2 D) N2'.
        -- rewrite /phi. by case: (disjoint3P z2 D) (nodes_end pz). 
Qed.


Lemma K4_of_triangle (x y z : link_graph G) : 
  x -- y -> y -- z -> z -- x -> minor (add_node G [set x;y;z]) K4.
Proof.
  move => xy yz zx.
  (* Rewrite K4 to match the conclusion of the [minor_with] lemma. *)
  apply: (@minor_trans _ (add_node C3 setT)); last first.
    by apply: strict_is_minor; apply: iso_strict_minor; exact: add_node_complete.
  (* By [C3_of_triangle], there is a minor map [phi : G -> option C3]. *)
  case: (C3_of_triangle xy yz zx) => phi mm_phi [phi_x phi_y phi_z].
  (* Precomposing [phi] with [val] makes it a minor map from [induced _] to C3
   * so that it fits the premiss of [minor_with]. *)
  have := minor_map_comp (@minor_induced_add_node G [set x; y; z]) mm_phi.
  apply: (minor_with (i := None : add_node _ _)); first by rewrite !inE.
  move=> u _.
  (* Rewrite the conclusion of [C3_of_triangle] in a more uniform way. *)
  (* TODO? change the statement of that lemma? *)
  have : exists2 v, phi v = Some u & v \in [set x; y; z].
    case: u; case=> [| [| [| // ] ] ] lt3;
    [exists x | exists y | exists z];
    rewrite ?phi_x ?phi_y ?phi_z ?inE ?eqxx // /ord0 /ord1 /ord2;
    do 2 f_equal; exact: bool_irrelevance.
  (* The remaining side-condition of [minor_with] then follows. *)
  case=> v eq_v v_in3.
  have sv_in : Some v \in [set~ None] by rewrite !inE.
  exists (Sub (Some v) sv_in) => //.
  by rewrite -mem_preim /= eq_v.
Qed.

(** ** Collapsing Bags *)

Lemma collapse_bags (U : {set G}) u0' (inU : u0' \in U) :
  let T := U :|: ~: \bigcup_(x in U) bag U x in 
  let G' := sgraph.induced T in 
  exists phi : G -> G',
    [/\ total_minor_map phi,
     (forall u : G', val u \in T :\: U -> phi @^-1 u = [set val u]) &
     (forall u : G', val u \in U -> phi @^-1 u = bag U (val u))].
Proof.
  move => T G'.
  have inT0 : u0' \in T by rewrite !inE inU.
  pose u0 : G' := Sub u0' inT0.  
  pose phi u := if [pick x in U | u \in bag U x] is Some x 
                then insubd u0 x else insubd u0 u.
  exists phi.
  have phiU (u : G') : val u \in U -> phi @^-1 u = bag U (val u).
  { move => uU. apply/setP => z. rewrite !inE /phi.
    case: pickP => [x /andP [X1 X2]|H]. 
    - rewrite -val_eqE insubdK ?inE ?X1 //. apply/eqP/idP => [<-//|].
      apply: contraTeq => C. 
      suff S: [disjoint bag U x & bag U (val u)] by rewrite (disjointFr S).
      apply: bag_disj => //; exact: CP_extensive. 
    - move: (H (val u)). rewrite uU /= => ->. 
      have zU : z \notin U. { move: (H z). by rewrite bag_id andbT => ->. }
      have zT : z \in T.
      { rewrite !inE (negbTE zU) /=. apply/negP => /bigcupP [x xU xP].
        move: (H x). by rewrite xU xP. }
      rewrite -val_eqE insubdK //. by apply: contraNF zU => /eqP->. }
  have phiT (u : G') : val u \in T :\: U -> phi @^-1 u = [set val u].
  { move/setDP => [uT uU]. apply/setP => z. rewrite !inE /phi. 
    case: pickP => [x /andP [xU xP]|H]. 
    - rewrite -val_eqE insubdK ?inE ?xU // (_ : z == val u = false). 
      + by apply: contraNF uU => /eqP <-.
      + apply: contraTF uT => /eqP ?. subst. 
        rewrite inE (negbTE uU) /= inE negbK. by apply/bigcupP; exists x. 
    - have zU : z \notin U. { move: (H z). by rewrite bag_id andbT => ->. }
      have zT : z \in T.
      { rewrite !inE (negbTE zU) /=. apply/negP => /bigcupP [x xU xP].
        move: (H x). by rewrite xU xP. }
      by rewrite -val_eqE insubdK. }
  have preim_G' (u : G') : val u \in phi @^-1 u.
  { case: (boolP (val u \in U)) => H; first by rewrite phiU // bag_id. 
    rewrite phiT ?set11 // inE H. exact: valP. }
  split => //.
  - split. 
    + move => y. exists (val y). apply/eqP. case: (boolP (val y \in U)) => x_inU. 
      * by rewrite mem_preim phiU // bag_id. 
      * rewrite mem_preim phiT inE // x_inU. exact: valP.
    + move => y. case: (boolP (val y \in U)) => xU.
      * rewrite phiU //. apply: connected_bag => //. exact: CP_extensive.
      * rewrite phiT; first exact: connected1. rewrite inE xU. exact: valP.
    + move => x y xy. exists (val x); exists (val y). by rewrite !preim_G'. 
Qed.

End CheckpointsAndMinors.
Arguments collapse_bags [G] conn_G U u0' _.

(** Neighbor Tree Lemma *)

Definition neighbours (G : sgraph) (x : G) := [set y | x -- y].

Lemma CP_tree (G : sgraph) (U : {set G}) :
  connected [set: G] -> K4_free (add_node G U) -> is_tree (CP U).
Proof.
  set H := add_node G U.
  move => G_conn H_K4_free.
  apply: CP_treeI => // x y z x_cp y_cp z_cp xy yz zx.
  apply: H_K4_free.
  move: (CP_triangle_bags G_conn x_cp y_cp z_cp xy yz zx) =>
    [x'] [y'] [z'] [[x_inU y_inU z_inU] [xX' yY' zZ']].
  set U3 : {set G} := [set x; y; z] in xX' yY' zZ'.
  pose X := bag U3 x.
  pose Y := bag U3 y.
  pose Z := bag U3 z.
  have xX : x \in X by apply: (@bag_id G).
  have yY : y \in Y by apply: (@bag_id G).
  have zZ : z \in Z by apply: (@bag_id G).
  move def_T: (~: (X :|: Y :|: Z)) => T.
  pose T' : {set G} := U3 :|: T.
  pose G' := @sgraph.induced G T'.
  
  have xH' : x \in T' by rewrite !inE eqxx.
  have yH' : y \in T' by rewrite !inE eqxx.
  have zH' : z \in T' by rewrite !inE eqxx.

  have def_T' : T' = U3 :|: ~: (\bigcup_(v in U3) bag U3 v).
  { by rewrite {2}/U3 !bigcup_setU !bigcup_set1 /T' -def_T. }

  case: (collapse_bags _ U3 x _) => //.
  { by rewrite !inE eqxx. }
  rewrite -def_T' -/G' => phi [mm_phi P1 P2].

  have irred_inT u v (p : Path G u v) : 
      u \in T' -> v \in T' -> irred p -> {subset p <= T'}.
  { rewrite def_T'. exact: bags_in_out. }
 
  have G'_conn : forall x y : G', connect sedge x y. 
  { apply: connectedTE. apply: connected_induced. 
    move => u v Hu Hv. case/uPathP : (connectedTE G_conn u v) => p irr_p. 
    apply: (connectRI (p := p)). exact: irred_inT irr_p. }

  have cp_lift u v w : 
    w \in @cp G' u v -> val w \in @cp G (val u) (val v).
  { apply: contraTT => /cpPn' [p] /irred_inT. move/(_ (valP u) (valP v)).
    case/Path_to_induced => q eq_nodes.
    rewrite in_collective -eq_nodes (mem_map val_inj).
    exact: cpNI'. }

  pose x0 : G' := Sub x xH'.
  pose y0 : G' := Sub y yH'.
  pose z0 : G' := Sub z zH'.
  (* pose H' := @add_node G' [set x0;y0;z0]. *)

  have link_xy : @link_rel G' x0 y0.
  { rewrite /= -val_eqE (sg_edgeNeq xy) /=. apply/subsetP.
    move => w /cp_lift. case/andP : (xy) => _ /subsetP S /S. 
    by rewrite !inE !sub_val_eq. }
  have link_yz : @link_rel G' y0 z0.
  { rewrite /= -val_eqE (sg_edgeNeq yz) /=. apply/subsetP.
    move => w /cp_lift. case/andP : (yz) => _ /subsetP S /S. 
    by rewrite !inE !sub_val_eq. }
  have link_zx : @link_rel G' z0 x0.
  { rewrite /= -val_eqE (sg_edgeNeq zx) /=. apply/subsetP.
    move => w /cp_lift. case/andP : (zx) => _ /subsetP S /S. 
    by rewrite !inE !sub_val_eq. }

  apply: minor_trans (K4_of_triangle link_xy link_yz link_zx).
  idtac => {link_xy link_yz link_zx}.
  rewrite /H. apply: add_node_minor mm_phi.
  move => b. rewrite !inE -orbA. case/or3P => /eqP ?; subst b.
  - exists x' => //. apply/eqP. rewrite mem_preim P2 //. by rewrite !inE eqxx.
  - exists y' => //. apply/eqP. rewrite mem_preim P2 //. by rewrite !inE eqxx.
  - exists z' => //. apply/eqP. rewrite mem_preim P2 //. by rewrite !inE eqxx.  
Qed.

(** Proposition 21(ii) *)
Definition igraph (G : sgraph) (x y : G) : sgraph     := induced (interval  x y).
Definition istart (G : sgraph) (x y : G) : igraph x y := Sub  x  (intervalL x y).
Definition iend   (G : sgraph) (x y : G) : igraph x y := Sub  y  (intervalR x y).

Arguments add_edge : clear implicits.
Arguments igraph : clear implicits.
Arguments istart {G x y}.
Arguments iend {G x y}.

Lemma add_edge_swap (G : sgraph) (i o : G) :
  sg_iso (add_edge G i o) (add_edge G o i).
Proof.
  exists (id : add_edge G o i -> add_edge G i o) id;
    move=>//= x y /orP[->//|]/orP[]/andP[xNy]/andP[->->]/=;
    by rewrite [in _ && true]eq_sym xNy.
Qed.

(* TOTHINK: This lemma can have a more general statement.
 * add_edge preserves sg_iso when the nodes are applied to the actual iso. *)
Lemma add_edge_induced_iso (G : sgraph) (S T : {set G})
      (u v : induced S) (x y : induced T) :
  S = T -> val u = val x -> val v = val y ->
  sg_iso (add_edge (induced S) u v) (add_edge (induced T) x y).
Proof.
  move=> eq_ST eq_ux eq_vy.
  have SofT z : z \in T -> z \in S by rewrite eq_ST.
  have TofS z : z \in S -> z \in T by rewrite eq_ST.
  set g : induced T -> induced S := fun z => Sub (val z) (SofT (val z) (valP z)).
  set f : induced S -> induced T := fun z => Sub (val z) (TofS (val z) (valP z)).
  exists (g : add_edge _ x y -> add_edge _ u v) f; rewrite {}/f {}/g;
    [ move=> ?; exact: val_inj .. | | ]; move=> a b /=/orP[->//|];
    rewrite -!(inj_eq val_inj) /= eq_ux eq_vy =>/orP[]/andP[aNb]/andP[->->];
    by rewrite /= aNb.
Qed.

(** ** K4-freenes of Intervals *)

Lemma igraph_K4F (G : sgraph) (i o x y : G) :
  connected [set: G] -> 
  x \in cp i o -> y \in cp i o -> x != y ->
  K4_free (add_edge G i o) ->
  K4_free (add_edge (igraph G x y) istart iend).
Proof.
  set H := add_edge G i o.
  set I := add_edge _ _ _.
  move=> G_conn x_cpio y_cpio xNy; apply: minor_K4_free.
  have iNo : i != o.
  { apply: contra_neq xNy => x_y. move: x_cpio y_cpio.
    by rewrite -{}x_y cpxx !inE =>/eqP->/eqP->. }

  have conn_io : connect sedge i o := connectedTE G_conn i o.
  wlog x_le_y : x y @I x_cpio y_cpio xNy / cpo conn_io x y.
  { move=> Hyp. case/orP: (cpo_total conn_io x y); first exact: Hyp.
    move=> ?; suff : minor (add_edge (igraph G y x) istart iend) I.
    { by apply: minor_trans; apply: Hyp; rewrite // 1?sg_sym 1?eq_sym. }
    apply: strict_is_minor; apply: iso_strict_minor.
    apply: (@sg_iso_trans I (add_edge (igraph G x y) iend istart)).
      exact: add_edge_swap.
    by apply: add_edge_induced_iso; first exact: interval_sym. }

  pose U2 := [set x; y].
  (* As a consequence, i (resp. o) is the the bag of x (resp. y) with
   * respect to {x, y}. *)
  have [i_Px o_Py] : i \in bag U2 x /\ o \in bag U2 y.
  { split; apply/bagP=> z; rewrite CP_set2 (cpo_cp x_cpio y_cpio x_le_y);
    move=> /andP[z_cpio] /andP[x_le_z z_le_y].
    + rewrite (cpo_cp (mem_cpl i o) z_cpio);
      repeat (apply/andP; split) => //; exact: cpo_min.
    + have o_cpio : o \in cp i o by rewrite cp_sym mem_cpl.
      rewrite cp_sym (cpo_cp z_cpio o_cpio);
      repeat (apply/andP; split) => //; exact: cpo_max. }

  case: (collapse_bags G_conn U2 x _); first by rewrite !inE eqxx.
  set T := U2 :|: _. have {T}-> : T = interval x y.
  { rewrite {}/T {-3}/U2 /interval bigcup_setU !bigcup_set1.
    congr ([set x; y] :|: _).
    rewrite -setTD (sinterval_bag_cover G_conn xNy).
    rewrite setUAC setDUl setDv set0U; apply/setDidPl.
    rewrite disjoint_sym disjoints_subset subUset -!disjoints_subset.
    by rewrite {2}sinterval_sym !interval_bag_disj //;
    apply: CP_extensive; rewrite !inE eqxx. }
  rewrite -[induced _]/(igraph G x y). set Gxy := igraph G x y in I *.

  move=> phi [[phi_surj preim_phi_conn phi_edge] preim_phi preim_phixy].
  apply: strict_is_minor. exists phi; split; first exact: phi_surj.
  + move=> u; have u_I : val u \in interval x y := valP u.
    case: (boolP (val u \in U2)) => u_xy.
    - rewrite preim_phixy //. apply: add_edge_connected.
      apply: (@connected_bag G G_conn (val u) U2).
      exact: CP_extensive.
    - rewrite preim_phi; first exact: connected1.
      by rewrite inE u_xy u_I.
  + move=> u v /orP[].
    - move/phi_edge => [u'] [v'] [? ? uv'].
      by exists u'; exists v'; split; rewrite //= uv'.
    - wlog [-> -> _] : u v / u = istart /\ v = iend.
      { case/(_ istart iend); [ by split | by rewrite /= !eqxx xNy | ].
        move=> u' [v'] [? ? ?]. have ? : v' -- u' by rewrite sg_sym.
        case/orP=> /andP[_]/andP[/eqP->/eqP->];
          [ by exists u'; exists v' | by exists v'; exists u' ]. }
      rewrite 2?preim_phixy ?inE ?eqxx // ![val _]/=.
      by exists i; exists o; split; rewrite //= iNo !eqxx.
Qed.

Lemma igraph_K4F_add_node (G : sgraph) (U : {set G}) :
  connected [set: G] -> forall x y, x \in CP U -> y \in CP U -> x != y ->
  K4_free (add_node G U) -> K4_free (add_edge (igraph G x y) istart iend).
Proof.
  set H := add_node G U => G_conn x y x_cp y_cp xy H_K4F.
  set I := add_edge _ _ _.

  case: (CP_base x_cp y_cp) => [i] [o] [i_U o_U].
  rewrite subUset !sub1set =>/andP[x_cpio y_cpio].
  suff : K4_free (add_edge G i o) by exact: igraph_K4F => //.
  set K := add_edge G i o.
  apply: minor_K4_free H_K4F. apply: strict_is_minor.

  set phi : H -> K := odflt i.
  have preim_phi u :
    phi @^-1 u = Some u |: if u == i then [set None] else set0.
  { by apply/setP=> v; case: ifP => u_i; rewrite -mem_preim !inE ?orbF;
    case: v => [v|] //=; rewrite eq_sym. }
  have preim_phixx u : Some u \in phi @^-1 u by rewrite -mem_preim.

  exists phi; split.
  + by move=> /= u; exists (Some u).
  + move=> /= u; rewrite preim_phi.
    case: ifP => [/eqP{u}->|_]; first exact: connected2.
    by rewrite setU0; exact: connected1.
  + move=> u v /orP[]; first by [ exists (Some u); exists (Some v); split ].
    move=> /orP[]/andP[_]/andP[/eqP->/eqP->];
    [ exists None; exists (Some o) | exists (Some o); exists None ];
    by split; rewrite // -mem_preim.
Qed.

(** ** Parallel Split Lemma *)

(** TODO: This proof can likely be simplified (though it will surely remain one
of the longer proofs of the development *)

Lemma ssplit_K4_nontrivial (G : sgraph) (i o : G) : 
  ~~ i -- o -> link_rel G i o -> K4_free (add_edge G i o) -> 
  bag [set i;o] i = [set i] ->
  connected [set: G] -> disconnected (sinterval i o).
Proof.
  move => /= io1 /andP [io2 io3] K4F bag_i conn_G. 
  pose G' := @sgraph.induced G [set~ i].

  (* Ad-hoc versions of Path_to_induced/Path_from_induced. *)
  have from_base (x y : G') (p : Path G (val x) (val y)) :
    i \notin p -> exists p' : Path G' x y, nodes p = map val (nodes p').
  { move=> iNp. suff : {subset p <= [set~ i]}
      by case/Path_to_induced => p' <-; exists p'.
    by move=> z; rewrite !inE; apply: contraTneq =>->. }
  have into_base (x y : G') (p' : Path G' x y) :
    exists2 p : Path G (val x) (val y), i \notin p & nodes p = map val (nodes p').
  { case: (Path_from_induced p') => [p] iNp eq_p.
    exists p; by [apply/negP=>/iNp; rewrite !inE eqxx|]. }

  have [node_G' conn_G'] : prod G' (connected [set: G']).
  { have Ho : o \in [set~ i] by rewrite !inE eq_sym.
    pose o' : G' := Sub o Ho; split; first exact: o'.
    suff S: forall x, connect sedge x o'.
    { apply: connectedTI => x y.
      apply: (connect_trans (y := o')) => //.
      rewrite connect_symI //. exact: sg_sym. }
    move => x.
    suff /cpPn'[p _] : i \notin @cp G (val x) o.
    { case/(from_base x o') => p' _; exact: Path_connect. }
    (* if i were a checkpoint between x and o, then
        x would be in [bag [set i; o] i] - contradiction *)
    have : val x \in [set ~i] := valP x; rewrite inE -{4}bag_i.
    apply: contraNN => i_cpxo. apply/bagP.
    rewrite CP_clique; last by [apply: clique2; rewrite /= io2 io3].
    by move=> ?; rewrite !inE =>/orP[]/eqP->; rewrite // cp_sym mem_cpl. }

  set U := o |: neighbours i.
  set U' : {set G'} := [set insubd node_G' x | x in U].
  have eqi_U (z : G') : (z \in U') = (val z \in U).
  { apply/imsetP/idP.
    + case=> x x_U ->; rewrite insubdK //. move: x_U; rewrite !inE.
      apply: contraTneq =>->; by rewrite negb_or io2 sgP.
    + by move=> z_U; exists (val z); last rewrite valKd. }

  have tree_CPU' : is_tree (CP U').
  { apply: CP_tree conn_G' _. apply: subgraph_K4_free K4F.
    exists (fun z => if z is Some x then val x else i).
    + case=> [x|] [y|] //; first by move=> /val_inj->.
      - move=> xy. by move: (valP x); rewrite !inE  xy eqxx.
      - move=> xy. by move: (valP y); rewrite !inE -xy eqxx.
    + suff Hyp (z : G') : z \in U' -> (i : add_edge G i o) -- val z.
      { case=> [x|] [y|] // H _ ; move: H;
        first by [move=>/=->]; by move=>/Hyp; first rewrite sg_sym. }
      rewrite eqi_U !inE /= =>/orP[/eqP->|->//].
      by rewrite io2 !eqxx. }

  have U_to_CP (x : G) : x \in U -> exists x'' : CP_ U', x = val (val x'').
  { move=> x_U. have xNi : x \in [set~ i].
    { move: x_U; rewrite !inE. apply: contraTneq =>->. by rewrite sg_irrefl. }
    set x' : G' := Sub x xNi.
    suff x_CPU' : x' \in CP U' by exists (Sub x' x_CPU').
    by apply: CP_extensive; rewrite eqi_U. }

  have /U_to_CP[o'' eq_o''] : o \in U by rewrite !inE eqxx.
  pose N := neighbours o''.
  have Ngt1: 1 < #|N|.
  { suff: 0 < #|N| /\ #|N| != 1. 
    { case: (#|N|) => [|[|]] //; rewrite ?ltnn ?eqxx; by case. }
    split. 
    - apply/card_gt0P.
      (* i must have a neighbor (that is not o) and CP(U') is connected *)
      case: (connected_card_gt1 conn_G _ _ io2) => // j _ ij.
      have /U_to_CP[j'' eq_j''] : j \in U by rewrite !inE ij.
      have conn_CPU' : connected [set: CP_ U'] by apply: CP_connected.
      have : o != j by apply: contraNneq io1 =>->.
      rewrite eq_o'' eq_j'' !(inj_eq val_inj).
      case/(connected_card_gt1 conn_CPU') => // x _ ox.
      by exists x; rewrite !inE.
    - apply/negP. case/cards1P => n E.
      have : n \in N by rewrite E inE eqxx. rewrite /N inE => on.
      have {E} n_uniq (z : CP_ U') : z -- o'' -> z = n.
      { move=> zo; have : z \in N by rewrite /N inE sg_sym.
        by rewrite E inE => /eqP. }
      (* for every neighbor z of i, [n \in cp z o].
         hence [n \in cp i o] (and different from both). Contradiction. *)
      suff : (val (val n) : G) \in cp i o.
      { move: io3 => /subsetP io3 /io3. rewrite !inE =>/orP[]; apply/negP.
        * by have := valP (val n); rewrite !inE.
        * rewrite eq_o'' !(inj_eq val_inj).
          by apply: contraTN on => /eqP<-; rewrite sg_irrefl. }
      apply: cp_neighbours => // z iz.
      (* By [cpPn'], take an irredundant [p : Path G z o] and show that [n ∈ p].
       * W.l.o.g. [i ∉ p] by cutting [p] at the unique occurence of [i]. *)
      apply/cpPn' => -[p] Ip; apply/negP; rewrite negbK.
      wlog iNp : z iz p Ip / i \notin p.
      { move=> Hyp. case: (boolP (i \in p)); last exact: Hyp.
        case/(isplitP Ip) => p1 p2 _ Ip2 _.
        rewrite mem_pcat; apply/orP; right; clear p1.
        case: (splitL p2 io2) Ip2 => [z'] [iz'] [p'] [-> _].
        rewrite irred_cat => /andP[_]/andP[Ip' disj'].
        rewrite mem_pcat; apply/orP; right; apply: Hyp => //.
        rewrite in_collective nodesE inE sg_edgeNeq //=.
        by rewrite (disjointFr disj') // nodes_start. }
      (* Using [from_base] (i.e. [Path_to_induced]), [p] lifts to G'. *)
      move: p Ip iNp. rewrite eq_o''.
      have /U_to_CP[z'' eq_z''] : z \in U by rewrite !inE iz.
      rewrite eq_z'' => p Ip /from_base[p' eq_p'].
      suff : val n \in p' by move=> /(map_f val); rewrite -eq_p'.
      have {p Ip eq_p'} Ip' : irred p'.
      { move: Ip; rewrite !irredE -!nodesE eq_p'. exact: map_uniq. }
      (* It then restricts to [q : Path (CP_ U') z o] which must have [n] as
       * its penultimate node. Thus [n ∈ q ⊆ p]. *)
      case: (CP_path conn_G' Ip') => q _ /subsetP. apply. apply: mem_imset.
      have : z != o by apply: contraTneq iz =>->.
      rewrite eq_o'' eq_z'' !(inj_eq val_inj).
      case/(splitR q) => z1 [q'] [z1o] eq_q.
      have {q' eq_q} : z1 \in q by rewrite eq_q mem_pcat nodes_end.
      by rewrite (n_uniq z1).
  }

  have CPU_sinterval (z : CP_ U') : o'' != z -> val (val z) \in sinterval i o.
  { have : val z \in CP U' := valP z.
    case/bigcupP => -[j0 j1]/= /setXP[]. rewrite !eqi_U => j0U j1U.
    wlog ij1 : j0 j1 j0U {j1U} / (val j1 : G) -- i.
    { move=> Hyp. move: j1U; rewrite 3!inE sg_sym.
      case/orP => [/eqP eq_j1|]; last exact: Hyp.
      move: j0U; rewrite 3!inE; case/orP => [/eqP eq_j0|].
      + move: eq_j0 eq_j1. rewrite {1 2}eq_o'' =>/val_inj->/val_inj->.
        by rewrite cpxx inE =>/eqP/val_inj->; rewrite eqxx.
      + by rewrite cp_sym sg_sym; apply: (Hyp j1 j0); rewrite eq_j1 2!inE eqxx.
    }
    case/uPathP: (connectedTE conn_G' j0 j1) => p' Ip'.
    move=> /(@cpP' G')/(_ p') z_p' zNo.
    set x := val (val z) : G. have {zNo} xNo : x != o.
    { by apply: contraNN zNo; rewrite eq_o'' !(inj_eq val_inj) eq_sym. }
    have {j0 j1 p' j0U ij1 Ip' z_p'} [j [p] [j_U Ip x_p]] :
      exists j (p : Path G j i), [/\ j \in U, irred p & x \in p].
    { case: (into_base _ _ p') => p iNp eq_p.
      exists (val j0); exists (pcat p (edgep ij1)); split; first exact: j0U.
      + move: Ip'; rewrite irred_cat irred_edge !irredE -!nodesE.
        rewrite eq_p map_inj_uniq =>[->/=|]; last exact: val_inj.
        rewrite /tail/= disjoint_sym disjoint_has; apply/hasPn=> ?.
        by rewrite /= inE => /eqP->.
      + by move: z_p'; rewrite /x mem_pcat 2!in_collective eq_p =>/map_f->. }
    apply/sintervalP2; split; last first.
    { case/uPathP: (connectedTE conn_G' (val z) (val o'')) => q' Iq'.
      case: (into_base _ _ q'); rewrite -eq_o'' => q iNq eq_q.
      exists q => //. move: Iq'; rewrite !irredE -!nodesE eq_q.
      rewrite map_inj_uniq //; exact: val_inj. }
    case: (isplitP Ip x_p) => {p Ip x_p} p1 p2 Ip1 Ip2 disj.
    case: (boolP (o \in p2)) =>[|?]; last by exists p2.
    rewrite in_collective nodesE inE eq_sym (negbTE xNo) /= -[pval]/tail.
    move=> /(disjointFl disj).
    move: j_U; rewrite !inE; case/orP =>[/eqP<-|]; first by rewrite nodes_start.
    rewrite sg_sym => ij /negbT oNp1. exists (pcat (prev p1) (edgep ij)).
    + rewrite irred_cat irred_edge prev_irred /tail //=.
      rewrite disjoint_sym (@eq_disjoint1 G i); last by move=> ?; rewrite !inE.
      rewrite mem_prev (disjointFl disj) // in_tail ?nodes_end //.
      by have : x \in [set~ i] := valP (val z); rewrite 2!inE eq_sym.
    + by rewrite mem_pcatT mem_prev negb_or oNp1 /tail/= inE eq_sym.
  }

  case/card_gt1P : Ngt1 => [x] [y]. rewrite !inE {N}. case=> ox oy xNy.
  (* TOTHINK: can we avoid nested vals using a proper lemma? *)
  exists (val (val x)). exists (val (val y)).
  split; last 1 [idtac] || by apply: CPU_sinterval; rewrite sg_edgeNeq.
  (* o, which is not in ]]i;o[[, is a checkpoint beween x and y *)
  apply/uPathRP => // -[p] Ip /subsetP p_io.
  have /from_base[p' eq_p'] : i \notin p.
  { by apply/negP => /p_io; rewrite sinterval_bounds. }
  pose q' := pcat (prev (edgep ox)) (edgep oy). have Iq' : irred q'.
  { by rewrite irredE/= !inE negb_or xNy eq_sym (sg_edgeNeq ox) (sg_edgeNeq oy). }
  have : o'' \in q' by rewrite mem_pcat mem_prev !nodes_start.
  move=>/(CP_tree_paths conn_G' _ tree_CPU' Iq')/(@cpP' G')/(_ p')/(map_f val).
  by rewrite -eq_p' -eq_o'' =>/p_io; rewrite sinterval_bounds.
Qed.
