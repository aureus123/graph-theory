Require Import RelationClasses.

From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries sgraph minor checkpoint.
Require Import multigraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.
Set Bullet Behavior "Strict Subproofs". 

(** * Skeletons *)

Definition sk_rel (G : graph) : rel G := 
  sc [rel x y | (x != y) && [exists e, (source e == x) && (target e == y)]].

Arguments sk_rel G _ _ : clear implicits.

Lemma sk_rel_sym (G : graph) : symmetric (sk_rel G).
Proof. move => x y. by rewrite /sk_rel /sc /= orbC. Qed.

Lemma sk_rel_irrefl (G : graph) : irreflexive (sk_rel G).
Proof. move => x. by rewrite /sk_rel /sc /= !eqxx. Qed.

Definition skeleton (G : graph) := 
  SGraph (@sk_rel_sym G) (@sk_rel_irrefl G).

Lemma skelP (G : graph) (P : G -> G -> Prop) : 
  Symmetric P -> 
  (forall e : edge G, P (source e) (target e)) -> 
  (forall x y : G,  sk_rel _ x y -> P x y).
Proof. 
  move => S H x y. 
  case/orP => /= /andP [_] /existsP [e] /andP [/eqP<- /eqP <-] //.
  exact: S.
Qed.

Definition ssk_rel (G : graph2) := 
  relU (sk_rel G) (sc [rel x y | [&& x != y, x == g_in & y == g_out]]).

Definition add_edge_rel (G:sgraph) (i o : G) := 
  relU (@sedge G) (sc [rel x y | [&& x != y, x == i & y == o]]).

Lemma add_edge_sym (G:sgraph) (i o : G) : symmetric (add_edge_rel i o).
Proof. apply: relU_sym'. exact: sg_sym. exact: sc_sym. Qed.

Lemma add_edge_irrefl (G:sgraph) (i o : G) : irreflexive (add_edge_rel i o).
Proof. move => x /=. by rewrite sg_irrefl eqxx. Qed.

Definition add_edge (G:sgraph) (i o : G) :=
  {| svertex := G;
     sedge := add_edge_rel i o;
     sg_sym := add_edge_sym i o;
     sg_irrefl := add_edge_irrefl i o |}.

Lemma add_edge_Path (G : sgraph) (i o x y : G) (p : @Path G x y) :
  exists q : @Path (add_edge i o) x y, nodes q = nodes p.
Proof.
  case: p => p p_pth.
  have p_iopth : @spath (add_edge i o) x y p.
  { case/andP: p_pth => p_path p_last. apply/andP; split=> //.
    apply: sub_path p_path. by move=> u v /=->. }
  by exists (Sub (p : seq (add_edge i o)) p_iopth).
Qed.

Lemma add_edge_connected (G : sgraph) (i o : G) (U : {set G}) :
  @connected G U -> @connected (add_edge i o) U.
Proof.
  move=> U_conn x y x_U y_U; move/(_ x y x_U y_U): U_conn.
  case: (boolP (x == y :> G)); first by move=>/eqP-> _; rewrite connect0.
  move=> xNy /(uPathRP xNy)[p _ /subsetP pU].
  case: (add_edge_Path i o p) => [q eq_q].
  apply: (@connectRI _ _ x y q) => z.
  rewrite in_collective eq_q; exact: pU.
Qed.

Definition sskeleton (G : graph2) := @add_edge (skeleton G) g_in g_out.

(* Lemma ssk_sym (G : graph2) : symmetric (ssk_rel G). *)
(* Proof. apply: relU_sym' (@sk_rel_sym _) _. exact: sc_sym. Qed. *)

(* Lemma ssk_irrefl (G : graph2) : irreflexive (ssk_rel G). *)
(* Proof. move => x /=. by rewrite sk_rel_irrefl eqxx. Qed. *)

(* Definition sskeleton (G : graph2) := SGraph (@ssk_sym G) (@ssk_irrefl G). *)

Lemma sskelP (G : graph2) (P : G -> G -> Prop) : 
  Symmetric P -> 
  (forall e : edge G, P (source e) (target e)) -> 
  (g_in != g_out :> G -> P g_in g_out) ->
  (forall x y : sskeleton G, x -- y -> P x y).
Proof. 
  move => S H IO x y. case/orP. exact: skelP. 
  case/orP => /= /and3P [A /eqP ? /eqP ?];subst; first exact: IO.
  apply: S. exact: IO.
Qed.


Lemma skel_sub (G : graph2) : sgraph.subgraph (skeleton G) (sskeleton G).
Proof.
  (* Note: This is really obsucre due to the abbiguity of [x -- y] *)
  exists id => //= x y H. right. exact: subrelUl. 
Qed.

(** Bridging Lemmas *)

Definition edges (G : graph) (x y : G) := 
  [set e : edge G | (source e == x) && (target e == y)].

Lemma edge_in_set (G : graph) e (A : {set G})  x y : 
  x \in A -> y \in A -> e \in edges x y -> e \in edge_set A.
Proof. move => Hx Hy. rewrite !inE => /andP[/eqP->/eqP->]. by rewrite Hx. Qed.

Definition adjacent (G : graph) (x y : G) := 
  [exists e, e \in edges x y] || [exists e, e \in edges y x].

Lemma adjacent_induced (G : graph) (x y : G) (V : {set G}) 
  (Hx : x \in V) (Hy : y \in V) : 
  adjacent x y -> @adjacent (induced V) (Sub x Hx) (Sub y Hy).
Proof.
  case/orP => /existsP [e He]. 
  all: have He': e \in edge_set V by exact: edge_in_set He.
  - apply/orP; left; apply/existsP. exists (Sub e He'). 
    rewrite inE -!val_eqE /=. by rewrite inE in He.
  - apply/orP; right; apply/existsP. exists (Sub e He'). 
    rewrite inE -!val_eqE /=. by rewrite inE in He.
Qed.

Lemma adjacentE (G : graph) (x y : skeleton G) : 
  (x != y) && adjacent x y = x -- y.
Proof.
  apply/andP/idP.
  - move=> /= [Hxy]. rewrite /sk_rel /= Hxy eq_sym Hxy /= /adjacent.
    case/orP => /existsP[e]; rewrite inE => ?; apply/orP; [left|right];
    by apply/existsP; exists e.
  - move=> xy; split; first by rewrite sg_edgeNeq.
    move: xy; rewrite /=/sk_rel/adjacent/=.
    case/orP=> /andP[_] /existsP[e He]; apply/orP; [left|right];
    by apply/existsP; exists e; rewrite inE.
Qed.

(* TODO: simplify edge_set, edges, adjacent, ... *)
Lemma edge_set_adj (G : graph2) : 
  @edge_set G [set g_in; g_out] == set0 -> ~~ @adjacent G g_in g_out. 
Proof. 
  apply: contraTN => /orP[] /existsP [e He]. 
  all: rewrite !inE in He; case/andP: He => He1 He2. 
  all: apply/set0Pn; exists e; by rewrite !inE ?He1 ?He2. 
Qed.

Lemma edge_set1 (G : graph) (x : G) : edge_set [set x] = edges x x.
Proof. apply/setP=> e. by rewrite !inE. Qed.

Lemma sskeleton_subgraph_for (G : graph2) (V : {set G}) (E : {set edge G})
  (con : consistent V E) (i o : sig [eta mem V]) : val i = g_in -> val o = g_out ->
  sgraph.subgraph (sskeleton (point (subgraph_for con) i o)) (sskeleton G).
Proof.
  rewrite /sskeleton/= => <- <-.
  (* TODO: Factor out some lemma about [add_edge] and [sgraph.subgraph]. *)
  exists val; first exact: val_inj.
  move=> x y /=; rewrite -!(inj_eq val_inj) /=.
  case/or3P=> [xy|->|->]; right=> //. apply/orP; left.
  move: xy; rewrite /sk_rel/= -!(inj_eq val_inj).
  case/orP=> /andP[->] /= /existsP[e];
  rewrite -!(inj_eq val_inj) /= => He; apply/orP; [left|right];
  apply/existsP; by exists (val e).
Qed.

Lemma sskeleton_adjacent (G : graph) (i o : G) :
  adjacent i o -> sg_iso (skeleton G) (sskeleton (point G i o)).
Proof.
  move=> Aio. pose id_G := id : vertex G -> vertex G.
  exists id_G id_G => // x y; last by move=> /= ->.
  case/or3P=> [->//||] /and3P[xNy /eqP Ei /eqP Eo] //.
  all: rewrite Ei Eo /id_G/= ?[sk_rel G o i]sk_rel_sym ?[o == i]eq_sym in xNy *.
  all: by rewrite -[sk_rel _ _ _]adjacentE xNy Aio.
Qed.



(** ** Intervals and Petals *)

(** TOTHINK: define intervals and petals on graph or sgraph, i.e.,
where to add theskeleton casts? *)

Fact intervalL (G : sgraph) (x y : G) : 
  x \in interval x y.
Proof. by rewrite !inE eqxx. Qed.

Fact intervalR (G : sgraph) (x y : G) : 
  y \in interval x y.
Proof. by rewrite !inE eqxx !orbT. Qed.

Definition remove_edges (G : graph) (E : {set edge G}) := 
  {| vertex := G;
     edge := [finType of { e : edge G | e \notin E }];
     source e := source (val e);
     target e := target (val e);
     label e := label (val e) |}.

Lemma remove_loops (G : graph) (E : {set edge G}) :
  {in E, forall e, source e = target e} ->
  sg_iso (skeleton G) (skeleton (remove_edges E)).
Proof.
  move=> Eloops. pose id_G := id : vertex G -> vertex G.
  have {Eloops} Nloops x y : x != y ->
      [exists e, e \in @edges G x y] = [exists e, e \in @edges (remove_edges E) x y].
  { move=> xNy. apply/existsP/existsP; case=> e; rewrite inE;
    case/andP=> /eqP Hsrc /eqP Htgt.
    - have He : e \notin E by apply: contraNN xNy =>/Eloops He; rewrite -Hsrc -Htgt He.
      exists (Sub e He). by rewrite inE /= Hsrc Htgt !eqxx.
    - exists (val e). by rewrite inE -Hsrc -Htgt !eqxx. }
  exists id_G id_G => // x y; rewrite /id_G -!adjacentE.
  all: case/andP=> xNy; by rewrite xNy /adjacent/= -!Nloops // eq_sym.
Qed.

Lemma remove_edges_connected (G : graph) (E : {set edge G}) :
  {in E, forall e : edge G, connect (sk_rel (remove_edges E)) (source e) (target e)} ->
  connected [set: skeleton G] -> connected [set: skeleton (remove_edges E)].
Proof.
  move=> E_conn G_conn. apply: connectedTI => x y. have := connectedTE G_conn x y.
  apply: connect_sub x y => /= x y. rewrite -[sk_rel _ _ _]adjacentE.
  case/andP=> xNy adj_xy.
  have [e] : exists e, e \in edges x y :|: edges y x.
  { case/orP: adj_xy => /existsP[e]; rewrite inE => /andP[/eqP Hsrc /eqP Htgt].
    all: by exists e; rewrite !inE ?Hsrc ?Htgt !eqxx. }
  rewrite !inE => e_xy. case: (boolP (e \in E)) => [/E_conn|He].
  - case/orP: e_xy => /andP[/eqP-> /eqP->] //. rewrite connect_symI //.
    exact: sk_rel_sym.
  - apply: connect1. rewrite -[sk_rel _ _ _]adjacentE xNy /=.
    case/orP: e_xy => /andP[/eqP<- /eqP<-]; apply/orP; [left|right].
    all: by apply/existsP; exists (Sub e He); rewrite !inE !eqxx.
Qed.

Lemma remove_edges_cross (G : graph) (V : {set G}) (E : {set edge G}) (x y : G) :
  E \subset edge_set V -> sk_rel G x y -> y \notin V -> sk_rel (remove_edges E) x y.
Proof.
  move=> E_subV xy yNV. move: xy. rewrite -![sk_rel _ _ _]adjacentE.
  case/andP=> xNy. rewrite xNy /= => adj_xy.
  have [e] : exists e, e \in edges x y :|: edges y x.
  { case/orP: adj_xy => /existsP[e]; rewrite inE => /andP[/eqP Hsrc /eqP Htgt].
    all: by exists e; rewrite !inE ?Hsrc ?Htgt !eqxx. }
  rewrite !inE => e_xy. case: (boolP (e \in E)) => He; last first.
  - case/orP: e_xy => /andP[/eqP<- /eqP<-]; apply/orP; [left|right].
    all: apply/existsP; exists (Sub e He); by rewrite !inE !eqxx.
  - move: He => /(subsetP E_subV). rewrite inE.
    by case/orP: e_xy => /andP[/eqP-> /eqP->]; rewrite (negbTE yNV) ?andbF.
Qed.

Lemma remove_edges_restrict (G : graph) (V : {set G}) (E : {set edge G}) (x y : G) :
  E \subset edge_set V -> connect (restrict (mem (~: V)) (sk_rel G)) x y ->
  connect (sk_rel (remove_edges E)) x y.
Proof.
  move=> E_subV. apply: connect_mono x y => x y /=. rewrite !inE -andbA.
  case/and3P=> xNV yNV xy. exact: remove_edges_cross xy yNV.
Qed.

Lemma sskeleton_remove_io (G : graph2) (E : {set edge G}) :
  E \subset @edge_set G [set g_in; g_out] ->
  sg_iso (sskeleton (point (remove_edges E) g_in g_out)) (sskeleton G).
Proof.
  move=> E_subIO. pose id_G := id : vertex G -> vertex G.
  exists id_G id_G => //= x y; rewrite {}/id_G.
  - suff H: sk_rel G x y -> @sedge (sskeleton (point (remove_edges E) g_in g_out)) x y.
      by case/or3P=> [/H|->|->].
    rewrite /= -![sk_rel _ _ _]adjacentE [y == x]eq_sym.
    case/andP=> xNy. rewrite xNy /= => adj_xy.
    have [e] : exists e, e \in edges x y :|: edges y x.
    { case/orP: adj_xy => /existsP[e]; rewrite inE => /andP[/eqP Hsrc /eqP Htgt].
      all: by exists e; rewrite !inE ?Hsrc ?Htgt !eqxx. }
    rewrite !inE => He. case: (boolP (e \in E)) => Ee; last first.
    + apply/orP; left. case/orP: He => /andP[/eqP<- /eqP<-]; apply/orP; [left|right].
      all: apply/existsP; exists (Sub e Ee); by rewrite !inE !eqxx.
    + move: Ee => /(subsetP E_subIO). rewrite !inE => /andP[Hsrc Htgt].
      apply/orP; right. case/orP: He xNy => /andP[/eqP<- /eqP<-].
      all: case/orP: Hsrc => /eqP->; rewrite eqxx ?andbT.
      all: by case/orP: Htgt => /eqP->; rewrite eqxx ?andbT.
  - case/or3P=> [xy|->//|->//]. apply/orP; left. move: xy.
    rewrite -![sk_rel _ _ _]adjacentE => /andP[xNy]; rewrite xNy /=.
    case/orP=> /existsP[e He]; apply/orP; [left|right]; apply/existsP; exists (val e).
    all: by move: He; rewrite !inE.
Qed.

Coercion skeleton : graph >-> sgraph.

Definition interval_edges (G : graph) (x y : G) :=
  edge_set (@interval G x y) :\: (edges x x :|: edges y y).

Lemma interval_edges_sym (G : graph) (x y : G) :
  interval_edges x y = interval_edges y x.
Proof. by rewrite /interval_edges interval_sym setUC. Qed.

Lemma igraph_proof (G : graph) (x y : skeleton G) :
  consistent (interval x y) (interval_edges x y).
Proof. move=> e. rewrite inE =>/andP[_]. by rewrite inE =>/andP. Qed.

Definition igraph (G : graph) (x y : skeleton G) :=
  @point (subgraph_for (@igraph_proof G x y))
         (Sub x (intervalL x y))
         (Sub y (intervalR x y)).

Definition pgraph (G : graph) (U : {set G}) (x:G) :=
  @point (induced (@petal (skeleton G) U x))
         (Sub x (@petal_id (skeleton G) U x))
         (Sub x (@petal_id (skeleton G) U x)).

Lemma pgraph_eq_io (G : graph) (U : {set G}) (x : G) : g_in = g_out :> @pgraph G U x.
Proof. by []. Qed.

Lemma interval_petal_edges_disj (G : graph) (U : {set G}) (x y : G) :
  connected [set: skeleton G] -> x \in @CP G U -> y \in @CP G U ->
  [disjoint edge_set (@petal G U x) & @interval_edges G x y].
Proof.
  move=> G_conn x_cp y_cp. rewrite -setI_eq0 -subset0. apply/subsetP => e.
  rewrite 3!inE => /and3P[]/andP[src_p tgt_p].
  rewrite 4!inE ![_ \in @interval G _ _]inE (lock sinterval) !inE -lock.
  rewrite negb_or !negb_and -!orbA => /andP[eNx eNy].
  case/andP=> /or3P[src_x|src_y|src_sI] /or3P[tgt_x|tgt_y|tgt_sI].
  all: move: eNx eNy; rewrite ?src_x ?src_y ?tgt_x ?tgt_y ?orbF //= => eNx eNy.
  - move: eNx. by rewrite (eqP tgt_y) -(@petal_cp G _ U) // -(eqP tgt_y) tgt_p.
  - by case: (disjointE (@interval_petal_disj G U x y y_cp) tgt_p tgt_sI).
  - move: eNx. by rewrite (eqP src_y) -(@petal_cp G _ U) // -(eqP src_y) src_p.
  - by case: (disjointE (@interval_petal_disj G U x y y_cp) tgt_p tgt_sI).
  - by case: (disjointE (@interval_petal_disj G U x y y_cp) src_p src_sI).
  - by case: (disjointE (@interval_petal_disj G U x y y_cp) src_p src_sI).
  - by case: (disjointE (@interval_petal_disj G U x y y_cp) src_p src_sI).
Qed.

Lemma petal_edges_disj (G : graph) (U : {set G}) (x y : G) :
  connected [set: skeleton G] -> x \in @CP G U -> y \in @CP G U -> x != y ->
  [disjoint edge_set (@petal G U x) & edge_set (@petal G U y)].
Proof.
  move=> G_conn x_cp y_cp xNy. rewrite -setI_eq0 -subset0. apply/subsetP => e.
  rewrite 3!inE. case/andP=> /andP[src_x tgt_x] /andP[src_y tgt_y].
  by case: (disjointE (@petal_disj G _ U x y _ _ _) src_x src_y).
Qed.

Lemma interval_edges_disj_cp (G : graph) (x y z : G) :
  z \in @cp G x y -> [disjoint interval_edges x z & interval_edges z y].
Proof.
  move=> z_cpxy. rewrite -setI_eq0 -subset0. apply/subsetP => e.
  rewrite 6!inE negb_or !negb_and. case/andP=> /and3P[_ src_Ixz tgt_Ixz].
  rewrite 5!inE negb_or !negb_and. case/and3P=> /andP[e_z _] src_Izy tgt_Izy.
  move: e_z.
  have : source e \in [set z] by rewrite -(intervalI_cp z_cpxy) inE src_Ixz src_Izy.
  rewrite inE =>->/=.
  have : target e \in [set z] by rewrite -(intervalI_cp z_cpxy) inE tgt_Ixz tgt_Izy.
  by rewrite inE =>->.
Qed.

Lemma interval_petal_edge_cover (G : graph) (x y : G) :
  connected [set: skeleton G] -> x != y ->
  [set: edge G] = edge_set (@petal G [set x; y] x) :|: @interval_edges G x y
                    :|: edge_set (@petal G [set x; y] y).
Proof.
  move=> G_conn xNy. apply/eqP. rewrite eq_sym -subTset. apply/subsetP=> e _.
  move: (sinterval_petal_cover G_conn xNy) => compU.
  have : target e \in [set: G] by []. have : source e \in [set: G] by [].
  rewrite !{}compU !in_setU -!orbA.
  case: (boolP (source e \in @sinterval G x y)) => [Hsrc _|Nsrc /= Hsrc].
  + case: (boolP (target e \in @sinterval G x y)) => [Htgt _|Ntgt /= Htgt].
    { rewrite ![e \in _]inE ![_ \in @interval G _ _]inE Hsrc Htgt.
      rewrite !orbT negb_or !negb_and. move: Hsrc.
      by rewrite 5!inE negb_or => /andP[]/andP[->->]. }
    wlog Htgt : x y xNy Hsrc Ntgt {Htgt} / target e \in @petal G [set x; y] x.
    { move=> Hyp. case/orP: Htgt; first exact: Hyp.
      rewrite setUC orbC orbAC orbC interval_edges_sym.
      apply: Hyp; rewrite 1?sinterval_sym //. by rewrite eq_sym. }
    have Nsrc : source e \notin @petal G [set x; y] x.
    { rewrite (disjointFl (@interval_petal_disj G _ x y _) Hsrc) //.
      apply: CP_extensive. by rewrite !inE eqxx. }
    have src_tgt : @sedge G (target e) (source e).
    { apply/orP; right. apply/andP. split; first by apply: contraNneq Ntgt =><-.
      apply/'exists_andP. by exists e; split. }
    have : target e = x := petal_exit_edge G_conn _ Htgt Nsrc src_tgt.
    move/(_ (CP_extensive _)). rewrite 3!inE eqxx => /(_ _)/Wrap[]// tgt_x.
    rewrite ![e \in _]inE tgt_x (@intervalL G) [_ \in @interval G _ _]inE Hsrc.
    rewrite orbT !andbT negb_or !negb_and.
    suff [->->] : source e != x /\ source e != y by [].
    by split; apply: contraTneq Hsrc =>->; rewrite (@sinterval_bounds G).
  + wlog Hsrc : x y xNy {Nsrc Hsrc} / source e \in @petal G [set x; y] x.
    { move=> Hyp. case/orP: Hsrc; first exact: Hyp.
      rewrite setUC sinterval_sym interval_edges_sym orbC orbAC orbC.
      rewrite [(e \in _) || _]orbC orbAC [_ || (e \in _)]orbC.
      by apply: Hyp; rewrite eq_sym. }
    case: (boolP (target e \in @petal G [set x; y] x)) => Ntgt /=.
      by rewrite [e \in _]inE Hsrc Ntgt.
    have src_tgt : @sedge G (source e) (target e).
    { apply/orP; left. apply/andP. split; first by apply: contraNneq Ntgt =><-.
      apply/'exists_andP. by exists e; split. }
    have : source e = x := petal_exit_edge G_conn _ Hsrc Ntgt src_tgt.
    move/(_ (CP_extensive _)). rewrite 3!inE eqxx => /(_ _)/Wrap[]// src_x.
    case/orP=> Htgt.
    * rewrite ![e \in _]inE src_x (@intervalL G) (negbTE xNy) orbF eqxx/=.
      have -> : target e != x.
      { apply: contraTneq Htgt =>->. by rewrite (@sinterval_bounds G). }
      by have -> : target e \in @interval G x y by rewrite inE Htgt.
    * have Nsrc : source e \notin @petal G [set x; y] y.
      { have yNx : y != x by rewrite eq_sym.
        rewrite (disjointFl (petal_disj G_conn _ _ yNx) Hsrc) //;
        by apply: CP_extensive; rewrite !inE eqxx. }
      have := petal_exit_edge G_conn (CP_extensive _) Htgt Nsrc _.
      rewrite sg_sym 3!inE eqxx => /(_ _ src_tgt)/Wrap[]// tgt_y.
      rewrite ![e \in _]inE src_x tgt_y (@intervalL G) (@intervalR G).
      by rewrite !eqxx eq_sym (negbTE xNy).
Qed.

Lemma interval_cp_edge_cover (G : graph) (x y z : G) :
  connected [set: skeleton G] -> z \in @cp G x y :\: [set x; y] ->
  @interval_edges G x y = @interval_edges G x z :|: edge_set (@petal G [set x; y] z)
                            :|: @interval_edges G z y.
Proof.
  move=> G_conn zPcpxy.
  have z_cpxy : z \in @cp G x y by move: z zPcpxy; apply/subsetP; exact: subsetDl.
  have z_cp : z \in @CP G [set x; y].
  { apply/bigcupP; exists (x, y); by [rewrite in_setX !in_set2 !eqxx |]. }
  have [x_cp y_cp] : x \in @CP G [set x; y] /\ y \in @CP G [set x; y]
    by split; apply: CP_extensive; rewrite !inE eqxx.
  apply/eqP. rewrite eqEsubset andbC !subUset [(_ \subset _) && _ && _]andbAC.
  apply/andP; split; first (apply/andP; split).
  - wlog suff : x y z zPcpxy {z_cpxy x_cp y_cp z_cp} /
                  interval_edges x z \subset interval_edges x y.
    { move=> Hyp. rewrite (Hyp x y z zPcpxy) /=.
      by rewrite interval_edges_sym (interval_edges_sym x) Hyp 1?cp_sym 1?setUC. }
    move: zPcpxy. rewrite in_setD in_set2 negb_or => /andP[]/andP[zNx zNy] z_cpxy.
    apply/subsetP=> e. rewrite ![e \in _]inE !negb_or.
    case/and3P=> /andP[eNx eNz] Hsrc Htgt. rewrite eNx /=.
    have -> : source e \in @interval G x y.
    { move: Hsrc. rewrite !in_setU !in_set1 -orbA.
      case/or3P=> [->//|/eqP->|/(subsetP (sinterval_sub G_conn z_cpxy))->//].
      move: z_cpxy => /(subsetP (cp_sub_interval G_conn _ _)).
      by rewrite !in_setU !in_set1. }
    have -> : target e \in @interval G x y.
    { move: Htgt. rewrite !in_setU !in_set1 -orbA.
      case/or3P=> [->//|/eqP->|/(subsetP (sinterval_sub G_conn z_cpxy))->//].
      move: z_cpxy => /(subsetP (cp_sub_interval G_conn _ _)).
      by rewrite !in_setU !in_set1. }
    rewrite /= andbT.
    suff : y \notin @interval G x z by apply: contraNN => /andP[/eqP<-].
    rewrite in_setU in_set2 [_ == z]eq_sym (negbTE zNy) orbF negb_or.
    apply/andP; split; first by apply: contraTneq z_cpxy =>->; rewrite cpxx inE.
    by rewrite (@sintervalP G) negb_and !negbK (@cp_sym G y x) z_cpxy.
  - apply/subsetP=> e. rewrite ![e \in _]inE negb_or.
    have /subsetP PsubI := petal_sub_sinterval G_conn x_cp y_cp zPcpxy.
    case/andP=> /PsubI Hsrc /PsubI Htgt.
    rewrite ![_ \in @interval G x y]inE Hsrc Htgt !orbT /= andbT.
    apply/andP; split; apply: contraTN Hsrc => /andP[/eqP<-];
    by rewrite sinterval_bounds.
  - apply/subsetP=> e.
    rewrite in_setD andbC !in_setU inE (interval_cp_cover G_conn zPcpxy).
    rewrite negb_or 2!in_setU 2!(in_setU (target e)) => /andP[]/andP[].
    rewrite [(_ \in _) || _]orbC -2!orbA. case/orP=> Hsrc Htgt.
    + wlog Htgt : x y z zPcpxy Hsrc x_cp y_cp z_cp {z_cpxy Htgt} /
          (target e \in @petal G [set x; y] z) || (target e \in x |: @sinterval G x z).
      { case/or3P: Htgt => /= Htgt Hyp.
        * apply: Hyp => //; by rewrite Htgt.
        * apply: Hyp => //; by rewrite Htgt.
        * rewrite andbC orbC orbCA orbC setUC (interval_edges_sym x)interval_edges_sym.
          by apply: Hyp; rewrite setUC 1?cp_sym // sinterval_sym Htgt. }
      case/orP: Htgt => Htgt _; first by rewrite ![e \in _]inE Hsrc Htgt.
      case: (altP (source e =P target e)) => He.
        by rewrite ![e \in _]inE -He Hsrc.
      have src_tgt : @sedge G (source e) (target e).
      { rewrite -adjacentE He. apply/orP; left; apply/existsP; exists e.
        by rewrite !inE !eqxx. }
      have zNx : z != x by move: zPcpxy; rewrite !inE negb_or -andbA => /and3P[].
      have Ntgt : target e \notin @petal G [set x; y] z.
      { move: Htgt; rewrite sinterval_sym in_setU1.
        case/orP=> [/eqP->|Htgt]; last first.
          by rewrite (disjointFl (interval_petal_disj _ x_cp) Htgt).
        apply/petalPn. exists x; by [|rewrite cpxx inE]. }
      move/cpP'/(_ (edgep src_tgt)): (petal_exit G_conn z_cp Hsrc Ntgt).
      rewrite mem_edgep orbC. have /negbTE->/= : z != target e
        by apply: contraNneq Ntgt =><-; rewrite (@petal_id G).
      move=> /eqP Esrc. rewrite ![e \in _]inE -Esrc eqxx (negbTE zNx) /=.
      rewrite {1}Esrc eq_sym He (@intervalR G) in_setU in_set2.
      by move: Htgt; rewrite in_setU1; case/orP=>->.
    + wlog Hsrc : x y z zPcpxy x_cp y_cp z_cp Htgt z_cpxy {Hsrc} /
          source e \in x |: @sinterval G x z.
      { case/orP: Hsrc => /= Hsrc; first by [apply]; move=> Hyp.
        rewrite andbC orbC orbCA orbC setUC (interval_edges_sym x) interval_edges_sym.
        apply: Hyp; rewrite 1?[_ |: set1 _]setUC 1?cp_sym //.
        * by rewrite orbC orbAC orbC (@sinterval_sym G y) sinterval_sym.
        * by rewrite sinterval_sym. }
      case/or3P: Htgt => Htgt.
      * case/andP=> eNx _. rewrite 2!inE negb_or eNx 2!inE negb_and.
        have ->/= : source e != z.
        { apply: contraTneq Hsrc => ->.
          rewrite in_setU1 (@sinterval_bounds G) orbF.
          move: zPcpxy; rewrite in_setD in_set2 negb_or; by case/andP=> /andP[]. }
        have -> : source e \in @interval G x z.
        { by move: Hsrc; rewrite !in_setU !in_set1 => /orP[]->. }
        suff -> : target e \in @interval G x z by [].
        by move: Htgt; rewrite !in_setU !in_set1 => /orP[]->.
      * case: (altP (source e =P target e)) => He _.
          by rewrite ![e \in _]inE He Htgt.
        have tgt_src : @sedge G (target e) (source e).
        { rewrite -adjacentE eq_sym He. apply/orP; right; apply/existsP; exists e.
          by rewrite !inE !eqxx. }
        have zNx : z != x by move: zPcpxy; rewrite !inE negb_or -andbA => /and3P[].
        have Nsrc : source e \notin @petal G [set x; y] z.
        { move: Hsrc; rewrite sinterval_sym in_setU1.
          case/orP=> [/eqP->|Hsrc]; last first.
            by rewrite (disjointFl (interval_petal_disj _ x_cp) Hsrc).
          apply/petalPn. exists x; by [|rewrite cpxx inE]. }
        move/cpP'/(_ (edgep tgt_src)): (petal_exit G_conn z_cp Htgt Nsrc).
        rewrite mem_edgep orbC. have /negbTE->/= : z != source e
          by apply: contraNneq Nsrc =><-; rewrite (@petal_id G).
        move=> /eqP Etgt. rewrite ![e \in _]inE -Etgt eqxx (negbTE zNx) andbF andbT /=.
        rewrite {1}Etgt He (@intervalR G) in_setU in_set2.
        by move: Hsrc; rewrite in_setU1; case/orP=>->.
      * have adj : adjacent (source e) (target e)
          by apply/orP; left; apply/existsP; exists e; rewrite inE !eqxx.
        case: (altP (source e =P target e)) Hsrc Htgt => [<-|He Hsrc Htgt].
        { rewrite !in_setU1; case/orP=> [/eqP->|Hsrc].
          - rewrite (@sintervalP G) z_cpxy /= orbF => /eqP Exy.
            move: zPcpxy. by rewrite -Exy cpxx setUid setDv inE.
          - rewrite (disjointFr (sinterval_disj_cp z_cpxy) Hsrc) orbF => /eqP Htgt.
            move: Hsrc. by rewrite Htgt (@sintervalP G) (@cp_sym G y x) z_cpxy andbF. }
        have {He adj} He : @sedge G (source e) (target e) by rewrite -adjacentE He adj.
        have [/negbTE srcNz /negbTE tgtNz] : source e != z /\ target e != z.
        { split; [apply: contraTneq Hsrc|apply: contraTneq Htgt]=>->.
          all: rewrite in_setU1 negb_or (@sintervalP G) mem_cpl ?andbF andbT.
          all: move: zPcpxy; by rewrite !inE negb_or -andbA =>/and3P[]. }
        have {Hsrc} Hsrc : source e \in @interval G x z.
        { move: Hsrc; rewrite /interval !in_setU !in_set1 => /orP[/eqP->|->//].
          by rewrite eqxx. }
        have {Htgt} Htgt : target e \in @interval G z y.
        { move: Htgt; rewrite /interval !in_setU !in_set1 => /orP[/eqP->|->//].
          by rewrite eqxx. }
        have := interval_edge_cp z_cpxy He Hsrc Htgt. by rewrite srcNz tgtNz.
Qed.

(** ** Connecting Multigraphs and their Skeletons *)

Lemma has_edge (G : graph) (x y : G) : 
  connected [set: skeleton G] -> x != y -> 0 < #|edge G|.
Proof.
  move/connectedTE/(_ x y). case/uPathP => p _ xy. 
  case: (splitL p xy) => x' [/= xx'] _. 
  apply/card_gt0P. rewrite /sk_rel /= in xx'. 
  case/orP : xx' => /andP [_ /existsP [e _]]; by exists e. 
Qed.

Lemma consistent_setD (G : graph) V E E' : 
  @consistent G V E -> consistent V (E :\: E').
Proof. move => con_E e /setDP [? _]. exact: con_E. Qed.

(* Is this the most general type? *)
Lemma card_val (T : finType) (P : pred T) (s : subFinType P) (A : pred s) : 
  #|val @: A| = #|A|.
Proof. rewrite card_imset //. exact: val_inj. Qed.

(* lifting connectedness from the skeleton *)
Lemma connected_skeleton' (G : graph) V E (con : @consistent G V E) :
  forall U : {set subgraph_for con}, @connected (skeleton G) (val @: U) ->
  (forall e, e \in edge_set (val @: U) -> source e != target e ->
             let x := source e in let y := target e in
             exists2 e, e \in E & (e \in edges x y) || (e \in edges y x)) ->
  @connected (skeleton (subgraph_for con)) U.
Proof.
  move => U. set U' := val @: U => conn_U all_edges x y x_U y_U.
  case/connectP: (conn_U _ _ (mem_imset val x_U) (mem_imset val y_U)) => p.
  elim: p x x_U => [|a p IH] x x_U /=; first by move=> _ /val_inj <-; exact: connect0.
  rewrite -!andbA. case/and4P=> _ a_U' xa.
  have Ha : a \in V by case/imsetP: a_U' => b _ ->; exact: valP.
  set b : subgraph_for con := Sub a Ha. rewrite -[a]/(val b) => p_path p_last.
  have b_U : b \in U by rewrite -(inj_imset _  _ val_inj).
  apply: connect_trans (IH b b_U p_path p_last). apply: connect1 => /=.
  apply/andP; split; first by apply/andP; split. move: xa.

  rewrite -[a]/(val b).
  move: b x b_U x_U {p_last p_path a_U' IH p} => {a Ha} b x b_U x_U.
  rewrite -![sk_rel _ _ _]adjacentE -(inj_eq val_inj).
  case/andP=> xNb. rewrite xNb /= => adjv_xb.
  wlog [e0] : b x b_U x_U xNb {adjv_xb} / exists e, e \in edges (val x) (val b).
  { move=> Hyp. case/orP: adjv_xb => /existsP[e He].
    - by apply: Hyp => //; exists e.
    - rewrite /adjacent orbC. apply: Hyp => //; by [rewrite eq_sym | exists e]. }
  rewrite inE. case/andP=> /eqP Hsrc /eqP Htgt.
  have Ne0 : source e0 != target e0 by rewrite Hsrc Htgt.
  have : e0 \in edge_set U'. rewrite inE Hsrc Htgt !mem_imset //.
  case/all_edges=> [//|] e' Ee'. rewrite Hsrc Htgt => He'.
  set e : edge (subgraph_for con) := Sub e' Ee'.
  have : (e \in edges x b) || (e \in edges b x).
  { move: He'. by rewrite !inE -[e']/(val e) -!(inj_eq val_inj). }
  by case/orP=> He; apply/orP; [left|right]; apply/existsP; exists e.
Qed.

Lemma connected_skeleton (G : graph) V E (con : @consistent G V E) :
  forall U : {set subgraph_for con}, @connected (skeleton G) (val @: U) ->
  (forall e, e \in edge_set (val @: U) -> source e != target e -> e \in E) ->
  @connected (skeleton (subgraph_for con)) U.
Proof.
  move=> U conn_U all_edges. apply: connected_skeleton' conn_U _.
  move=> e E1 E2; exists e; rewrite ?inE ?eqxx //. exact: all_edges.
Qed.

Lemma connected_pgraph (G : graph2) (U : {set G}) (x : G) : 
  connected [set: skeleton G] -> x \in @CP (skeleton G) U -> 
  connected [set: skeleton (pgraph U x)].
Proof.
  move => conn_G cp_x.
  apply: connected_skeleton; rewrite imset_valT memKset //. exact: connected_petal.
Qed.

Lemma connected_igraph (G : graph2) (x y: G) : 
  connected [set: skeleton G] -> 
  connected [set: skeleton (igraph x y)].
Proof.
  move=> conn_G. apply: connected_skeleton; rewrite imset_valT memKset.
  + exact: connected_interval.
  + move => e E1 E2. rewrite 4!inE E1 andbT negb_or. apply/andP;split.
    * apply: contraNN E2 => /andP [/eqP -> /eqP ->]; by rewrite eqxx.
    * apply: contraNN E2 => /andP [/eqP -> /eqP ->]; by rewrite eqxx.
Qed.

Lemma iso_pointxx (G : graph) (x : G) :
  sg_iso (sskeleton (point _ x x)) (skeleton G).
Proof.
  exists (id : skeleton G -> sskeleton (point G x x)) id => // u v /=;
  first by move=>->. case/or3P => // /and3P[uNv /eqP eq1 /eqP eq2];
  move: uNv; by rewrite eq1 eq2 eqxx.
Qed.

Lemma sub_pointxx (G : graph) (x:G) :
  sgraph.subgraph (sskeleton (point _ x x))
                  (skeleton G).
Proof. apply: iso_subgraph; exact: iso_pointxx. Qed.

(* The subgraph relation lifts to skeletons *)
Lemma sub_sub (G H : graph) : 
  subgraph G H -> sgraph.subgraph G H.
Proof.
  move => [[hv he]] [/= hom_h lab_h] [/= inj_hv inj_he]. 
  exists hv => // x y. rewrite -!adjacentE => /andP[E adj]. right.
  apply/andP;split; first by apply: contraNN E => /eqP/inj_hv->.
  case/orP : adj => /existsP[e]. 
  - rewrite inE => /andP[/eqP<- /eqP<-]. rewrite !hom_h.
    apply/orP; left. apply/existsP; exists (he e). by rewrite !inE !eqxx.
  - rewrite inE => /andP[/eqP<- /eqP<-]. rewrite !hom_h.
    apply/orP; right. apply/existsP; exists (he e). by rewrite !inE !eqxx.
Qed.

Definition flesh_out_graph (G : sgraph) (z : G) : graph2 :=
  {| graph_of :=
       {| vertex := G ; edge := [finType of { p : G * G | p.1 -- p.2 }];
          source := fst \o val; target := snd \o val; label := fun _ => sym0 |} ;
     g_in := z; g_out := z |}.

Lemma flesh_out (G : sgraph) (z : G) :
  exists G', sg_iso (sskeleton G') G /\ sg_iso (skeleton G') G.
Proof.
  pose G' := flesh_out_graph z. exists G'.
  suff iso : sg_iso (skeleton G') G.
  { split=> //. apply: sg_iso_trans iso. exact: iso_pointxx. }
  exists (id : G -> skeleton G') id; move=> //= x y; rewrite /sk_rel/=.
  - move=> xy. apply/orP; left. rewrite sg_edgeNeq //=.
    apply/existsP; exists (Sub (x, y) xy); by rewrite /= !eqxx.
  - case/orP=> /andP[_] /existsP[][/=][u v /=] ? /andP[/eqP<- /eqP<-] //.
    by rewrite sg_sym.
Qed.
