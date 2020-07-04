
(* Experimenting with TGraphs *)

From mathcomp Require Import all_ssreflect.
Require Import preliminaries digraph sgraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Record tgraph (T : finType) := TGraph {
          tvertex : {set T} ; 
          tedge: rel T ; 
          tg_sym : symmetric tedge ;
          tg_irrefl : irreflexive tedge ;
          tg_ofvert: forall u v : T, tedge u v -> (u \in tvertex) && (v \in tvertex)
}.


(**********************************************************************************)
(** * Transforms TGraph to SGraph; also TGraph coerces to SGraph *)
Section Transformation_from_TGraph_to_SGraph.

Variable T : finType.

Variable G : tgraph T.

Let svertex' := sig_finType [eta mem (tvertex G)].

Let sedge' := fun u v : svertex' => tedge G (val u) (val v).

Let p_tg_sym' : symmetric sedge'.
Proof. rewrite /symmetric /sedge' => ? ? ; exact: (tg_sym G). Qed.

Let p_tg_irrefl' : irreflexive sedge'.
Proof. rewrite /irreflexive /sedge' => ? ; exact: (tg_irrefl G). Qed.

Definition ugr2tgr := @SGraph svertex' sedge' p_tg_sym' p_tg_irrefl'.

End Transformation_from_TGraph_to_SGraph.

Coercion ugr2tgr : tgraph >-> sgraph.


(**********************************************************************************)
(** * Big section with a predefined universal "T" for vertices and "G" for graphs *)
Section Domination_Theory.

Variable T : finType.


(**********************************************************************************)
(** * Basic facts about graphs *)
Section Neighborhoods_definitions.

Variable G : tgraph T.

Definition open_neigh (u : T) := [set v | tedge G u v].
Local Notation "N( x )" := (open_neigh x) (at level 0, x at level 99).

(* Warning: if u \notin V(G), N[u] is still {u} *)
Definition closed_neigh (u : T) := N(u) :|: [set u].
Local Notation "N[ x ]" := (closed_neigh x) (at level 0, x at level 99).

Definition cl_tedge (u v : T) : bool := (tedge G u v) || (u == v).

Definition edges := [set [set x;y] | x in T, y in T & tedge G x y].

Lemma edgesP (e : {set T}) : 
  reflect (exists x y, e = [set x;y] /\ tedge G x y) (e \in edges).
Proof.
  apply: (iffP imset2P) => [[x y]|[x] [y] [E xy]].
  - rewrite !inE /= => _ xy ->. by exists x; exists y.
  - exists x y => //. by rewrite inE.
Qed.

Variable D : {set T}.

Definition open_neigh_set : {set T} := \bigcup_(w in T | w \in D) N(w).

Definition closed_neigh_set : {set T} := \bigcup_(w in T | w \in D) N[w].

End Neighborhoods_definitions.

Notation "N( G ; x )" := (open_neigh G x) (at level 0, G at level 99, x at level 99).
Notation "N[ G ; x ]" := (closed_neigh G x) (at level 0, G at level 99, x at level 99).
Notation "V( G )" := (tvertex G) (at level 0, G at level 99).
Notation "E( G )" := (edges G) (at level 0, G at level 99).
Notation "NS( G ; D )" := (open_neigh_set G D) (at level 0, G at level 99, D at level 99).
Notation "NS[ G ; D ]" := (closed_neigh_set G D) (at level 0, G at level 99, D at level 99).


(* Here, we define "G" and gives notation that consider "G" implicitly *)
Variable G : tgraph T.

Local Notation "N( x )" := (open_neigh G x) (at level 0, x at level 99, only parsing).
Local Notation "N[ x ]" := (closed_neigh G x) (at level 0, x at level 99, only parsing).
Local Notation "x -- y" := (tedge G x y) (at level 30).
Local Notation "x -*- y" := (cl_tedge G x y) (at level 30).
Local Notation "NS( D )" := (open_neigh_set G D) (at level 0, D at level 99).
Local Notation "NS[ D ]" := (closed_neigh_set G D) (at level 0, D at level 99).


(**********************************************************************************)
Section Basic_Facts_Neighborhoods.

Lemma tg_opneigh : forall u v : T, (u -- v) = (u \in N(v)).
Proof. move=> u v ; by rewrite /open_neigh in_set tg_sym. Qed.

Lemma v_notin_opneigh : forall v : T, v \notin N(v).
Proof. move=> v ; by rewrite -tg_opneigh tg_irrefl. Qed.

Lemma cltg_clneigh : forall u v : T, (u -*- v) = (u \in N[v]).
Proof.
  move=> u v.
  rewrite /closed_neigh in_set in_set1.
  apply: orb_id2r => _.
  exact: tg_opneigh.
Qed.

Lemma cl_tg_sym : symmetric (@cl_tedge G). (* cl_tedge u v = cl_tedge v u *)
Proof. rewrite /symmetric /cl_tedge /closed_neigh => x y ; by rewrite tg_sym eq_sym. Qed.

Lemma cl_tg_refl : reflexive (@cl_tedge G). (* cl_sedge u u = true *)
Proof. rewrite /reflexive /cl_tedge /closed_neigh => u ; by rewrite eq_refl orbT. Qed.

Lemma v_in_clneigh : forall v : T, v \in N[v].
Proof. move=> v ; by rewrite -cltg_clneigh cl_tg_refl. Qed.

Lemma opneigh_proper_clneigh : forall v : T, N(v) \proper N[v].
Proof.
  move=> v.
  apply/properP.
  rewrite /closed_neigh.
  split.
  by rewrite subsetUl.
  exists v.
  by rewrite in_set in_set1 eq_refl orbT.
  exact: v_notin_opneigh.
Qed.

Proposition tg_in_edge_set : forall u v : T, (u -- v) <-> [set u; v] \in E(G).
Proof.
  move=> u v.
  rewrite /iff ; split.
  (* case: -> *)
  move=> adjuv.
  apply/edgesP.
  exists u.
  exists v.
  split => //.
  (* case: <- *)
  move/edgesP.
  elim=> x.
  elim=> y.
  rewrite (doubleton_eq_iff u v x y) ; elim ; case ; case.
  by move-> ; move->.
  by move-> ; move-> ; rewrite tg_sym.
Qed.

Proposition empty_open_neigh : NS(set0 : {set T}) = set0.
Proof.
  apply/eqP.
  rewrite -subset0.
  apply/subsetP => x.
  rewrite /open_neigh_set.
  move/bigcupP.
  elim=> z /andP [_ zinset0] _.
  move: zinset0.
  apply: contraLR => _.
  by rewrite in_set0.
Qed.

Proposition empty_closed_neigh : NS[set0 : {set T}] = set0.
Proof.
  apply/eqP.
  rewrite -subset0.
  apply/subsetP => x.
  rewrite /closed_neigh_set.
  move/bigcupP.
  elim=> z /andP [_ zinset0] _.
  move: zinset0.
  apply: contraLR => _.
  by rewrite in_set0.
Qed.

Variables D1 D2 : {set T}.

Proposition neigh_in_open_neigh : {in D1, forall v, N(v) \subset NS(D1)}.
Proof.
  move=> v vinD1.
  apply/subsetP => x xinD1.
  rewrite /open_neigh_set.
  apply/bigcupP.
  by exists v.
Qed.

Proposition neigh_in_closed_neigh : {in D1, forall v, N[v] \subset NS[D1]}.
Proof.
  move=> v vinD1.
  apply/subsetP => x xinD1.
  rewrite /closed_neigh_set.
  apply/bigcupP.
  by exists v.
Qed.

Proposition D_in_closed_neigh_set : D1 \subset NS[D1].
Proof.
  apply/subsetP => x xinD1.
  rewrite /closed_neigh_set.
  apply/bigcupP.
  exists x.
  by rewrite xinD1.
  exact: v_in_clneigh.
Qed.

Proposition dominated_belongs_to_open_neigh_set : forall u v : T, u \in D1 -> u -- v -> v \in NS(D1).
Proof.
  move=> u v uinD1 adjuv.
  rewrite /open_neigh_set.
  apply/bigcupP.
  exists u.
  apply/andP ; split=> [// | //].
  by rewrite -tg_opneigh tg_sym.
Qed.

Proposition open_neigh_set_subset_closed_neigh_set : NS(D1) \subset NS[D1].
Proof.
  apply/subsetP => u.
  rewrite /open_neigh_set /closed_neigh_set.
  move/bigcupP.
  elim=> v /andP [_ vinD1] uinNv.
  apply/bigcupP.
  exists v => [// | ].
  by rewrite /closed_neigh in_setU uinNv orTb.
Qed.

Proposition dominated_belongs_to_closed_neigh_set : forall u v : T, u \in D1 -> u -- v -> v \in NS[D1].
Proof.
  move=> u v uinD1 adjuv.
  apply: (subsetP open_neigh_set_subset_closed_neigh_set v).
  exact: dominated_belongs_to_open_neigh_set adjuv.
Qed.

Proposition closed_neigh_set_subset : D1 \subset D2 -> NS[D1] \subset NS[D2].
Proof.
  move=> D1subD2.
  rewrite /closed_neigh_set.
  apply/subsetP => x /bigcupP.
  elim=> i /andP [_ iinD1] xinNi.
  apply/bigcupP.
  exists i.
  apply/andP ; split=> //.
  exact: subsetP D1subD2 i iinD1.
  exact: xinNi.
Qed.

End Basic_Facts_Neighborhoods.





