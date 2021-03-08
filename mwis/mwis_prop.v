
(* Formalization of resolution of the Upper Weighted Irredundant Problem
 * via the Maximum Weighted Stable Set Problem
 *
 * Contributors: Ricardo Katz, Daniel Severin, Mauricio Salichs *)

From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import preliminaries digraph sgraph dom.
Require Import prelim mwis.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


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

(* converse results *)

Lemma forallOrdinalI4 (p : 'I_4 -> Prop) :
  (forall v : 'I_4, p v) <-> (p 'v0@4 /\ p 'v1@4 /\ p 'v2@4 /\ p 'v3@4).
Proof.
  split.
  - by move=> H; do 3 try split; apply: H.
  - move=> [pv0 [pv1 [pv2 pv3]]] [v vlt4].
    do 4 try destruct v.
    all: try by rewrite (bool_irrelevance vlt4 isT).
    suff: False by contradiction.
    by move: vlt4 ; apply/negP.
Qed.

Lemma forallOrdinalI5 (p : 'I_5 -> Prop) :
  (forall v : 'I_5, p v) <-> (p 'v0@5 /\ p 'v1@5 /\ p 'v2@5 /\ p 'v3@5 /\ p 'v4@5).
Proof.
  split.
  - by move=> H; do 4 try split; apply: H.
  - move=> [pv0 [pv1 [pv2 [pv3 pv4]]]] [v vlt5].
    do 5 try destruct v.
    all: try by rewrite (bool_irrelevance vlt5 isT).
    suff: False by contradiction.
    by move: vlt5 ; apply/negP.
Qed.

Lemma forallOrdinalI6 (p : 'I_6 -> Prop) :
  (forall v : 'I_6, p v) <-> (p 'v0@6 /\ p 'v1@6 /\ p 'v2@6 /\ p 'v3@6 /\ p 'v4@6 /\ p 'v5@6).
Proof.
  split.
  - by move=> H; do 5 try split; apply: H.
  - move=> [pv0 [pv1 [pv2 [pv3 [pv4 pv5]]]]] [v vlt6].
    do 6 try destruct v.
    all: try by rewrite (bool_irrelevance vlt6 isT).
    suff: False by contradiction.
    by move: vlt6 ; apply/negP.
Qed.

Lemma forallOrdinalI7 (p : 'I_7 -> Prop) :
  (forall v : 'I_7, p v) <-> (p 'v0@7 /\ p 'v1@7 /\ p 'v2@7 /\ p 'v3@7 /\ p 'v4@7 /\ p 'v5@7 /\ p 'v6@7).
Proof.
  split.
  - by move=> H; do 6 try split; apply: H.
  - move=> [pv0 [pv1 [pv2 [pv3 [pv4 [pv5 pv6]]]]]] [v vlt7].
    do 7 try destruct v.
    all: try by rewrite (bool_irrelevance vlt7 isT).
    suff: False by contradiction.
    by move: vlt7 ; apply/negP.
Qed.

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

Lemma h'_G4_inj (h' : 'I_4 -> G)
    (v0v1 : h' 'v0@4 != h' 'v1@4) (v0v2 : h' 'v0@4 != h' 'v2@4)
    (v0v3 : h' 'v0@4 != h' 'v3@4) (v1v2 : h' 'v1@4 != h' 'v2@4)
    (v1v3 : h' 'v1@4 != h' 'v3@4) (v2v3 : h' 'v2@4 != h' 'v3@4)
       : forall x1 x2 : copaw, h' x1 = h' x2 -> x1 = x2.
Proof.
  move: (negP v0v1) => ?; move: (negP v0v2) => ?; move: (negP v0v3) => ?;
  move: (negP v1v2) => ?; move: (negP v1v3) => ?; move: (negP v2v3) => ?.
  rewrite !forallOrdinalI4 ; do 6 try split.
  all: try by [].
  all: try by move/eqP ; contradiction.
  all: by move/eqP ; rewrite eq_sym ; contradiction.
Qed.

Lemma h'_G5_inj (h' : 'I_5 -> G)
  (v0v1 : h' 'v0@5 != h' 'v1@5) (v0v2 : h' 'v0@5 != h' 'v2@5)
  (v0v3 : h' 'v0@5 != h' 'v3@5) (v0v4 : h' 'v0@5 != h' 'v4@5)
  (v1v2 : h' 'v1@5 != h' 'v2@5) (v1v3 : h' 'v1@5 != h' 'v3@5)
  (v1v4 : h' 'v1@5 != h' 'v4@5) (v2v3 : h' 'v2@5 != h' 'v3@5)
  (v2v4 : h' 'v2@5 != h' 'v4@5) (v3v4 : h' 'v3@5 != h' 'v4@5)
       : forall x1 x2 : 'I_5, h' x1 = h' x2 -> x1 = x2.
Proof.
move: (negP v0v1) => ?; move: (negP v0v2) => ?;
move: (negP v0v3) => ?; move: (negP v0v4) => ?;
move: (negP v1v2) => ?; move: (negP v1v3) => ?;
move: (negP v1v4) => ?; move: (negP v2v3) => ?;
move: (negP v2v4) => ?; move: (negP v3v4) => ?.
rewrite !forallOrdinalI5 ; do 10 try split.
all: try by done.
all: try by move/eqP ; contradiction.
all: by move/eqP ; rewrite eq_sym ; contradiction.
Qed.

Lemma h'_G6_inj (h' : 'I_6 -> G)
  (v0v1 : h' 'v0@6 != h' 'v1@6) (v0v2 : h' 'v0@6 != h' 'v2@6)
  (v0v3 : h' 'v0@6 != h' 'v3@6) (v0v4 : h' 'v0@6 != h' 'v4@6)
  (v0v5 : h' 'v0@6 != h' 'v5@6) 
  (v1v2 : h' 'v1@6 != h' 'v2@6) (v1v3 : h' 'v1@6 != h' 'v3@6)
  (v1v4 : h' 'v1@6 != h' 'v4@6) (v1v5 : h' 'v1@6 != h' 'v5@6)
  (v2v3 : h' 'v2@6 != h' 'v3@6)
  (v2v4 : h' 'v2@6 != h' 'v4@6) (v2v5 : h' 'v2@6 != h' 'v5@6)
  (v3v4 : h' 'v3@6 != h' 'v4@6)
  (v3v5 : h' 'v3@6 != h' 'v5@6)
  (v4v5 : h' 'v4@6 != h' 'v5@6) 
       : forall x1 x2 : 'I_6, h' x1 = h' x2 -> x1 = x2.
Proof.
move: (negP v0v1) => ?; move: (negP v0v2) => ?;
move: (negP v0v3) => ?; move: (negP v0v4) => ?;
move: (negP v0v5) => ?;
move: (negP v1v2) => ?; move: (negP v1v3) => ?;
move: (negP v1v4) => ?; move: (negP v1v5) => ?;
move: (negP v2v3) => ?;
move: (negP v2v4) => ?; move: (negP v2v5) => ?;
move: (negP v3v4) => ?;
move: (negP v3v5) => ?;
move: (negP v4v5) => ?.
rewrite !forallOrdinalI6 ; do 10 try split.
all: try by done.
all: try by move/eqP; contradiction.
all: by move/eqP; rewrite eq_sym; contradiction.
Qed.

Lemma h'_G7_inj (h' : 'I_7 -> G)
  (v0v1 : h' 'v0@7 != h' 'v1@7) (v0v2 : h' 'v0@7 != h' 'v2@7)
  (v0v3 : h' 'v0@7 != h' 'v3@7) (v0v4 : h' 'v0@7 != h' 'v4@7)
  (v0v5 : h' 'v0@7 != h' 'v5@7) (v0v6 : h' 'v0@7 != h' 'v6@7)
  (v1v2 : h' 'v1@7 != h' 'v2@7) (v1v3 : h' 'v1@7 != h' 'v3@7)
  (v1v4 : h' 'v1@7 != h' 'v4@7) (v1v5 : h' 'v1@7 != h' 'v5@7)
  (v1v6 : h' 'v1@7 != h' 'v6@7) (v2v3 : h' 'v2@7 != h' 'v3@7)
  (v2v4 : h' 'v2@7 != h' 'v4@7) (v2v5 : h' 'v2@7 != h' 'v5@7)
  (v2v6 : h' 'v2@7 != h' 'v6@7) (v3v4 : h' 'v3@7 != h' 'v4@7)
  (v3v5 : h' 'v3@7 != h' 'v5@7) (v3v6 : h' 'v3@7 != h' 'v6@7)
  (v4v5 : h' 'v4@7 != h' 'v5@7) (v4v6 : h' 'v4@7 != h' 'v6@7)
  (v5v6 : h' 'v5@7 != h' 'v6@7)
       : forall x1 x2 : 'I_7, h' x1 = h' x2 -> x1 = x2.
Proof.
move: (negP v0v1) => ?; move: (negP v0v2) => ?;
move: (negP v0v3) => ?; move: (negP v0v4) => ?;
move: (negP v0v5) => ?; move: (negP v0v6) => ?;
move: (negP v1v2) => ?; move: (negP v1v3) => ?;
move: (negP v1v4) => ?; move: (negP v1v5) => ?;
move: (negP v1v6) => ?; move: (negP v2v3) => ?;
move: (negP v2v4) => ?; move: (negP v2v5) => ?;
move: (negP v2v6) => ?; move: (negP v3v4) => ?;
move: (negP v3v5) => ?; move: (negP v3v6) => ?;
move: (negP v4v5) => ?; move: (negP v4v6) => ?;
move: (negP v5v6) => ?.
rewrite !forallOrdinalI7; do 12 try split.
all: try by done.
all: try by move/eqP; contradiction.
all: by move/eqP; rewrite eq_sym; contradiction.
Qed.

Lemma h'_copaw_hom (h' : copaw -> G)
    (e_v0v1 : h' 'v0@4 -- h' 'v1@4) (e_v1v2 : h' 'v1@4 -- h' 'v2@4)
    (n_v0v2 : ~~ h' 'v0@4 -- h' 'v2@4) (n_v0v3 : ~~ h' 'v0@4 -- h' 'v3@4)
    (n_v1v3 : ~~ h' 'v1@4 -- h' 'v3@4) (n_v2v3 : ~~ h' 'v2@4 -- h' 'v3@4)
       : forall x1 x2 : copaw, x1 -- x2 <-> h' x1 -- h' x2.
Proof.
  rewrite !forallOrdinalI4; do 7 try split.
  all: try by done.
  all: try by rewrite !sg_irrefl; apply/implyP.
  all: try by rewrite [in X in _ -> X]sg_sym.
  all: try by apply: contraLR.
  all: by rewrite [in X in X -> _]sg_sym; apply: contraLR.
Qed.

Lemma h'_bull_hom (h' : bull -> G)
    (e_v0v2 : h' 'v0@5 -- h' 'v2@5) (e_v1v3 : h' 'v1@5 -- h' 'v3@5)
    (e_v2v3 : h' 'v2@5 -- h' 'v3@5) (e_v2v4 : h' 'v2@5 -- h' 'v4@5)
    (e_v3v4 : h' 'v3@5 -- h' 'v4@5)
    (n_v0v1 : ~~ h' 'v0@5 -- h' 'v1@5) (n_v0v3 : ~~ h' 'v0@5 -- h' 'v3@5)
    (n_v0v4 : ~~ h' 'v0@5 -- h' 'v4@5) (n_v1v2 : ~~ h' 'v1@5 -- h' 'v2@5)
    (n_v1v4 : ~~ h' 'v1@5 -- h' 'v4@5)
       : forall x1 x2 : bull, x1 -- x2 <-> h' x1 -- h' x2.
Proof.
  rewrite !forallOrdinalI5; do 9 try split.
  all: try by done.
  all: try by rewrite !sg_irrefl; apply/implyP.
  all: try by rewrite [in X in _ -> X]sg_sym.
  all: try by apply: contraLR.
  all: by rewrite [in X in X -> _]sg_sym; apply: contraLR.
Qed.

Lemma h'_P_6_hom (h' : 'P_6 -> G)
  (e_v0v1 : h' 'v0@6 -- h' 'v1@6) (e_v1v2 : h' 'v1@6 -- h' 'v2@6)
  (e_v2v3 : h' 'v2@6 -- h' 'v3@6) (e_v3v4 : h' 'v3@6 -- h' 'v4@6) 
  (e_v4v5 : h' 'v4@6 -- h' 'v5@6) 
  (e_v0v2 : ~~ h' 'v0@6 -- h' 'v2@6) (e_v0v3 : ~~ h' 'v0@6 -- h' 'v3@6) 
  (e_v0v4 : ~~ h' 'v0@6 -- h' 'v4@6) (e_v0v5 : ~~ h' 'v0@6 -- h' 'v5@6)
  (n_v1v3 : ~~ h' 'v1@6 -- h' 'v3@6) (n_v1v4 : ~~ h' 'v1@6 -- h' 'v4@6)
  (n_v1v5 : ~~ h' 'v1@6 -- h' 'v5@6) (n_v2v4 : ~~ h' 'v2@6 -- h' 'v4@6)
  (n_v2v5 : ~~ h' 'v2@6 -- h' 'v5@6) (n_v3v5 : ~~ h' 'v3@6 -- h' 'v5@6)
       : forall x1 x2 : 'P_6, x1 -- x2 <-> h' x1 -- h' x2.
Proof.
rewrite !forallOrdinalI6; do 12 try split.
all: try by done.
all: try by rewrite !sg_irrefl; apply/implyP.
all: try by rewrite [in X in _ -> X]sg_sym.
all: try by apply: contraLR.
all: by rewrite [in X in X -> _]sg_sym; apply: contraLR.
Qed.

Lemma h'_CC_6_hom (h' : 'CC_6 -> G)
  (e_v0v2 : h' 'v0@6 -- h' 'v2@6) (e_v0v3 : h' 'v0@6 -- h' 'v3@6)
  (e_v0v4 : h' 'v0@6 -- h' 'v4@6) 
  (e_v1v3 : h' 'v1@6 -- h' 'v3@6) (e_v1v4 : h' 'v1@6 -- h' 'v4@6)
  (e_v1v5 : h' 'v1@6 -- h' 'v5@6) 
  (e_v2v4 : h' 'v2@6 -- h' 'v4@6) (e_v2v5 : h' 'v2@6 -- h' 'v5@6) 
  (e_v3v5 : h' 'v3@6 -- h' 'v5@6) 
  (n_v0v1 : ~~ h' 'v0@6 -- h' 'v1@6) (n_v0v5 : ~~ h' 'v0@6 -- h' 'v5@6)
  (n_v1v2 : ~~ h' 'v1@6 -- h' 'v2@6) (n_v2v3 : ~~ h' 'v2@6 -- h' 'v3@6)
  (n_v3v4 : ~~ h' 'v3@6 -- h' 'v4@6) (n_v4v5 : ~~ h' 'v4@6 -- h' 'v5@6)
       : forall x1 x2 : 'CC_6, x1 -- x2 <-> h' x1 -- h' x2.
Proof.
rewrite !forallOrdinalI6; do 12 try split.
all: try by done.
all: try by rewrite !sg_irrefl; apply/implyP.
all: try by rewrite [in X in _ -> X]sg_sym.
all: try by apply: contraLR.
all: by rewrite [in X in X -> _]sg_sym; apply: contraLR.
Qed.

Lemma h'_G7_1_hom (h' : G7_1 -> G)
  (e_v0v2 : h' 'v0@7 -- h' 'v2@7) (e_v0v3 : h' 'v0@7 -- h' 'v3@7)
  (e_v0v4 : h' 'v0@7 -- h' 'v4@7) (e_v0v6 : h' 'v0@7 -- h' 'v6@7)
  (e_v1v3 : h' 'v1@7 -- h' 'v3@7) (e_v1v4 : h' 'v1@7 -- h' 'v4@7)
  (e_v1v5 : h' 'v1@7 -- h' 'v5@7) (e_v1v6 : h' 'v1@7 -- h' 'v6@7)
  (e_v2v4 : h' 'v2@7 -- h' 'v4@7) (e_v2v5 : h' 'v2@7 -- h' 'v5@7) 
  (e_v3v5 : h' 'v3@7 -- h' 'v5@7) (e_v3v6 : h' 'v3@7 -- h' 'v6@7) 
  (e_v4v6 : h' 'v4@7 -- h' 'v6@7)
  (n_v0v1 : ~~ h' 'v0@7 -- h' 'v1@7) (n_v0v5 : ~~ h' 'v0@7 -- h' 'v5@7)
  (n_v1v2 : ~~ h' 'v1@7 -- h' 'v2@7) (n_v2v3 : ~~ h' 'v2@7 -- h' 'v3@7)
  (n_v2v6 : ~~ h' 'v2@7 -- h' 'v6@7) (n_v3v4 : ~~ h' 'v3@7 -- h' 'v4@7)
  (n_v4v5 : ~~ h' 'v4@7 -- h' 'v5@7) (n_v5v6 : ~~ h' 'v5@7 -- h' 'v6@7)
       : forall x1 x2 : G7_1, x1 -- x2 <-> h' x1 -- h' x2.
Proof.
rewrite !forallOrdinalI7; do 13 try split.
all: try by done.
all: try by rewrite !sg_irrefl; apply/implyP.
all: try by rewrite [in X in _ -> X]sg_sym.
all: try by apply: contraLR.
all: by rewrite [in X in X -> _]sg_sym; apply: contraLR.
Qed.

Lemma h'_G7_2_hom (h' : G7_2 -> G)
  (e_v0v2 : h' 'v0@7 -- h' 'v2@7) (e_v0v3 : h' 'v0@7 -- h' 'v3@7)
  (e_v0v4 : h' 'v0@7 -- h' 'v4@7) (e_v0v6 : h' 'v0@7 -- h' 'v6@7)
  (e_v1v3 : h' 'v1@7 -- h' 'v3@7) (e_v1v4 : h' 'v1@7 -- h' 'v4@7)
  (e_v1v5 : h' 'v1@7 -- h' 'v5@7) (e_v1v6 : h' 'v1@7 -- h' 'v6@7)
  (e_v2v4 : h' 'v2@7 -- h' 'v4@7) (e_v2v5 : h' 'v2@7 -- h' 'v5@7)
  (e_v2v6 : h' 'v2@7 -- h' 'v6@7) (e_v3v5 : h' 'v3@7 -- h' 'v5@7)
  (e_v3v6 : h' 'v3@7 -- h' 'v6@7) (e_v4v6 : h' 'v4@7 -- h' 'v6@7)
  (n_v0v1 : ~~ h' 'v0@7 -- h' 'v1@7) (n_v0v5 : ~~ h' 'v0@7 -- h' 'v5@7)
  (n_v1v2 : ~~ h' 'v1@7 -- h' 'v2@7) (n_v2v3 : ~~ h' 'v2@7 -- h' 'v3@7)
  (n_v3v4 : ~~ h' 'v3@7 -- h' 'v4@7) (n_v4v5 : ~~ h' 'v4@7 -- h' 'v5@7)
  (n_v5v6 : ~~ h' 'v5@7 -- h' 'v6@7)
       : forall x1 x2 : G7_2, x1 -- x2 <-> h' x1 -- h' x2.
Proof.
rewrite !forallOrdinalI7; do 13 try split.
all: try by done.
all: try by rewrite !sg_irrefl; apply/implyP.
all: try by rewrite [in X in _ -> X]sg_sym.
all: try by apply: contraLR.
all: by rewrite [in X in X -> _]sg_sym; apply: contraLR.
Qed.

Definition hom_G4_def (v1 v2 v3 v4 : G) (v : 'I_4) :=
  match v with
  | Ordinal 0 _ => v1
  | Ordinal 1 _ => v2
  | Ordinal 2 _ => v3
  | Ordinal _ _ => v4
  end.

Definition hom_G5_def (v1 v2 v3 v4 v5 : G) (v : 'I_5) :=
  match v with
  | Ordinal 0 _ => v1
  | Ordinal 1 _ => v2
  | Ordinal 2 _ => v3
  | Ordinal 3 _ => v4
  | Ordinal _ _ => v5
  end.

Definition hom_G6_def (v1 v2 v3 v4 v5 v6 : G) (v : 'I_6) :=
  match v with
  | Ordinal 0 _ => v1
  | Ordinal 1 _ => v2
  | Ordinal 2 _ => v3
  | Ordinal 3 _ => v4
  | Ordinal 4 _ => v5
  | Ordinal _ _ => v6
  end.

Definition hom_G7_def (v1 v2 v3 v4 v5 v6 v7 : G) (v : 'I_7) :=
  match v with
  | Ordinal 0 _ => v1
  | Ordinal 1 _ => v2
  | Ordinal 2 _ => v3
  | Ordinal 3 _ => v4
  | Ordinal 4 _ => v5
  | Ordinal 5 _ => v6
  | Ordinal _ _ => v7
  end.

Lemma case_aa_b1b2_c1c2 (h : copaw -> trfgraph G) (a1 a2 b1 b2 c1 c2 d1 d2 : G) :
  (d1 == d2) || d1 -- d2 ->
  (a1 == b2) || a1 -- b2 || (a2 == b1) || a2 -- b1 ->
  (b1 == c2) || b1 -- c2 || (b2 == c1) || b2 -- c1 ->
  a1 != c2 ->
  ~~ a1 -- c2 ->
  a2 != c1 ->
  ~~ a2 -- c1 ->
  a1 != d2 ->
  ~~ a1 -- d2 ->
  a2 != d1 ->
  ~~ a2 -- d1 ->
  b1 != d2 ->
  ~~ b1 -- d2 ->
  b2 != d1 ->
  ~~ b2 -- d1 ->
  c1 != d2 ->
  ~~ c1 -- d2 ->
  c2 != d1 ->
  ~~ c2 -- d1 ->
  a1 = a2 ->
  b1 -- b2 ->
  c1 -- c2 ->
    (exists2 h0 : copaw -> G, injective h0 & induced_hom h0).
Proof.
move => d1d2 a1b2a2b1 b1c2b2c1 ? ? ? ? ? ? ? ? ? b1_nadj_d2 ? b2_nadj_d1 ? c1_nadj_d2 ? c2_nadj_d1 a1_eq_a2 b1_adj_b2 c1_adj_c2.
have b1_neq_b2: b1 != b2 by rewrite sg_edgeNeq.
case: (orP d1d2)=> [/eqP d1_eq_d2 | d1_adj_d2].
- (* a a --- b1 b2 --- c1 c2 *)
  (*          d d            *)
  case: (boolP (a1 -- b1))=> [a1_adj_b1 | a1_nadj_b1].
  + case: (boolP (a1 -- b2))=> [a1_adj_b2 | a1_nadj_b2].
    * case: (boolP (c1 -- b2))=> [c1_adj_b2 | c1_nadj_b2].
      -- exists (hom_G4_def a2 b2 c1 d2).
         ++ apply: h'_G4_inj; rewrite /=; try by done.
            all: try by rewrite -d1_eq_d2.
            ** by move: a1_adj_b2; apply/contraTneq => <-; rewrite a1_eq_a2 sg_irrefl.
            ** by move: c1_adj_b2; apply/contraTneq => <-; rewrite sg_irrefl.
         ++ apply: h'_copaw_hom; rewrite /=; try by done.
            all: try by rewrite -d1_eq_d2.
            ** by rewrite -a1_eq_a2.
            ** by rewrite sg_sym.
      -- exists (hom_G4_def a1 b1 c2 d2).
         ++ apply: h'_G4_inj; rewrite /=; try by done.
            ** by move: a1_adj_b1; apply/contraTneq => <-; rewrite sg_irrefl.
            ** by move: a1_adj_b1; apply/contraTneq => ->.
            ** by rewrite -d1_eq_d2.
         ++ apply: h'_copaw_hom; rewrite /=; try by done.
            ** have b1_neq_c2: b1 != c2 by move: a1_adj_b1; apply/contraTneq => ->.
               have b2_neq_c1: b2 != c1 by move: a1_adj_b2; apply/contraTneq => ->; rewrite a1_eq_a2.
               rewrite sg_sym in c1_nadj_b2.
               by rewrite (negbTE b1_neq_c2) (negbTE b2_neq_c1) (negbTE c1_nadj_b2) /= orbC /= orbC /= in b1c2b2c1.
            ** by rewrite -d1_eq_d2.
    * case: (boolP (a1 == b2))=> [/eqP a1_eq_b2 | a1_neq_b2].
      -- (* c1 -- c2 -- b1 -- b2 = a1 = a2 *)
         (*           d1 = d2              *)
         have b1_neq_c2: b1 != c2 by move: a1_adj_b1; apply/contraTneq => ->.
         have b2_neq_c1: b2 != c1 by rewrite -a1_eq_b2 a1_eq_a2.
         have b2_nadj_c1: ~~ b2 -- c1 by rewrite -a1_eq_b2 a1_eq_a2.
         exists (hom_G4_def b2 b1 c2 d1).
         ++ apply: h'_G4_inj; rewrite /=; try by done.
            ** by move: b1_adj_b2; apply/contraTneq => <-; rewrite sg_irrefl.
            ** by rewrite -a1_eq_b2.
            ** by rewrite d1_eq_d2.
         ++ apply: h'_copaw_hom; rewrite /=; try by done.
            ** by rewrite sg_sym.
            ** by rewrite (negbTE b1_neq_c2) (negbTE b2_neq_c1) (negbTE b2_nadj_c1) /= orbC /= orbC /= in b1c2b2c1.
            ** by rewrite -a1_eq_b2.
            ** by rewrite d1_eq_d2.
      -- exists (hom_G4_def a1 b1 b2 d1).
         ++ apply: h'_G4_inj; rewrite /=; try by done.
            all: try by rewrite d1_eq_d2.
            by move: a1_adj_b1; apply/contraTneq => <-; rewrite a1_eq_a2 sg_irrefl.
         ++ apply: h'_copaw_hom; rewrite /=; try by done.
            all: by rewrite d1_eq_d2.
  + case: (boolP (a1 == b2))=> [/eqP a1_eq_b2 | a1_neq_b2];
      first by move: a1_nadj_b1; rewrite a1_eq_b2 sg_sym b1_adj_b2.
    case: (boolP (a1 == b1))=> [/eqP a1_eq_b1 | a1_neq_b1].
    * have b1_neq_c2: b1 != c2 by rewrite -a1_eq_b1.
      have b2_neq_c1: b2 != c1 by move: b1_adj_b2; apply/contraTneq => ->; rewrite -a1_eq_b1 a1_eq_a2.
      have b1_nadj_c2: ~~ b1 -- c2 by rewrite -a1_eq_b1.
      exists (hom_G4_def a1 b2 c1 d2).
      -- apply: h'_G4_inj; rewrite /=; try by done.
         ++ by rewrite a1_eq_a2.
         ++ by rewrite -d1_eq_d2.
      -- apply: h'_copaw_hom; rewrite /=; try by done.
         ++ by rewrite a1_eq_b1.
         ++ by rewrite (negbTE b1_neq_c2) (negbTE b2_neq_c1) (negbTE b1_nadj_c2) //= in b1c2b2c1.
         ++ by rewrite a1_eq_a2.
         ++ by rewrite -d1_eq_d2.
    * exists (hom_G4_def a1 b2 b1 d2).
      -- apply: h'_G4_inj; rewrite /=; try by done.
         ++ by move: b1_adj_b2; apply/contraTneq => <-; rewrite sg_irrefl.
         ++ by rewrite -d1_eq_d2.
      -- apply: h'_copaw_hom; rewrite /=; try by done.
         ++ rewrite a1_eq_a2 in a1_nadj_b1.
            rewrite a1_eq_a2 in a1_neq_b1.
            by rewrite (negbTE a1_neq_b2) (negbTE a1_neq_b1) (negbTE a1_nadj_b1) /= orbC /= orbC /= in a1b2a2b1.
         ++ by rewrite sg_sym.
         ++ by rewrite -d1_eq_d2.
- (* a a --- b1 b2 --- c1 c2 *)
  (*         d1 d2           *)
  case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1].
  + exists (hom_G4_def c1 d1 d2 a2).
    * apply: h'_G4_inj; rewrite /=; try by done.
      all: try by rewrite eq_sym.
      all: try by rewrite sg_edgeNeq.
      by rewrite -a1_eq_a2 eq_sym.
    * apply: h'_copaw_hom; rewrite /=; try by done.
      all: try by rewrite sg_sym.
      by rewrite -a1_eq_a2 sg_sym.
  + case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2].
    * exists (hom_G4_def c1 c2 d2 a1).
      -- apply: h'_G4_inj; rewrite /=; try by done.
         all: try by rewrite eq_sym.
         all: try by rewrite sg_edgeNeq.
         by rewrite a1_eq_a2 eq_sym.
      -- apply: h'_copaw_hom; rewrite /=; try by done.
         all: try by rewrite sg_sym.
         by rewrite a1_eq_a2 sg_sym.
    * case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1].
      -- case: (boolP (b1 -- c2)) => [b1_adj_c2 | b1_nadj_c2].
         ++ exists (hom_G4_def a2 b1 c2 d2).
            ** apply: h'_G4_inj; rewrite /=; try by done.
               all: try by rewrite sg_edgeNeq.
               all: try by rewrite -a1_eq_a2.
               by move: c1_nadj_d2; apply/contraTneq => <-; rewrite c1_adj_c2.
            ** apply: h'_copaw_hom; rewrite /=; try by done.
               all: by rewrite -a1_eq_a2.
         ++ case: (boolP (b1 -- c1)) => [b1_adj_c1 | b1_nadj_c1].
            ** exists (hom_G4_def b1 c1 c2 d2).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite sg_edgeNeq.
                   +++ by move: a2_adj_b1; apply/contraTneq => ->; rewrite -a1_eq_a2.
                   +++ by move: c1_nadj_d2; apply/contraTneq => <-; rewrite c1_adj_c2.
               --- apply: h'_copaw_hom; rewrite /=; try by done.
            ** case: (boolP (b2 -- c2))=> [b2_adj_c2 | b2_nadj_c2].
               --- case: (boolP (b1 -- d1))=> [b1_adj_d1 | b1_nadj_d1].
                   +++ exists (hom_G4_def a2 b1 d1 c2).
                       *** apply: h'_G4_inj; rewrite /=; try by done.
                           all: try by rewrite eq_sym.
                           all: try by rewrite sg_edgeNeq.
                           ---- by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                           ---- by move: b1_adj_d1; apply/contraTneq => ->.
                       *** apply: h'_copaw_hom; rewrite /=; try by done.
                           ---- by rewrite -a1_eq_a2.
                           ---- by rewrite sg_sym.
                   +++ case: (boolP (a1 -- b2))=> [a1_adj_b2 | a1_nadj_b2].
                       *** exists (hom_G4_def a1 b2 c2 d1).
                             ---- apply: h'_G4_inj; rewrite /=; try by done.
                                  all: try by rewrite sg_edgeNeq.
                                  by rewrite a1_eq_a2.
                             ---- apply: h'_copaw_hom; rewrite /=; try by done.
                                  by rewrite a1_eq_a2.
                       *** exists (hom_G4_def a2 b1 b2 d1).
                           ---- apply: h'_G4_inj; rewrite /=; try by done.
                                all: try by rewrite sg_edgeNeq.
                                ++++ by move: b2_adj_c2; apply/contraTneq => <-; rewrite -a1_eq_a2.
                                ++++ by move: b2_nadj_d1; apply/contraTneq => <-; rewrite sg_sym b1_adj_b2.
                           ---- apply: h'_copaw_hom; rewrite /=; try by done.
                                by rewrite -a1_eq_a2.
               --- have b2_neq_c1: b2 != c1 by move: b2_nadj_c2; apply/contraTneq => ->; rewrite c1_adj_c2.
                   have b1_neq_c2: b1 != c2 by move: b1_nadj_c1; apply/contraTneq => ->; rewrite sg_sym c1_adj_c2.
                   exists (hom_G4_def b2 c1 c2 d1).
                   +++ apply: h'_G4_inj; rewrite /=; try by done.
                       all: try by rewrite sg_edgeNeq.
                       *** by move: b1_nadj_c2; apply/contraTneq => <-; rewrite b1_adj_b2.
                       *** by move: c2_nadj_d1; apply/contraTneq => <-; rewrite sg_sym c1_adj_c2.
                   +++ apply: h'_copaw_hom; rewrite /=; try by done.
                       by rewrite (negbTE b2_neq_c1) (negbTE b1_neq_c2) (negbTE b1_nadj_c2) in b1c2b2c1.
      -- case: (boolP (a1 -- b2)) => [a1_adj_b2 | a1_nadj_b2].
         ++ case: (boolP (b2 -- c1)) => [b2_adj_c1 | b2_nadj_c1].
            ** exists (hom_G4_def a1 b2 c1 d1).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite sg_edgeNeq.
                   +++ by move: c1_adj_c2; apply/contraTneq => <-.
                   +++ by rewrite a1_eq_a2.
                   +++ by move: b2_adj_c1; apply/contraTneq => ->.
               --- apply: h'_copaw_hom; rewrite /=; try by done.
                   all: by rewrite a1_eq_a2.
            ** case: (boolP (b2 -- c2)) => [b2_adj_c2 | b2_nadj_c2].
               --- exists (hom_G4_def b2 c2 c1 d1).
                   +++ apply: h'_G4_inj; rewrite /=; try by done.
                       *** by move: b2_adj_c2; apply/contraTneq => <-; rewrite sg_irrefl.
                       *** by move: a1_adj_b2; apply/contraTneq => ->; rewrite a1_eq_a2.
                       *** by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_irrefl.
                       *** by move: c2_nadj_d1; apply/contraTneq => <-; rewrite sg_sym c1_adj_c2.
                   +++ apply: h'_copaw_hom; rewrite /=; try by done.
                       by rewrite sg_sym.
               --- case: (boolP (b1 -- c1)) => [b1_adj_c1 | b1_nadj_c1].
                   +++ case: (boolP (b2 -- d2)) => [b2_adj_d2 | b2_nadj_d2].
                       *** exists (hom_G4_def a1 b2 d2 c1).
                           ---- apply: h'_G4_inj; rewrite /=; try by done.
                                all: try by rewrite sg_edgeNeq.
                                ++++ by move: c1_adj_c2; apply/contraTneq => <-. 
                                ++++ by move: b2_adj_d2; apply/contraTneq => ->.
                                ++++ by move: b1_adj_c1; apply/contraTneq => <-.
                           ---- apply: h'_copaw_hom; rewrite /=; try by done.
                                ++++ by rewrite a1_eq_a2.
                                ++++ by rewrite sg_sym.
                       *** exists (hom_G4_def a1 b2 b1 d2).
                           ---- apply: h'_G4_inj; rewrite /=; try by done. 
                                all: try by rewrite eq_sym.
                                all: try by rewrite sg_edgeNeq.
                                ++++ by move: b1_adj_c1; apply/contraTneq => <-; rewrite a1_eq_a2.
                                ++++ by move: b1_nadj_d2; apply/contraTneq => <-; rewrite b1_adj_b2.
                           ---- apply: h'_copaw_hom; rewrite /=; try by done.
                                ++++ by rewrite sg_sym.
                                ++++ by rewrite a1_eq_a2.
                   +++ have b1_neq_c2: b1 != c2 by move: b1_nadj_c1; apply/contraTneq => ->; rewrite sg_sym c1_adj_c2.
                       have b2_neq_c1: b2 != c1 by move: b2_nadj_c2; apply/contraTneq => ->; rewrite c1_adj_c2.
                       exists (hom_G4_def b1 c2 c1 d2).
                       *** apply: h'_G4_inj; rewrite /=; try by done.
                           ---- by move: b2_nadj_c1; apply/contraTneq => <-; rewrite sg_sym b1_adj_b2.
                           ---- by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_irrefl.
                           ---- by move: c1_nadj_d2; apply/contraTneq => <-; rewrite c1_adj_c2.
                       *** apply: h'_copaw_hom; rewrite /=; try by done.
                           ---- by rewrite (negbTE b2_neq_c1) (negbTE b1_neq_c2) (negbTE b2_nadj_c1) /= orbC /= orbC /= in b1c2b2c1.
                           ---- by rewrite sg_sym.
         ++ rewrite (negbTE a2_nadj_b1) (negbTE a1_nadj_b2) /= in a1b2a2b1.
            case: (orP a1b2a2b1) => // a1b2a2b1'.
            case: (orP a1b2a2b1') => //= a2_eq_b1.
            ** case: (orP a2_eq_b1) => // /eqP a1_eq_b2.
               (* b1 b2 = a1 = a2 -- c1 c2 *)
               (*          d1  d2          *)
               have b1_neq_c2: b1 != c2 by move: b1_adj_b2; apply/contraTneq => ->; rewrite -a1_eq_b2 sg_sym.
               have b2_neq_c1: b2 != c1 by rewrite -a1_eq_b2 a1_eq_a2.
               have b2_nadj_c1: ~~ (b2 -- c1) by rewrite -a1_eq_b2 a1_eq_a2.
               exists (hom_G4_def c2 b1 b2 d2).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   +++ by move: b1_adj_b2; apply/contraTneq => <-; rewrite -a1_eq_b2 sg_sym.
                   +++ by rewrite -a1_eq_b2 eq_sym.
                   +++ by move: c1_adj_c2; apply/contraTneq => ->.
                   +++ by rewrite -a1_eq_b2.
               --- apply: h'_copaw_hom; rewrite /=; try by done.
                   +++ by rewrite (negbTE b1_neq_c2) (negbTE b2_neq_c1) (negbTE b2_nadj_c1) /= orbC /= orbC /= sg_sym in b1c2b2c1.
                   +++ by rewrite -a1_eq_b2 sg_sym.
                   +++ by rewrite -a1_eq_b2.
            ** have b1_neq_c2: b1 != c2 by rewrite -(eqP a2_eq_b1) -a1_eq_a2.
               have b2_neq_c1: b2 != c1 by move: b1_adj_b2; apply/contraTneq => ->; rewrite -(eqP a2_eq_b1).
               have b1_nadj_c2: ~~ (b1 -- c2) by rewrite -(eqP a2_eq_b1) -a1_eq_a2.
               have b2_nadj_c1: b2 -- c1 by rewrite (negbTE b1_neq_c2) (negbTE b2_neq_c1) (negbTE b1_nadj_c2) /= in b1c2b2c1.
               exists (hom_G4_def c1 b2 b1 d1).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym sg_edgeNeq.
                   +++ by rewrite -(eqP a2_eq_b1) eq_sym.
                   +++ by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                   +++ by rewrite -(eqP a2_eq_b1).
               --- apply: h'_copaw_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   +++ by rewrite -(eqP a2_eq_b1) sg_sym.
                   +++ by rewrite -(eqP a2_eq_b1).
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
    + case/orP: c1c2 => [/eqP c1_eq_c2 | c1_adj_c2].
      (* a a --- b b --- c c *)
      * left; exists (hom_G4_def a1 b1 c1 d1).
        -- apply: h'_G4_inj; rewrite /=; try by done.
           ++ by move: a1a2b1b2 ; rewrite a1_eq_a2 b1_eq_b2 orbb.
           ++ by move: a1a2c1c2 ; rewrite a1_eq_a2 c1_eq_c2 orbb.
           ++ by rewrite a1_eq_a2.
           ++ by move: b1b2c1c2 ; rewrite b1_eq_b2 c1_eq_c2 orbb.
           ++ by rewrite b1_eq_b2.
           ++ by rewrite c1_eq_c2.
        -- apply: h'_copaw_hom; rewrite /=; try by done.
           all: try by rewrite a1_eq_a2.
           ++ move: a1a2b1b2 ; rewrite a1_eq_a2 b1_eq_b2 orbb.
              move: a1b2a2b1 ; rewrite a1_eq_a2 b1_eq_b2 -orbA orbb.
              case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by []].
           ++ move: b1b2c1c2 ; rewrite b1_eq_b2 c1_eq_c2 orbb.
              move: b1c2b2c1 ; rewrite b1_eq_b2 c1_eq_c2 -orbA orbb.
              case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by []].
           ++ by rewrite b1_eq_b2.
           ++ by rewrite c1_eq_c2.
        * (* a a --- b b --- c1 c2 *)
          have c1_neq_c2: c1 != c2 by rewrite sg_edgeNeq.
          case/orP: d1d2 => [/eqP d1_eq_d2 | d1_adj_d2 ].
          -- left.
             case: (orP b1c2b2c1)=> [b1c2b2c1' | b2_adj_c1].
             ++ case: (orP b1c2b2c1')=> [b1_dom_c2 |/eqP b2_eq_c1].
                ** case: (orP b1_dom_c2)=> [/eqP b1_eq_c2 | a1_adj_b2].
                   --- exists (hom_G4_def a1 b1 c1 d1).
                       +++ apply: h'_G4_inj; rewrite /=; try by done.
                           all: try by rewrite a1_eq_a2.
                           *** by move: a1a2b1b2 ; rewrite a1_eq_a2 b1_eq_b2 orbb.
                           *** by rewrite b1_eq_c2 eq_sym.
                           *** by rewrite b1_eq_b2.
                           *** by rewrite d1_eq_d2.
                       +++ apply: h'_copaw_hom; rewrite /=; try by done.
                           all: try by rewrite a1_eq_a2.
                           *** move: a1a2b1b2 ; rewrite a1_eq_a2 b1_eq_b2 orbb.
                               move: a1b2a2b1 ; rewrite a1_eq_a2 b1_eq_b2 -orbA orbb.
                               case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by []].
                           *** by rewrite b1_eq_c2 sg_sym.
                           *** by rewrite b1_eq_b2.
                           *** by rewrite d1_eq_d2.
                   --- have b1_neq_c2: b1 != c2 by rewrite sg_edgeNeq.
                       exists (hom_G4_def a1 b1 c2 d1).
                       +++ apply: h'_G4_inj; rewrite /=; try by done.
                           *** by move: a1a2b1b2 ; rewrite a1_eq_a2 b1_eq_b2 orbb.
                           *** by rewrite a1_eq_a2.
                           *** by rewrite b1_eq_b2.
                       +++ apply: h'_copaw_hom; rewrite /=; try by done.
                           *** move: a1a2b1b2 ; rewrite a1_eq_a2 b1_eq_b2 orbb.
                               move: a1b2a2b1 ; rewrite a1_eq_a2 b1_eq_b2 -orbA orbb.
                               case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by []].
                           *** by rewrite a1_eq_a2.
                           *** by rewrite b1_eq_b2.
                ** exists (hom_G4_def a1 b1 c2 d1).
                   --- apply: h'_G4_inj; rewrite /=; try by done.
                       +++ by move: a1a2b1b2 ; rewrite a1_eq_a2 b1_eq_b2 orbb.
                       +++ by rewrite a1_eq_a2.
                       +++ by rewrite b1_eq_b2 b2_eq_c1.
                       +++ by rewrite b1_eq_b2.
                   --- apply: h'_copaw_hom; rewrite /=; try by done.
                       +++ move: a1a2b1b2 ; rewrite a1_eq_a2 b1_eq_b2 orbb.
                           move: a1b2a2b1 ; rewrite a1_eq_a2 b1_eq_b2 -orbA orbb.
                           case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by []].
                       +++ by rewrite b1_eq_b2 b2_eq_c1.
                       +++ by rewrite a1_eq_a2.
                       +++ by rewrite b1_eq_b2.
           ++ exists (hom_G4_def a1 b1 c1 d1).
              ** apply: h'_G4_inj; rewrite /=; try by done.
                 all: try by rewrite a1_eq_a2.
                 --- by move: a1a2b1b2 ; rewrite a1_eq_a2 b1_eq_b2 orbb.
                 --- by rewrite b1_eq_b2 sg_edgeNeq.
                 --- by rewrite b1_eq_b2.
                 --- by rewrite d1_eq_d2.
              ** apply: h'_copaw_hom; rewrite /=; try by done.
                 all: try by rewrite a1_eq_a2.
                 all: try by rewrite b1_eq_b2.
                 --- move: a1a2b1b2 ; rewrite a1_eq_a2 b1_eq_b2 orbb.
                     move: a1b2a2b1 ; rewrite a1_eq_a2 b1_eq_b2 -orbA orbb.
                     case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by []].
                 --- by rewrite d1_eq_d2.
          -- left.
             case: (orP b1c2b2c1)=> [b1c2b2c1' | b2_adj_c1].
             ++ case: (orP b1c2b2c1')=> [b1_dom_c2 |/eqP b2_eq_c1].
                ** case: (orP b1_dom_c2)=> [/eqP b1_eq_c2 | b1_adj_c2].
                   --- exists (hom_G4_def a1 b1 c1 d2).
                       +++ apply: h'_G4_inj; rewrite /=; try by done.
                           *** by move: a1a2b1b2; rewrite a1_eq_a2 b1_eq_b2 orbb.
                           *** by rewrite a1_eq_a2.
                           *** by rewrite b1_eq_c2 eq_sym.
                       +++ apply: h'_copaw_hom; rewrite /=; try by done.
                           *** move: a1a2b1b2; rewrite a1_eq_a2 b1_eq_b2 orbb.
                               move: a1b2a2b1; rewrite a1_eq_a2 b1_eq_b2 -orbA orbb.
                               case/orP; [move/eqP=> ?; move/eqP; contradiction | by done].
                           *** by rewrite b1_eq_c2 sg_sym.
                           *** by rewrite a1_eq_a2.
                   --- exists (hom_G4_def a1 b1 c2 d1).
                       +++ apply: h'_G4_inj; rewrite /=; try by done.
                           *** by move: a1a2b1b2; rewrite a1_eq_a2 b1_eq_b2 orbb.
                           *** by rewrite a1_eq_a2.
                           *** by rewrite sg_edgeNeq.
                           *** by rewrite b1_eq_b2.
                       +++ apply: h'_copaw_hom; rewrite /=; try by done.
                           *** move: a1a2b1b2; rewrite a1_eq_a2 b1_eq_b2 orbb.
                               move: a1b2a2b1; rewrite a1_eq_a2 b1_eq_b2 -orbA orbb.
                               case/orP; [move/eqP=> ?; move/eqP; contradiction | by done].
                           *** by rewrite a1_eq_a2.
                           *** by rewrite b1_eq_b2.
                ** exists (hom_G4_def a1 b1 c2 d1).
                   --- apply: h'_G4_inj; rewrite /=; try by done.
                       +++ by move: a1a2b1b2; rewrite a1_eq_a2 b1_eq_b2 orbb.
                       +++ by rewrite a1_eq_a2.
                       +++ by rewrite b1_eq_b2 b2_eq_c1.
                       +++ by rewrite b1_eq_b2.
                   --- apply: h'_copaw_hom; rewrite /=; try by done.
                       +++ move: a1a2b1b2; rewrite a1_eq_a2 b1_eq_b2 orbb.
                           move: a1b2a2b1; rewrite a1_eq_a2 b1_eq_b2 -orbA orbb.
                           case/orP; [move/eqP=> ?; move/eqP; contradiction | by done].
                       +++ by rewrite b1_eq_b2 b2_eq_c1.
                       +++ by rewrite a1_eq_a2.
                       +++ by rewrite b1_eq_b2.
           ++ exists (hom_G4_def a1 b1 c1 d2).
              ** apply: h'_G4_inj; rewrite /=; try by done.
                 --- by move: a1a2b1b2 ; rewrite a1_eq_a2 b1_eq_b2 orbb.
                 --- by rewrite a1_eq_a2.
                 --- by rewrite b1_eq_b2 sg_edgeNeq.
              ** apply: h'_copaw_hom; rewrite /=; try by done.
                 --- move: a1a2b1b2; rewrite a1_eq_a2 b1_eq_b2 orbb.
                     move: a1b2a2b1; rewrite a1_eq_a2 b1_eq_b2 -orbA orbb.
                     case/orP; [move/eqP=> ?; move/eqP; contradiction | by done].
                 --- by rewrite b1_eq_b2.
                 --- by rewrite a1_eq_a2.
    + case/orP: c1c2 => [/eqP c1_eq_c2 | c1_adj_c2].
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
                       exists (hom_G4_def b2 b1 c2 d2).
                       +++ apply: h'_G4_inj; rewrite /=; try by done.
                           all: try by rewrite -a1_eq_b2.
                           *** apply/contraT; rewrite negbK => /eqP b2_eq_b1.
                               rewrite -b2_eq_b1 -a1_eq_b2 in b1_adj_c2.
                               by rewrite b1_adj_c2 in a1_nadj_c2.
                           *** by move: b1_adj_c2; apply/contraTneq => ->; rewrite sg_irrefl.
                           *** apply/contraT; rewrite negbK => /eqP c2_eq_d2.
                               by rewrite -c2_eq_d2 b1_adj_c2 in b1_nadj_d2.
                       +++ apply: h'_copaw_hom; rewrite /=; try by done.
                           all: try by rewrite -a1_eq_b2.
                           *** by rewrite sg_sym.
                           *** by rewrite -c1_eq_c2.
                   --- case: (orP b1c2b2c1)=> [b1c2b2c1' | b2_adj_c1].
                       +++ case: (orP b1c2b2c1')=> [b1_dom_c2 |/eqP b2_eq_c1];
                             last by rewrite -c1_eq_c2 -b2_eq_c1 a1_adj_b2 in a1_nadj_c2.
                           case: (orP b1_dom_c2)=> [/eqP b1_eq_c2 | b1_adj_c2].
                           *** exists (hom_G4_def a1 b2 b1 d1).
                               ---- apply: h'_G4_inj; rewrite /=; try by done.
                                    all: try by rewrite b1_eq_c2.
                                    ++++ by move: a1_adj_b2; apply/contraTneq => ->; rewrite sg_irrefl.
                                    ++++ by rewrite a1_eq_a2.
                                    ++++ by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_irrefl.
                               ---- apply: h'_copaw_hom; rewrite /=; try by done.
                                    all: try by rewrite b1_eq_c2.
                                    ++++ by rewrite sg_sym.
                                    ++++ by rewrite a1_eq_a2.
                           *** case: (boolP (c1 -- b2))=> [c1_adj_b2 | c1_nadj_b2].
                               ---- exists (hom_G4_def c1 b2 a1 d1).
                                    ++++ apply: h'_G4_inj; rewrite /=; try by done.
                                         **** by move: c1_adj_b2; apply/contraTneq => ->; rewrite sg_irrefl.
                                         **** by rewrite a1_eq_a2 eq_sym.
                                         **** by rewrite c1_eq_c2.
                                         **** by move: a1_adj_b2; apply/contraTneq => ->; rewrite sg_irrefl.
                                         **** by rewrite a1_eq_a2.
                                    ++++ apply: h'_copaw_hom; rewrite /=; try by done.
                                         **** by rewrite sg_sym.
                                         **** by rewrite a1_eq_a2 sg_sym.
                                         **** by rewrite c1_eq_c2.
                                         **** by rewrite a1_eq_a2.
                               ---- case: (boolP (b2 -- d2))=> [b2_adj_d2 | b2_nadj_d2].
                                    ++++ exists (hom_G4_def d2 b2 a2 c1).
                                         **** apply: h'_G4_inj; rewrite /=; try by done. 
                                              ----- by move: b2_adj_d2; apply/contraTneq => ->; rewrite sg_irrefl.
                                              ----- by rewrite -a1_eq_a2 eq_sym.
                                              ----- by rewrite eq_sym.
                                              ----- by move: a1_adj_b2; apply/contraTneq => ->; rewrite a1_eq_a2 sg_irrefl.
                                              ----- by move: a1_adj_b2; apply/contraTneq => ->; rewrite c1_eq_c2.
                                         **** apply: h'_copaw_hom; rewrite /=; try by done.
                                              all: try by rewrite sg_sym.
                                              all: by rewrite -a1_eq_a2 sg_sym.
                                    ++++ exists (hom_G4_def c2 b1 b2 d2).
                                         **** apply: h'_G4_inj; rewrite /=; try by done.
                                              ----- by move: b1_adj_c2; apply/contraTneq => ->; rewrite sg_irrefl.
                                              ----- by move: a1_adj_b2; apply/contraTneq => <-.
                                              ----- by rewrite -c1_eq_c2.
                                              ----- by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_irrefl.
                                              ----- by move: b1_adj_b2; apply/contraTneq => ->.
                                         **** apply: h'_copaw_hom; rewrite /=; try by done.
                                              all: try by rewrite -c1_eq_c2.
                                              by rewrite sg_sym.
                      +++ exists (hom_G4_def a1 b2 c1 d1).
                          *** apply: h'_G4_inj; rewrite /=; try by done.
                              all: try by rewrite a1_eq_a2.
                              ---- by move: a1_adj_b2; apply/contraTneq => ->; rewrite sg_irrefl.
                              ---- by move: b2_adj_c1; apply/contraTneq => ->; rewrite sg_irrefl.
                              ---- by rewrite c1_eq_c2.
                          *** apply: h'_copaw_hom; rewrite /=; try by done.
                              all: try by rewrite a1_eq_a2.
                              by rewrite c1_eq_c2.
                ** case: (orP b1c2b2c1)=> [b1c2b2c1' | b2_adj_c1].
                   --- case: (orP b1c2b2c1')=> [b1_dom_c2 |/eqP b2_eq_c1];
                         last by move: a2_nadj_c1; rewrite -b2_eq_c1 a2_eq_b1 b1_adj_b2.
                       by case: (orP b1_dom_c2)=> [/eqP b1_eq_c2 | b1_adj_c2];
                            [move: a1a2c1c2; rewrite a1_eq_a2 c1_eq_c2 a2_eq_b1 b1_eq_c2 eq_refl
                               | move: a1_nadj_c2; rewrite a1_eq_a2 a2_eq_b1 b1_adj_c2].
                   --- exists (hom_G4_def b1 b2 c1 d1).
                       +++ apply: h'_G4_inj; rewrite /=; try by done.
                           all: try by rewrite -a2_eq_b1.
                           *** by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_irrefl.
                           *** by move: b2_adj_c1; apply/contraTneq => ->; rewrite sg_irrefl.
                           *** by rewrite c1_eq_c2.
                       +++ apply: h'_copaw_hom; rewrite /=; try by done.
                           all: try by rewrite -a2_eq_b1.
                           by rewrite c1_eq_c2.
             ++ case: (orP b1c2b2c1)=> [b1c2b2c1' | b2_adj_c1].
                   ** case: (orP b1c2b2c1')=> [b1_dom_c2 |/eqP b2_eq_c1].
                      --- case: (orP b1_dom_c2)=> [/eqP b1_eq_c2 | b1_adj_c2];
                            first by move: a2_nadj_c1; rewrite c1_eq_c2 -b1_eq_c2 a2_adj_b1.
                          exists (hom_G4_def a2 b1 c2 d2).
                          +++ apply: h'_G4_inj; rewrite /=; try by done.
                              all: try by rewrite -a1_eq_a2.
                              *** by move: a2_adj_b1; apply/contraTneq => ->; rewrite sg_irrefl.
                              *** by move: b1_adj_c2; apply/contraTneq => ->; rewrite sg_irrefl.
                              *** by rewrite -c1_eq_c2.
                          +++ apply: h'_copaw_hom; rewrite /=; try by done.
                              all: try by rewrite -a1_eq_a2.
                              by rewrite -c1_eq_c2.
                      --- exists (hom_G4_def a2 b1 c2 d2).
                          +++ apply: h'_G4_inj; rewrite /=; try by done.
                              all: try by rewrite -a1_eq_a2.
                              *** by move: a2_adj_b1; apply/contraTneq => ->; rewrite sg_irrefl.
                              *** by move: b1_adj_b2; apply/contraTneq => ->; rewrite -c1_eq_c2 -b2_eq_c1 sg_irrefl.
                              *** by rewrite -c1_eq_c2.
                          +++ apply: h'_copaw_hom; rewrite /=; try by done.
                              all: try by rewrite -a1_eq_a2.
                              *** by rewrite -c1_eq_c2 -b2_eq_c1.
                              *** by rewrite -c1_eq_c2.
                   ** case: (boolP (a1 -- b2))=> [a1_adj_b2 | a1_nadj_b2].
                      --- exists (hom_G4_def a1 b2 c1 d1).
                          +++ apply: h'_G4_inj; rewrite /=; try by done.
                              all: try by rewrite a1_eq_a2.
                              *** by move: a1_adj_b2; apply/contraTneq => <-; rewrite sg_irrefl.
                              *** by move: b2_adj_c1; apply/contraTneq => ->; rewrite sg_irrefl.
                              *** by rewrite c1_eq_c2.
                          +++ apply: h'_copaw_hom; rewrite /=; try by done.
                              all: try by rewrite a1_eq_a2.
                              by rewrite c1_eq_c2.
                      --- case: (boolP (b2 -- d2))=> [b2_adj_d2 | b2_nadj_d2].
                          +++ exists (hom_G4_def d2 b2 c1 a1).
                              *** apply: h'_G4_inj; rewrite /=; try by done.
                                  all: try by rewrite eq_sym.
                                  ---- by rewrite eq_sym sg_edgeNeq.
                                  ---- by rewrite sg_edgeNeq.
                                  ---- by move: b2_adj_c1; apply/contraTneq => ->; rewrite a1_eq_a2.
                                  ---- by rewrite c1_eq_c2 eq_sym.
                              *** apply: h'_copaw_hom; rewrite /=; try by done.
                                  all: try by rewrite sg_sym.
                                  by rewrite a1_eq_a2 sg_sym.
                          +++ exists (hom_G4_def a1 b1 b2 d2).
                              *** apply: h'_G4_inj; rewrite /=; try by done.
                                  ---- by move: a2_adj_b1; apply/contraTneq => <-; rewrite a1_eq_a2 sg_irrefl.
                                  ---- by move: b2_adj_c1; apply/contraTneq => <-; rewrite a1_eq_a2.
                                  ---- by rewrite sg_edgeNeq.
                                  ---- by move: b1_adj_b2; apply/contraTneq => ->.
                              *** apply: h'_copaw_hom; rewrite /=; try by done.
                                  by rewrite a1_eq_a2.
      -- by left; apply/(@case_aa_b1b2_c1c2 h a1 a2 b1 b2 c1 c2 d1 d2).
  - have a1_neq_a2: a1 != a2 by rewrite sg_edgeNeq.
    case/orP: b1b2 => [/eqP b1_eq_b2 | b1_adj_b2 ].
    + case/orP: c1c2 => [/eqP c1_eq_c2 | c1_adj_c2 ].
      * have b2_adj_c2: b2 -- c2.
          rewrite c1_eq_c2 b1_eq_b2 orbb in b1b2c1c2.
          by rewrite  c1_eq_c2 b1_eq_b2 -orbA orbb (negbTE b1b2c1c2) /= in b1c2b2c1.
        case/orP: d1d2 => [/eqP d1_eq_d2 | d1_adj_d2 ].
        -- left.
           case: (orP a1b2a2b1)=> [a1b2a2b1' | a2_adj_b1].
           ++ case: (orP a1b2a2b1')=> [b1_dom_c2 |/eqP a2_eq_b1].
              ** case: (orP b1_dom_c2)=> [/eqP a1_eq_b2 | a1_adj_b2].
                 --- exists (hom_G4_def a2 b2 c2 d2).
                     +++ apply: h'_G4_inj; rewrite /=; try by done.
                         all: try by rewrite -d1_eq_d2.
                         *** by rewrite -a1_eq_b2 eq_sym.
                         *** by rewrite -c1_eq_c2.
                         *** by rewrite -a1_eq_b2.
                     +++ apply: h'_copaw_hom; rewrite /=; try by done.
                         all: try by rewrite -c1_eq_c2.
                         *** by rewrite -a1_eq_b2 sg_sym.
                         *** by rewrite -d1_eq_d2.
                         *** by rewrite -b1_eq_b2.
                 --- exists (hom_G4_def c2 b2 a1 d2).
                     +++ apply: h'_G4_inj; rewrite /=; try by done.
                         all: try by rewrite -d1_eq_d2.
                         *** by move: b1b2c1c2; rewrite c1_eq_c2 b1_eq_b2 orbb eq_sym.
                         *** by rewrite eq_sym.
                         *** by rewrite eq_sym sg_edgeNeq.
                     +++ apply: h'_copaw_hom; rewrite /=; try by done.
                         all: try by rewrite sg_sym.
                         *** by rewrite -c1_eq_c2.
                         *** by rewrite -b1_eq_b2.
              ** exists (hom_G4_def c2 b2 a1 d2).
                 --- apply: h'_G4_inj; rewrite /=; try by done.
                     +++ by move: b1b2c1c2 ; rewrite c1_eq_c2 b1_eq_b2 orbb eq_sym.
                     +++ by rewrite eq_sym.
                     +++ by rewrite -c1_eq_c2.
                     +++ by rewrite -b1_eq_b2 -a2_eq_b1 eq_sym.
                     +++ by rewrite -b1_eq_b2.
                 --- apply: h'_copaw_hom; rewrite /=; try by done.
                     all: try by rewrite sg_sym.
                     +++ by rewrite -b1_eq_b2 -a2_eq_b1 sg_sym.
                     +++ by rewrite -c1_eq_c2.
                     +++ by rewrite -b1_eq_b2.
           ++ exists (hom_G4_def c2 b2 a2 d2).
              ** apply: h'_G4_inj; rewrite /=; try by done.
                 --- by move: b1b2c1c2; rewrite c1_eq_c2 b1_eq_b2 orbb eq_sym.
                 --- by rewrite -c1_eq_c2 eq_sym.
                 --- by rewrite -c1_eq_c2.
                 --- by rewrite -b1_eq_b2 eq_sym sg_edgeNeq.
                 --- by rewrite -b1_eq_b2.
                 --- by rewrite -d1_eq_d2.
              ** apply: h'_copaw_hom; rewrite /=; try by done.
                 --- by rewrite sg_sym.
                 --- by rewrite -b1_eq_b2 sg_sym.
                 --- by rewrite -c1_eq_c2 sg_sym.
                 --- by rewrite -c1_eq_c2.
                 --- by rewrite -b1_eq_b2.
                 --- by rewrite -d1_eq_d2.
        -- left.
           case: (orP a1b2a2b1)=> [a1b2a2b1' | a2_adj_b1].
           ++ case: (orP a1b2a2b1')=> [a1_dom_b2 |/eqP a2_eq_b1].
              ** case: (orP a1_dom_b2)=> [/eqP a1_eq_b2 | a1_adj_b2].
                 --- exists (hom_G4_def c2 b2 a2 d1).
                     +++ apply: h'_G4_inj; rewrite /=; try by done.
                         *** by move: b1b2c1c2 ; rewrite c1_eq_c2 b1_eq_b2 orbb eq_sym.
                         *** by rewrite -c1_eq_c2 eq_sym.
                         *** by rewrite -a1_eq_b2.
                     +++ apply: h'_copaw_hom; rewrite /=; try by done.
                         *** by rewrite sg_sym.
                         *** by rewrite -a1_eq_b2.
                         *** by rewrite -c1_eq_c2 sg_sym.
                 --- exists (hom_G4_def c2 b2 a1 d2).
                     +++ apply: h'_G4_inj; rewrite /=; try by done.
                         *** by move: b1b2c1c2 ; rewrite c1_eq_c2 b1_eq_b2 orbb eq_sym.
                         *** by rewrite eq_sym.
                         *** by rewrite -c1_eq_c2.
                         *** by rewrite eq_sym sg_edgeNeq.
                         *** by rewrite -b1_eq_b2.
                     +++ apply: h'_copaw_hom; rewrite /=; try by done.
                         all: try by rewrite sg_sym.
                         *** by rewrite -c1_eq_c2.
                         *** by rewrite -b1_eq_b2.
              ** exists (hom_G4_def c2 b2 a1 d2).
                 --- apply: h'_G4_inj; rewrite /=; try by done.
                     +++ by move: b1b2c1c2 ; rewrite c1_eq_c2 b1_eq_b2 orbb eq_sym.
                     +++ by rewrite eq_sym.
                     +++ by rewrite -c1_eq_c2.
                     +++ by rewrite -b1_eq_b2 -a2_eq_b1 eq_sym sg_edgeNeq.
                     +++ by rewrite -b1_eq_b2.
                 --- apply: h'_copaw_hom; rewrite /=; try by done.
                     all: try by rewrite sg_sym.
                     +++ by rewrite -b1_eq_b2 -a2_eq_b1 sg_sym.
                     +++ by rewrite -c1_eq_c2.
                     +++ by rewrite -b1_eq_b2.
           ++ exists (hom_G4_def c2 b2 a2 d1).
              ** apply: h'_G4_inj; rewrite /=; try by done.
                 --- by move: b1b2c1c2 ; rewrite c1_eq_c2 b1_eq_b2 orbb eq_sym.
                 --- by rewrite -c1_eq_c2 eq_sym.
                 --- by rewrite -b1_eq_b2 eq_sym sg_edgeNeq.
              ** apply: h'_copaw_hom; rewrite /=; try by done.
                 --- by rewrite sg_sym.
                 --- by rewrite -b1_eq_b2 sg_sym.
                 --- by rewrite -c1_eq_c2 sg_sym.
      * case/orP: d1d2 => [/eqP d1_eq_d2 | d1_adj_d2 ].
        -- have c1_neq_c2: c1 != c2 by rewrite sg_edgeNeq.
           left.
           case: (boolP (a1 -- b2))=> [a1_adj_b2 | a1_nadj_b2].
           ++ have b1_neq_c2: b1 != c2 by move: a1_adj_b2; rewrite b1_eq_b2; apply/contraTneq => ->.
              case: (boolP (b1 -- c2))=> [b1_adj_c2 | b1_nadj_c2].
              ** exists (hom_G4_def a1 b2 c2 d1).
                 --- apply: h'_G4_inj; rewrite /=; try by done.
                     +++ by rewrite sg_edgeNeq.
                     +++ by rewrite d1_eq_d2.
                     +++ by rewrite -b1_eq_b2 sg_edgeNeq.
                 --- apply: h'_copaw_hom; rewrite /=; try by done.
                     +++ by rewrite -b1_eq_b2.
                     +++ by rewrite d1_eq_d2.
              ** case: (boolP (a2 -- b1))=> [a2_adj_b1 | a2_nadj_b1].
                 --- exists (hom_G4_def a2 b1 c1 d2).
                     +++ apply: h'_G4_inj; rewrite /=; try by done.
                         *** by rewrite sg_edgeNeq.
                         *** by rewrite -d1_eq_d2.
                         *** by move: c1_adj_c2; apply/contraTneq => <-.
                     +++ apply: h'_copaw_hom; rewrite /=; try by done.
                         *** have b2_neq_c1: b2 != c1 by move: c1_adj_c2; apply/contraTneq => <-; rewrite -b1_eq_b2.
                             by rewrite (negbTE b2_neq_c1) (negbTE b1_neq_c2) (negbTE b1_nadj_c2) -b1_eq_b2 in b1c2b2c1.
                         *** by rewrite -d1_eq_d2.
                 --- exists (hom_G4_def a2 a1 b2 d1).
                     +++ apply: h'_G4_inj; rewrite /=; try by done.
                         *** by rewrite eq_sym sg_edgeNeq.
                         *** move: b1c2b2c1; apply/contraTneq => <-.
                             by rewrite !negb_or b1_nadj_c2 a2_nadj_c1 a2_neq_c1 b1_neq_c2.
                         *** by rewrite sg_edgeNeq.
                         *** by rewrite d1_eq_d2.
                     +++ apply: h'_copaw_hom; rewrite /=; try by done.
                         *** by rewrite sg_sym.
                         *** by rewrite -b1_eq_b2.
                         *** by rewrite d1_eq_d2.
           ++ case: (boolP (a1 == b1))=> [/eqP a1_eq_b1 | a1_neq_b1].
              ** exists (hom_G4_def a1 c1 c2 d1).
                 --- apply: h'_G4_inj; rewrite /=; try by done.
                     +++ by move: c1_adj_c2; apply/contraTneq => <-.
                     +++ by rewrite a1_eq_b1 b1_eq_b2.
                     +++ by rewrite d1_eq_d2.
                 --- apply: h'_copaw_hom; rewrite /=; try by done.
                     all: try by rewrite d1_eq_d2.
                     have a1_neq_c1: a1 != c1 by move: c1_adj_c2; apply/contraTneq => <-.
                     by rewrite -b1_eq_b2 -a1_eq_b1 (negbTE a1_neq_c2) (negbTE a1_nadj_c2) (negbTE a1_neq_c1) in b1c2b2c1.
              ** exists (hom_G4_def a1 a2 b1 d2).
                 --- apply: h'_G4_inj; rewrite /=; try by done.
                     +++ by rewrite b1_eq_b2; move: a1_nadj_b2; apply/contraTneq => <-; rewrite a1_adj_a2.
                     +++ by rewrite -d1_eq_d2.
                 --- apply: h'_copaw_hom; rewrite /=; try by done.
                     +++ have a2_neq_b1: a2 != b1 by rewrite b1_eq_b2; move: a1_nadj_b2; apply/contraTneq => <-; rewrite a1_adj_a2.
                         rewrite b1_eq_b2 in a1_neq_b1.
                         by rewrite (negbTE a1_neq_b1) (negbTE a1_nadj_b2) (negbTE a2_neq_b1) in a1b2a2b1.
                     +++ by rewrite b1_eq_b2.
                     +++ by rewrite -d1_eq_d2.
        -- case: (boolP (a1 -- c1))=> [a1_adj_c1 | a1_nadj_c1].
           ++ case: (boolP (a2 -- d2))=> [a2_adj_d2 | a2_nadj_d2]; last first.
              ** left; exists (hom_G4_def a2 a1 c1 d2).
                 --- apply: h'_G4_inj; rewrite /=; try by done.
                     +++ by rewrite eq_sym sg_edgeNeq.
                     +++ by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
                     +++ by rewrite sg_edgeNeq.
                 --- apply: h'_copaw_hom; rewrite /=; try by done.
                     by rewrite sg_sym.
              ** case: (boolP (a2 -- b1))=> [a2_adj_b1 | a2_nadj_b1]; last first.
                 --- left; exists (hom_G4_def a2 d2 d1 b1).
                     +++ apply: h'_G4_inj; rewrite /=; try by done.
                         *** by rewrite sg_edgeNeq.
                         *** by move: a2_adj_d2; apply/contraTneq => ->.
                         *** by rewrite eq_sym sg_edgeNeq.
                         *** by rewrite eq_sym.
                         *** by rewrite b1_eq_b2 eq_sym.
                     +++ apply: h'_copaw_hom; rewrite /=; try by done.
                         all: try by rewrite sg_sym.
                         by rewrite b1_eq_b2 sg_sym.
                 --- case: (boolP (b2 -- c1))=> [b2_adj_c1 | b2_nadj_c1]; last first.
                     +++ left; exists (hom_G4_def d2 a2 b1 c1).
                         *** apply: h'_G4_inj; rewrite /=; try by done.
                             all: try by rewrite eq_sym.
                             ---- by rewrite eq_sym sg_edgeNeq.
                             ---- by rewrite sg_edgeNeq.
                             ---- by move: a2_adj_b1; apply/contraTneq => ->.
                         *** apply: h'_copaw_hom; rewrite /=; try by done.
                             all: try by rewrite sg_sym.
                             by rewrite b1_eq_b2.
                     +++ case: (boolP (c1 -- d1))=> [c1_adj_d1 | c1_nadj_d1]; last first.
                         *** left; exists (hom_G4_def a2 d2 d1 c1).
                             ---- apply: h'_G4_inj; rewrite /=; try by done.
                                  ++++ by rewrite sg_edgeNeq.
                                  ++++ by rewrite eq_sym sg_edgeNeq.
                                  ++++ by rewrite eq_sym.
                                  ++++ by move: d1_adj_d2; apply/contraTneq => ->.
                             ---- apply: h'_copaw_hom; rewrite /=; try by done.
                                  all: try by rewrite sg_sym.
                         *** case: (boolP (a2 -- c2))=> [a2_adj_c2 | a2_nadj_c2]; last first.
                             ---- left; exists (hom_G4_def c2 c1 d1 a2).
                                  ++++ apply: h'_G4_inj; rewrite /=; try by done.
                                       **** by rewrite eq_sym sg_edgeNeq.
                                       **** by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                       **** by rewrite sg_edgeNeq.
                                       **** by rewrite eq_sym.
                                       **** by move: c1_adj_d1; apply/contraTneq => ->; rewrite sg_sym.
                                  ++++ apply: h'_copaw_hom; rewrite /=; try by done.
                                       all: try by rewrite sg_sym.
                             ---- case: (boolP (a1 -- d1))=> [a1_adj_d1 | a1_nadj_d1]; last first.
                                  ++++ left; exists (hom_G4_def a1 a2 c2 d1).
                                       **** apply: h'_G4_inj; rewrite /=; try by done.
                                            all: try by rewrite sg_edgeNeq.
                                            by move: a1_adj_a2; apply/contraTneq => ->; rewrite sg_sym.
                                       **** by apply: h'_copaw_hom.
                                  ++++ case: (boolP (c2 -- d2))=> [c2_adj_d2 | c2_nadj_d2]; last first.
                                       **** left; exists (hom_G4_def a1 c1 c2 d2).
                                            ----- apply: h'_G4_inj; rewrite /=; try by done.
                                                  all: try by rewrite sg_edgeNeq.
                                                  by move: c1_adj_c2; apply/contraTneq => ->.
                                            ----- by apply: h'_copaw_hom.
                                       **** case: (boolP (a1 -- b2))=> [a1_adj_b2 | a1_nadj_b2]; last first.
                                            ----- left; exists (hom_G4_def a1 c1 b2 d2).
                                                  +++++ apply: h'_G4_inj; rewrite /=; try by done.
                                                        ***** by rewrite sg_edgeNeq.
                                                        ***** by move: a1_adj_d1; apply/contraTneq => ->.
                                                        ***** by rewrite eq_sym sg_edgeNeq.
                                                        ***** by rewrite -b1_eq_b2.
                                                  +++++ apply: h'_copaw_hom; rewrite /=; try by done.
                                                        ***** by rewrite sg_sym.
                                                        ***** by rewrite -b1_eq_b2.
                                            ----- case: (boolP (b1 -- c2))=> [b1_adj_c2 | b1_nadj_c2]; last first.
                                                  +++++ left; exists (hom_G4_def b1 a2 c2 d1).
                                                        ***** apply: h'_G4_inj; rewrite /=; try by done.
                                                              ------ by rewrite eq_sym sg_edgeNeq.
                                                              ------ by move: c2_adj_d2; apply/contraTneq => <-.
                                                              ------ by rewrite b1_eq_b2.
                                                              ------ by rewrite sg_edgeNeq.
                                                        ***** apply: h'_copaw_hom; rewrite /=; try by done.
                                                              ------ by rewrite sg_sym.
                                                              ------ by rewrite b1_eq_b2.
                                                  +++++ right; left; exists (hom_G7_def a1 c2 d1 a2 c1 d2 b1).
                                                        ***** apply: h'_G7_inj; rewrite /=; try by done.
                                                              all: try by rewrite eq_sym.
                                                              all: try by rewrite sg_edgeNeq.
                                                              all: try by rewrite eq_sym sg_edgeNeq.
                                                              ------ by rewrite b1_eq_b2 sg_edgeNeq.
                                                              ------ by rewrite eq_sym b1_eq_b2.
                                                              ------ by rewrite b1_eq_b2 eq_sym sg_edgeNeq.
                                                        ***** apply: h'_G7_1_hom; rewrite /=; try by done.
                                                              all: try by rewrite sg_sym.
                                                              all: try by rewrite b1_eq_b2 sg_sym.
                                                              by rewrite b1_eq_b2.
           ++ case: (boolP (c2 -- d2))=> [c2_adj_d2 | c2_nadj_d2].
              ** left; exists (hom_G4_def c1 c2 d2 a1).
                 --- apply: h'_G4_inj; rewrite /=; try by done.
                     all: try by rewrite eq_sym.
                     all: try by rewrite sg_edgeNeq.
                     by move: c1_adj_c2; apply/contraTneq => ->.
                 --- apply: h'_copaw_hom; rewrite /=; try by done.
                     all: by rewrite sg_sym.
              ** case: (boolP (a1 -- d1))=> [a1_adj_d1 | a1_nadj_d1].
                 --- left; exists (hom_G4_def a1 d1 d2 c2).
                     +++ apply: h'_G4_inj; rewrite /=; try by done.
                         all: try by rewrite sg_edgeNeq.
                         *** by rewrite eq_sym.
                         *** by move: c1_adj_c2; apply/contraTneq => <-.
                     +++ apply: h'_copaw_hom; rewrite /=; try by done.
                         all: by rewrite sg_sym.
                 --- case: (boolP (a2 -- c2))=> [a2_adj_c2 | a2_nadj_c2].
                     +++ left; exists (hom_G4_def a1 a2 c2 d1).
                         *** apply: h'_G4_inj; rewrite /=; try by done.
                             all: try by rewrite sg_edgeNeq.
                             by move: d1_adj_d2; apply/contraTneq => <-.
                         *** by apply: h'_copaw_hom.
                     +++ case: (boolP (a2 -- d2))=> [a2_adj_d2 | a2_nadj_d2].
                         *** left; exists (hom_G4_def a2 d2 d1 c2).
                            ---- apply: h'_G4_inj; rewrite /=; try by done.
                                 ++++ by rewrite sg_edgeNeq.
                                 ++++ by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                                 ++++ by rewrite eq_sym sg_edgeNeq.
                                 ++++ by move: d1_adj_d2; apply/contraTneq => ->; rewrite sg_sym.
                                 ++++ by rewrite eq_sym.
                            ---- apply: h'_copaw_hom; rewrite /=; try by done.
                                 all: by rewrite sg_sym.
                         *** case: (boolP (c1 -- d1))=> [c1_adj_d1 | c1_nadj_d1].
                             ---- left; exists (hom_G4_def c1 d1 d2 a1).
                                  ++++ apply: h'_G4_inj; rewrite /=; try by done.
                                       all: try by rewrite sg_edgeNeq.
                                       **** by move: c1_adj_c2; apply/contraTneq => ->.
                                       **** by move: d1_adj_d2; apply/contraTneq => ->.
                                       **** by rewrite eq_sym.
                                  ++++ apply: h'_copaw_hom; rewrite /=; try by done.
                                       all: by rewrite sg_sym.
                             ---- case: (boolP (a2 -- b1))=> [a2_adj_b1 | a2_nadj_b1]; last first.
                                  ++++ have a2_neq_c2: a2 != c2 by move: a1_adj_a2; apply/contraTneq => ->.
                                       have a1_neq_b2: a1 != b2 by move: a1_adj_a2; apply/contraTneq => ->; rewrite -b1_eq_b2 sg_sym.
                                       have a2_neq_b1: a2 != b1.
                                         move: b1c2b2c1; rewrite -b1_eq_b2; apply/contraTneq => <-.
                                         by rewrite !negb_or a2_nadj_c2 a2_nadj_c1 a2_neq_c1 a2_neq_c2.
                                       left; exists (hom_G4_def a2 a1 b2 d2).
                                       **** apply: h'_G4_inj; rewrite /=; try by done.
                                            all: try by rewrite -b1_eq_b2.
                                            ----- by rewrite eq_sym sg_edgeNeq.
                                            ----- by move: a1_adj_a2; apply/contraTneq => ->.
                                       **** apply: h'_copaw_hom; rewrite /=; try by done.
                                            all: try by rewrite -b1_eq_b2.
                                            ----- by rewrite sg_sym.
                                            ----- by rewrite (negbTE a1_neq_b2) (negbTE a2_neq_b1) (negbTE a2_nadj_b1) /= orbC /= orbC /= in a1b2a2b1.
                                  ++++ case: (boolP (b2 -- c1))=> [b2_adj_c1 | b2_nadj_c1].
                                       **** left; exists (hom_G4_def a2 b1 c1 d2).
                                            ----- apply: h'_G4_inj; rewrite /=; try by done.
                                                  +++++ by rewrite sg_edgeNeq.
                                                  +++++ by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
                                                  +++++ by move: a2_adj_b1; apply/contraTneq => ->.
                                            ----- apply: h'_copaw_hom; rewrite /=; try by done.
                                                  by rewrite b1_eq_b2.
                                       **** have b1_neq_c2: b1 != c2 by move: a2_adj_b1; apply/contraTneq => ->. 
                                            have b2_neq_c1: b2 != c1 by rewrite -b1_eq_b2; move: a2_adj_b1; apply/contraTneq => ->.
                                            left; exists (hom_G4_def a2 b1 c2 d1).
                                            ----- apply: h'_G4_inj; rewrite /=; try by done.
                                                  +++++ by rewrite sg_edgeNeq.
                                                  +++++ by move: a1_adj_a2; apply/contraTneq => ->.
                                                  +++++ by move: a2_adj_b1; apply/contraTneq => ->.
                                            ----- apply: h'_copaw_hom; rewrite /=; try by done.
                                                  +++++ by rewrite (negbTE b1_neq_c2) (negbTE b2_neq_c1) (negbTE b2_nadj_c1) /= orbC /= orbC /= in b1c2b2c1.
                                                  +++++ by rewrite b1_eq_b2.
    + have b1_neq_b2 : b1 != b2 by rewrite sg_edgeNeq.
      case/orP: c1c2 => [/eqP c1_eq_c2 | c1_adj_c2].
      * left; apply/(@case_aa_b1b2_c1c2 h c1 c2 b1 b2 a1 a2 d1 d2); try by done.
        all: try by rewrite eq_sym.
        all: try by rewrite sg_sym.
        -- case: (orP b1c2b2c1) => [/orP H | H]; last by do 2 (apply/orP; left); apply/orP; right; rewrite sg_sym.
           case: H => [/orP H' | H']; last by do 3 (apply/orP; left); rewrite eq_sym.
           case: H' => [? | ?]; first by apply/orP; left; apply/orP; right; rewrite eq_sym.
           by apply/orP; right; rewrite sg_sym.
        -- case: (orP a1b2a2b1) => [/orP H | H]; last by do 2 (apply/orP; left); apply/orP; right; rewrite sg_sym.
           case: H => [/orP H' | H']; last by do 3 (apply/orP; left); rewrite eq_sym.
           case: H' => [? | ?]; first by apply/orP; left; apply/orP; right; rewrite eq_sym.
           by apply/orP; right; rewrite sg_sym.
      * have c1_neq_c2: c1 != c2 by rewrite sg_edgeNeq.
        have a1_neq_c1: a1 != c1 by move: c1_adj_c2; apply/contraTneq => <-.
        have a2_neq_c2: a2 != c2 by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
        case/orP: d1d2 => [/eqP d1_eq_d2 | d1_adj_d2].
        -- case: (boolP (a1 -- c1))=> [a1_adj_c1 | a1_nadj_c1].
           ++ left; exists (hom_G4_def a2 a1 c1 d2).
              ** apply: h'_G4_inj; rewrite /=; try by done.
                 --- by rewrite eq_sym sg_edgeNeq.
                 --- by rewrite -d1_eq_d2.
              ** apply: h'_copaw_hom; rewrite /=; try by done.
                 --- by rewrite sg_sym.
                 --- by rewrite -d1_eq_d2.
           ++ case: (boolP (a2 -- c2))=> [a2_adj_c2 | a2_nadj_c2].
              ** left; exists (hom_G4_def a1 a2 c2 d1).
                 --- apply: h'_G4_inj; rewrite /=; try by done.
                     all: try by rewrite sg_edgeNeq.
                     by rewrite d1_eq_d2.
                 --- apply: h'_copaw_hom; rewrite /=; try by done.
                     by rewrite d1_eq_d2.
              ** case: (orP a1b2a2b1)=> [a1b2a2b1' | a2_adj_b1].
                 --- case: (orP a1b2a2b1')=> [a1_dom_b2 |/eqP a2_eq_b1].
                     +++ case: (orP a1_dom_b2)=> [/eqP a1_eq_b2 | a1_adj_b2].
                         *** case: (boolP (a2 -- b1))=> [a2_adj_b1 | a2_nadj_b1]; last first.
                             ---- left; exists (hom_G4_def a2 b2 b1 d1).
                                  ++++ apply: h'_G4_inj; rewrite /=; try by done.
                                       **** by rewrite -a1_eq_b2 eq_sym sg_edgeNeq.
                                       **** move: b1c2b2c1; apply/contraTneq => <-.
                                            by rewrite -a1_eq_b2 !negb_or a2_neq_c2 a1_neq_c1 a1_nadj_c1 a2_nadj_c2 /=.
                                       **** by rewrite eq_sym sg_edgeNeq.
                                       **** by rewrite d1_eq_d2.
                                  ++++ apply: h'_copaw_hom; rewrite /=; try by done.
                                       **** by rewrite -a1_eq_b2 sg_sym.
                                       **** by rewrite sg_sym.
                                       **** by rewrite d1_eq_d2.
                             ---- case: (boolP (b1 -- c2))=> [b1_adj_c2 | b1_nadj_c2].
                                  ++++ left; exists (hom_G4_def b2 b1 c2 d1).
                                       **** apply: h'_G4_inj; rewrite /=; try by done.
                                            ----- by rewrite eq_sym sg_edgeNeq.
                                            ----- by rewrite -a1_eq_b2.
                                            ----- by rewrite sg_edgeNeq.
                                            ----- by rewrite d1_eq_d2.
                                       **** apply: h'_copaw_hom; rewrite /=; try by done.
                                            ----- by rewrite sg_sym.
                                            ----- by rewrite -a1_eq_b2.
                                            ----- by rewrite d1_eq_d2.
                                  ++++ have b1_neq_c2: b1 != c2 by move: a2_adj_b1; apply/contraTneq => ->.
                                       have b2_neq_c1: b2 != c1 by move: c1_adj_c2; apply/contraTneq => <-; rewrite -a1_eq_b2.
                                       left; exists (hom_G4_def a2 b2 c1 d1).
                                       **** apply: h'_G4_inj; rewrite /=; try by done.
                                            ----- by rewrite -a1_eq_b2 eq_sym sg_edgeNeq.
                                            ----- by rewrite d1_eq_d2.
                                       **** apply: h'_copaw_hom; rewrite /=; try by done.
                                            ----- by rewrite -a1_eq_b2 sg_sym.
                                            ----- by rewrite (negbTE b1_neq_c2) (negbTE b2_neq_c1) (negbTE b1_nadj_c2) in b1c2b2c1.
                                            ----- by rewrite d1_eq_d2.
                         *** case: (boolP (b2 -- c1))=> [b2_adj_c1 | b2_nadj_c1].
                             ---- left; exists (hom_G4_def a1 b2 c1 d2).
                                  ++++ apply: h'_G4_inj; rewrite /=; try by done.
                                       all: try by rewrite sg_edgeNeq.
                                       by rewrite -d1_eq_d2.
                                  ++++ apply: h'_copaw_hom; rewrite /=; try by done.
                                       by rewrite -d1_eq_d2.
                             ---- case: (boolP (b2 -- c2))=> [b2_adj_c2 | b2_nadj_c2].
                                  ++++ left; exists (hom_G4_def b2 c2 c1 d1).
                                       **** apply: h'_G4_inj; rewrite /=; try by done.
                                            ----- by rewrite sg_edgeNeq.
                                            ----- by move: a1_adj_b2; apply/contraTneq => ->.
                                            ----- by rewrite eq_sym sg_edgeNeq.
                                            ----- by rewrite d1_eq_d2.
                                       **** apply: h'_copaw_hom; rewrite /=; try by done.
                                            ----- by rewrite sg_sym.
                                            ----- by rewrite d1_eq_d2.
                                  ++++ have b1_neq_c2: b1 != c2 by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym. 
                                       have b2_neq_c1: b2 != c1 by move: a1_adj_b2; apply/contraTneq => ->.
                                       left; exists (hom_G4_def b2 b1 c2 d1).
                                       **** apply: h'_G4_inj; rewrite /=; try by done.
                                            ----- by rewrite eq_sym sg_edgeNeq.
                                            ----- by move: a1_adj_b2; apply/contraTneq => ->.
                                            ----- by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                       **** apply: h'_copaw_hom; rewrite /=; try by done.
                                            ----- by rewrite sg_sym.
                                            ----- by rewrite (negbTE b1_neq_c2) (negbTE b2_neq_c1) (negbTE b2_nadj_c1) /= orbC /= orbC /= in b1c2b2c1.
                                            ----- by rewrite d1_eq_d2.
                     +++ 
                         *** case: (boolP (a1 -- b2))=> [a1_adj_b2 | a1_nadj_b2]; last first.
                             ---- left; exists (hom_G4_def a1 a2 b2 d1).
                                  ++++ apply: h'_G4_inj; rewrite /=; try by done.
                                       **** move: b1c2b2c1; apply/contraTneq => <-.
                                            by rewrite -a2_eq_b1 !negb_or a2_neq_c2 a1_neq_c1 a1_nadj_c1 a2_nadj_c2 /=.
                                       **** by move: a1_adj_a2; apply/contraTneq => ->; rewrite sg_sym.
                                       **** by rewrite a2_eq_b1 sg_edgeNeq.
                                  ++++ apply: h'_copaw_hom; rewrite /=; try by done.
                                       **** by rewrite a2_eq_b1.
                                       **** by rewrite d1_eq_d2.
                             ---- case: (boolP (b2 -- c1))=> [b2_adj_c1 | b2_nadj_c1].
                                  ++++ left; exists (hom_G4_def a1 b2 c1 d2).
                                       **** apply: h'_G4_inj; rewrite /=; try by done.
                                            all: try by rewrite sg_edgeNeq.
                                            by rewrite -d1_eq_d2.
                                       **** apply: h'_copaw_hom; rewrite /=; try by done.
                                            by rewrite -d1_eq_d2.
                                  ++++ left; exists (hom_G4_def a1 b1 c2 d2).
                                       **** apply: h'_G4_inj; rewrite /=; try by done.
                                            ----- by rewrite -a2_eq_b1 sg_edgeNeq.
                                            ----- by move: c1_adj_c2; apply/contraTneq => <-; rewrite -a2_eq_b1 sg_sym.
                                            ----- by rewrite -d1_eq_d2.
                                       **** apply: h'_copaw_hom; rewrite /=; try by done.
                                            ----- by rewrite -a2_eq_b1.
                                            ----- have b1_neq_c2: b1 != c2 by move: c1_adj_c2; apply/contraTneq => <-; rewrite -a2_eq_b1 sg_sym.
                                                  have b2_neq_c1: b2 != c1 by move: a1_adj_b2; apply/contraTneq => ->.
                                                  by rewrite (negbTE b1_neq_c2) (negbTE b2_neq_c1) (negbTE b2_nadj_c1) /= orbC /= orbC /= in b1c2b2c1.
                                            ----- by rewrite -d1_eq_d2.
                 --- case: (boolP (b1 -- c2))=> [b1_adj_c2 | b1_nadj_c2].
                     +++ left; exists (hom_G4_def a2 b1 c2 d1).
                         *** apply: h'_G4_inj; rewrite /=; try by done.
                             all: try by rewrite sg_edgeNeq.
                             by rewrite d1_eq_d2.
                         *** apply: h'_copaw_hom; rewrite /=; try by done.
                             by rewrite d1_eq_d2.
                     +++ case: (boolP (b1 -- c1))=> [b1_adj_c1 | b1_nadj_c1].
                         *** left; exists (hom_G4_def b1 c1 c2 d2).
                             ---- apply: h'_G4_inj; rewrite /=; try by done.
                                  all: try by rewrite sg_edgeNeq.
                                  ++++ by move: a2_adj_b1; apply/contraTneq => ->.
                                  ++++ by rewrite -d1_eq_d2.
                             ---- apply: h'_copaw_hom; rewrite /=; try by done.
                                  by rewrite -d1_eq_d2.
                         *** left; exists (hom_G4_def b1 b2 c1 d2).
                             ---- apply: h'_G4_inj; rewrite /=; try by done.
                                  ++++ by move: a2_adj_b1; apply/contraTneq => ->.
                                  ++++ by move: b1_adj_b2; apply/contraTneq => ->.
                                  ++++ by rewrite -d1_eq_d2.
                             ---- apply: h'_copaw_hom; rewrite /=; try by done.
                                  ++++ have b1_neq_c2: b1 != c2 by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym. 
                                       have b2_neq_c1: b2 != c1 by move: b1_adj_b2; apply/contraTneq => ->.
                                       by rewrite (negbTE b1_neq_c2) (negbTE b2_neq_c1) (negbTE b1_nadj_c2) /= in b1c2b2c1.
                                  ++++ by rewrite -d1_eq_d2.
         -- have d1_neq_d2: d1 != d2 by rewrite sg_edgeNeq.
            case: (boolP (a2 -- d2))=> [a2_adj_d2 | a2_nadj_d2].
                 ++ case: (boolP (a1 -- c1))=> [a1_adj_c1 | a1_nadj_c1]; last first.
                    ** left; exists (hom_G4_def a1 a2 d2 c1).
                       --- apply: h'_G4_inj; rewrite /=; try by done.
                           all: try by rewrite eq_sym.
                           all: by rewrite sg_edgeNeq.
                       --- apply: h'_copaw_hom; rewrite /=; try by done.
                           by rewrite sg_sym.
                    ** case: (boolP (c2 -- d2))=> [c2_adj_d2 | c2_nadj_d2]; last first.
                       --- left; exists (hom_G4_def a1 c1 c2 d2).
                           +++ apply: h'_G4_inj; rewrite /=; try by done.
                               all: try by rewrite eq_sym.
                               by move: c1_adj_c2; apply/contraTneq => ->.
                           +++ by apply: h'_copaw_hom.
                       --- case: (boolP (c1 -- d1))=> [c1_adj_d1 | c1_nadj_d1]; last first.
                           +++ left; exists (hom_G4_def a2 d2 d1 c1).
                               *** apply: h'_G4_inj; rewrite /=; try by done.
                                   all: try by rewrite eq_sym.
                                   all: try by rewrite sg_edgeNeq.
                                   by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                               *** apply: h'_copaw_hom; rewrite /=; try by done.
                                   all: by rewrite sg_sym.
                           +++ case: (boolP (a1 -- d1))=> [a1_adj_d1 | a1_nadj_d1]; last first.
                               *** left; exists (hom_G4_def c2 d2 d1 a1).
                                   ---- apply: h'_G4_inj; rewrite /=; try by done.
                                        all: try by rewrite eq_sym.
                                        all: try by rewrite sg_edgeNeq.
                                        by move: a1_adj_a2; apply/contraTneq => <-; rewrite sg_sym.
                                   ---- apply: h'_copaw_hom; rewrite /=; try by done.
                                        all: by rewrite sg_sym.
                               *** case: (boolP (a2 -- c2))=> [a2_adj_c2 | a2_nadj_c2]; last first.
                                   ---- left; exists (hom_G4_def c2 c1 d1 a2).
                                        ++++ apply: h'_G4_inj; rewrite /=; try by done.
                                             all: try by rewrite eq_sym.
                                             all: by rewrite sg_edgeNeq.
                                        ++++ apply: h'_copaw_hom; rewrite /=; try by done.
                                             all: by rewrite sg_sym.
                                   ---- case: (boolP (a2 -- b1))=> [a2_adj_b1 | a2_nadj_b1].
                                        ++++ case: (boolP (b1 -- c1))=> [b1_adj_c1 | b1_nadj_c1]; last first.
                                             **** left; exists (hom_G4_def b1 a2 d2 c1).
                                                  ----- apply: h'_G4_inj; rewrite /=; try by done.
                                                        all: try by rewrite eq_sym.
                                                        all: try by rewrite sg_edgeNeq.
                                                        all: try by rewrite eq_sym sg_edgeNeq.
                                                        by move: a2_adj_b1; apply/contraTneq => ->.
                                                  ----- apply: h'_copaw_hom; rewrite /=; try by done.
                                                        all: by rewrite sg_sym.
                                             **** case: (boolP (a1 -- b1))=> [a1_adj_b1 | a1_nadj_b1].
                                                  ----- case: (boolP (b1 -- c2))=> [b1_adj_c2 | b1_nadj_c2].
                                                        +++++ case: (boolP (b1 -- d1))=> [b1_adj_d1 | b1_nadj_d1]; last first.
                                                              ***** right; left; exists (hom_G7_def a2 c1 d2 a1 c2 d1 b1).
                                                                    ------ apply: h'_G7_inj; rewrite /=; try by done.
                                                                           all: try by rewrite eq_sym.
                                                                           all: try by rewrite sg_edgeNeq.
                                                                           all: try by rewrite eq_sym sg_edgeNeq.
                                                                           by move: b1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
                                                                    ------ apply: h'_G7_1_hom; rewrite /=; try by done.
                                                                           all: by rewrite sg_sym.
                                                              ***** right; right; exists (hom_G7_def c1 a2 d1 c2 a1 d2 b1).
                                                                    ------ apply: h'_G7_inj; rewrite /=; try by done.
                                                                           all: try by rewrite eq_sym.
                                                                           all: try by rewrite sg_edgeNeq.
                                                                           all: by rewrite eq_sym sg_edgeNeq.
                                                                    ------ apply: h'_G7_2_hom; rewrite /=; try by done.
                                                                           all: by rewrite sg_sym.
                                                        +++++ case: (boolP (b1 -- d1))=> [b1_adj_d1 | b1_nadj_c1]; last first.
                                                              ***** left; exists (hom_G4_def d1 d2 c2 b1).
                                                                    ------ apply: h'_G4_inj; rewrite /=; try by done.
                                                                           all: try by rewrite eq_sym.
                                                                           all: try by rewrite sg_edgeNeq.
                                                                           all: try by rewrite eq_sym sg_edgeNeq.
                                                                           ++++++ by move: d1_adj_d2; apply/contraTneq => ->.
                                                                           ++++++ by move: a1_adj_b1; apply/contraTneq => <-.
                                                                    ------ apply: h'_copaw_hom; rewrite /=; try by done.
                                                                           all: by rewrite sg_sym.
                                                              ***** case: (boolP (b2 -- c2))=> [b2_adj_c2 | b2_nadj_c2]; last first.
                                                                    ------ left; exists (hom_G4_def b2 b1 d1 c2).
                                                                           ++++++ apply: h'_G4_inj; rewrite /=; try by done.
                                                                                  ****** by rewrite eq_sym sg_edgeNeq.
                                                                                  ****** by move: b1_adj_b2; apply/contraTneq => ->.
                                                                                  ****** by rewrite sg_edgeNeq.
                                                                                  ****** by move: c2_adj_d2; apply/contraTneq => <-.
                                                                                  ****** by rewrite eq_sym.
                                                                           ++++++ apply: h'_copaw_hom; rewrite /=; try by done.
                                                                                  all: by rewrite sg_sym.
                                                                    ------ case: (boolP (a2 -- b2))=> [a2_adj_b2 | a2_nadj_b2]; last first.
                                                                           ++++++ have b2_neq_c1: b2 != c1 by move: c1_adj_d1; apply/contraTneq => <-.
                                                                                  have b1_neq_c2: b1 != c2 by move: c2_adj_d2; apply/contraTneq => <-.
                                                                                  have b2_adj_c1: b2 -- c1.
                                                                                    by rewrite (negbTE b1_neq_c2) (negbTE b2_neq_c1) (negbTE b1_nadj_c2) /= in b1c2b2c1.
                                                                                  left; exists (hom_G4_def b2 c1 d1 a2).
                                                                                  ****** apply: h'_G4_inj; rewrite /=; try by done.
                                                                                         all: try by rewrite eq_sym.
                                                                                         ------- by move: b2_adj_c1; apply/contraTneq => ->.
                                                                                         ------- by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                                                                  ****** apply: h'_copaw_hom; rewrite /=; try by done.
                                                                                         all: try by rewrite sg_sym.
                                                                           ++++++ case: (boolP (a1 -- b2))=> [a1_adj_b2 | a1_nadj_b2]; last first.
                                                                                  ****** case: (boolP (b2 -- d2))=> [b2_adj_d2 | b2_nadj_d2]; last first.
                                                                                         ------- left; exists (hom_G4_def a1 d1 d2 b2).
                                                                                                 +++++++ apply: h'_G4_inj; rewrite /=; try by done.
                                                                                                         all: try by by rewrite sg_edgeNeq.
                                                                                                         ******* by move: a1_adj_d1; apply/contraTneq => ->.
                                                                                                         ******* by rewrite eq_sym.
                                                                                                         ******* by move: d1_adj_d2; apply/contraTneq => ->; rewrite sg_sym.
                                                                                                 +++++++ apply: h'_copaw_hom; rewrite /=; try by done.
                                                                                                         all: by rewrite sg_sym.
                                                                                         ------- have b2_neq_c1: b2 != c1 by move: a1_adj_c1; apply/contraTneq => <-.
                                                                                                 have b1_neq_c2: b1 != c2 by move: a1_adj_b1; apply/contraTneq => ->.
                                                                                                 have b2_adj_c1: b2 -- c1 by rewrite (negbTE b1_neq_c2) (negbTE b2_neq_c1) (negbTE b1_nadj_c2) /= in b1c2b2c1.
                                                                                                 right; right; exists (hom_G7_def a1 b2 d1 a2 c1 d2 b1).
                                                                                                 +++++++ apply: h'_G7_inj; rewrite /=; try by done.
                                                                                                         all: try by rewrite eq_sym.
                                                                                                         all: try by rewrite sg_edgeNeq.
                                                                                                         all: try by rewrite eq_sym sg_edgeNeq.
                                                                                                         by move: b2_adj_d2; apply/contraTneq => <-.
                                                                                                 +++++++ apply: h'_G7_2_hom; rewrite /= ; try by done.
                                                                                                         all: by rewrite sg_sym.
                                                                                  ****** have b2_neq_c1: b2 != c1 by move: c1_adj_d1; apply/contraTneq => <-.
                                                                                         have b1_neq_c2: b1 != c2 by move: b1_adj_d1; apply/contraTneq => ->.
                                                                                         rewrite (negbTE b1_neq_c2) (negbTE b2_neq_c1) (negbTE b1_nadj_c2) /= in b1c2b2c1.
                                                                                         case: (boolP (b2 -- d2))=> [b2_adj_d2 | b2_nadj_d2]; last first.
                                                                                         ------- right; left; exists (hom_G7_def a2 c1 d2 a1 c2 d1 b2).
                                                                                                 +++++++ apply: h'_G7_inj; rewrite /=; try by done.
                                                                                                         all: try by rewrite eq_sym.
                                                                                                         all: try by rewrite sg_edgeNeq.
                                                                                                         all: try by rewrite eq_sym sg_edgeNeq.
                                                                                                         by move: a1_adj_b2; apply/contraTneq => <-.
                                                                                                 +++++++ apply: h'_G7_1_hom; rewrite /=; try by done.
                                                                                                         all: by rewrite sg_sym.
                                                                                         ------- right; right; exists (hom_G7_def a2 c1 d2 a1 c2 d1 b2).
                                                                                                 +++++++ apply: h'_G7_inj; rewrite /=; try by done.
                                                                                                         all: try by rewrite eq_sym.
                                                                                                         all: try by rewrite sg_edgeNeq.
                                                                                                         all: by rewrite eq_sym sg_edgeNeq.
                                                                                                 +++++++ apply: h'_G7_2_hom; rewrite /=; try by done.
                                                                                                         all: by rewrite sg_sym.
                                                  ----- case: (boolP (b1 -- c2))=> [b1_adj_c2 | b1_nadj_c2].
                                                        +++++ left; exists (hom_G4_def b1 c2 d2 a1).
                                                              ***** apply: h'_G4_inj; rewrite /=; try by done.
                                                                    all: try by rewrite eq_sym.
                                                                    ------ by rewrite sg_edgeNeq.
                                                                    ------ by move: b1_adj_c2; apply/contraTneq => ->.
                                                                    ------ by rewrite sg_edgeNeq.
                                                              ***** apply: h'_copaw_hom; rewrite /=; try by done.
                                                                    all: try by rewrite sg_sym.
                                                       +++++ have b2_neq_c1: b2 != c1 by move: c1_adj_d1; apply/contraTneq => <-.
                                                             have b1_neq_c2: b1 != c2 by move: c2_adj_d2; apply/contraTneq => <-.
                                                             have b2_adj_c1: b2 -- c1 by rewrite (negbTE b1_neq_c2) (negbTE b2_neq_c1) (negbTE b1_nadj_c2) /= in b1c2b2c1.
                                                             case: (boolP (b2 -- c2))=> [b2_adj_c2 | b2_nadj_c2].
                                                             ***** case: (boolP (b1 -- d1))=> [b1_adj_d1 | b1_nadj_d1]; last first.
                                                                   ------ left; exists (hom_G4_def b1 b2 c2 d1).
                                                                          ++++++ apply: h'_G4_inj; rewrite /=; try by done.
                                                                                 ****** by move: d1_adj_d2; apply/contraTneq => <-.
                                                                                 ****** by rewrite sg_edgeNeq.
                                                                          ++++++ by apply: h'_copaw_hom.
                                                                   ------ case: (boolP (b2 -- d2))=> [b2_adj_d2 | b2_nadj_d2].
                                                                          +++++++ case: (boolP (a1 -- b2))=> [a1_adj_b2 | a1_nadj_b2]; last first.
                                                                                  ******* left; exists (hom_G4_def b1 b2 d2 a1).
                                                                                          -------- apply: h'_G4_inj; rewrite /=; try by done.
                                                                                                   ++++++++ by move: b1_adj_b2; apply/contraTneq => ->.
                                                                                                   ++++++++ by rewrite sg_edgeNeq.
                                                                                                   ++++++++ by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                                                                   ++++++++ by rewrite eq_sym.
                                                                                          -------- apply: h'_copaw_hom; rewrite /=; try by done.
                                                                                                   all: by rewrite sg_sym.
                                                                                  ******* case: (boolP (a2 -- b2))=> [a2_adj_b2 | a2_nadj_b2].
                                                                                          -------- right; right; exists (hom_G7_def a2 c1 d2 a1 c2 d1 b2).
                                                                                                   ++++++++ apply: h'_G7_inj; rewrite /=; try by done.
                                                                                                            all: try by rewrite eq_sym.
                                                                                                            all: try by rewrite sg_edgeNeq.
                                                                                                            all: by rewrite eq_sym sg_edgeNeq.
                                                                                                   ++++++++ apply: h'_G7_2_hom; rewrite /=; try by done.
                                                                                                            all: by rewrite sg_sym.
                                                                                          -------- left; exists (hom_G4_def a2 c2 b2 d1).
                                                                                                   ++++++++ apply: h'_G4_inj; rewrite /=; try by done.
                                                                                                            all: try by rewrite sg_edgeNeq.
                                                                                                            all: try by rewrite eq_sym sg_edgeNeq.
                                                                                                            by move: b2_adj_c1; apply/contraTneq => <-.
                                                                                                   ++++++++ apply: h'_copaw_hom; rewrite /=; try by done.
                                                                                                            all: by rewrite sg_sym.
                                                                          +++++++ case: (boolP (a1 -- b2))=> [a1_adj_b2 | a1_nadj_b2]; last first.
                                                                                  ******* left; exists (hom_G4_def a1 d1 d2 b2).
                                                                                          -------- apply: h'_G4_inj; rewrite /=; try by done.
                                                                                                   all: try by rewrite eq_sym.
                                                                                                   all: try by rewrite sg_edgeNeq.
                                                                                                   all: try by rewrite eq_sym sg_edgeNeq.
                                                                                                   ++++++++ by move: a1_adj_d1; apply/contraTneq => ->.
                                                                                                   ++++++++ by move: d1_adj_d2; apply/contraTneq => ->; rewrite sg_sym.
                                                                                          -------- apply: h'_copaw_hom; rewrite /=; try by done.
                                                                                                   all: by rewrite sg_sym.
                                                                                  ******* case: (boolP (a2 -- b2))=> [a2_adj_b2 | a2_nadj_b2]; last first.
                                                                                          -------- left; exists (hom_G4_def a2 d2 d1 b2).
                                                                                                   ++++++++ apply: h'_G4_inj; rewrite /=; try by done.
                                                                                                            ******** by rewrite sg_edgeNeq.
                                                                                                            ******** by move: a2_adj_d2; apply/contraTneq => ->.
                                                                                                            ******** by rewrite eq_sym sg_edgeNeq.
                                                                                                            ******** by move: a2_adj_d2; apply/contraTneq => ->.
                                                                                                            ******** by rewrite eq_sym.
                                                                                                   ++++++++ apply: h'_copaw_hom; rewrite /=; try by done.
                                                                                                            all: by rewrite sg_sym.
                                                                                          -------- right; left; exists (hom_G7_def a2 c1 d2 a1 c2 d1 b2).
                                                                                                   ++++++++ apply: h'_G7_inj; rewrite /=; try by done.
                                                                                                            all: try by rewrite eq_sym.
                                                                                                            all: try by rewrite sg_edgeNeq.
                                                                                                            all: try by rewrite eq_sym sg_edgeNeq.
                                                                                                            by move: a1_adj_b2; apply/contraTneq => <-.
                                                                                                   ++++++++ apply: h'_G7_1_hom; rewrite /=; try by done.
                                                                                                            all: by rewrite sg_sym.
                                                             ***** case: (boolP (b1 -- d1))=> [b1_adj_d1 | b1_nadj_d1]; last first.
                                                                   ------ left; exists (hom_G4_def a1 d1 d2 b1).
                                                                          ++++++ apply: h'_G4_inj; rewrite /=; try by done.
                                                                                 ****** by rewrite sg_edgeNeq.
                                                                                 ****** by move: a1_adj_d1; apply/contraTneq => ->.
                                                                                 ****** by move: a1_adj_d1; apply/contraTneq => ->.
                                                                                 ****** by rewrite eq_sym.
                                                                          ++++++ apply: h'_copaw_hom; rewrite /=; try by done.
                                                                                 all: by rewrite sg_sym.
                                                                   ------ case: (boolP (b2 -- d2))=> [b2_adj_d2 | b2_nadj_d2]; last first.
                                                                          ++++++ left; exists (hom_G4_def d1 d2 c2 b2).
                                                                                 ****** apply: h'_G4_inj; rewrite /=; try by done.
                                                                                        all: try by rewrite eq_sym.
                                                                                        ------- by rewrite eq_sym sg_edgeNeq.
                                                                                        ------- by move: b1_adj_b2; apply/contraTneq => <-.
                                                                                        ------- by move: b1_adj_b2; apply/contraTneq => <-.
                                                                                 ****** apply: h'_copaw_hom; rewrite /=; try by done.
                                                                                        all: by rewrite sg_sym.
                                                                          ++++++ case: (boolP (a1 -- b2))=> [a1_adj_b2 | a1_nadj_b2].
                                                                                 ****** left; exists (hom_G4_def b2 a1 d1 c2).
                                                                                        ------- apply: h'_G4_inj; rewrite /=; try by done.
                                                                                                +++++++ by rewrite eq_sym sg_edgeNeq.
                                                                                                +++++++ by move: a1_adj_b2; apply/contraTneq => ->.
                                                                                                +++++++ by move: d1_adj_d2; apply/contraTneq => <-.
                                                                                                +++++++ by rewrite eq_sym.
                                                                                        ------- apply: h'_copaw_hom; rewrite /=; try by done.
                                                                                                all: by rewrite sg_sym.
                                                                                 ****** case: (boolP (a2 -- b2))=> [a2_adj_b2 | a2_nadj_b2]; last first.
                                                                                        ------- left; exists (hom_G4_def a1 a2 c2 b2).
                                                                                                +++++++ apply: h'_G4_inj; rewrite /=; try by done.
                                                                                                        ******* by move: a1_adj_a2; apply/contraTneq => ->; rewrite sg_sym.
                                                                                                        ******* by move: a1_adj_a2; apply/contraTneq => ->.
                                                                                                        ******* by move: a2_adj_c2; apply/contraTneq => ->.
                                                                                                +++++++ apply: h'_copaw_hom; rewrite /=; try by done.
                                                                                                        by rewrite sg_sym.
                                                                                        ------- left; exists (hom_G4_def b2 d2 c2 a1).
                                                                                                +++++++ apply: h'_G4_inj; rewrite /=; try by done.
                                                                                                        all: try by rewrite eq_sym.
                                                                                                        ******* by rewrite sg_edgeNeq.
                                                                                                        ******* by move: b1_adj_b2; apply/contraTneq => ->.
                                                                                                        ******* by move: b2_adj_d2; apply/contraTneq => ->.
                                                                                                        ******* by rewrite eq_sym sg_edgeNeq.
                                                                                                +++++++ apply: h'_copaw_hom; rewrite /=; try by done.
                                                                                                        all: by rewrite sg_sym.
                                        ++++ case: (boolP (b1 -- d1))=> [b1_adj_d1 | b1_nadj_d1]; last first.
                                             **** left; exists (hom_G4_def a2 d2 d1 b1).
                                                  ----- apply: h'_G4_inj; rewrite /=; try by done.
                                                        all: try by rewrite eq_sym.
                                                        +++++ by rewrite sg_edgeNeq.
                                                        +++++ by move: a2_adj_d2; apply/contraTneq => ->.
                                                        +++++ by move: d1_adj_d2; apply/contraTneq => ->.
                                                  ----- apply: h'_copaw_hom; rewrite /=; try by done.
                                                        all: by rewrite sg_sym.
                                             **** case: (boolP (a2 -- b2))=> [a2_adj_b2 | a2_nadj_b2]; last first.
                                                  ----- left; exists (hom_G4_def b2 b1 d1 a2).
                                                        +++++ apply: h'_G4_inj; rewrite /=; try by done.
                                                              all: try  by rewrite eq_sym.
                                                              ***** by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                              ***** by rewrite (sg_edgeNeq b1_adj_d1).
                                                              ***** by move: a2_adj_d2; apply/contraTneq => <-.
                                                        +++++ apply: h'_copaw_hom; rewrite /=; try by done.
                                                              all: by rewrite sg_sym.
                                                  ----- case: (boolP (a1 -- b1))=> [a1_adj_b1 | a1_nadj_b1]; last first.
                                                        +++++ left; exists (hom_G4_def a1 a2 d2 b1).
                                                              ***** apply: h'_G4_inj; rewrite /=; try by done.
                                                                    ------ by move: a1_adj_a2; apply/contraTneq => ->; rewrite sg_sym.
                                                                    ------ by rewrite sg_edgeNeq.
                                                                    ------ by move: b1_adj_d1; apply/contraTneq => <-.
                                                                    ------ by rewrite eq_sym. 
                                                              ***** apply: h'_copaw_hom; rewrite /=; try by done.
                                                                    by rewrite sg_sym.
                                                        +++++ case: (boolP (b2 -- d2))=> [b2_adj_d2 | b2_nadj_d2]; last first.
                                                              ***** case: (boolP (b2 -- c2))=> [b2_adj_c2 | b2_nadj_c2]; last first.
                                                                    ------ left; exists (hom_G4_def d1 d2 c2 b2).
                                                                           ++++++ apply: h'_G4_inj; rewrite /=; try by done.
                                                                                  ****** by rewrite eq_sym.
                                                                                  ****** by move: a2_adj_b2; apply/contraTneq => <-.
                                                                                  ****** by rewrite eq_sym sg_edgeNeq.
                                                                                  ****** by move: d1_adj_d2; apply/contraTneq => ->; rewrite sg_sym. 
                                                                                  ****** by move: c2_adj_d2; apply/contraTneq => ->.
                                                                           ++++++ apply: h'_copaw_hom; rewrite /=; try by done.
                                                                                  all: by rewrite sg_sym.
                                                                    ------ case: (boolP (a1 -- b2))=> [a1_adj_b2 | a1_nadj_b2]; last first.
                                                                           ++++++ left; exists (hom_G4_def b2 c2 d2 a1).
                                                                                  ****** apply: h'_G4_inj; rewrite /=; try by done.
                                                                                         all: try by rewrite eq_sym.
                                                                                         ------- by rewrite sg_edgeNeq.
                                                                                         ------- by move: b1_adj_b2; apply/contraTneq => ->.
                                                                                         ------- by move: a1_adj_d1; apply/contraTneq => <-.
                                                                                         ------- by rewrite sg_edgeNeq.
                                                                                  ****** apply: h'_copaw_hom; rewrite /=; try by done.
                                                                                         all: by rewrite sg_sym.
                                                                           ++++++ case: (boolP (b2 -- c1))=> [b2_adj_c1 | b2_nadj_c1]; last first.
                                                                                  ****** left; exists (hom_G4_def c1 d1 d2 b2).
                                                                                         ------- apply: h'_G4_inj; rewrite /=; try by done.
                                                                                                 +++++++ by rewrite sg_edgeNeq.
                                                                                                 +++++++ by move: c1_adj_d1; apply/contraTneq => ->.
                                                                                                 +++++++ by rewrite eq_sym.
                                                                                                 +++++++ by move: a1_adj_b2; apply/contraTneq => <-.
                                                                                         ------- apply: h'_copaw_hom; rewrite /=; try by done.
                                                                                                 all: by rewrite sg_sym.
                                                                                  ****** right; left; exists (hom_G7_def a2 c1 d2 a1 c2 d1 b2).
                                                                                         -------- apply: h'_G7_inj; rewrite /=; try by done.
                                                                                                  all: try by rewrite eq_sym.
                                                                                                  all: try by rewrite sg_edgeNeq.
                                                                                                  all: try by rewrite eq_sym sg_edgeNeq.
                                                                                                  by move: b1_adj_b2; apply/contraTneq => <-.
                                                                                         -------- apply: h'_G7_1_hom; rewrite /=; try by done.
                                                                                                  all: by rewrite sg_sym.
                                                              ***** case: (boolP (b2 -- c2))=> [b2_adj_c2 | b2_nadj_c2]; last first.
                                                                    ------ have a1_neq_b2: a1 != b2 by move: a1_adj_d1; apply/contraTneq => ->.
                                                                           have a2_neq_b1: a2 != b1 by move: a2_adj_d2; apply/contraTneq => ->.
                                                                           have a1_adj_b2: a1 -- b2 by rewrite (negbTE a1_neq_b2) (negbTE a2_neq_b1) (negbTE a2_nadj_b1) /= orbC /= orbC /= in a1b2a2b1.
                                                                           left; exists (hom_G4_def b2 a1 d1 c2).
                                                                           ++++++ apply: h'_G4_inj; rewrite /=; try by done.
                                                                                  all: try by rewrite eq_sym.
                                                                                  all: try by rewrite sg_edgeNeq.
                                                                                  all: try by rewrite eq_sym sg_edgeNeq.
                                                                                  by move: a1_adj_b2; apply/contraTneq => ->.
                                                                           ++++++ apply: h'_copaw_hom; rewrite /=; try by done.
                                                                                  all: by rewrite sg_sym.
                                                                    ------ have a1_neq_b2: a1 != b2 by move: a1_adj_d1; apply/contraTneq => ->.
                                                                           have a2_neq_b1: a2 != b1 by move: a2_adj_d2; apply/contraTneq => ->.
                                                                           have a1_adj_b2: a1 -- b2 by rewrite (negbTE a1_neq_b2) (negbTE a2_neq_b1) (negbTE a2_nadj_b1) /= orbC /= orbC /= in a1b2a2b1.
                                                                           case: (boolP (b2 -- c1))=> [b2_adj_c1 | b2_nadj_c1]; last first.
                                                                           ++++++ have b2_neq_c1: b2 != c1 by move: c1_adj_d1; apply/contraTneq => <-.
                                                                                  have b1_neq_c2: b1 != c2 by move: b1_adj_d1; apply/contraTneq => ->.
                                                                                  have b1_adj_c2: b1 -- c2 by rewrite (negbTE b1_neq_c2) (negbTE b2_neq_c1) (negbTE b2_nadj_c1) /= orbC /= orbC /= in b1c2b2c1.
                                                                                  case: (boolP (b1 -- c1))=> [b1_adj_c1 | b1_nadj_c1]; last first.
                                                                                  ****** left; exists (hom_G4_def b1 a1 c1 d2).
                                                                                         ------- apply: h'_G4_inj; rewrite /=; try by done.
                                                                                                 +++++++ by move: a1_adj_a2; apply/contraTneq => <-; rewrite sg_sym.
                                                                                                 +++++++ by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                                                         ------- apply: h'_copaw_hom; rewrite /=; try by done.
                                                                                                 by rewrite sg_sym.
                                                                                  ****** right; right; exists (hom_G7_def c1 b2 d1 c2 a1 d2 b1).
                                                                                         -------- apply: h'_G7_inj; rewrite /=; try by done.
                                                                                                  all: try by rewrite eq_sym.
                                                                                                  all: try by rewrite sg_edgeNeq.
                                                                                                  all: by rewrite eq_sym sg_edgeNeq.
                                                                                         -------- apply: h'_G7_2_hom; rewrite /=; try by done.
                                                                                                  all: by rewrite sg_sym.
                                                                           ++++++ right; right; exists (hom_G7_def c2 a1 d2 c1 a2 d1 b2).
                                                                                  ****** apply: h'_G7_inj; rewrite /=; try by done.
                                                                                         all: try by rewrite eq_sym.
                                                                                         all: try by rewrite sg_edgeNeq.
                                                                                         all: by rewrite eq_sym sg_edgeNeq.
                                                                                  ****** apply: h'_G7_2_hom; rewrite /=; try by done.
                                                                                         all: by rewrite sg_sym.
                 ++ case: (boolP (c1 -- d1))=> [d1_adj_d1 | c1_nadj_d1].
                    ** left; exists (hom_G4_def c1 d1 d2 a2).
                       --- apply: h'_G4_inj; rewrite /=; try by done.
                           all: try by rewrite eq_sym.
                           all: try by rewrite sg_edgeNeq.
                           all: try by rewrite eq_sym sg_edgeNeq.
                           by move: d1_adj_d2; apply/contraTneq => ->; rewrite sg_sym.
                       --- apply: h'_copaw_hom; rewrite /=; try by done.
                           all: by rewrite sg_sym.
                    ** case: (boolP (a2 -- c2))=> [a2_adj_c2 | a2_nadj_c2].
                       --- left; exists (hom_G4_def a2 c2 c1 d1).
                           +++ apply: h'_G4_inj; rewrite /=; try by done.
                               all: try by rewrite sg_edgeNeq.
                               all: try by rewrite eq_sym sg_edgeNeq.
                               by move: d1_adj_d2; apply/contraTneq => <-.
                           +++ apply: h'_copaw_hom; rewrite /=; try by done.
                               by rewrite sg_sym.
                       --- case: (boolP (a1 -- c1))=> [a1_adj_c1 | a1_nadj_c1].
                           +++ left; exists (hom_G4_def a2 a1 c1 d2).
                               *** apply: h'_G4_inj; rewrite /=; try by done.
                                   ---- by rewrite eq_sym.
                                   ---- by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
                               *** apply: h'_copaw_hom; rewrite /=; try by done.
                                   by rewrite sg_sym.
                           +++ case: (boolP (a1 -- d1))=> [a1_adj_d1 | a1_nadj_d1].
                               ---- left; exists (hom_G4_def a1 d1 d2 c1).
                                    ++++ apply: h'_G4_inj; rewrite /=; try by done.
                                         all: try by rewrite eq_sym.
                                         all: try by rewrite sg_edgeNeq.
                                         all: try by rewrite eq_sym sg_edgeNeq.
                                         by move: a1_adj_d1; apply/contraTneq => ->.
                                    ++++ apply: h'_copaw_hom; rewrite /=; try by done.
                                         all: by rewrite sg_sym.
                              ---- case: (boolP (c2 -- d2))=> [c2_adj_d2 | c2_nadj_d2].
                                   ++++ left; exists (hom_G4_def c2 d2 d1 a1).
                                        **** apply: h'_G4_inj; rewrite /=; try by done.
                                             all: try by rewrite eq_sym.
                                             ----- by rewrite sg_edgeNeq.
                                             ----- by move: d1_adj_d2; apply/contraTneq => ->.
                                        **** apply: h'_copaw_hom; rewrite /=; try by done.
                                             all: by rewrite sg_sym.
                                   ++++ case: (boolP (b1 -- d1))=> [b1_adj_d1 | b1_nadj_d1].
                                        **** left.
                                             case: (boolP (a2 -- b1))=> [a2_adj_b1 | a2_nadj_b1]; last first.
                                             ----- exists (hom_G4_def b1 d1 d2 a2).
                                                   +++++ apply: h'_G4_inj; rewrite /=; try by done.
                                                         all: try by rewrite eq_sym.
                                                         all: try by rewrite sg_edgeNeq.
                                                         ***** by move: b1_adj_d1; apply/contraTneq => ->.
                                                         ***** by move: a1_adj_a2; apply/contraTneq => <-.
                                                   +++++ apply: h'_copaw_hom; rewrite /=; try by done.
                                                         all: by rewrite sg_sym.
                                             ----- case: (boolP (a1 -- b1))=> [a1_adj_b1 | a1_nadj_b1]; last first.
                                                   +++++ exists (hom_G4_def a1 a2 b1 d2).
                                                         ***** apply: h'_G4_inj; rewrite /=; try by done.
                                                               all: try by rewrite eq_sym.
                                                               all: try by rewrite sg_edgeNeq.
                                                               ------ by move: b1_adj_d1; apply/contraTneq => <-.
                                                               ------ by move: a1_adj_a2; apply/contraTneq => ->.
                                                         ***** by apply: h'_copaw_hom.
                                                   +++++ case: (boolP (b1 -- c1))=> [b1_adj_c1 | b1_nadj_c1]; last first.
                                                         ***** exists (hom_G4_def b1 d1 d2 c1).
                                                               ------ apply: h'_G4_inj; rewrite /=; try by done.
                                                                      all: try by rewrite eq_sym.
                                                                      all: try by rewrite sg_edgeNeq.
                                                                      ++++++ by move: b1_adj_d1; apply/contraTneq => ->.
                                                                      ++++++ by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                                                               ------ apply: h'_copaw_hom; rewrite /=; try by done.
                                                                      all: by rewrite sg_sym.
                                                         ***** exists (hom_G4_def a2 b1 c1 d2).
                                                               ------ apply: h'_G4_inj; rewrite /=; try by done.
                                                                      all: try by rewrite sg_edgeNeq.
                                                                      by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
                                                               ------ by apply: h'_copaw_hom.
                                        **** case: (boolP (b2 -- d2))=> [b2_adj_d2 | b2_nadj_d2].
                                             ----- case: (boolP (b2 -- c1))=> [b2_adj_c1 | b2_nadj_c1]; last first.
                                                   +++++ left; exists (hom_G4_def b2 d2 d1 c1).
                                                         ***** apply: h'_G4_inj; rewrite /=; try by done.
                                                               all: try by rewrite eq_sym.
                                                               all: try by rewrite sg_edgeNeq.
                                                               all: try by rewrite eq_sym sg_edgeNeq.
                                                               ------ by move: b2_adj_d2; apply/contraTneq => ->.
                                                               ------ by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                                                         ***** apply: h'_copaw_hom; rewrite /=; try by done.
                                                               all: by rewrite sg_sym.
                                                   +++++ case: (boolP (b2 -- c2))=> [b2_adj_c2 | b2_nadj_c2]; last first.
                                                         ***** left; exists (hom_G4_def b2 c1 c2 d1).
                                                               ------ apply: h'_G4_inj; rewrite /=; try by done.
                                                                      ++++++ by rewrite sg_edgeNeq.
                                                                      ++++++ by move: b2_adj_d2; apply/contraTneq => ->.
                                                                      ++++++ by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                                               ------ by apply: h'_copaw_hom.
                                                         ***** case: (boolP (a2 -- b2))=> [a2_adj_b2 | a2_nadj_b2]; last first.
                                                               ------ left; exists (hom_G4_def b2 d2 d1 a2).
                                                                      ++++++ apply: h'_G4_inj; rewrite /=; try by done.
                                                                             ****** by rewrite sg_edgeNeq.
                                                                             ****** by move: b2_adj_d2; apply/contraTneq => ->.
                                                                             ****** by rewrite eq_sym.
                                                                             ****** by move: a1_adj_a2; apply/contraTneq => <-.
                                                                             ****** by rewrite eq_sym.
                                                                      ++++++ apply: h'_copaw_hom; rewrite /=; try by done.
                                                                             all: by rewrite sg_sym.
                                                               ------ left; exists (hom_G4_def a2 b2 c1 d1).
                                                                      ++++++ apply: h'_G4_inj; rewrite /=; try by done.
                                                                             ****** by rewrite sg_edgeNeq.
                                                                             ****** by move: b2_adj_d2; apply/contraTneq => ->.
                                                                             ****** by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                                                      ++++++ by apply: h'_copaw_hom.
                                             ----- case: (boolP (a2 -- b1))=> [a2_adj_b1 | a2_nadj_b1].
                                                   +++++ case: (boolP (a1 -- b1))=> [a1_adj_b1 | a1_nadj_b1]; last first.
                                                         ***** case: (boolP (a1 == b1))=> [/eqP a1_eq_b1 | a1_neq_b1]; last first.
                                                               ------ left; exists (hom_G4_def a1 a2 b1 d2).
                                                                      ++++++ apply: h'_G4_inj; rewrite /=; try by done.
                                                                             ****** by rewrite sg_edgeNeq.
                                                                             ****** by move: a1_adj_a2; apply/contraTneq => ->.
                                                                      ++++++ by apply: h'_copaw_hom.
                                                               ------ case: (boolP (a2 -- b2))=> [a2_adj_b2 | a2_nadj_b2]; last first.
                                                                      ++++++ left; exists (hom_G4_def a2 b1 b2 d1).
                                                                             ****** apply: h'_G4_inj; rewrite /=; try by done.
                                                                                    ------- by rewrite sg_edgeNeq.
                                                                                    ------- by rewrite a1_eq_b1 eq_refl in a1a2b1b2.
                                                                                    ------- by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                                             ****** by apply: h'_copaw_hom.
                                                                      ++++++ case: (boolP (b2 -- c1))=> [b2_adj_c1 | b2_nadj_c1].
                                                                             ****** left; exists (hom_G4_def a2 b2 c1 d1).
                                                                                    ------- apply: h'_G4_inj; rewrite /=; try by done.
                                                                                            all: try by rewrite sg_edgeNeq.
                                                                                            by move: b2_adj_c1; apply/contraTneq => ->.
                                                                                    ------- by apply: h'_copaw_hom.
                                                                             ****** suff b1_adj_c2: b1 -- c2 by rewrite a1_eq_b1 b1_adj_c2 in a1_nadj_c2.
                                                                                    have b1_neq_c2: b1 != c2 by rewrite -a1_eq_b1.
                                                                                    have b2_neq_c1: b2 != c1 by move: a2_adj_b2; apply/contraTneq => ->.
                                                                                    by rewrite (negbTE b1_neq_c2) (negbTE b2_neq_c1) (negbTE b2_nadj_c1) /= orbC /= orbC /= in b1c2b2c1.
                                                         ***** case: (boolP (b1 -- c1))=> [b1_adj_c1 | b1_nadj_c1].
                                                               ------ left; exists (hom_G4_def a1 b1 c1 d2).
                                                                      ++++++ apply: h'_G4_inj; rewrite /=; try by done.
                                                                             all: by rewrite sg_edgeNeq.
                                                                      ++++++ by apply: h'_copaw_hom.
                                                               ------ case: (boolP (b1 -- c2))=> [b1_adj_c2 | b1_nadj_c2].
                                                                      ++++++ left; exists (hom_G4_def a1 b1 c2 d2).
                                                                             ****** apply: h'_G4_inj; rewrite /=; try by done.
                                                                                    all: try by rewrite sg_edgeNeq.
                                                                                    by move: b1_adj_c2; apply/contraTneq => ->.
                                                                             ****** by apply: h'_copaw_hom.
                                                                      ++++++ have b2_neq_c1 : b2 != c1 by move: b1_adj_b2; apply/contraTneq => ->.
                                                                             have b1_neq_c2:  b1 != c2 by move: a2_adj_b1; apply/contraTneq => ->.
                                                                             left; exists (hom_G4_def b1 b2 c1 d2).
                                                                             ****** apply: h'_G4_inj; rewrite /=; try by done.
                                                                                    ------- by move: a2_adj_b1; apply/contraTneq => ->.
                                                                                    ------- by move: b1_adj_b2; apply/contraTneq => ->.
                                                                             ****** apply: h'_copaw_hom; rewrite /=; try by done.
                                                                                    ------- by rewrite (negbTE b1_neq_c2) (negbTE b2_neq_c1) (negbTE b1_nadj_c2) /= in b1c2b2c1.
                                                   +++++ case: (boolP (a2 -- b2))=> [a2_adj_b2 | a2_nadj_b2].
                                                         ***** case: (boolP (a2 == b1))=> [/eqP a2_eq_b1 | a2_neq_b1]; last first.
                                                               ------ left; exists (hom_G4_def a2 b2 b1 d1).
                                                                      ++++++ apply: h'_G4_inj; rewrite /=; try by done.
                                                                             ****** by rewrite sg_edgeNeq.
                                                                             ****** by rewrite eq_sym sg_edgeNeq.
                                                                             ****** by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                                      ++++++ apply: h'_copaw_hom; rewrite /=; try by done.
                                                                             by rewrite sg_sym.
                                                               ------ case: (boolP (b2 -- c1))=> [b2_adj_c1 | b2_nadj_c1].
                                                                      ++++++ left; exists (hom_G4_def a2 b2 c1 d1).
                                                                             ****** apply: h'_G4_inj; rewrite /=; try by done.
                                                                                    ------- by rewrite sg_edgeNeq.
                                                                                    ------- by move: b1_adj_b2; apply/contraTneq => ->; rewrite -a2_eq_b1.
                                                                                    ------- by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                                                             ****** by apply: h'_copaw_hom.
                                                                      ++++++ have b1_neq_c2: b1 != c2 by rewrite -a2_eq_b1; move: a1_adj_a2; apply/contraTneq => ->.
                                                                             have b2_neq_c1: b2 != c1 by move: b1_adj_b2; apply/contraTneq => ->; rewrite -a2_eq_b1.
                                                                             left; exists (hom_G4_def a1 a2 c2 d1).
                                                                             ****** apply: h'_G4_inj; rewrite /=; try by done.
                                                                                    by move: d1_adj_d2; apply/contraTneq => <-.
                                                                             ****** apply: h'_copaw_hom; rewrite /=; try by done.
                                                                                    rewrite a2_eq_b1.
                                                                                    by rewrite (negbTE b1_neq_c2) (negbTE b2_neq_c1) (negbTE b2_nadj_c1) /= orbC /= orbC /= in b1c2b2c1.
                                                         ***** have a1_neq_b2: a1 != b2 by move: a1_adj_a2; apply/contraTneq => ->; rewrite sg_sym.
                                                               have a2_neq_b1: a2 != b1 by move: a2_nadj_b2; apply/contraTneq => ->; rewrite b1_adj_b2.
                                                               left; exists (hom_G4_def a2 a1 b2 d1).
                                                               ------ apply: h'_G4_inj; rewrite /=; try by done.
                                                                      ++++++ by rewrite eq_sym sg_edgeNeq.
                                                                      ++++++ by move: b1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
                                                                      ++++++ by move: a1_adj_a2; apply/contraTneq => ->; rewrite sg_sym.
                                                               ------ apply: h'_copaw_hom; rewrite /=; try by done.
                                                                      ++++++ by rewrite sg_sym.
                                                                      ++++++ by rewrite (negbTE a1_neq_b2) (negbTE a2_neq_b1) (negbTE a2_nadj_b1) /= orbC /= orbC /= in a1b2a2b1.
Qed.

Lemma h'_claw_hom (h' : claw -> G)
    (e_v0v1 : h' 'v0@4 -- h' 'v1@4) (e_v0v2 : h' 'v0@4 -- h' 'v2@4)
    (e_v0v3 : h' 'v0@4 -- h' 'v3@4) (n_v1v2 : ~~ h' 'v1@4 -- h' 'v2@4)
    (n_v1v3 : ~~ h' 'v1@4 -- h' 'v3@4) (n_v2v3 : ~~ h' 'v2@4 -- h' 'v3@4)
       : forall x1 x2 : claw, x1 -- x2 <-> h' x1 -- h' x2.
Proof.
  { rewrite !forallOrdinalI4 ; do 7 try split.
    all: try by [].
    all: try by rewrite !sg_irrefl ; apply/implyP.
    all: try by rewrite [in X in _ -> X]sg_sym.
    all: try by apply: contraLR.
    all: try by rewrite [in X in X -> _]sg_sym ; apply: contraLR.
  }
Qed.

Lemma case_aa_bb_c1c2_d1d2 (h : claw -> trfgraph G) (a1 a2 b1 b2 c1 c2 d1 d2 : G) :
  (d1 == d2) || d1 -- d2 ->
  (a1 == b2) || a1 -- b2 || (a2 == b1) || a2 -- b1 ->
  (a1 == c2) || a1 -- c2 || (a2 == c1) || a2 -- c1 ->
  (a1 == d2) || a1 -- d2 || (a2 == d1) || a2 -- d1 ->
  (a1 != b1) || (a2 != b2) ->
  b1 != c2 ->
  ~~ b1 -- c2 ->
  b2 != c1 ->
  ~~ b2 -- c1 ->
  b1 != d2 ->
  ~~ b1 -- d2 ->
  b2 != d1 ->
  ~~ b2 -- d1 ->
  c1 != d2 ->
  ~~ c1 -- d2 ->
  c2 != d1 ->
  ~~ c2 -- d1 ->
  a1 = a2 ->
  b1 = b2 ->
  c1 -- c2 ->
    (exists2 h0 : claw -> G, injective h0 & induced_hom h0) \/
    (exists2 h0 : bull -> G, injective h0 & induced_hom h0) \/
    (exists2 h0 : 'P_6 -> G, injective h0 & induced_hom h0) \/
    (exists2 h0 : 'CC_6 -> G, injective h0 & induced_hom h0).
Proof.
move => d1d2 a1b2a2b1 a1c2a2c1 a1d2a2d1 a1a2b1b2 ? ? b2_neq_c1 b2_nadj_c1 b1_neq_d2 b1_nadj_d2 b2_neq_d1 b2_nadj_d1 ? ? ? ? a1_eq_a2 b1_eq_b2 c1_adj_c2.
have a1_adj_b1: a1 -- b1.
  case: (orP a1b2a2b1) => [/orP H | ]; last by rewrite a1_eq_a2.
  case: H => [/orP H' | /eqP a2_eq_b1]; last by rewrite -b1_eq_b2 a1_eq_a2 a2_eq_b1 eq_refl in a1a2b1b2.
  case: H' => [/eqP a1_eq_b2 | ]; last by rewrite b1_eq_b2.
  by rewrite  b1_eq_b2 -a1_eq_a2 a1_eq_b2 eq_refl in a1a2b1b2.
have a1_neq_b1: a1 != b1 by rewrite sg_edgeNeq.
have c1_neq_c2: c1 != c2 by rewrite sg_edgeNeq.
case: (boolP (a2 -- c1)) => [a2_adj_c1 | a2_nadj_c1].
- have a2_neq_c1: a2 != c1 by rewrite sg_edgeNeq.
  case: (boolP (a1 -- d2)) => [a1_adj_d2 | a1_nadj_d2].
  + have a1_neq_d2: a1 != d2 by rewrite sg_edgeNeq.
    left; exists (hom_G4_def a1 b1 c1 d2).
    * apply: h'_G4_inj; rewrite /=; try by done.
      all: try by rewrite eq_sym.
      -- by move: a1_adj_d2; apply/contraTneq => ->.
      -- by rewrite b1_eq_b2.
    * apply: h'_claw_hom; rewrite /=; try by done.
      all: try by rewrite sg_sym.
      -- by rewrite a1_eq_a2.
      -- by rewrite b1_eq_b2.
  + have a2_neq_d1: a2 != d1 by move: a1b2a2b1; rewrite a1_eq_a2 b1_eq_b2; apply/contraTneq => ->; rewrite eq_sym sg_sym (negbTE b2_nadj_d1) (negbTE b2_neq_d1).
    have a1_neq_d2: a1 != d2 by move: a1b2a2b1; rewrite -a1_eq_a2 -b1_eq_b2; apply/contraTneq => ->; rewrite eq_sym sg_sym (negbTE b1_nadj_d2) (negbTE b1_neq_d2).
    have a2_adj_d1: a2 -- d1 by rewrite (negbTE a1_neq_d2) (negbTE a2_neq_d1) (negbTE a1_nadj_d2) in a1d2a2d1.
    case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
    * left; exists (hom_G4_def a2 b2 c1 d1).
      -- apply: h'_G4_inj; rewrite /=; try by done.
         all: try by rewrite eq_sym.
         ++ by move: a1a2b1b2; rewrite a1_eq_a2 b1_eq_b2; apply/contraTneq => <-; rewrite eq_refl.
         ++ by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
      -- apply: h'_claw_hom; rewrite /=; try by done.
         all: try by rewrite sg_sym.
         case: (orP a1b2a2b1) => [/orP H |]; last by rewrite b1_eq_b2.
         case: H => [/orP H |/eqP a2_eq_b1]; last by rewrite a1_eq_a2 -b1_eq_b2 a2_eq_b1 eq_refl in a1a2b1b2.
         case: H => [/eqP a1_eq_b2 |]; last by rewrite a1_eq_a2.
         by rewrite -a1_eq_a2 b1_eq_b2 a1_eq_b2 eq_refl in a1a2b1b2.
    * have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
      case: (orP d1d2) => [/eqP d1_eq_d2 | d1_adj_d2].
      -- by rewrite -d1_eq_d2 a1_eq_a2 a2_adj_d1 in a1_nadj_d2.
      -- have d1_neq_d2: d1 != d2 by rewrite sg_edgeNeq.
         case: (boolP (a1 -- c2)) => [a1_adj_c2 | a1_nadj_c2].
         ++ have a1_neq_c2: a1 != c2 by rewrite sg_edgeNeq.
            left; exists (hom_G4_def a2 b1 c2 d1).
            ** apply: h'_G4_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               --- by rewrite -a1_eq_a2.
               --- by rewrite -a1_eq_a2.
               --- by move: c1_adj_d1; apply/contraTneq => <-; rewrite b1_eq_b2 sg_sym.
            ** apply: h'_claw_hom; rewrite /=; try by done.
               all: try by rewrite sg_sym.
               --- by rewrite -a1_eq_a2.
               --- by rewrite -a1_eq_a2.
               --- by rewrite b1_eq_b2.
         ++ right; left; exists (hom_G5_def b1 d2 a1 d1 c1).
            ** apply: h'_G5_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               --- by rewrite b1_eq_b2.
               --- by rewrite b1_eq_b2.
               --- by rewrite a1_eq_a2.
               --- by rewrite a1_eq_a2.
         ** apply: h'_bull_hom; rewrite /=; try by done.
            all: try by rewrite sg_sym.
            --- by rewrite a1_eq_a2.
            --- by rewrite a1_eq_a2.
            --- by rewrite b1_eq_b2.
            --- by rewrite b1_eq_b2.
- have a1_neq_c2: a1 != c2 by move: c1_adj_c2; apply/contraTneq => <-; rewrite a1_eq_a2 sg_sym.
  have a2_neq_c1: a2 != c1 by move: a1b2a2b1; rewrite a1_eq_a2; apply/contraTneq => ->; rewrite b1_eq_b2 eq_sym sg_sym (negbTE b2_nadj_c1) (negbTE b2_neq_c1).
  have a1_adj_c2: a1 -- c2 by rewrite (negbTE a1_neq_c2) (negbTE a2_neq_c1) (negbTE a2_nadj_c1) /= orbC /= orbC /= in a1c2a2c1.
  case: (boolP (a1 -- d2)) => [a1_adj_d2 | a1_nadj_d2].
  + have a1_neq_d2: a1 != d2 by rewrite sg_edgeNeq.
    case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2].
    * have c2_neq_d2: c2 != d2 by rewrite sg_edgeNeq.
      right; left; exists (hom_G5_def b2 c1 a1 c2 d2).
      -- apply: h'_G5_inj; rewrite /=; try by done.
         all: try by rewrite eq_sym.
         ++ by rewrite -b1_eq_b2 eq_sym.
         ++ by rewrite -b1_eq_b2.
         ++ by rewrite -b1_eq_b2.
         ++ by rewrite a1_eq_a2 eq_sym.
      -- apply: h'_bull_hom; rewrite /=; try by done.
         all: try by rewrite sg_sym.
         ++ by rewrite -b1_eq_b2 sg_sym.
         ++ by rewrite -b1_eq_b2.
         ++ by rewrite -b1_eq_b2.
         ++ by rewrite a1_eq_a2 sg_sym.
    * left; exists (hom_G4_def a1 b2 c2 d2).
      -- apply: h'_G4_inj; rewrite /=; try by done.
         all: try by rewrite eq_sym.
         ++ by rewrite -b1_eq_b2.
         ++ by rewrite -b1_eq_b2.
         ++ by rewrite -b1_eq_b2.
         ++ by move: c1_adj_c2; apply/contraTneq => ->.
      -- apply: h'_claw_hom; rewrite /=; try by done.
         all: try by rewrite sg_sym.
         ++ by rewrite -b1_eq_b2.
         ++ by rewrite -b1_eq_b2.
         ++ by rewrite -b1_eq_b2.
  + have a2_neq_d1: a2 != d1 by move: a1_adj_c2; rewrite a1_eq_a2; apply/contraTneq => ->; rewrite sg_sym.
    have a1_neq_d2: a1 != d2 by move: a1b2a2b1; rewrite a1_eq_a2; apply/contraTneq => ->; rewrite -b1_eq_b2 eq_sym sg_sym (negbTE b1_nadj_d2) (negbTE b1_neq_d2).
    have a2_adj_d1: a2 -- d1 by rewrite (negbTE a2_neq_d1) (negbTE a1_neq_d2) (negbTE a1_nadj_d2) in a1d2a2d1.
         left; exists (hom_G4_def a1 b1 c2 d1).
         * apply: h'_G4_inj; rewrite /=; try by done.
           all: try by rewrite eq_sym.
           -- by rewrite a1_eq_a2.
           -- by rewrite b1_eq_b2.
         * apply: h'_claw_hom; rewrite /=; try by done.
           all: try by rewrite sg_sym.
           -- by rewrite a1_eq_a2.
           -- by rewrite b1_eq_b2.
Qed.

Lemma case_aa_b1b2_c1c2_d1d2 (h : claw -> trfgraph G) (a1 a2 b1 b2 c1 c2 d1 d2 : G) :
  (a1 == c2) || a1 -- c2 || (a2 == c1) || a2 -- c1 ->
  (a1 == d2) || a1 -- d2 || (a2 == d1) || a2 -- d1 ->
  b1 != c2 ->
  ~~ b1 -- c2 ->
  b2 != c1 ->
  ~~ b2 -- c1 ->
  b1 != d2 ->
  ~~ b1 -- d2 ->
  b2 != d1 ->
  ~~ b2 -- d1 ->
  c1 != d2 ->
  ~~ c1 -- d2 ->
  c2 != d1 ->
  ~~ c2 -- d1 ->
  a1 = a2 ->
  b1 -- b2 ->
  c1 -- c2 ->
  d1 -- d2 ->
  a2 -- b1 ->
    ((exists2 h0 : claw -> G, injective h0 & induced_hom h0) \/
    (exists2 h0 : bull -> G, injective h0 & induced_hom h0) \/
    (exists2 h0 : 'P_6 -> G, injective h0 & induced_hom h0) \/
    (exists2 h0 : 'CC_6 -> G, injective h0 & induced_hom h0)).
Proof.
move => a1c2a2c1 a1d2a2d1 ? ? ? ? ? ? ? ? ? ? ? ? a1_eq_a2 b1_adj_b2 c1_adj_c2 d1_adj_d2 a2_adj_b1.
have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
have b1_neq_b2: b1 != b2 by rewrite sg_edgeNeq.
have c1_neq_c2: c1 != c2 by rewrite sg_edgeNeq.
have d1_neq_d2: d1 != d2 by rewrite sg_edgeNeq.
case: (boolP (a2 -- c1)) => [a2_adj_c1 | a2_nadj_c1].
- have a2_neq_c1: a2 != c1 by rewrite sg_edgeNeq.
  case: (boolP (a1 -- d2)) => [a1_adj_d2 | a1_nadj_d2].
  + have a1_neq_d2: a1 != d2 by rewrite sg_edgeNeq.
    case: (boolP (b1 -- c1)) => [b1_adj_c1 | b1_nadj_c1]; last first.
    * left; exists (hom_G4_def a2 b1 c1 d2).
      -- apply: h'_G4_inj; rewrite /=; try by done.
         all: try by rewrite eq_sym.
         ++ by rewrite -a1_eq_a2.
         ++ by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
      -- apply: h'_claw_hom; rewrite /=; try by done.
         all: try by rewrite sg_sym.
         by rewrite -a1_eq_a2.
    * have b1_neq_c1: b1 != c1 by rewrite sg_edgeNeq.
      case: (boolP (b2 -- d2)) => [b2_adj_d2 | b2_nadj_d2]; last first.
      -- case: (boolP (a1 -- b2)) => [a1_adj_b2 | a1_nadj_b2]; last first.
         ++ right; left; exists (hom_G5_def b2 d2 b1 a1 c1).
            ** apply: h'_G5_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               --- by move: b1_adj_b2; apply/contraTneq => ->.
               --- by rewrite a1_eq_a2; move: a2_adj_c1; apply/contraTneq => <-.
               --- by rewrite a1_eq_a2 eq_sym.
               --- by rewrite a1_eq_a2.
            ** apply: h'_bull_hom; rewrite /=; try by done.
               all: try by rewrite sg_sym.
               --- by rewrite a1_eq_a2 sg_sym.
               --- by rewrite a1_eq_a2.
         ++ have a1_neq_b2: a1 != b2 by rewrite sg_edgeNeq.
            left; exists (hom_G4_def a1 b2 c1 d2).
            ** apply: h'_G4_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               --- by rewrite a1_eq_a2.
               --- by move: b1_adj_b2; apply/contraTneq => ->.
            ** apply: h'_claw_hom; rewrite /=; try by done.
               all: try by rewrite sg_sym.
               by rewrite a1_eq_a2.
      -- have b2_neq_d2: b2 != d2 by rewrite sg_edgeNeq.
         case: (boolP (a1 -- c2)) => [a1_adj_c2 | a1_nadj_c2]; last first.
         ++ case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2]; last first.
            ** right; left; exists (hom_G5_def c2 d2 c1 a1 b1).
               --- apply: h'_G5_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   all: try by move: a1_adj_d2; apply/contraTneq => <-.
                   by rewrite a1_eq_a2.
               --- apply: h'_bull_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   +++ by rewrite a1_eq_a2 sg_sym.
                   +++ by rewrite a1_eq_a2.
            ** have c2_neq_d2: c2 != d2 by rewrite sg_edgeNeq.
               case: (boolP (b2 -- c2)) => [b2_adj_c2 | b2_nadj_c2]; last first.
               --- left; exists (hom_G4_def d2 d1 c2 b2).
                   +++ apply: h'_G4_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                   +++ apply: h'_claw_hom; rewrite /=; try by done.
                       all: by rewrite sg_sym.
               --- have b2_neq_c2: b2 != c2 by rewrite sg_edgeNeq.
                   case: (boolP (b1 -- d1)) => [b1_adj_d1 | b1_nadj_d1]; last first.
                   +++ right; left; exists (hom_G5_def d1 b1 d2 b2 c2).
                       *** apply: h'_G5_inj; rewrite /=; try by done.
                           all: try by rewrite eq_sym.
                           by move: d1_adj_d2; apply/contraTneq => ->.
                       *** apply: h'_bull_hom; rewrite /=; try by done.
                           all: by rewrite sg_sym.
                   +++ have b1_neq_d1: b1 != d1 by rewrite sg_edgeNeq.
                       case: (boolP (a2 -- d1)) => [a2_adj_d1 | a2_nadj_d1]; last first.
                       *** case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
                           ---- right; left; exists (hom_G5_def c2 d1 c1 b1 a2).
                                ++++ apply: h'_G5_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     **** by move: a2_adj_b1; apply/contraTneq => <-; rewrite sg_sym.
                                     **** by move: d1_adj_d2; apply/contraTneq => ->.
                                     **** by move: a2_adj_c1; apply/contraTneq => <-; rewrite sg_sym.
                                ++++ apply: h'_bull_hom; rewrite /=; try by done.
                                     all: try by rewrite sg_sym.
                                     by rewrite -a1_eq_a2 sg_sym.
                           ---- have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
                                case: (boolP (a1 -- b2)) => [a1_adj_b2 | a1_nadj_b2].
                                ++++ have a1_neq_b2: a1 != b2 by rewrite sg_edgeNeq.
                                     left; exists (hom_G4_def c1 c2 d1 a2).
                                     **** apply: h'_G4_inj; rewrite /=; try by done.
                                          all: try by rewrite eq_sym.
                                          ----- by move: a2_adj_b1; apply/contraTneq => <-; rewrite sg_sym.
                                          ----- by move: a1_adj_b2; rewrite a1_eq_a2; apply/contraTneq => <-; rewrite sg_sym.
                                     **** apply: h'_claw_hom; rewrite /=; try by done.
                                          all: try by rewrite sg_sym.
                                          by rewrite -a1_eq_a2 sg_sym.
                                ++++ case: (boolP (a2 == d1)) => [/eqP a2_eq_d1 | a2_neq_d1]; last first. 
                                     ----- left; exists (hom_G4_def b1 b2 a2 d1).
                                           +++++ apply: h'_G4_inj; rewrite /=; try by done.
                                                 all: try by rewrite eq_sym.
                                                 by move: a2_adj_c1; apply/contraTneq => <-.
                                           +++++ apply: h'_claw_hom; rewrite /=; try by done.
                                                 all: try by rewrite sg_sym.
                                                 by rewrite -a1_eq_a2 sg_sym.
                                     ----- right; right; right; exists (hom_G6_def a1 c2 b1 d2 c1 b2).
                                           +++++ apply: h'_G6_inj; rewrite /=; try by done.
                                                 all: try by rewrite eq_sym.
                                                 all: by rewrite a1_eq_a2 a2_eq_d1 eq_sym.
                                           +++++ apply: h'_CC_6_hom; rewrite /=; try by done.
                                                 all: try by rewrite sg_sym.
                                                 all: by rewrite a1_eq_a2.
                       *** have a2_neq_d1: a2 != d1 by rewrite sg_edgeNeq.
                           case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1].
                           ---- have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
                                right; right; right; exists (hom_G6_def d2 c1 b2 d1 c2 b1).
                                ++++ apply: h'_G6_inj; rewrite /=; try by done.
                                     all: by rewrite eq_sym.
                                ++++ apply: h'_CC_6_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
                           ---- case: (boolP (a1 -- b2)) => [a1_adj_b2 | a1_nadj_b2].
                                ++++ have a1_neq_b2: a1 != b2 by rewrite sg_edgeNeq.
                                     left; exists (hom_G4_def a2 b2 d1 c1).
                                     **** apply: h'_G4_inj; rewrite /=; try by done.
                                          all: try by rewrite eq_sym.
                                          ----- by rewrite -a1_eq_a2.
                                          ----- by move: d1_adj_d2; apply/contraTneq => ->.
                                     **** apply: h'_claw_hom; rewrite /=; try by done.
                                          all: try by rewrite sg_sym.
                                          by rewrite -a1_eq_a2.
                                ++++ right; left; exists (hom_G5_def b2 c1 d2 a1 d1).
                                     **** apply: h'_G5_inj; rewrite /=; try by done.
                                          all: try by rewrite eq_sym.
                                          ----- by rewrite a1_eq_a2; move: a2_adj_c1; apply/contraTneq => <-.
                                          ----- by rewrite a1_eq_a2 eq_sym.
                                          ----- by move: d1_adj_d2; apply/contraTneq => <-.
                                          ----- by rewrite a1_eq_a2.
                                     **** apply: h'_bull_hom; rewrite /=; try by done.
                                          all: try by rewrite sg_sym.
                                          ----- by rewrite a1_eq_a2 sg_sym.
                                          ----- by rewrite a1_eq_a2.
         ++ have a1_neq_c2: a1 != c2 by rewrite sg_edgeNeq.
            case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2]; last first.
            ** left; exists (hom_G4_def a1 b1 d2 c2).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   +++ by rewrite a1_eq_a2.
                   +++ by move: d1_adj_d2; apply/contraTneq => ->; rewrite sg_sym.
               --- apply: h'_claw_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   by rewrite a1_eq_a2.
            ** have c2_neq_d2: c2 != d2 by rewrite sg_edgeNeq.
               case: (boolP (b2 -- c2)) => [b2_adj_c2 | b2_nadj_c2]; last first.
               --- left; exists (hom_G4_def d2 d1 c2 b2).
                   +++ apply: h'_G4_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                   +++ apply: h'_claw_hom; rewrite /=; try by done.
                       all: by rewrite sg_sym.
               --- have b2_neq_c2: b2 != c2 by rewrite sg_edgeNeq.
                   case: (boolP (b1 -- d1)) => [b1_adj_d1 | b1_nadj_d1]; last first.
                   +++ right; left; exists (hom_G5_def b1 d1 b2 d2 c2).
                       *** apply: h'_G5_inj; rewrite /=; try by done.
                           all: try by rewrite eq_sym.
                           by move: d1_adj_d2; apply/contraTneq => <-.
                       *** apply: h'_bull_hom; rewrite /=; try by done.
                           all: by rewrite sg_sym.
                   +++ have b1_neq_d1: b1 != d1 by rewrite sg_edgeNeq.
                       case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
                       *** right; left; exists (hom_G5_def c1 d1 c2 d2 b2).
                           ---- apply: h'_G5_inj; rewrite /=; try by done.
                                all: try by rewrite eq_sym.
                                by move: d1_adj_d2; apply/contraTneq => <-.
                           ---- apply: h'_bull_hom; rewrite /=; try by done.
                                all: by rewrite sg_sym.
                       *** have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
                           right; right; right; exists (hom_G6_def d2 c1 b2 d1 c2 b1).
                           ---- apply: h'_G6_inj; rewrite /=; try by done.
                                all: by rewrite eq_sym.
                           ---- apply: h'_CC_6_hom; rewrite /=; try by done.
                                all: by rewrite sg_sym.
  + have a1_neq_d2: a1 != d2 by move: a2_adj_b1; rewrite a1_eq_a2; apply/contraTneq => ->; rewrite sg_sym.
    have a2_neq_d1: a2 != d1 by move: d1_adj_d2; apply/contraTneq => <-; rewrite -a1_eq_a2.
    have a2_adj_d1: a2 -- d1 by rewrite (negbTE a2_neq_d1) (negbTE a1_neq_d2) (negbTE a1_nadj_d2) in a1d2a2d1.
    case: (boolP (a1 -- b2)) => [a1_adj_b2 | a1_nadj_b2].
    * have a1_neq_b2: a1 != b2 by rewrite sg_edgeNeq.
      case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
      -- left; exists (hom_G4_def a2 b2 c1 d1).
         ++ apply: h'_G4_inj; rewrite /=; try by done.
            all: try by rewrite eq_sym.
            ** by rewrite -a1_eq_a2.
            ** by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
         ++ apply: h'_claw_hom; rewrite /=; try by done.
            all: try by rewrite sg_sym.
            by rewrite -a1_eq_a2.
      -- have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
         case: (boolP (b1 -- c1)) => [b1_adj_c1 | b1_nadj_c1]; last first.
         ++ case: (boolP (b1 -- d1)) => [b1_adj_d1 | b1_nadj_d1]; last first.
            ** right; left; exists (hom_G5_def d2 b1 d1 a2 c1).
               --- apply: h'_G5_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   all: try by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                   by rewrite -a1_eq_a2 eq_sym.
               --- apply: h'_bull_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   by rewrite -a1_eq_a2 sg_sym.
            ** have b1_neq_d1: b1 != d1 by rewrite sg_edgeNeq.
               left; exists (hom_G4_def d1 d2 c1 b1).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   by move: b1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
               --- apply: h'_claw_hom; rewrite /=; try by done.
                   all: by rewrite sg_sym.
         ++ have b1_neq_c1: b1 != c1 by rewrite sg_edgeNeq.
            case: (boolP (b1 -- d1)) => [b1_adj_d1 | b1_nadj_d1]; last first.
            *** left; exists (hom_G4_def c1 b1 d1 c2).
                ---- apply: h'_G4_inj; rewrite /=; try by done.
                     all: try by rewrite eq_sym.
                     by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                ---- apply: h'_claw_hom; rewrite /=; try by done.
                     all: by rewrite sg_sym.
            *** have b1_neq_d1: b1 != d1 by rewrite sg_edgeNeq.
                case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2]; last first.
                ---- right; left; exists (hom_G5_def c2 d2 c1 d1 b1).
                     ++++ apply: h'_G5_inj; rewrite /=; try by done.
                          all: try by rewrite eq_sym.
                          by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
                     ++++ apply: h'_bull_hom; rewrite /=; try by done.
                          all: by rewrite sg_sym.
                ---- have c2_neq_d2: c2 != d2 by rewrite sg_edgeNeq.
                     case: (boolP (b2 -- c2)) => [b2_adj_c2 | b2_nadj_c2]; last first.
                     ++++ right; left; exists (hom_G5_def c2 b2 c1 b1 d1).
                          **** apply: h'_G5_inj; rewrite /=; try by done.
                               all: try by rewrite eq_sym.
                               by move: b1_adj_b2; apply/contraTneq => <-.
                          **** apply: h'_bull_hom; rewrite /=; try by done.
                               all: by rewrite sg_sym.
                     ++++ have b2_neq_c2: b2 != c2 by rewrite sg_edgeNeq.
                          case: (boolP (b2 -- d2)) => [b2_adj_d2 | b2_nadj_d2].
                          **** have b2_neq_d2: b2 != d2 by rewrite sg_edgeNeq.
                               right; right; right; exists (hom_G6_def b1 c2 d1 b2 c1 d2).
                               ----- apply: h'_G6_inj; rewrite /=; try by done.
                                     all: by rewrite eq_sym.
                               ----- apply: h'_CC_6_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
                          **** left; exists (hom_G4_def c2 d2 b2 c1).
                               ----- apply: h'_G4_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     by move: b1_adj_b2; apply/contraTneq => <-.
                               ----- apply: h'_claw_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
    * case: (boolP (b1 -- c1)) => [b1_adj_c1 | b1_nadj_c1].
      -- have b1_neq_c1: b1 != c1 by rewrite sg_edgeNeq.
         case: (boolP (b1 -- d1)) => [b1_adj_d1 | b1_nadj_d1]; last first.
         ++ case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
            ** right; left; exists (hom_G5_def b2 d1 b1 a2 c1).
               --- apply: h'_G5_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   +++ by move: a2_adj_c1; apply/contraTneq => <-.
                   +++ by move: b1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
                   +++ by move: d1_adj_d2; apply/contraTneq => ->.
               --- apply: h'_bull_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   by rewrite -a1_eq_a2 sg_sym.
            ** have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
               case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2]; last first.
               --- case: (boolP (a1 -- c2)) => [a1_adj_c2 | a1_nadj_c2]; last first.
                   +++ right; left; exists (hom_G5_def c2 d2 c1 d1 a1).
                       *** apply: h'_G5_inj; rewrite /=; try by done.
                           all: try by rewrite eq_sym.
                           all: try by rewrite a1_eq_a2 eq_sym.
                           ---- by move: c1_adj_c2; apply/contraTneq => ->.
                           ---- by rewrite a1_eq_a2; move: a2_adj_d1; apply/contraTneq => <-.
                       *** apply: h'_bull_hom; rewrite /=; try by done.
                           all: try by rewrite sg_sym.
                           all: by rewrite a1_eq_a2 sg_sym.
                   +++ have a1_neq_c2: a1 != c2 by rewrite sg_edgeNeq.
                       left; exists (hom_G4_def a2 c2 d1 b1).
                       ---- apply: h'_G4_inj; rewrite /=; try by done.
                            all: try by rewrite eq_sym.
                            ++++ by rewrite -a1_eq_a2.
                            ++++ by move: d1_adj_d2; apply/contraTneq => ->.
                       ---- apply: h'_claw_hom; rewrite /=; try by done.
                            all: try by rewrite sg_sym.
                            by rewrite -a1_eq_a2.
               --- have c2_neq_d2: c2 != d2 by rewrite sg_edgeNeq.
                   left; exists (hom_G4_def c1 c2 d1 b1).
                   +++ apply: h'_G4_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       by move: d1_adj_d2; apply/contraTneq => ->.
                   +++ apply: h'_claw_hom; rewrite /=; try by done.
                       all: by rewrite sg_sym.
         ++ have b1_neq_d1: b1 != d1 by rewrite sg_edgeNeq.
            case: (boolP (b2 -- d2)) => [b2_adj_d2 | b2_nadj_d2]; last first.
            ** right; left; exists (hom_G5_def b2 d2 b1 d1 a1).
               --- apply: h'_G5_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   all: try by rewrite a1_eq_a2 eq_sym.
                   +++ by move: b1_adj_b2; apply/contraTneq => ->.
                   +++ by rewrite a1_eq_a2; move: a2_adj_c1; apply/contraTneq => <-.
               --- apply: h'_bull_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   all: by rewrite a1_eq_a2 sg_sym.
            ** have b2_neq_d2: b2 != d2 by rewrite sg_edgeNeq.
               case: (boolP (b2 -- c2)) => [b2_adj_c2 | b2_nadj_c2]; last first.
               --- case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2].
                   +++ have c2_neq_d2: c2 != d2 by rewrite sg_edgeNeq.
                       left; exists (hom_G4_def d2 b2 c2 d1).
                       *** apply: h'_G4_inj; rewrite /=; try by done.
                           all: try by rewrite eq_sym.
                           by move: b1_adj_b2; apply/contraTneq => ->.
                       *** apply: h'_claw_hom; rewrite /=; try by done.
                           all: by rewrite sg_sym.
                   +++ case: (boolP (a1 -- c2)) => [a1_adj_c2 | a1_nadj_c2]; last first.
                       ---- right; left; exists (hom_G5_def b2 c2 b1 c1 a1).
                            ++++ apply: h'_G5_inj; rewrite /=; try by done.
                                 all: try by rewrite eq_sym.
                                 all: try by rewrite a1_eq_a2 eq_sym.
                                 **** by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                                 **** by rewrite a1_eq_a2; move: a2_adj_c1; apply/contraTneq => <-.
                                 **** by rewrite a1_eq_a2; move: a2_adj_d1; apply/contraTneq => <-.
                            ++++ apply: h'_bull_hom; rewrite /=; try by done.
                                 all: try by rewrite sg_sym.
                                 all: by rewrite a1_eq_a2 sg_sym.
                       ---- have a1_neq_c2: a1 != c2 by rewrite sg_edgeNeq.
                            right; left; exists (hom_G5_def d2 c2 d1 a1 b1).
                            ++++ apply: h'_G5_inj; rewrite /=; try by done.
                                 all: try by rewrite eq_sym.
                                 **** by move: a1_adj_c2; apply/contraTneq => <-.
                                 **** by rewrite a1_eq_a2 eq_sym.
                                 **** by rewrite a1_eq_a2.
                            ++++ apply: h'_bull_hom; rewrite /=; try by done.
                                 all: try by rewrite sg_sym.
                                 **** by rewrite a1_eq_a2 sg_sym.
                                 **** by rewrite a1_eq_a2.
               --- have b2_neq_c2: b2 != c2 by rewrite sg_edgeNeq.
                   case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
                   +++ left; exists (hom_G4_def b1 b2 c1 d1).
                       *** apply: h'_G4_inj; rewrite /=; try by done.
                           all: try by rewrite eq_sym.
                           by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                       *** apply: h'_claw_hom; rewrite /=; try by done.
                           all: by rewrite sg_sym.
                   +++ have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
                       case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2]; last first.
                       *** left; exists (hom_G4_def b2 b1 d2 c2).
                           ---- apply: h'_G4_inj; rewrite /=; try by done.
                                all: try by rewrite eq_sym.
                                by move: d1_adj_d2; apply/contraTneq => ->; rewrite sg_sym.
                           ---- apply: h'_claw_hom; rewrite /=; try by done.
                                all: by rewrite sg_sym.
                       *** have c2_neq_d2: c2 != d2 by rewrite sg_edgeNeq.
                           right; right; right; exists (hom_G6_def b1 c2 d1 b2 c1 d2).
                           ---- apply: h'_G6_inj; rewrite /=; try by done.
                                all: by rewrite eq_sym.
                           ---- apply: h'_CC_6_hom; rewrite /=; try by done.
                                all: by rewrite sg_sym.
      -- case: (boolP (b1 -- d1)) => [b1_adj_d1 | b1_nadj_d1]; last first.
         ++ case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
            ** left; exists (hom_G4_def a2 b1 c1 d1).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   +++ by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                   +++ by move: d1_adj_d2; apply/contraTneq => <-.
                   +++ by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
               --- by apply: h'_claw_hom.
            ** have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
               right; left; exists (hom_G5_def d2 b1 d1 a2 c1).
               --- apply: h'_G5_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   +++ by rewrite -a1_eq_a2 eq_sym.
                   +++ by move: d1_adj_d2; apply/contraTneq => <-.
                   +++ by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
               --- apply: h'_bull_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   by rewrite -a1_eq_a2 sg_sym.
         ++ have b1_neq_d1: b1 != d1 by rewrite sg_edgeNeq.
            case: (boolP (b2 -- d2)) => [b2_adj_d2 | b2_nadj_d2]; last first.
            ** right; left; exists (hom_G5_def d2 b2 d1 b1 a2).
               --- apply: h'_G5_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   +++ by move: b1_adj_b2; apply/contraTneq => <-.
                   +++ by rewrite -a1_eq_a2 eq_sym.
                   +++ by move: a2_adj_c1; apply/contraTneq => <-.
               --- apply: h'_bull_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   all: by rewrite -a1_eq_a2 sg_sym.
            ** case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
               --- right; left; exists (hom_G5_def d2 c1 d1 a2 b1).
                   +++ apply: h'_G5_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       *** by rewrite -a1_eq_a2 eq_sym.
                       *** by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                       *** by move: b1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
                   +++ apply: h'_bull_hom; rewrite /=; try by done.
                       all: try by rewrite sg_sym.
                       by rewrite -a1_eq_a2 sg_sym.
               --- have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
                   left; exists (hom_G4_def d1 d2 b1 c1).
                   +++ apply: h'_G4_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       by move: c1_adj_c2; apply/contraTneq => <-.
                   +++ apply: h'_claw_hom; rewrite /=; try by done.
                       all: by rewrite sg_sym.
- have a1_neq_c2: a1 != c2 by rewrite a1_eq_a2; move: a2_adj_b1; apply/contraTneq => ->; rewrite sg_sym.
  case: (boolP (a1 -- d2)) => [a1_adj_d2 | a1_nadj_d2].
  + have a1_neq_d2: a1 != d2 by rewrite sg_edgeNeq.
    have a2_neq_c1: a2 != c1 by rewrite -a1_eq_a2; move: a1_adj_d2; apply/contraTneq => ->.
    have a1_adj_c2: a1 -- c2 by rewrite (negbTE a2_neq_c1) (negbTE a1_neq_c2) (negbTE a2_nadj_c1) /= orbC /= orbC /= in a1c2a2c1.
    case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2]; last first.
    * left; exists (hom_G4_def a2 b1 d2 c2).
      -- apply: h'_G4_inj; rewrite /=; try by done.
         all: try by rewrite eq_sym.
         all: try by rewrite -a1_eq_a2.
         by move: d1_adj_d2; apply/contraTneq => ->; rewrite sg_sym.
      -- apply: h'_claw_hom; rewrite /=; try by done.
         all: try by rewrite sg_sym.
         all: by rewrite -a1_eq_a2.
    * have c2_neq_d2: c2 != d2 by rewrite sg_edgeNeq.
      case: (boolP (b1 -- c1)) => [b1_adj_c1 | b1_nadj_c1]; last first.
      -- right; left; exists (hom_G5_def c1 b1 c2 a2 d2).
         ++ apply: h'_G5_inj; rewrite /=; try by done.
            all: try by rewrite eq_sym.
            ** by move: b1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
            ** by rewrite -a1_eq_a2 eq_sym.
            ** by rewrite -a1_eq_a2.
         ++ apply: h'_bull_hom; rewrite /=; try by done.
            all: try by rewrite sg_sym.
            ** by rewrite -a1_eq_a2 sg_sym.
            ** by rewrite -a1_eq_a2.
      -- have b1_neq_c1: b1 != c1 by rewrite sg_edgeNeq.
         case: (boolP (a1 -- b2)) => [a1_adj_b2 | a1_nadj_b2]; last first.
         ++ case: (boolP (b2 -- c2)) => [b2_adj_c2 | b2_nadj_c2]; last first.
            ** left; exists (hom_G4_def b1 b2 c1 a2).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   by rewrite -a1_eq_a2; move: a1_adj_c2; apply/contraTneq => <-.
               --- apply: h'_claw_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   by rewrite -a1_eq_a2 sg_sym.
            ** have b2_neq_c2: b2 != c2 by rewrite sg_edgeNeq.
               case: (boolP (b2 -- d2)) => [b2_adj_d2 | b2_nadj_d2]; last first.
               --- left; exists (hom_G4_def c2 c1 b2 a1).
                   +++ apply: h'_G4_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       *** by rewrite a1_eq_a2 eq_sym.
                       *** by move: a1_adj_d2; apply/contraTneq => <-.
                   +++ apply: h'_claw_hom; rewrite /=; try by done.
                       all: try by rewrite sg_sym.
                       by rewrite a1_eq_a2 sg_sym.
               --- have b2_neq_d2: b2 != d2 by rewrite sg_edgeNeq.
                   case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
                   +++ right; left; exists (hom_G5_def c1 d1 c2 d2 b2).
                       *** apply: h'_G5_inj; rewrite /=; try by done.
                           all: try by rewrite eq_sym.
                           by move: d1_adj_d2; apply/contraTneq => <-.
                       *** apply: h'_bull_hom; rewrite /=; try by done.
                           all: by rewrite sg_sym.
                   +++ have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
                       case: (boolP (b1 -- d1)) => [b1_adj_d1 | b1_nadj_d1]; last first.
                       *** right; left; exists (hom_G5_def b1 d1 b2 d2 c2).
                           ---- apply: h'_G5_inj; rewrite /=; try by done.
                                all: try by rewrite eq_sym.
                                by move: d1_adj_d2; apply/contraTneq => <-.
                           ---- apply: h'_bull_hom; rewrite /=; try by done.
                                all: by rewrite sg_sym.
                       *** have b1_neq_d1: b1 != d1 by rewrite sg_edgeNeq.
                           right; right; right; exists (hom_G6_def b1 c2 d1 b2 c1 d2).
                           ---- apply: h'_G6_inj; rewrite /=; try by done.
                                all: by rewrite eq_sym.
                           ---- apply: h'_CC_6_hom; rewrite /=; try by done.
                                all: by rewrite sg_sym.
         ++ have a1_neq_b2: a1 != b2 by rewrite sg_edgeNeq.
            case: (boolP (b2 -- d2)) => [b2_adj_d2 | b2_nadj_d2]; last first.
            ** right; left; exists (hom_G5_def c1 d2 b1 a1 b2).
               --- apply: h'_G5_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   all: try by rewrite a1_eq_a2 eq_sym.
                   by move: b1_adj_b2; apply/contraTneq => <-.
               --- apply: h'_bull_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   all: by rewrite a1_eq_a2 sg_sym.
            ** have b2_neq_d2: b2 != d2 by rewrite sg_edgeNeq.
               case: (boolP (a2 -- d1)) => [a2_adj_d1 | a2_nadj_d1].
               --- have a2_neq_d1: a2 != d1 by rewrite sg_edgeNeq.
                   case: (boolP (b2 -- c2)) => [b2_adj_c2 | b2_nadj_c2]; last first.
                   +++ left; exists (hom_G4_def a1 b2 c2 d1).
                       *** apply: h'_G4_inj; rewrite /=; try by done.
                           all: try by rewrite eq_sym.
                           ---- by rewrite a1_eq_a2.
                           ---- by move: b1_adj_b2; apply/contraTneq => ->.
                       *** apply: h'_claw_hom; rewrite /=; try by done.
                           all: try by rewrite sg_sym.
                           by rewrite a1_eq_a2.
                   +++ have b2_neq_c2: b2 != c2 by rewrite sg_edgeNeq.
                       case: (boolP (b1 -- d1)) => [b1_adj_d1 | b1_nadj_d1]; last first.
                       *** left; exists (hom_G4_def a2 b1 c2 d1).
                           ---- apply: h'_G4_inj; rewrite /=; try by done.
                                all: try by rewrite eq_sym.
                                ++++ by rewrite -a1_eq_a2.
                                ++++ by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                           ---- apply: h'_claw_hom; rewrite /=; try by done.
                                all: try by rewrite sg_sym.
                                by rewrite -a1_eq_a2.
                       *** have b1_neq_d1: b1 != d1 by rewrite sg_edgeNeq.
                           case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
                           ---- left; exists (hom_G4_def b1 d1 c1 b2).
                                ++++ apply: h'_G4_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                                ++++ apply: h'_claw_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
                           ---- have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
                                right; right; right; exists (hom_G6_def b1 c2 d1 b2 c1 d2).
                                ++++ apply: h'_G6_inj; rewrite /=; try by done.
                                     all: by rewrite eq_sym.
                                ++++ apply: h'_CC_6_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
               --- case: (boolP (b1 -- d1)) => [b1_adj_d1 | b1_nadj_d1]; last first.
                   +++ right; left; exists (hom_G5_def b1 d1 a2 d2 c2).
                       *** apply: h'_G5_inj; rewrite /=; try by done.
                           all: try by rewrite eq_sym.
                           all: try by rewrite -a1_eq_a2.
                           ---- by move: d1_adj_d2; apply/contraTneq => <-.
                           ---- by rewrite -a1_eq_a2; move: a1_adj_c2; apply/contraTneq => <-; rewrite sg_sym. 
                       *** apply: h'_bull_hom; rewrite /=; try by done.
                           all: try by rewrite sg_sym.
                           all: by rewrite -a1_eq_a2.
                   +++ have b1_neq_d1: b1 != d1 by rewrite sg_edgeNeq.
                       case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
                       *** left; exists (hom_G4_def b1 d1 a2 c1).
                           ---- apply: h'_G4_inj; rewrite /=; try by done.
                                all: try by rewrite eq_sym.
                                ++++ by rewrite -a1_eq_a2; move: a1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                                ++++ by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                           ---- apply: h'_claw_hom; rewrite /=; try by done.
                                all: by rewrite sg_sym.
                       *** have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
                           case: (boolP (b2 -- c2)) => [b2_adj_c2 | b2_nadj_c2]; last first.
                           ---- right; left; exists (hom_G5_def c2 d1 a1 b1 b2).
                                ++++ apply: h'_G5_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     **** by move: b1_adj_b2; apply/contraTneq => <-.
                                     **** by move: a1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                                     **** by move: a1_adj_d2; apply/contraTneq => ->.
                                ++++ apply: h'_bull_hom; rewrite /=; try by done.
                                     all: try by rewrite sg_sym.
                                     **** by rewrite a1_eq_a2.
                                     **** by rewrite a1_eq_a2 sg_sym.
                           ---- have b2_neq_c2: b2 != c2 by rewrite sg_edgeNeq.
                                right; right; right; exists (hom_G6_def b1 c2 d1 b2 c1 d2).
                                ++++ apply: h'_G6_inj; rewrite /=; try by done.
                                     all: by rewrite eq_sym.
                                ++++ apply: h'_CC_6_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
  + have a1_neq_d2: a1 != d2 by rewrite a1_eq_a2; move: a2_adj_b1; apply/contraTneq => ->; rewrite sg_sym.
    have a2_neq_d1: a2 != d1 by move: d1_adj_d2; apply/contraTneq => <-; rewrite -a1_eq_a2.
    have a2_adj_d1: a2 -- d1 by rewrite (negbTE a2_neq_d1) (negbTE a1_neq_d2) (negbTE a1_nadj_d2) in a1d2a2d1.
    have a1_adj_c2: a1 -- c2.
      apply/contraT => a1_nadj_c2.
      have a2_neq_c1: a2 != c1 by move: c1_adj_c2; apply/contraTneq => <-; rewrite -a1_eq_a2.
      by rewrite (negbTE a2_neq_c1) (negbTE a1_neq_c2) (negbTE a1_nadj_c2) (negbTE a2_nadj_c1) in a1c2a2c1.
    have a2_neq_c1: a1 != c2 by rewrite sg_edgeNeq.
    case: (boolP (b1 -- d1)) => [b1_adj_d1 | b1_nadj_d1]; last first.
    * left; exists (hom_G4_def a2 d1 b1 c2).
      -- apply: h'_G4_inj; rewrite /=; try by done.
         all: try by rewrite eq_sym.
         ++ by rewrite -a1_eq_a2.
         ++ by move: d1_adj_d2; apply/contraTneq => ->.
      -- apply: h'_claw_hom; rewrite /=; try by done.
         all: try by rewrite sg_sym.
         by rewrite -a1_eq_a2.
    * have b1_neq_d1: b1 != d1 by rewrite sg_edgeNeq.
      case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2]; last first.
      -- right; left; exists (hom_G5_def c2 d2 a1 d1 b1).
         ++ apply: h'_G5_inj; rewrite /=; try by done.
            all: try by rewrite eq_sym.
            all: try by rewrite a1_eq_a2.
            by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
         ++ apply: h'_bull_hom; rewrite /=; try by done.
            all: try by rewrite sg_sym.
            all: by rewrite a1_eq_a2.
      -- have c2_neq_d2: c2 != d2 by rewrite sg_edgeNeq.
         case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
         ++ left; exists (hom_G4_def c2 d2 a1 c1).
            ** apply: h'_G4_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               by rewrite a1_eq_a2; move: a2_adj_d1; apply/contraTneq => ->. 
            ** apply: h'_claw_hom; rewrite /=; try by done.
               all: try by rewrite sg_sym.
               by rewrite a1_eq_a2.
         ++ have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
            case: (boolP (b1 -- c1)) => [b1_adj_c1 | b1_nadj_c1]; last first.
            ** left; exists (hom_G4_def d1 d2 b1 c1).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   by move: a2_adj_b1; apply/contraTneq => ->. 
               --- apply: h'_claw_hom; rewrite /=; try by done.
                   all: by rewrite sg_sym.
            ** have b1_neq_c1: b1 != c1 by rewrite sg_edgeNeq.
               case: (boolP (b2 -- d2)) => [b2_adj_d2 | b2_nadj_d2]; last first.
               --- right; left; exists (hom_G5_def b2 d2 b1 d1 c1).
                   +++ apply: h'_G5_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       by move: b1_adj_b2; apply/contraTneq => ->.
                   +++ apply: h'_bull_hom; rewrite /=; try by done.
                       all: by rewrite sg_sym.
               --- have b2_neq_d2: b2 != d2 by rewrite sg_edgeNeq.
                   case: (boolP (b2 -- c2)) => [b2_adj_c2 | b2_nadj_c2]; last first.
                   +++ left; exists (hom_G4_def d2 d1 c2 b2).
                       *** apply: h'_G4_inj; rewrite /=; try by done.
                           all: try by rewrite eq_sym.
                           by move: b1_adj_b2; apply/contraTneq => <-.
                       *** apply: h'_claw_hom; rewrite /=; try by done.
                           all: by rewrite sg_sym.
                   +++ have b2_neq_c2: b2 != c2 by rewrite sg_edgeNeq.
                       right; right; right; exists (hom_G6_def b1 c2 d1 b2 c1 d2).
                       *** apply: h'_G6_inj; rewrite /=; try by done.
                           all: by rewrite eq_sym.
                       *** apply: h'_CC_6_hom; rewrite /=; try by done.
                           all: by rewrite sg_sym.
Qed.

Lemma case_a1a2_bb_c1c2_d1d2 (h : claw -> trfgraph G) (a1 a2 b1 b2 c1 c2 d1 d2 : G) :
  (a1 == c2) || a1 -- c2 || (a2 == c1) || a2 -- c1 ->
  (a1 == d2) || a1 -- d2 || (a2 == d1) || a2 -- d1 ->
  b1 != c2 ->
  ~~ b1 -- c2 ->
  b2 != c1 ->
  ~~ b2 -- c1 ->
  b1 != d2 ->
  ~~ b1 -- d2 ->
  b2 != d1 ->
  ~~ b2 -- d1 ->
  c1 != d2 ->
  ~~ c1 -- d2 ->
  c2 != d1 ->
  ~~ c2 -- d1 ->
  a1 -- a2 ->
  b1 = b2 ->
  c1 -- c2 ->
  d1 -- d2 ->
  a1 -- b1 ->
    ((exists2 h0 : claw -> G, injective h0 & induced_hom h0) \/
    (exists2 h0 : bull -> G, injective h0 & induced_hom h0) \/
    (exists2 h0 : 'P_6 -> G, injective h0 & induced_hom h0) \/
    (exists2 h0 : 'CC_6 -> G, injective h0 & induced_hom h0)).
Proof.
move => a1c2a2c1 a1d2a2d1 ? ? ? ? ? ? ? ? ? ? ? ? a1_adj_a2 b1_eq_b2 c1_adj_c2 d1_adj_d2 a1_adj_b1.
have a1_neq_a2: a1 != a2 by rewrite sg_edgeNeq.
have c1_neq_c2: c1 != c2 by rewrite sg_edgeNeq.
have d1_neq_d2: d1 != d2 by rewrite sg_edgeNeq.
have a1_neq_b1: a1 != b1 by rewrite sg_edgeNeq.
case: (boolP (a1 -- d2)) => [a1_adj_d2 | a1_nadj_d2].
- have a1_neq_d2: a1 != d2 by rewrite sg_edgeNeq.
  case: (boolP (a1 -- c1)) => [a1_adj_c1 | a1_nadj_c1].
  + have a1_neq_c1: a1 != c1 by rewrite sg_edgeNeq.
    left; exists (hom_G4_def a1 b1 c1 d2).
    * apply: h'_G4_inj; rewrite /=; try by done.
      all: try by rewrite eq_sym.
      by move: c1_adj_c2; apply/contraTneq => <-. 
    * apply: h'_claw_hom; rewrite /=; try by done.
      all: try by rewrite sg_sym.
      by rewrite b1_eq_b2.
  + case: (boolP (a1 -- c2)) => [a1_adj_c2 | a1_nadj_c2].
    * have a1_neq_c2: a1 != c2 by rewrite sg_edgeNeq.
      case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2]; last first.
      -- left; exists (hom_G4_def a1 b1 c2 d2).
         ++ apply: h'_G4_inj; rewrite /=; try by done.
            all: try by rewrite eq_sym.
            by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
         ++ apply: h'_claw_hom; rewrite /=; try by done.
            all: by rewrite sg_sym.
      -- have c2_neq_d2: c2 != d2 by rewrite sg_edgeNeq.
         case: (boolP (a1 -- d1)) => [a1_adj_d1 | a1_nadj_d1].
         ++ have a1_neq_d1: a1 != d1 by rewrite sg_edgeNeq.
            left; exists (hom_G4_def a1 b1 c2 d1).
            ** apply: h'_G4_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               by move: d1_adj_d2; apply/contraTneq => <-.
            ** apply: h'_claw_hom; rewrite /=; try by done.
               all: try by rewrite sg_sym.
               by rewrite b1_eq_b2.
         ++ right; left; exists (hom_G5_def b1 d1 a1 d2 c2).
            ** apply: h'_G5_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               --- by move: d1_adj_d2; apply/contraTneq => <-.
               --- by move: a1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
            ** apply: h'_bull_hom; rewrite /=; try by done.
               all: try by rewrite sg_sym.
               by rewrite b1_eq_b2.
    * have a2_neq_c1: a2 != c1 by move: a1_adj_a2; apply/contraTneq => ->.
      have a1_neq_c2: a1 != c2 by move: a1_adj_b1; apply/contraTneq => ->; rewrite sg_sym.
      have a2_adj_c1: a2 -- c1 by rewrite (negbTE a2_neq_c1) (negbTE a1_neq_c2) (negbTE a1_nadj_c2) in a1c2a2c1.
      case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2].
      -- have c2_neq_d2: c2 != d2 by rewrite sg_edgeNeq.
         case: (boolP (a1 -- d1)) => [a1_adj_d1 | a1_nadj_d1]; last first.
         ++ left; exists (hom_G4_def d2 d1 c2 a1).
            ** apply: h'_G4_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               by move: a1_adj_b1; apply/contraTneq => <-; rewrite sg_sym b1_eq_b2.
            ** apply: h'_claw_hom; rewrite /=; try by done.
               all: by rewrite sg_sym.
         ++ have a1_neq_d1: a1 != d1 by rewrite sg_edgeNeq.
            right; left; exists (hom_G5_def b1 c2 a1 d2 d1).
            ** apply: h'_G5_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               by rewrite b1_eq_b2.
            ** apply: h'_bull_hom; rewrite /=; try by done.
               all: try by rewrite sg_sym.
               by rewrite b1_eq_b2.
      -- case: (boolP (a2 -- d2)) => [a2_adj_d2 | a2_nadj_d2]; last first.
         ++ case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1].
            ** have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
               right; left; exists (hom_G5_def d2 c1 a1 a2 b1).
               --- apply: h'_G5_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   +++ by move: a2_adj_c1; apply/contraTneq => <-; rewrite sg_sym.
                   +++ by move: a1_adj_b1; apply/contraTneq => <-; rewrite sg_sym b1_eq_b2.
                   +++ by move: a1_adj_b1; apply/contraTneq => <-.
               --- apply: h'_bull_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   by rewrite sg_sym b1_eq_b2.
            ** left; exists (hom_G4_def a1 b1 a2 d2).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   +++ by move: a2_adj_c1; apply/contraTneq => <-; rewrite b1_eq_b2.
                   +++ by move: a2_adj_c1; apply/contraTneq => ->; rewrite sg_sym.
               --- apply: h'_claw_hom; rewrite /=; try by done.
                   all: by rewrite sg_sym.
         ++ have a2_neq_d2: a2 != d2 by rewrite sg_edgeNeq.
            case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1]; last first.
            ** right; left; exists (hom_G5_def b1 c1 a1 a2 d2).
               --- apply: h'_G5_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   +++ by rewrite b1_eq_b2.
                   +++ by move: a2_adj_c1; apply/contraTneq => <-; rewrite b1_eq_b2.
                   +++ by move: a1_adj_b1; apply/contraTneq => <-; rewrite sg_sym b1_eq_b2.
               --- apply: h'_bull_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   by rewrite b1_eq_b2.
            ** have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
               left; exists (hom_G4_def a2 b1 c1 d2).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   by rewrite b1_eq_b2.
               --- apply: h'_claw_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   by rewrite b1_eq_b2.
- have a1_neq_d2: a1 != d2 by move: a1_adj_b1; apply/contraTneq => ->; rewrite sg_sym.
  case: (boolP (a1 -- d1)) => [a1_adj_d1 | a1_nadj_d1]; last first.
  + have a2_neq_d1: a2 != d1 by move: a1_adj_a2; apply/contraTneq => ->.
    have a2_adj_d1: a2 -- d1 by rewrite (negbTE a2_neq_d1) (negbTE a1_neq_d2) (negbTE a1_nadj_d2) in a1d2a2d1.
    case: (boolP (a2 -- c2)) => [a2_adj_c2 | a2_nadj_c2].
    * have a2_neq_c2: a2 != c2 by rewrite sg_edgeNeq.
      case: (boolP (a1 -- c2)) => [a1_adj_c2 | a1_nadj_c2]; last first.
      -- left; exists (hom_G4_def a2 a1 d1 c2).
         ++ apply: h'_G4_inj; rewrite /=; try by done.
            all: try by rewrite eq_sym.
            ** by move: a1_adj_b1; apply/contraTneq => ->; rewrite b1_eq_b2 sg_sym.
            ** by move: a1_adj_b1; apply/contraTneq => ->; rewrite sg_sym.
         ++ apply: h'_claw_hom; rewrite /=; try by done.
            all: by rewrite sg_sym.
      -- have a1_neq_c2: a1 != c2 by rewrite sg_edgeNeq.
         case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1]; last first.
         ++ right; left; exists (hom_G5_def b1 d1 a1 a2 c2).
            ** apply: h'_G5_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               --- by rewrite b1_eq_b2.
               --- by move: a2_adj_d1; apply/contraTneq => <-; rewrite b1_eq_b2.
               --- by move: a1_adj_b1; apply/contraTneq => <-; rewrite sg_sym b1_eq_b2.
            ** apply: h'_bull_hom; rewrite /=; try by done.
               all: try by rewrite sg_sym.
               by rewrite b1_eq_b2.
         ++ have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
            left; exists (hom_G4_def a2 b1 d1 c2).
            ** apply: h'_G4_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               by rewrite b1_eq_b2.
            ** apply: h'_claw_hom; rewrite /=; try by done.
               all: try by rewrite sg_sym.
               by rewrite b1_eq_b2.
    * case: (boolP (a1 -- c2)) => [a1_adj_c2 | a1_nadj_c2].
      -- have a1_neq_c2: a1 != c2 by rewrite sg_edgeNeq.
         case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1]; last first.
         ++ left; exists (hom_G4_def a1 a2 c2 b1).
            ** apply: h'_G4_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               --- by move: a2_adj_d1; apply/contraTneq => ->.
               --- by move: a2_adj_d1; apply/contraTneq => ->; rewrite b1_eq_b2.
            ** apply: h'_claw_hom; rewrite /=; try by done.
               all: by rewrite sg_sym.
         ++ have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq. 
            right; left; exists (hom_G5_def c2 d1 a1 a2 b1).
            ** apply: h'_G5_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               --- by move: a2_adj_d1; apply/contraTneq => <-.
               --- by move: a1_adj_b1; apply/contraTneq => <-; rewrite sg_sym b1_eq_b2.
               --- by rewrite b1_eq_b2 eq_sym.
            ** apply: h'_bull_hom; rewrite /=; try by done.
               all: try by rewrite sg_sym.
               by rewrite b1_eq_b2 sg_sym.
      -- have a1_neq_c2: a1 != c2 by move: a1_adj_a2; apply/contraTneq => ->; rewrite sg_sym.
         have a2_neq_c1: a2 != c1 by move: c1_adj_c2; apply/contraTneq => <-.
         have a2_adj_c1: a2 -- c1 by rewrite (negbTE a2_neq_c1) (negbTE a1_neq_c2) (negbTE a1_nadj_c2) in a1c2a2c1.
         case: (boolP (a1 -- c1)) => [a1_adj_c1 | a1_nadj_c1].
         ++ have a1_neq_c1: a1 != c1 by rewrite sg_edgeNeq.
            case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1]; last first.
            ** right; left; exists (hom_G5_def c2 b1 c1 a1 a2).
               --- apply: h'_G5_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   +++ by move: a2_adj_d1; apply/contraTneq => <-.
                   +++ by move: a2_adj_c1; apply/contraTneq => <-.
                   +++ by move: a2_adj_c1; apply/contraTneq => <-; rewrite b1_eq_b2.
               --- apply: h'_bull_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   by rewrite b1_eq_b2.
            ** have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
               case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
               --- left; exists (hom_G4_def a2 b1 c1 d1).
                   +++ apply: h'_G4_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       *** by move: c1_adj_c2; apply/contraTneq => <-.
                       *** by rewrite b1_eq_b2.
                       *** by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                   +++ apply: h'_claw_hom; rewrite /=; try by done.
                       all: try by rewrite sg_sym.
                       all: by rewrite b1_eq_b2.
               --- have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
                   right; left; exists (hom_G5_def c2 b1 c1 a2 d1).
                   +++ apply: h'_G5_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       *** by move: a2_adj_d1; apply/contraTneq => <-.
                       *** by move: c1_adj_c2; apply/contraTneq => <-.
                       *** by rewrite b1_eq_b2.
                   +++ apply: h'_bull_hom; rewrite /=; try by done.
                       all: try by rewrite sg_sym.
                       all: by rewrite b1_eq_b2.
         ++ case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
            ** left; exists (hom_G4_def a2 a1 c1 d1).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   +++ by move: c1_adj_c2; apply/contraTneq => <-.
                   +++ by move: a1_adj_b1; apply/contraTneq => ->; rewrite sg_sym b1_eq_b2.
                   +++ by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
               --- apply: h'_claw_hom; rewrite /=; try by done.
                   all: by rewrite sg_sym.
            ** have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
               case: (boolP (a2 -- d2)) => [a2_adj_d2 | a2_nadj_d2]; last first.
               --- right; left; exists (hom_G5_def a1 d2 a2 d1 c1).
                   +++ apply: h'_G5_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       *** by move: a1_adj_b1; apply/contraTneq => ->; rewrite sg_sym b1_eq_b2.
                       *** by move: c1_adj_c2; apply/contraTneq => <-.
                       *** by move: a2_adj_c1; apply/contraTneq => <-; rewrite sg_sym.
                   +++ apply: h'_bull_hom; rewrite /=; try by done.
                       all: by rewrite sg_sym.
               --- have a2_neq_d2: a2 != d2 by rewrite sg_edgeNeq.
                   left; exists (hom_G4_def a2 a1 c1 d2).
                   +++ apply: h'_G4_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       by move: a1_adj_b1; apply/contraTneq => ->; rewrite sg_sym b1_eq_b2.
                   +++ apply: h'_claw_hom; rewrite /=; try by done.
                       all: by rewrite sg_sym.
  + have a1_neq_d1: a1 != d1 by rewrite sg_edgeNeq.
    case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1].
    * have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
      have a2_neq_d1: a2 != d1 by move: a2_adj_b1; apply/contraTneq => ->; rewrite sg_sym b1_eq_b2.
      have a2_adj_d1: a2 -- d1 by rewrite (negbTE a2_neq_d1) (negbTE a1_neq_d2) (negbTE a1_nadj_d2) in a1d2a2d1.
      have a1_neq_c2: a1 != c2 by move: a1_adj_b1; apply/contraTneq => ->; rewrite sg_sym.
      have a2_neq_c1: a2 != c1 by move: a2_adj_b1; apply/contraTneq => ->; rewrite sg_sym b1_eq_b2.
      case: (boolP (a1 -- c2)) => [a1_adj_c2 | a1_nadj_c2].
      -- left; exists (hom_G4_def a1 b1 c2 d1).
         ++ apply: h'_G4_inj; rewrite /=; try by done.
            all: try by rewrite eq_sym.
            by rewrite b1_eq_b2.
         ++ apply: h'_claw_hom; rewrite /=; try by done.
            all: try by rewrite sg_sym.
            by rewrite b1_eq_b2.
      -- have a2_adj_c1: a2 -- c1 by rewrite (negbTE a2_neq_c1) (negbTE a1_neq_c2) (negbTE a1_nadj_c2) in a1c2a2c1.
         case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
         ++ left; exists (hom_G4_def a2 b1 c1 d1).
            ** apply: h'_G4_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               all: try by rewrite b1_eq_b2.
               by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
            ** apply: h'_claw_hom; rewrite /=; try by done.
               all: try by rewrite sg_sym.
               all: by rewrite b1_eq_b2.
         ++ have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
            case: (boolP (a2 -- c2)) => [a2_adj_c2 | a2_nadj_c2]; last first.
            ** right; left; exists (hom_G5_def c2 b1 c1 a2 d1).
               --- apply: h'_G5_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   all: try by rewrite b1_eq_b2.
                   by move: a2_adj_d1; apply/contraTneq => <-.
               --- apply: h'_bull_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   all: by rewrite b1_eq_b2.
            ** have a2_neq_c2: a2 != c2 by rewrite sg_edgeNeq.
               left; exists (hom_G4_def a2 c2 d1 b1).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   by rewrite b1_eq_b2 eq_sym.
               --- apply: h'_claw_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   by rewrite b1_eq_b2 sg_sym.
    * case: (boolP (a2 -- d1)) => [a2_adj_d1 | a2_nadj_d1]; last first.
      -- case: (boolP (a2 -- c2)) => [a2_adj_c2 | a2_nadj_c2].
         ++ have a2_neq_c2: a2 != c2 by rewrite sg_edgeNeq.
            left; exists (hom_G4_def a1 b1 a2 d1).
            ** apply: h'_G4_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               --- by move: a2_adj_c2; apply/contraTneq => <-.
               --- by move: d1_adj_d2; apply/contraTneq => <-.
               --- by move: a2_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
            ** apply: h'_claw_hom; rewrite /=; try by done.
               all: try by rewrite sg_sym.
               by rewrite b1_eq_b2.
         ++ case: (boolP (a2 -- c1)) => [a2_adj_c1 | a2_nadj_c1].
            ** have a2_neq_c1: a2 != c1 by rewrite sg_edgeNeq.
               case: (boolP (a2 -- d2)) => [a2_adj_d2 | a2_nadj_d2]; last first.
               --- left; exists (hom_G4_def a1 b1 a2 d1).
                   +++ apply: h'_G4_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       all: try by move: d1_adj_d2; apply/contraTneq => <-.
                       by move: a2_adj_c1; apply/contraTneq => <-; rewrite b1_eq_b2.
                   +++ apply: h'_claw_hom; rewrite /=; try by done.
                       all: try by rewrite sg_sym.
                       by rewrite b1_eq_b2.
               --- have a2_neq_d2: a2 != d2 by rewrite sg_edgeNeq.
                   case: (boolP (a1 -- c1)) => [a1_adj_c1 | a1_nadj_c1]; last first.
                   +++ left; exists (hom_G4_def a2 a1 c1 d2).
                       *** apply: h'_G4_inj; rewrite /=; try by done.
                           all: try by rewrite eq_sym.
                           by move: a1_adj_b1; apply/contraTneq => ->; rewrite b1_eq_b2 sg_sym.
                       *** apply: h'_claw_hom; rewrite /=; try by done.
                           all: by rewrite sg_sym.
                   +++ have a1_neq_c1: a1 != c1 by rewrite sg_edgeNeq.
                       case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
                       *** left; exists (hom_G4_def a1 b1 c1 d1).
                           ---- apply: h'_G4_inj; rewrite /=; try by done.
                                all: try by rewrite eq_sym.
                                all: try by rewrite b1_eq_b2.
                                by move: d1_adj_d2; apply/contraTneq => <-.
                           ---- apply: h'_claw_hom; rewrite /=; try by done.
                                all: try by rewrite sg_sym.
                                all: by rewrite b1_eq_b2.
                       *** have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
                           right; left; exists (hom_G5_def b1 d2 a1 d1 c1).
                           ---- apply: h'_G5_inj; rewrite /=; try by done.
                                all: try by rewrite eq_sym.
                                all: by rewrite b1_eq_b2.
                           ---- apply: h'_bull_hom; rewrite /=; try by done.
                                all: try by rewrite sg_sym.
                                all: by rewrite b1_eq_b2.
            ** have a2_neq_c1: a2 != c1 by move: c1_adj_c2; apply/contraTneq => <-.
               have a1_neq_c2: a1 != c2 by move: a1_adj_a2; apply/contraTneq => ->; rewrite sg_sym.
               have a1_adj_c2: a1 -- c2 by rewrite (negbTE a2_neq_c1) (negbTE a1_neq_c2) (negbTE a2_nadj_c1) /= orbC /= orbC /= in a1c2a2c1.
               left; exists (hom_G4_def a1 b1 c2 d1).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   by rewrite b1_eq_b2.
               --- apply: h'_claw_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   by rewrite b1_eq_b2.
      -- have a2_neq_d1: a2 != d1 by rewrite sg_edgeNeq.
         case: (boolP (a2 -- d2)) => [a2_adj_d2 | a2_nadj_d2]; last first.
         ++ right; left; exists (hom_G5_def b1 d2 a1 d1 a2).
            ** apply: h'_G5_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               --- by rewrite b1_eq_b2.
               --- by move: a2_adj_d1; apply/contraTneq => <-; rewrite b1_eq_b2.
               --- by move: a1_adj_a2; apply/contraTneq => <-.
            ** apply: h'_bull_hom; rewrite /=; try by done.
               all: try by rewrite sg_sym.
               by rewrite b1_eq_b2.
         ++ have a2_neq_d2: a2 != d2 by rewrite sg_edgeNeq.
            case: (boolP (a1 -- c1)) => [a1_adj_c1 | a1_nadj_c1]; last first.
            ** case: (boolP (a2 -- c1)) => [a2_adj_c1 | a2_nadj_c1].
               --- have a2_neq_c1: a2 != c1 by rewrite sg_edgeNeq.
                   left; exists (hom_G4_def a2 a1 c1 d2).
                   +++ apply: h'_G4_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       by move: a1_adj_b1; apply/contraTneq => ->; rewrite b1_eq_b2 sg_sym.
                   +++ apply: h'_claw_hom; rewrite /=; try by done.
                       all: by rewrite sg_sym.
               --- have a2_neq_c1: a2 != c1 by move: a1_adj_a2; apply/contraTneq => ->.
                   have a1_neq_c2: a1 != c2 by move: a1_adj_b1; apply/contraTneq => ->; rewrite sg_sym.
                   have a1_adj_c2: a1 -- c2 by rewrite (negbTE a2_neq_c1) (negbTE a1_neq_c2) (negbTE a2_nadj_c1) /= orbC /= orbC /= in a1c2a2c1.
                   left; exists (hom_G4_def a1 b1 c2 d1).
                   +++ apply: h'_G4_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       by rewrite b1_eq_b2.
                   +++ apply: h'_claw_hom; rewrite /=; try by done.
                       all: try by rewrite sg_sym.
                       by rewrite b1_eq_b2.
            ** have a1_neq_c1: a1 != c1 by rewrite sg_edgeNeq.
               case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
               --- left; exists (hom_G4_def a1 b1 c1 d1).
                   +++ apply: h'_G4_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       all: try by rewrite b1_eq_b2.
                       by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                   +++ apply: h'_claw_hom; rewrite /=; try by done.
                       all: try by rewrite sg_sym.
                       all: by rewrite b1_eq_b2.
               --- have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
                   right; left; exists (hom_G5_def b1 d2 a1 d1 c1).
                   +++ apply: h'_G5_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       all: by rewrite b1_eq_b2.
                   +++ apply: h'_bull_hom; rewrite /=; try by done.
                       all: try by rewrite sg_sym.
                       all: by rewrite b1_eq_b2.
Qed.

Lemma case_a1a2_bb_c1c2_dd (h : claw -> trfgraph G) (a1 a2 b1 b2 c1 c2 d1 d2 : G) :
  (a1 == b2) || a1 -- b2 || (a2 == b1) || (a2 -- b1) ->
  (a1 == c2) || a1 -- c2 || (a2 == c1) || (a2 -- c1) ->
  (a1 == d2) || a1 -- d2 || (a2 == d1) || (a2 -- d1) ->
  b1 != c2 ->
  ~~ b1 -- c2 ->
  b2 != c1 ->
  ~~ b2 -- c1 ->
  b1 != d2 ->
  ~~ b1 -- d2 ->
  b2 != d1 ->
  ~~ b2 -- d1 ->
  c1 != d2 ->
  ~~ c1 -- d2 ->
  c2 != d1 ->
  ~~ c2 -- d1 ->
  a1 -- a2 ->
  b1 = b2 ->
  c1 -- c2 ->
  d1 = d2 ->
    ((exists2 h0 : claw -> G, injective h0 & induced_hom h0) \/
    (exists2 h0 : bull -> G, injective h0 & induced_hom h0) \/
    (exists2 h0 : 'P_6 -> G, injective h0 & induced_hom h0) \/
    (exists2 h0 : 'CC_6 -> G, injective h0 & induced_hom h0)).
Proof.
move => a1b2a2b1 a1c2a2c1 a1d2a2d1 ? ? ? ? ? ? ? ? ? ? ? ? a1_adj_a2 b1_eq_b2 c1_adj_c2 d1_eq_d2.
have a1_neq_a2: a1 != a2 by rewrite sg_edgeNeq.
have c1_neq_c2: c1 != c2 by rewrite sg_edgeNeq.
case: (boolP (a1 -- b2)) => [a1_adj_b2 | a1_nadj_b2].
- have a1_neq_b2: a1 != b2 by rewrite sg_edgeNeq.
  have a1_neq_d2: a1 != d2 by move: a1_adj_b2; apply/contraTneq => ->; rewrite sg_sym -b1_eq_b2.
  case: (boolP (a1 -- c2)) => [a1_adj_c2 | a1_nadj_c2].
  + have a1_neq_c2: a1 != c2 by rewrite sg_edgeNeq.
    case: (boolP (a1 -- d2)) => [a1_adj_d2 | a1_nadj_d2].
    * left; exists (hom_G4_def a1 b2 c2 d2).
      -- apply: h'_G4_inj; rewrite /=; try by done.
         all: try by rewrite eq_sym.
         all: try by rewrite -d1_eq_d2.
         by rewrite -b1_eq_b2.
      -- apply: h'_claw_hom; rewrite /=; try by done.
         all: try by rewrite sg_sym.
         all: try by rewrite -d1_eq_d2.
         by rewrite -b1_eq_b2.
    * have a2_neq_d1: a2 != d1 by move: a1_adj_a2; apply/contraTneq => ->; rewrite d1_eq_d2.
      have a2_adj_d1 : a2 -- d1 by rewrite (negbTE a2_neq_d1) (negbTE a1_neq_d2) (negbTE a1_nadj_d2) in a1d2a2d1.
      case: (boolP (a2 -- c1)) => [a2_adj_c1 | a2_nadj_c1].
      -- have a2_neq_c1: a2 != c1 by rewrite sg_edgeNeq.
         case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1].
         ++ have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
            left; exists (hom_G4_def a2 b1 c1 d1).
            ** apply: h'_G4_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               all: try by rewrite b1_eq_b2.
               by rewrite d1_eq_d2.
            ** apply: h'_claw_hom; rewrite /=; try by done.
               all: try by rewrite sg_sym.
               all: try by rewrite b1_eq_b2.
               by rewrite d1_eq_d2.
         ++ case: (boolP (a1 -- c1)) => [a1_adj_c1 | a1_nadj_c1]; last first.
            ** left; exists (hom_G4_def a2 a1 c1 d1).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   all: try by rewrite d1_eq_d2.
                   by move: a1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
               --- apply: h'_claw_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   all: by rewrite d1_eq_d2.
            ** have a1_neq_c1: a1 != c1 by rewrite sg_edgeNeq.
               right; left; exists (hom_G5_def b2 d1 a1 a2 c1).
               --- apply: h'_G5_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   all: try by rewrite d1_eq_d2 eq_sym.
                   by move: a2_adj_d1; apply/contraTneq => <-.
               --- apply: h'_bull_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   all: try by rewrite d1_eq_d2 sg_sym.
                   by rewrite -b1_eq_b2 sg_sym.
      -- case: (boolP (a2 -- c2)) => [a2_adj_c2 | a2_nadj_c2].
         ++ have a2_neq_c2: a2 != c2 by rewrite sg_edgeNeq.
            case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1]; last first.
            ** right; left; exists (hom_G5_def b2 d1 a1 a2 c2).
               --- apply: h'_G5_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   +++ by move: a2_adj_d1; apply/contraTneq => <-.
                   +++ by rewrite -b1_eq_b2.
                   +++ by rewrite d1_eq_d2 eq_sym.
               --- apply: h'_bull_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   +++ by rewrite -b1_eq_b2 sg_sym.
                   +++ by rewrite -b1_eq_b2.
                   +++ by rewrite d1_eq_d2 sg_sym.
            ** have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
               left; exists (hom_G4_def a2 b1 c2 d1).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   by rewrite b1_eq_b2.
               --- apply: h'_claw_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   by rewrite b1_eq_b2.
         ++ case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1]; last first.
            ** left; exists (hom_G4_def a1 a2 c2 b2).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   +++ by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                   +++ by move: a2_adj_d1; apply/contraTneq => ->. 
                   +++ by rewrite -b1_eq_b2 eq_sym.
               --- apply: h'_claw_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   +++ by rewrite -b1_eq_b2.
                   +++ by rewrite -b1_eq_b2 sg_sym.
            ** have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
               right; left; exists (hom_G5_def c2 d1 a1 a2 b2).
               --- apply: h'_G5_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   +++ by move: a2_adj_d1; apply/contraTneq => <-.
                   +++ by rewrite -b1_eq_b2 eq_sym.
                   +++ by rewrite d1_eq_d2 eq_sym.
                   +++ by rewrite -b1_eq_b2.
               --- apply: h'_bull_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   +++ by rewrite -b1_eq_b2.
                   +++ by rewrite -b1_eq_b2 sg_sym.
                   +++ by rewrite d1_eq_d2 sg_sym.
  + have a1_neq_c2: a1 != c2 by move: a1_adj_b2; apply/contraTneq => ->; rewrite -b1_eq_b2 sg_sym.
    case: (boolP (a2 -- d1)) => [a2_adj_d1 | a2_nadj_d1].
    * have a2_neq_d1: a2 != d1 by rewrite sg_edgeNeq.
      have a2_neq_c1: a2 != c1 by move: a2_adj_d1; apply/contraTneq => ->; rewrite d1_eq_d2.
      have a2_adj_c1: a2 -- c1 by rewrite (negbTE a2_neq_c1) (negbTE a1_neq_c2) (negbTE a1_nadj_c2) in a1c2a2c1.
      case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1].
      -- have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
         left; exists (hom_G4_def a2 b1 c1 d1).
         ++ apply: h'_G4_inj; rewrite /=; try by done.
            all: try by rewrite eq_sym.
            all: try by rewrite b1_eq_b2.
            by rewrite d1_eq_d2.
         ++ apply: h'_claw_hom; rewrite /=; try by done.
            all: try by rewrite sg_sym.
            all: try by rewrite b1_eq_b2.
            by rewrite d1_eq_d2.
      -- case: (boolP (a1 -- c1)) => [a1_adj_c1 | a1_nadj_c1].
         ++ have a1_neq_c1: a1 != c1 by rewrite sg_edgeNeq.
            case: (boolP (a1 -- d2)) => [a1_adj_d2 | a1_nadj_d2]; last first.
            ** right; left; exists (hom_G5_def b2 d1 a1 a2 c1).
               --- apply: h'_G5_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   +++ by move: a2_adj_d1; apply/contraTneq => <-.
                   +++ by move: a1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
                   +++ by rewrite d1_eq_d2 eq_sym.
               --- apply: h'_bull_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   all: try by rewrite d1_eq_d2 sg_sym.
                   by rewrite -b1_eq_b2 sg_sym.
            ** left; exists (hom_G4_def a1 b2 c1 d2).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   by rewrite -b1_eq_b2.
               --- apply: h'_claw_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   by rewrite -b1_eq_b2.
         ++ case: (boolP (a1 -- d2)) => [a1_adj_d2 | a1_nadj_d2]; last first.
            ** left; exists (hom_G4_def a2 a1 c1 d2).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   +++ by rewrite -d1_eq_d2.
                   +++ by move: a1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
               --- apply: h'_claw_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   by rewrite -d1_eq_d2.
            ** right; left; exists (hom_G5_def b2 c1 a1 a2 d2).
               --- apply: h'_G5_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   +++ by move: a2_adj_d1; apply/contraTneq => <-.
                   +++ by rewrite -b1_eq_b2.
                   +++ by move: a1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
                   +++ by rewrite -d1_eq_d2.
               --- apply: h'_bull_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   +++ by rewrite -d1_eq_d2.
                   +++ by rewrite -b1_eq_b2 sg_sym.
                   +++ by rewrite -b1_eq_b2.
    * have a1_adj_d2: a1 -- d2.
        apply: contraT => a1_nadj_d2.
        have a2_neq_d1: a2 != d1 by move: a1_adj_a2; apply/contraTneq => ->; rewrite d1_eq_d2.
        by rewrite (negbTE a2_neq_d1) (negbTE a1_neq_d2) (negbTE a1_nadj_d2) (negbTE a2_nadj_d1) in a1d2a2d1.
      case: (boolP (a2 -- c2)) => [a2_adj_c2 | a2_nadj_c2]; last first.
      -- have a2_neq_c1: a2 != c1 by move: c1_adj_c2; apply/contraTneq => <-.
         have a2_adj_c1: a2 -- c1 by rewrite (negbTE a2_neq_c1) (negbTE a1_neq_c2) (negbTE a1_nadj_c2) in a1c2a2c1.
         case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1]; last first.
         ++ left; exists (hom_G4_def a1 a2 b2 d2).
            ** apply: h'_G4_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               --- by move: a2_adj_c1; apply/contraTneq => ->.
               --- by move: a2_adj_c1; apply/contraTneq => ->; rewrite sg_sym.
               --- by rewrite -b1_eq_b2.
            ** apply: h'_claw_hom; rewrite /=; try by done.
               all: try by rewrite sg_sym.
               all: try by rewrite -b1_eq_b2.
               by rewrite -d1_eq_d2.
         ++ have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
            case: (boolP (a1 -- c1)) => [a1_adj_c1 | a1_nadj_c1]; last first.
            ** right; left; exists (hom_G5_def c1 d2 a2 a1 b2).
               --- apply: h'_G5_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   +++ by move: a1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
                   +++ by move: a2_adj_b1; apply/contraTneq => <-; rewrite sg_sym.
                   +++ by rewrite -d1_eq_d2 eq_sym.
                   +++ by rewrite -b1_eq_b2.
               --- apply: h'_bull_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   +++ by rewrite -b1_eq_b2.
                   +++ by rewrite -d1_eq_d2 sg_sym.
                   +++ by rewrite -b1_eq_b2 sg_sym.
            ** have a1_neq_c1: a1 != c1 by rewrite sg_edgeNeq.
               left; exists (hom_G4_def a1 b2 c1 d2).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   by rewrite -b1_eq_b2.
               --- apply: h'_claw_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   by rewrite -b1_eq_b2.
      -- have a2_neq_c2: a2 != c2 by rewrite sg_edgeNeq.
         case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1]; last first.
         ++ left; exists (hom_G4_def a1 b2 a2 d2).
            ** apply: h'_G4_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               --- by move: a2_adj_c2; apply/contraTneq => <-; rewrite -b1_eq_b2.
               --- by rewrite -b1_eq_b2.
               --- by move: a2_adj_c2; apply/contraTneq => ->; rewrite -d1_eq_d2 sg_sym.
            ** apply: h'_claw_hom; rewrite /=; try by done.
               all: try by rewrite sg_sym.
               --- by rewrite -b1_eq_b2 sg_sym.
               --- by rewrite -b1_eq_b2.
               --- by rewrite -d1_eq_d2.
         ++ have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
            right; left; exists (hom_G5_def c2 d2 a2 a1 b1).
            ** apply: h'_G5_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               --- by move: c1_adj_c2; apply/contraTneq => ->.
               --- by move: a2_adj_b1; apply/contraTneq => <-; rewrite sg_sym.
               --- by rewrite b1_eq_b2.
            ** apply: h'_bull_hom; rewrite /=; try by done.
               all: try by rewrite sg_sym.
               --- by rewrite b1_eq_b2.
               --- by rewrite -d1_eq_d2.
               --- by rewrite -d1_eq_d2 sg_sym.
- have a2_neq_b1: a2 != b1 by move: a1_adj_a2; apply/contraTneq => ->; rewrite b1_eq_b2.
  have a2_adj_b1: a2 -- b1.
    apply: contraT => a2_nadj_b1.
    have a1_neq_b2: a1 != b2 by move: a1_adj_a2; apply/contraTneq => ->; rewrite -b1_eq_b2 sg_sym.
    by rewrite (negbTE a2_neq_b1) (negbTE a1_neq_b2) (negbTE a1_nadj_b2) (negbTE a2_nadj_b1) in a1b2a2b1.
  have a2_neq_d1: a2 != d1 by move: a2_adj_b1; apply/contraTneq => ->; rewrite b1_eq_b2 sg_sym.
  have a2_neq_c1: a2 != c1 by move: a2_adj_b1; apply/contraTneq => ->; rewrite b1_eq_b2 sg_sym.
  case: (boolP (a2 -- d1)) => [a2_adj_d1 | a2_nadj_d1]; last first.
  + have a1_neq_d2: a1 != d2 by move: a1_adj_a2; apply/contraTneq => ->; rewrite -d1_eq_d2 sg_sym.
    have a1_adj_d2: a1 -- d2 by rewrite (negbTE a2_neq_d1) (negbTE a1_neq_d2) (negbTE a2_nadj_d1) /= orbC /= orbC /= in a1d2a2d1.
    have a1_neq_c2: a1 != c2 by move: a1_adj_d2; apply/contraTneq => ->; rewrite -d1_eq_d2.
    case: (boolP (a1 -- c2)) => [a1_adj_c2 | a1_nadj_c2].
    * case: (boolP (a2 -- c2)) => [a2_adj_c2 | a2_nadj_c2]; last first.
      -- left; exists (hom_G4_def a1 a2 c2 d2).
         ++ apply: h'_G4_inj; rewrite /=; try by done.
            all: try by rewrite eq_sym.
            all: try by rewrite -d1_eq_d2.
            by move: a2_adj_b1; apply/contraTneq => ->; rewrite sg_sym.
         ++ apply: h'_claw_hom; rewrite /=; try by done.
            all: try by rewrite sg_sym.
            all: by rewrite -d1_eq_d2.
      -- have a2_neq_c2: a2 != c2 by rewrite sg_edgeNeq.
         right; left; exists (hom_G5_def b1 d2 a2 a1 c2).
         ++ apply: h'_G5_inj; rewrite /=; try by done.
            all: try by rewrite eq_sym.
            all: try by rewrite -d1_eq_d2 eq_sym.
            by move: a1_adj_d2; apply/contraTneq => <-.
         ++ apply: h'_bull_hom; rewrite /=; try by done.
            all: try by rewrite sg_sym.
            ** by rewrite b1_eq_b2 sg_sym.
            ** by rewrite -d1_eq_d2 sg_sym.
            ** by rewrite -d1_eq_d2 sg_sym.
    * have a2_adj_c1 : a2 -- c1 by rewrite (negbTE a2_neq_c1) (negbTE a1_neq_c2) (negbTE a1_nadj_c2) in a1c2a2c1.
      case: (boolP (a1 -- c1)) => [a1_adj_c1 | a1_nadj_c1]; last first.
      -- left; exists (hom_G4_def a2 a1 b1 c1).
         ++ apply: h'_G4_inj; rewrite /=; try by done.
            all: try by rewrite eq_sym.
            all: try by move: a1_adj_d2; apply/contraTneq => ->.
            by rewrite b1_eq_b2.
         ++ apply: h'_claw_hom; rewrite /=; try by done.
            all: try by rewrite sg_sym.
            all: by rewrite b1_eq_b2.
      -- have a1_neq_c1: a1 != c1 by rewrite sg_edgeNeq.
         right; left; exists (hom_G5_def b1 d2 a2 a1 c1).
         ++ apply: h'_G5_inj; rewrite /=; try by done.
            all: try by rewrite eq_sym.
            ** by move: a1_adj_d2; apply/contraTneq => <-.
            ** by rewrite b1_eq_b2.
            ** by rewrite -d1_eq_d2 eq_sym.
         ++ apply: h'_bull_hom; rewrite /=; try by done.
            all: try by rewrite sg_sym.
            ** by rewrite b1_eq_b2 sg_sym.
            ** by rewrite b1_eq_b2.
            ** by rewrite -d1_eq_d2 sg_sym.
  + case: (boolP (a1 -- c2)) => [a1_adj_c2 | a1_nadj_c2].
    * have a1_neq_c2: a1 != c2 by rewrite sg_edgeNeq.
      case: (boolP (a1 -- d2)) => [a1_adj_d2 | a1_nadj_d2]; last first.
      -- left; exists (hom_G4_def a2 a1 b1 d1).
         ++ apply: h'_G4_inj; rewrite /=; try by done.
            all: try by rewrite eq_sym.
            ** by move: a1_adj_c2; apply/contraTneq => ->.
            ** by move: a1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
            ** by rewrite b1_eq_b2.
         ++ apply: h'_claw_hom; rewrite /=; try by done.
            all: try by rewrite sg_sym.
            all: try by rewrite b1_eq_b2.
            by rewrite d1_eq_d2.
      -- have a1_neq_d2: a1 != d2 by rewrite sg_edgeNeq.
         case: (boolP (a2 -- c2)) => [a2_adj_c2 | a2_nadj_c2]; last first.
         ++ right; left; exists (hom_G5_def b1 c2 a2 a1 d1).
            ** apply: h'_G5_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               --- by move: a1_adj_d2; apply/contraTneq => <-.
               --- by rewrite b1_eq_b2.
               --- by move: a2_adj_b1; apply/contraTneq => <-; rewrite sg_sym.
               --- by rewrite d1_eq_d2.
            ** apply: h'_bull_hom; rewrite /=; try by done.
               all: try by rewrite sg_sym.
               all: try by rewrite d1_eq_d2.
               by rewrite b1_eq_b2 sg_sym.
         ++ have a2_neq_c2: a2 != c2 by rewrite sg_edgeNeq.
            left; exists (hom_G4_def a2 b1 c2 d1).
            ** apply: h'_G4_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               by rewrite b1_eq_b2.
            ** apply: h'_claw_hom; rewrite /=; try by done.
               all: try by rewrite sg_sym.
               by rewrite b1_eq_b2.
    * case: (boolP (a2 -- c2)) => [a2_adj_c2 | a2_nadj_c2].
      -- have a2_neq_c2: a2 != c2 by rewrite sg_edgeNeq.
         left; exists (hom_G4_def a2 b1 c2 d1).
         ++ apply: h'_G4_inj; rewrite /=; try by done.
            all: try by rewrite eq_sym.
            by rewrite b1_eq_b2.
         ++ apply: h'_claw_hom; rewrite /=; try by done.
            all: try by rewrite sg_sym.
            by rewrite b1_eq_b2.
      -- have a2_adj_c1: a2 -- c1.
           apply: contraT => a2_nadj_c1.
           have a1_neq_c2: a1 != c2 by move: a1_adj_a2; apply/contraTneq => ->; rewrite sg_sym.
           by rewrite (negbTE a2_neq_c1) (negbTE a1_neq_c2) (negbTE a1_nadj_c2) (negbTE a2_nadj_c1) in a1c2a2c1.
         case: (boolP (a1 -- c1)) => [a1_adj_c1 | a1_nadj_c1].
         ++ have a1_neq_c1: a1 != c1 by rewrite sg_edgeNeq.
            right; left; exists (hom_G5_def b1 c2 a2 c1 a1).
            ** apply: h'_G5_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               all: try by move: a1_adj_c1; apply/contraTneq => <-; rewrite b1_eq_b2.
               --- by move: a2_adj_b1; apply/contraTneq => <-; rewrite sg_sym.
               --- by move: a1_adj_a2; apply/contraTneq => <-; rewrite sg_sym.
            ** apply: h'_bull_hom; rewrite /=; try by done.
               all: try by rewrite sg_sym.
               --- by rewrite b1_eq_b2.
               --- by rewrite b1_eq_b2 sg_sym.
         ++ left; exists (hom_G4_def a2 b1 c1 d1).
            ** apply: h'_G4_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               all: try by rewrite b1_eq_b2.
               by rewrite d1_eq_d2.
            ** apply: h'_claw_hom; rewrite /=; try by done.
               all: try by rewrite sg_sym.
               all: try by rewrite b1_eq_b2.
               by rewrite d1_eq_d2.
Qed.

Lemma case_a1a2_bb_cc_dd (h : claw -> trfgraph G) (a1 a2 b1 b2 c1 c2 d1 d2 : G) :
  (a1 == c2) || a1 -- c2 || (a2 == c1) || a2 -- c1 ->
  (a1 == d2) || a1 -- d2 || (a2 == d1) || a2 -- d1 ->
  b1 != c2 ->
  ~~ b1 -- c2 ->
  b2 != c1 ->
  ~~ b2 -- c1 ->
  b1 != d2 ->
  ~~ b1 -- d2 ->
  b2 != d1 ->
  ~~ b2 -- d1 ->
  c1 != d2 ->
  ~~ c1 -- d2 ->
  c2 != d1 ->
  ~~ c2 -- d1 ->
  a1 -- a2 ->
  b1 = b2 ->
  c1 = c2 ->
  d1 = d2 ->
  a1 -- b2 ->
    ((exists2 h0 : claw -> G, injective h0 & induced_hom h0) \/
    (exists2 h0 : bull -> G, injective h0 & induced_hom h0) \/
    (exists2 h0 : 'P_6 -> G, injective h0 & induced_hom h0) \/
    (exists2 h0 : 'CC_6 -> G, injective h0 & induced_hom h0)).
Proof.
move => a1c2a2c1 a1d2a2d1 ? ? ? ? ? ? ? ? ? ? ? ? a1_adj_a2 b1_eq_b2 c1_eq_c2 d1_eq_d2 a1_adj_b2.
have a1_neq_a2: a1 != a2 by rewrite sg_edgeNeq.
have a1_neq_b2: a1 != b2 by rewrite sg_edgeNeq.
case: (boolP (a1 -- c2)) => [a1_adj_c2 | a1_nadj_c2].
- have a1_neq_c2: a1 != c2 by rewrite sg_edgeNeq.
  case: (boolP (a1 -- d2)) => [a1_adj_d2 | a1_nadj_d2].
  + have a1_neq_d2: a1 != d2 by rewrite sg_edgeNeq.
    left; exists (hom_G4_def a1 b2 c2 d2).
    * apply: h'_G4_inj; rewrite /=; try by done.
      all: try by rewrite eq_sym.
      all: try by rewrite -b1_eq_b2.
      by rewrite -c1_eq_c2.
    * apply: h'_claw_hom; rewrite /=; try by done.
      all: try by rewrite sg_sym.
      all: try by rewrite -b1_eq_b2.
      by rewrite -c1_eq_c2.
  + have a1_neq_d2: a1 != d2 by move: a1_adj_b2; apply/contraTneq => ->; rewrite -b1_eq_b2 sg_sym.
    have a2_neq_d1: a2 != d1 by move: a1_adj_a2; apply/contraTneq => ->; rewrite d1_eq_d2.
    have a2_adj_d1: a2 -- d1 by rewrite (negbTE a2_neq_d1) (negbTE a1_neq_d2) (negbTE a1_nadj_d2) in a1d2a2d1.
    case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1]; last first.
    * case: (boolP (a2 -- c1)) => [a2_adj_c1 | a2_nadj_c1]; last first.
      -- left; exists (hom_G4_def a1 b2 c2 a2).
         ++ apply: h'_G4_inj; rewrite /=; try by done.
            all: try by rewrite eq_sym.
            all: try by move: a2_adj_d1; apply/contraTneq => <-.
            by rewrite -b1_eq_b2.
         ++ apply: h'_claw_hom; rewrite /=; try by done.
            all: try by rewrite sg_sym.
            ** by rewrite -b1_eq_b2.
            ** by rewrite -b1_eq_b2 sg_sym.
            ** by rewrite -c1_eq_c2 sg_sym.
      -- have a2_neq_c1: a2 != c1 by rewrite sg_edgeNeq.
         right; left; exists (hom_G5_def b2 d1 a1 a2 c1).
         ++ apply: h'_G5_inj; rewrite /=; try by done.
            all: try by rewrite eq_sym.
            all: try by rewrite d1_eq_d2 eq_sym.
            ** by move: a2_adj_c1; apply/contraTneq => <-.
            ** by rewrite c1_eq_c2.
         ++ apply: h'_bull_hom; rewrite /=; try by done.
            all: try by rewrite sg_sym.
            ** by rewrite c1_eq_c2.
            ** by rewrite -b1_eq_b2 sg_sym.
            ** by rewrite d1_eq_d2 sg_sym.
            ** by rewrite c1_eq_c2 sg_sym.
    * have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
      case: (boolP (a2 -- c1)) => [a2_adj_c1 | a2_nadj_c1]; last first.
      -- right; left; exists (hom_G5_def c2 d1 a1 a2 b1).
         ++ apply: h'_G5_inj; rewrite /=; try by done.
            all: try by rewrite eq_sym.
            all: try by rewrite d1_eq_d2 eq_sym.
            ** by move: a2_adj_d1; apply/contraTneq => <-.
            ** by rewrite b1_eq_b2.
         ++ apply: h'_bull_hom; rewrite /=; try by done.
            all: try by rewrite sg_sym.
            all: try by rewrite d1_eq_d2 sg_sym.
            ** by rewrite b1_eq_b2.
            ** by rewrite -c1_eq_c2 sg_sym.
      -- have a2_neq_c1: a2 != c1 by rewrite sg_edgeNeq.
         left; exists (hom_G4_def a2 b1 c1 d1).
         ++ apply: h'_G4_inj; rewrite /=; try by done.
            all: try by rewrite eq_sym.
            all: try by rewrite b1_eq_b2.
            by rewrite c1_eq_c2.
         ++ apply: h'_claw_hom; rewrite /=; try by done.
            all: try by rewrite sg_sym.
            all: try by rewrite b1_eq_b2.
            by rewrite c1_eq_c2.
- have a1_neq_c2: a1 != c2 by move: a1_adj_b2; apply/contraTneq => ->; rewrite -b1_eq_b2 sg_sym.
  have a2_neq_c1: a2 != c1 by move: a1_adj_a2; apply/contraTneq => ->; rewrite c1_eq_c2.
  have a2_adj_c1: a2 -- c1 by rewrite (negbTE a2_neq_c1) (negbTE a1_neq_c2) (negbTE a1_nadj_c2) in a1c2a2c1.
  case: (boolP (a2 -- d1)) => [a2_adj_d1 | a2_nadj_d1].
  + have a2_neq_d1: a2 != d1 by rewrite sg_edgeNeq.
    case: (boolP (a1 -- d2)) => [a1_adj_d2 | a1_nadj_d2]; last first.
    * left; exists (hom_G4_def a2 a1 c1 d2).
      -- apply: h'_G4_inj; rewrite /=; try by done.
         all: try by rewrite eq_sym.
         ++ by rewrite -d1_eq_d2.
         ++ by rewrite c1_eq_c2.
         ++ by move: a1_adj_b2; apply/contraTneq => ->; rewrite -b1_eq_b2 sg_sym.
      -- apply: h'_claw_hom; rewrite /=; try by done.
         all: try by rewrite sg_sym.
         ++ by rewrite -d1_eq_d2.
         ++ by rewrite c1_eq_c2.
    * have a1_neq_d2: a1 != d2 by rewrite sg_edgeNeq.
      case: (boolP (a2 -- b1)) => [a2_adj_b1 | a1_nadj_b1]; last first.
      -- right; left; exists (hom_G5_def b2 c1 a1 a2 d1).
         ++ apply: h'_G5_inj; rewrite /=; try by done.
            all: try by rewrite eq_sym.
            ** by move: a2_adj_d1; apply/contraTneq => <-.
            ** by rewrite c1_eq_c2 eq_sym.
            ** by rewrite c1_eq_c2.
            ** by rewrite d1_eq_d2.
         ++ apply: h'_bull_hom; rewrite /=; try by done.
            all: try by rewrite sg_sym.
            all: try by rewrite d1_eq_d2.
            ** by rewrite -b1_eq_b2 sg_sym.
            ** by rewrite c1_eq_c2 sg_sym.
      -- have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
         left; exists (hom_G4_def a2 b1 c1 d1).
         ++ apply: h'_G4_inj; rewrite /=; try by done.
            all: try by rewrite eq_sym.
            all: try by rewrite b1_eq_b2.
            by rewrite c1_eq_c2.
         ++ apply: h'_claw_hom; rewrite /=; try by done.
            all: try by rewrite sg_sym.
            all: try by rewrite b1_eq_b2.
            by rewrite c1_eq_c2.
  + have a2_neq_d1: a2 != d1 by move: a2_adj_c1; apply/contraTneq => ->; rewrite d1_eq_d2 sg_sym.
    have a1_neq_d2: a1 != d2 by move: a1_adj_b2; apply/contraTneq => ->; rewrite -b1_eq_b2 sg_sym.
    have a1_adj_d2: a1 -- d2 by rewrite (negbTE a2_neq_d1) (negbTE a1_neq_d2) (negbTE a2_nadj_d1) /= orbC /= orbC /= in a1d2a2d1.
    case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1].
    * have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
      right; left; exists (hom_G5_def c1 d2 a2 a1 b2).
      -- apply: h'_G5_inj; rewrite /=; try by done.
         all: try by rewrite eq_sym.
         ++ by move: a1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
         ++ by move: a2_adj_c1; apply/contraTneq => <-; rewrite sg_sym.
         ++ by rewrite -d1_eq_d2 eq_sym.
         ++ by rewrite -b1_eq_b2.
      -- apply: h'_bull_hom; rewrite /=; try by done.
         all: try by rewrite sg_sym.
         all: try by rewrite -d1_eq_d2 sg_sym.
         ++ by rewrite -b1_eq_b2.
         ++ by rewrite c1_eq_c2 sg_sym.
    * left; exists (hom_G4_def a1 a2 b2 d2).
      -- apply: h'_G4_inj; rewrite /=; try by done.
         all: try by rewrite eq_sym.
         ++ by move: a2_adj_c1; apply/contraTneq => ->.
         ++ by rewrite -d1_eq_d2.
         ++ by rewrite -b1_eq_b2.
      -- apply: h'_claw_hom; rewrite /=; try by done.
         all: try by rewrite sg_sym.
         all: try by rewrite -b1_eq_b2.
         by rewrite -d1_eq_d2.
Qed.

Lemma subcase1_a1a2_b1b2_c1c2_d1d22_with_a1_adj_b2 (h : claw -> trfgraph G) (a1 a2 b1 b2 c1 c2 d1 d2 : G) :
  (a1 == b2) || a1 -- b2 || (a2 == b1) || a2 -- b1 ->
  (a1 == c2) || a1 -- c2 || (a2 == c1) || a2 -- c1 ->
  (a1 == d2) || a1 -- d2 || (a2 == d1) || a2 -- d1 ->
  b1 != c2 ->
  ~~ b1 -- c2 ->
  b2 != c1 ->
  ~~ b2 -- c1 ->
  b1 != d2 ->
  ~~ b1 -- d2 ->
  b2 != d1 ->
  ~~ b2 -- d1 ->
  c1 != d2 ->
  ~~ c1 -- d2 ->
  c2 != d1 ->
  ~~ c2 -- d1 ->
  a1 -- a2 ->
  b1 -- b2 ->
  c1 -- c2 ->
  d1 -- d2 ->
  a1 -- b2 ->
  a1 -- d2 ->
    ((exists2 h0 : claw -> G, injective h0 & induced_hom h0) \/
    (exists2 h0 : bull -> G, injective h0 & induced_hom h0) \/
    (exists2 h0 : 'P_6 -> G, injective h0 & induced_hom h0) \/
    (exists2 h0 : 'CC_6 -> G, injective h0 & induced_hom h0)).
Proof.
move => a1b2a2b1 a1c2a2c1 a1d2a2d1 ? ? ? ? ? ? ? ? ? ? ? ? a1_adj_a2 b1_adj_b2 c1_adj_c2 d1_adj_d2 a1_adj_b2 a1_adj_d2.
have a1_neq_a2: a1 != a2 by rewrite sg_edgeNeq.
have b1_neq_b2: b1 != b2 by rewrite sg_edgeNeq.
have c1_neq_c2: c1 != c2 by rewrite sg_edgeNeq.
have d1_neq_d2: d1 != d2 by rewrite sg_edgeNeq.
have a1_neq_b2: a1 != b2 by rewrite sg_edgeNeq.
have a1_neq_d2: a1 != d2 by rewrite sg_edgeNeq.
case: (boolP (a1 -- c1)) => [a1_adj_c1 | a1_nadj_c1].
- have a1_neq_c1: a1 != c1 by rewrite sg_edgeNeq.
  case: (boolP (b2 -- d2)) => [b2_adj_d2 | b2_nadj_d2]; last first.
  + left; exists (hom_G4_def a1 b2 c1 d2).
    * apply: h'_G4_inj; rewrite /=; try by done.
      all: try by rewrite eq_sym.
      by move: b1_adj_b2; apply/contraTneq => ->.
    * apply: h'_claw_hom; rewrite /=; try by done.
      all: by rewrite sg_sym.
  + have b2_neq_d2: b2 != d2 by rewrite sg_edgeNeq.
    case: (boolP (a1 -- b1)) => [a1_adj_b1 | a1_nadj_b1]; last first.
    * case: (boolP (b1 -- c1)) => [b1_adj_c1 | b1_nadj_c1]; last first.
      -- right; left; exists (hom_G5_def b1 c1 b2 a1 d2).
         ++ apply: h'_G5_inj; rewrite /=; try by done.
            all: try by rewrite eq_sym.
            ** by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
            ** by move: a1_adj_d2; apply/contraTneq => <-.
         ++ apply: h'_bull_hom; rewrite /=; try by done.
            all: by rewrite sg_sym.
      -- have b1_neq_c1: b1 != c1 by rewrite sg_edgeNeq.
         case: (boolP (a1 -- d1)) => [a1_adj_d1 | a1_nadj_d1]; last first.
         ++ case: (boolP (b1 -- d1)) => [b1_adj_d1 | b1_nadj_d1]; last first.
            ** right; left; exists (hom_G5_def b1 d1 b2 d2 a1).
               --- apply: h'_G5_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   +++ by move: d1_adj_d2; apply/contraTneq => <-.
                   +++ by move: a1_adj_d2; apply/contraTneq => <-.
                   +++ by move: a1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
               --- apply: h'_bull_hom; rewrite /=; try by done.
                   all: by rewrite sg_sym.
            ** have b1_neq_d1: b1 != d1 by rewrite sg_edgeNeq.
               case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
               --- left; exists (hom_G4_def b1 b2 c1 d1).
                   +++ apply: h'_G4_inj; rewrite /=; try by done.
                       by move: d1_adj_d2; apply/contraTneq => <-.
                   +++ by apply: h'_claw_hom.
               --- have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
                   case: (boolP (b2 -- c2)) => [b2_adj_c2 | b2_nadj_c2]; last first.
                   +++ right; left; exists (hom_G5_def b2 c2 b1 c1 d1).
                       *** apply: h'_G5_inj; rewrite /=; try by done.
                           all: try by rewrite eq_sym.
                           by move: b1_adj_b2; apply/contraTneq => ->.
                       *** apply: h'_bull_hom; rewrite /=; try by done.
                           all: by rewrite sg_sym.
                   +++ have b2_neq_c2: b2 != c2 by rewrite sg_edgeNeq.
                       case: (boolP (a1 -- c2)) => [a1_adj_c2 | a1_nadj_c2]; last first.
                       *** case: (boolP (a2 -- c2)) => [a2_adj_c2 | a2_nadj_c2]; last first.
                           ---- left; exists (hom_G4_def b2 a1 b1 c2).
                                ++++ apply: h'_G4_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     **** by move: a1_adj_d2; apply/contraTneq => ->.
                                     **** by move: a1_adj_a2; apply/contraTneq => ->; rewrite sg_sym.
                                ++++ apply: h'_claw_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
                           ---- have a2_neq_c2: a2 != c2 by rewrite sg_edgeNeq.
                                case: (boolP (a2 -- d1)) => [a2_adj_d1 | a2_nadj_d1].
                                ++++ have a2_neq_c1: a2 != d1 by rewrite sg_edgeNeq.
                                     case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2]; last first.
                                     **** left; exists (hom_G4_def a2 a1 c2 d1).
                                          ----- apply: h'_G4_inj; rewrite /=; try by done.
                                                all: try by rewrite eq_sym.
                                                +++++ by move: a1_adj_d2; apply/contraTneq => ->.
                                                +++++ by move: b1_adj_d1; apply/contraTneq => <-; rewrite sg_sym.
                                          ----- apply: h'_claw_hom; rewrite /=; try by done.
                                                all: by rewrite sg_sym.
                                     **** have c2_neq_d2: c2 != d2 by rewrite sg_edgeNeq.
                                          right; right; right; exists (hom_G6_def b1 c2 d1 b2 c1 d2).
                                          ----- apply: h'_G6_inj; rewrite /=; try by done.
                                                all: by rewrite eq_sym.
                                          ----- apply: h'_CC_6_hom; rewrite /=; try by done.
                                                all: by rewrite sg_sym.
                                ++++ case: (boolP (a2 -- b2)) => [a2_adj_b2 | a2_nadj_b2]; last first.
                                     **** case: (boolP (a2 -- d2)) => [a2_adj_d2 | a2_nadj_d2]; last first.
                                          ----- case: (boolP (b2 -- d1)) => [b2_adj_d1 | b2_nadj_d1].
                                                +++++ have b2_neq_d1: b2 != d1 by rewrite sg_edgeNeq.
                                                      right; left; exists (hom_G5_def a2 d1 a1 d2 b2).
                                                      ***** apply: h'_G5_inj; rewrite /=; try by done.
                                                            all: try by rewrite eq_sym.
                                                            ------ by move: a2_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                                            ------ by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
                                                            ------ by move: b2_adj_d1; apply/contraTneq => <-.
                                                            ------ by move: a1_adj_a2; apply/contraTneq => <-; rewrite sg_sym.
                                                      ***** apply: h'_bull_hom; rewrite /=; try by done.
                                                            all: by rewrite sg_sym.
                                                +++++ right; left; exists (hom_G5_def a2 d1 a1 d2 b2).
                                                      ***** apply: h'_G5_inj; rewrite /=; try by done.
                                                            all: try by rewrite eq_sym.
                                                            ------ by move: a1_adj_a2; apply/contraTneq => ->.
                                                            ------ by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
                                                            ------ by move: b2_adj_d2; apply/contraTneq => <-.
                                                            ------ by move: a1_adj_a2; apply/contraTneq => <-; rewrite sg_sym.
                                                      ***** apply: h'_bull_hom; rewrite /=; try by done.
                                                            all: by rewrite sg_sym.
                                          ----- have a2_neq_d2: a2 != d2 by rewrite sg_edgeNeq.
                                                case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1]; last first.
                                                +++++ left; exists (hom_G4_def d2 b2 a2 d1).
                                                      ***** apply: h'_G4_inj; rewrite /=; try by done.
                                                            all: try by rewrite eq_sym.
                                                            ------ by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                            ------ by move: a2_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                                      ***** apply: h'_claw_hom; rewrite /=; try by done.
                                                            all: by rewrite sg_sym.
                                                +++++ have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
                                                      case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2]; last first.
                                                      ***** left; exists (hom_G4_def b2 b1 a1 c2).
                                                            ------ apply: h'_G4_inj; rewrite /=; try by done.
                                                                   all: try by rewrite eq_sym.
                                                                   ++++++ by move: a1_adj_d2; apply/contraTneq => <-.
                                                                   ++++++ by move: a1_adj_d2; apply/contraTneq => ->.
                                                            ------ apply: h'_claw_hom; rewrite /=; try by done.
                                                                   all: by rewrite sg_sym.
                                                      ***** have c2_neq_d2: c2 != d2 by rewrite sg_edgeNeq.
                                                            right; right; right; exists (hom_G6_def b1 c2 d1 b2 c1 d2).
                                                            ------ apply: h'_G6_inj; rewrite /=; try by done.
                                                                   all: by rewrite eq_sym.
                                                            ------ apply: h'_CC_6_hom; rewrite /=; try by done.
                                                                   all: by rewrite sg_sym.
                                     **** have a2_neq_b2: a2 != b2 by rewrite sg_edgeNeq.
                                          case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2].
                                          ----- have c2_neq_d2: c2 != d2 by rewrite sg_edgeNeq.
                                                right; right; right; exists (hom_G6_def b1 c2 d1 b2 c1 d2).
                                                +++++ apply: h'_G6_inj; rewrite /=; try by done.
                                                      all: by rewrite eq_sym.
                                                +++++ apply: h'_CC_6_hom; rewrite /=; try by done.
                                                      all: by rewrite sg_sym.
                                          ----- left; exists (hom_G4_def b2 b1 a1 c2).
                                                +++++ apply: h'_G4_inj; rewrite /=; try by done.
                                                      all: try by rewrite eq_sym.
                                                      ***** by move: a1_adj_d2; apply/contraTneq => <-.
                                                      ***** by move: a1_adj_d2; apply/contraTneq => ->.
                                                +++++ apply: h'_claw_hom; rewrite /=; try by done.
                                                      all: by rewrite sg_sym.
                       *** have a1_neq_c2: a1 != c2 by rewrite sg_edgeNeq.
                           case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2].
                           ---- have c2_neq_d2: c2 != d2 by rewrite sg_edgeNeq.
                                right; right; right; exists (hom_G6_def b1 c2 d1 b2 c1 d2).
                                ++++ apply: h'_G6_inj; rewrite /=; try by done.
                                     all: by rewrite eq_sym.
                                ++++ apply: h'_CC_6_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
                           ---- left; exists (hom_G4_def b2 b1 c2 d2).
                                ++++ apply: h'_G4_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
                                ++++ apply: h'_claw_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
         ++ have a1_neq_d1: a1 != d1 by rewrite sg_edgeNeq.
            case: (boolP (a1 -- c2)) => [a1_adj_c2 | a1_nadj_c2]; last first.
            ** left; exists (hom_G4_def c1 a1 b1 c2).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   +++ by move: a1_adj_d2; apply/contraTneq => ->.
                   +++ by move: a1_adj_d1; apply/contraTneq => ->.
               --- apply: h'_claw_hom; rewrite /=; try by done.
                   all: by rewrite sg_sym.
            ** have a1_neq_c2: a1 != c2 by rewrite sg_edgeNeq.
               case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
               --- left; exists (hom_G4_def a1 b2 c1 d1).
                   +++ apply: h'_G4_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                   +++ apply: h'_claw_hom; rewrite /=; try by done.
                       all: by rewrite sg_sym.
               --- have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
                   case: (boolP (b2 -- c2)) => [b2_adj_c2 | b2_nadj_c2]; last first.
                   +++ left; exists (hom_G4_def a1 b2 c2 d1).
                       *** apply: h'_G4_inj; rewrite /=; try by done.
                           all: try by rewrite eq_sym.
                           by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                       *** by apply: h'_claw_hom.
                   +++ have b2_neq_c2: b2 != c2 by rewrite sg_edgeNeq.
                       case: (boolP (b1 -- d1)) => [b1_adj_d1 | b1_nadj_d1]; last first.
                       *** left; exists (hom_G4_def c1 b1 c2 d1).
                           ---- apply: h'_G4_inj; rewrite /=; try by done.
                                all: try by rewrite eq_sym.
                                by move: a1_adj_d1; apply/contraTneq => <-.
                           ---- apply: h'_claw_hom; rewrite /=; try by done.
                                all: by rewrite sg_sym.
                       *** have b1_neq_d1: b1 != d1 by rewrite sg_edgeNeq.
                           case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2].
                           ---- have c2_neq_d2: c2 != d2 by rewrite sg_edgeNeq.
                                right; right; right; exists (hom_G6_def b1 c2 d1 b2 c1 d2).
                                ++++ apply: h'_G6_inj; rewrite /=; try by done.
                                     all: by rewrite eq_sym.
                                ++++ apply: h'_CC_6_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
                           ---- right; left; exists (hom_G5_def b1 d2 c1 a1 c2).
                                ++++ apply: h'_G5_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     **** by move: a1_adj_d2; apply/contraTneq => <-.
                                     **** by move: d1_adj_d2; apply/contraTneq => ->; rewrite sg_sym.
                                ++++ apply: h'_bull_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
    * have a1_neq_b1: a1 != b1 by rewrite sg_edgeNeq.
      case: (boolP (a1 -- d1)) => [a1_adj_d1 | a1_nadj_d1]; last first.
      -- case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
         ++ right; left; exists (hom_G5_def c1 d1 a1 d2 b2).
            ** apply: h'_G5_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               --- by move: d1_adj_d2; apply/contraTneq => <-.
               --- by move: a1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
            ** apply: h'_bull_hom; rewrite /=; try by done.
               all: by rewrite sg_sym.
         ++ have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
            case: (boolP (a1 -- c2)) => [a1_adj_c2 | a1_nadj_c2]; last first.
            ** left; exists (hom_G4_def c1 a1 c2 d1).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   +++ by move: a1_adj_b1; apply/contraTneq => ->; rewrite sg_sym.
                   +++ by move: a1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
               --- apply: h'_claw_hom; rewrite /=; try by done.
                   all: by rewrite sg_sym.
            ** have a1_neq_c2: a1 != c2 by rewrite sg_edgeNeq.
               case: (boolP (b2 -- c2)) => [b2_adj_c2 | b2_nadj_c2]; last first.
               --- right; left; exists (hom_G5_def b2 d1 a1 c1 c2).
                   +++ apply: h'_G5_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       *** by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                       *** by move: a1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
                   +++ apply: h'_bull_hom; rewrite /=; try by done.
                       all: by rewrite sg_sym.
               --- have b2_neq_c2: b2 != c2 by rewrite sg_edgeNeq.
                   case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2]; last first.
                   +++ left; exists (hom_G4_def a1 b1 c2 d2).
                       *** apply: h'_G4_inj; rewrite /=; try by done.
                           all: try by rewrite eq_sym.
                           by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
                       *** apply: h'_claw_hom; rewrite /=; try by done.
                           all: by rewrite sg_sym.
                   +++ have c2_neq_d2: c2 != d2 by rewrite sg_edgeNeq.
                       case: (boolP (b1 -- c1)) => [b1_adj_c1 | b1_nadj_c1]; last first.
                       *** left; exists (hom_G4_def a1 b1 c1 d2).
                           ---- apply: h'_G4_inj; rewrite /=; try by done.
                                all: try by rewrite eq_sym.
                                by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                           ---- apply: h'_claw_hom; rewrite /=; try by done.
                                all: by rewrite sg_sym.
                       *** have b1_neq_c1: b1 != c1 by rewrite sg_edgeNeq.
                           case: (boolP (b1 -- d1)) => [b1_adj_d1 | b1_nadj_d1].
                           ---- have b1_neq_d1: b1 != d1 by rewrite sg_edgeNeq.
                                right; right; right; exists (hom_G6_def b1 c2 d1 b2 c1 d2).
                                ++++ apply: h'_G6_inj; rewrite /=; try by done.
                                     all: by rewrite eq_sym.
                                ++++ apply: h'_CC_6_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
                           ---- left; exists (hom_G4_def c1 b1 c2 d1).
                                ++++ apply: h'_G4_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     by move: d1_adj_d2; apply/contraTneq => <-.
                                ++++ apply: h'_claw_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
      -- have a1_neq_d1: a1 != d1 by rewrite sg_edgeNeq.
         case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
         ++ left; exists (hom_G4_def a1 b2 c1 d1).
            ** apply: h'_G4_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               by move: d1_adj_d2; apply/contraTneq => <-.
            ** apply: h'_claw_hom; rewrite /=; try by done.
               all: by rewrite sg_sym.
         ++ have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
            case: (boolP (b1 -- c1)) => [b1_adj_c1 | b1_nadj_c1]; last first.
            ** left; exists (hom_G4_def a1 b1 c1 d2).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
               --- apply: h'_claw_hom; rewrite /=; try by done.
                   all: by rewrite sg_sym.
            ** have b1_neq_c1: b1 != c1 by rewrite sg_edgeNeq.
               case: (boolP (b1 -- d1)) => [b1_adj_d1 | b1_nadj_d1]; last first.
               --- left; exists (hom_G4_def c1 b1 c2 d1).
                   +++ apply: h'_G4_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       by move: d1_adj_d2; apply/contraTneq => <-.
                   +++ apply: h'_claw_hom; rewrite /=; try by done.
                       all: by rewrite sg_sym.
               --- have b1_neq_d1: b1 != d1 by rewrite sg_edgeNeq.
                   case: (boolP (a1 -- c2)) => [a1_adj_c2 | a1_nadj_c2].
                   +++ have a1_neq_c2: a1 != c2 by rewrite sg_edgeNeq.
                       case: (boolP (b2 -- c2)) => [b2_adj_c2 | b2_nadj_c2]; last first.
                       *** left; exists (hom_G4_def a1 b2 c2 d1).
                           ---- apply: h'_G4_inj; rewrite /=; try by done.
                                all: try by rewrite eq_sym.
                                by move: b1_adj_b2; apply/contraTneq => ->.
                           ---- apply: h'_claw_hom; rewrite /=; try by done.
                                all: by rewrite sg_sym.
                       *** have b2_neq_c2: b2 != c2 by rewrite sg_edgeNeq.
                           case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2].
                           ---- have c2_neq_d2: c2 != d2 by rewrite sg_edgeNeq.
                                right; right; right; exists (hom_G6_def b1 c2 d1 b2 c1 d2).
                                ++++ apply: h'_G6_inj; rewrite /=; try by done.
                                     all: by rewrite eq_sym.
                                ++++ apply: h'_CC_6_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
                           ---- left; exists (hom_G4_def a1 b1 c2 d2).
                                ++++ apply: h'_G4_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
                                ++++ apply: h'_claw_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
                   +++ case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2]; last first.
                       *** right; left; exists (hom_G5_def c2 d2 c1 a1 b1).
                           ---- apply: h'_G5_inj; rewrite /=; try by done.
                                all: try by rewrite eq_sym.
                                ++++ by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
                                ++++ by move: a1_adj_d1; apply/contraTneq => <-.
                           ---- apply: h'_bull_hom; rewrite /=; try by done.
                                all: by rewrite sg_sym.
                       *** have c2_neq_d2: c2 != d2 by rewrite sg_edgeNeq.
                           case: (boolP (b2 -- c2)) => [b2_adj_c2 | b2_nadj_c2].
                           ---- have b2_neq_c2: b2 != c2 by rewrite sg_edgeNeq.
                                right; right; right; exists (hom_G6_def b1 c2 d1 b2 c1 d2).
                                ++++ apply: h'_G6_inj; rewrite /=; try by done.
                                     all: by rewrite eq_sym.
                                ++++ apply: h'_CC_6_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
                           ---- left; exists (hom_G4_def d2 b2 c2 d1).
                                ++++ apply: h'_G4_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     by move: a1_adj_b2; apply/contraTneq => ->.
                                ++++ apply: h'_claw_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
- case: (boolP (b2 -- d2)) => [b2_adj_d2 | b2_nadj_d2]; last first.
  + case: (boolP (a1 -- d1)) => [a1_adj_d1 | a1_nadj_d1].
    * have a1_neq_d1: a1 != d1 by rewrite sg_edgeNeq.
      case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1].
      -- have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
         right; left; exists (hom_G5_def b2 c1 a1 d1 d2).
         ++ apply: h'_G5_inj; rewrite /=; try by done.
            all: try by rewrite eq_sym.
            ** by move: b1_adj_b2; apply/contraTneq => ->.
            ** by move: a1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
         ++ apply: h'_bull_hom; rewrite /=; try by done.
            all: by rewrite sg_sym.
      -- case: (boolP (a1 -- c2)) => [a1_adj_c2 | a1_nadj_c2].
         ++ have a1_neq_c2: a1 != c2 by rewrite sg_edgeNeq.
            case: (boolP (b2 -- c2)) => [b2_adj_c2 | b2_nadj_c2]; last first.
            ** left; exists (hom_G4_def a1 b2 c2 d1).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   by move: b1_adj_b2; apply/contraTneq => ->.
               --- by apply: h'_claw_hom.
            ** have b2_neq_c2: b2 != c2 by rewrite sg_edgeNeq.
               case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2]; last first.
               --- right; left; exists (hom_G5_def c1 d2 c2 a1 b2).
                   +++ apply: h'_G5_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       *** by move: a1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
                       *** by move: c1_adj_c2; apply/contraTneq => <-.
                       *** by move: d1_adj_d2; apply/contraTneq => ->; rewrite sg_sym.
                   +++ apply: h'_bull_hom; rewrite /=; try by done.
                       all: by rewrite sg_sym.
               --- have c2_neq_d2: c2 != d2 by rewrite sg_edgeNeq.
                   left; exists (hom_G4_def c2 c1 b2 d2).
                   +++ apply: h'_G4_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       by move: b1_adj_b2; apply/contraTneq => ->.
                   +++ apply: h'_claw_hom; rewrite /=; try by done.
                       all: by rewrite sg_sym.
         ++ have a1_neq_c2: a1 != c2 by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
            have a2_neq_c1: a2 != c1 by move: a1_adj_a2; apply/contraTneq => ->.
            have a2_adj_c1: a2 -- c1 by rewrite (negbTE a1_neq_c2) (negbTE a2_neq_c1) (negbTE a1_nadj_c2) in a1c2a2c1.
            case: (boolP (a2 -- d1)) => [a2_adj_d1 | a2_nadj_d1]; last first.
            ** case: (boolP (a2 -- b2)) => [a2_adj_b2 | a2_nadj_b2].
               --- have a2_neq_b2: a2 != b2 by rewrite sg_edgeNeq.
                   right; left; exists (hom_G5_def c1 d1 a2 a1 b2).
                   +++ apply: h'_G5_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       *** by move: a1_adj_d1; apply/contraTneq => <-.
                       *** by move: a1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
                       *** by move: a2_adj_c1; apply/contraTneq => <-; rewrite sg_sym.
                   +++ apply: h'_bull_hom; rewrite /=; try by done.
                       all: by rewrite sg_sym.
               --- left; exists (hom_G4_def a1 a2 b2 d1).
                   +++ apply: h'_G4_inj; rewrite /=; try by done.
                       *** by move: a2_adj_c1; apply/contraTneq => ->.
                       *** by move: a2_adj_c1; apply/contraTneq => ->; rewrite sg_sym.
                   +++ apply: h'_claw_hom; rewrite /=; try by done.
                       all: by rewrite sg_sym.
            ** have a2_neq_d1: a2 != d1 by rewrite sg_edgeNeq.
               case: (boolP (a2 -- b2)) => [a2_adj_b2 | a2_nadj_b2]; last first.
               --- right; left; exists (hom_G5_def c1 b2 a2 a1 d1).
                   +++ apply: h'_G5_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       *** by move: a1_adj_d1; apply/contraTneq => <-.
                       *** by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                       *** by move: a2_adj_c1; apply/contraTneq => <-.
                   +++ apply: h'_bull_hom; rewrite /=; try by done.
                       all: by rewrite sg_sym.
               --- have a2_neq_b2: a2 != b2 by rewrite sg_edgeNeq.
                   left; exists (hom_G4_def a2 b2 c1 d1).
                   +++ apply: h'_G4_inj; rewrite /=; try by done.
                       by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                   +++ apply: h'_claw_hom; rewrite /=; try by done.
                       all: by rewrite sg_sym.
    * case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2].
      -- have c2_neq_d2: c2 != d2 by rewrite sg_edgeNeq.
         case: (boolP (a1 -- c2)) => [a1_adj_c2 | a1_nadj_c2]; last first.
         ++ left; exists (hom_G4_def d2 a1 c2 d1).
            ** apply: h'_G4_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               --- by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
               --- by move: a1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
            ** apply: h'_claw_hom; rewrite /=; try by done.
               all: by rewrite sg_sym.
         ++ have a1_neq_c2: a1 != c2 by rewrite sg_edgeNeq.
            case: (boolP (b2 -- c2)) => [b2_adj_c2 | b2_nadj_c2]; last first.
            ** right; left; exists (hom_G5_def b2 c1 a1 c2 d2).
               --- apply: h'_G5_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   +++ by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                   +++ by move: b1_adj_b2; apply/contraTneq => ->.
                   +++ by move: a1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
               --- apply: h'_bull_hom; rewrite /=; try by done.
                   all: by rewrite sg_sym.
            ** have b2_neq_c2: b2 != c2 by rewrite sg_edgeNeq.
               left; exists (hom_G4_def c2 c1 b2 d2).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   by move: b1_adj_b2; apply/contraTneq => ->.
               --- apply: h'_claw_hom; rewrite /=; try by done.
                   all: by rewrite sg_sym.
      -- case: (boolP (a1 -- c2)) => [a1_adj_c2 | a1_nadj_c2].
         ++ have a1_neq_c2: a1 != c2 by rewrite sg_edgeNeq.
            case: (boolP (b2 -- c2)) => [b2_adj_c2 | b2_nadj_c2]; last first.
            ** left; exists (hom_G4_def a1 b2 c2 d2).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   +++ by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                   +++ by move: b1_adj_b2; apply/contraTneq => ->.
                   +++ by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
               --- by apply: h'_claw_hom.
            ** have b2_neq_c2: b2 != c2 by rewrite sg_edgeNeq.
               right; left; exists (hom_G5_def c1 d2 c2 a1 b2).
               --- apply: h'_G5_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   +++ by move: a1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
                   +++ by move: d1_adj_d2; apply/contraTneq => ->; rewrite sg_sym.
                   +++ by move: b1_adj_b2; apply/contraTneq => <-.
               --- apply: h'_bull_hom; rewrite /=; try by done.
                   all: by rewrite sg_sym.
         ++ have a1_neq_c2: a1 != c2 by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
            have a2_neq_c1: a2 != c1 by move: a1_adj_a2; apply/contraTneq => ->.
            have a2_adj_c1: a2 -- c1 by rewrite (negbTE a1_neq_c2) (negbTE a2_neq_c1) (negbTE a1_nadj_c2) in a1c2a2c1.
            case: (boolP (a2 -- b2)) => [a2_adj_b2 | a2_nadj_b2]; last first.
            ** case: (boolP (a2 -- d2)) => [a2_adj_d2 | a2_nadj_d2].
               --- have a2_neq_d2: a2 != d2 by rewrite sg_edgeNeq.
                   right; left; exists (hom_G5_def b2 c1 a1 a2 d2).
                   +++ apply: h'_G5_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       *** by move: a2_adj_c1; apply/contraTneq => <-.
                       *** by move: b1_adj_b2; apply/contraTneq => ->.
                       *** by move: a1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
                   +++ apply: h'_bull_hom; rewrite /=; try by done.
                       all: by rewrite sg_sym.
               --- left; exists (hom_G4_def a1 a2 b2 d2).
                   +++ apply: h'_G4_inj; rewrite /=; try by done.
                       *** by move: a2_adj_c1; apply/contraTneq => ->.
                       *** by move: a2_adj_c1; apply/contraTneq => ->; rewrite sg_sym.
                       *** by move: b1_adj_b2; apply/contraTneq => ->.
                   +++ apply: h'_claw_hom; rewrite /=; try by done.
                       all: by rewrite sg_sym.
            ** have a2_neq_b2: a2 != b2 by rewrite sg_edgeNeq.
               case: (boolP (a2 -- d2)) => [a2_adj_d2 | a2_nadj_d2]; last first.
               --- right; left; exists (hom_G5_def c1 d2 a2 a1 b2).
                   +++ apply: h'_G5_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       *** by move: a1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
                       *** by move: a2_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
                       *** by move: b1_adj_b2; apply/contraTneq => <-.
                   +++ apply: h'_bull_hom; rewrite /=; try by done.
                       all: by rewrite sg_sym.
               --- have a2_neq_d2: a2 != d2 by rewrite sg_edgeNeq.
                   left; exists (hom_G4_def a2 b2 c1 d2).
                   +++ apply: h'_G4_inj; rewrite /=; try by done.
                       by move: b1_adj_b2; apply/contraTneq => ->.
                   +++ apply: h'_claw_hom; rewrite /=; try by done.
                       all: by rewrite sg_sym.
  + have b2_neq_d2: b2 != d2 by rewrite sg_edgeNeq.
    case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2]; last first.
    * case: (boolP (b2 -- c2)) => [b2_adj_c2 | b2_nadj_c2].
      -- have b2_neq_c2: b2 != c2 by rewrite sg_edgeNeq.
         left; exists (hom_G4_def b2 b1 c2 d2).
         ++ apply: h'_G4_inj; rewrite /=; try by done.
            all: try by rewrite eq_sym.
            by move: c1_adj_c2; apply/contraTneq => ->.
         ++ apply: h'_claw_hom; rewrite /=; try by done.
            all: by rewrite sg_sym.
      -- case: (boolP (a1 -- b1)) => [a1_adj_b1 | a1_nadj_b1]; last first.
         ++ case: (boolP (a1 -- c2)) => [a1_adj_c2 | a1_nadj_c2].
            ** have a1_neq_c2: a1 != c2 by rewrite sg_edgeNeq.
               right; left; exists (hom_G5_def b1 c2 b2 a1 d2).
               --- apply: h'_G5_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   +++ by move: a1_adj_d2; apply/contraTneq => <-.
                   +++ by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                   +++ by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
               --- apply: h'_bull_hom; rewrite /=; try by done.
                   all: by rewrite sg_sym.
            ** have a1_neq_c2: a1 != c2 by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
               have a2_neq_c1: a2 != c1 by move: a1_adj_a2; apply/contraTneq => ->.
               have a2_adj_c1: a2 -- c1 by rewrite (negbTE a1_neq_c2) (negbTE a2_neq_c1) (negbTE a1_nadj_c2) in a1c2a2c1.
               case: (boolP (a1 -- d1)) => [a1_adj_d1 | a1_nadj_d1]; last first.
               --- case: (boolP (b1 -- d1)) => [b1_adj_d1 | b1_nadj_d1]; last first.
                   +++ right; left; exists (hom_G5_def b1 d1 b2 d2 a1).
                       *** apply: h'_G5_inj; rewrite /=; try by done.
                           all: try by rewrite eq_sym.
                           ---- by move: d1_adj_d2; apply/contraTneq => <-.
                           ---- by move: a1_adj_d2; apply/contraTneq => <-.
                           ---- by move: a1_adj_b2; apply/contraTneq => <-; rewrite sg_sym. 
                       *** apply: h'_bull_hom; rewrite /=; try by done.
                           all: by rewrite sg_sym.
                   +++ have b1_neq_d1: b1 != d1 by rewrite sg_edgeNeq.
                       case: (boolP (b1 -- c1)) => [b1_adj_c1 | b1_nadj_c1].
                       *** have b1_neq_c1: b1 != c1 by rewrite sg_edgeNeq.
                           case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
                           ---- left; exists (hom_G4_def b1 b2 c1 d1).
                                ++++ apply: h'_G4_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                ++++ apply: h'_claw_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
                           ---- have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
                                right; left; exists (hom_G5_def b2 c2 b1 c1 d1).
                                ++++ apply: h'_G5_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     by move: b1_adj_b2; apply/contraTneq => ->.
                                ++++ apply: h'_bull_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
                       *** case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1].
                           ---- have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
                                left; exists (hom_G4_def d1 b1 c1 d2).
                                ++++ apply: h'_G4_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                ++++ apply: h'_claw_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
                           ---- case: (boolP (a2 -- b2)) => [a2_adj_b2 | a2_nadj_b2]; last first.
                                ++++ case: (boolP (a2 -- c2)) => [a2_adj_c2 | a2_nadj_c2]; last first.
                                     **** case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1]; last first.
                                          ----- right; right; left; exists (hom_G6_def b1 b2 a1 a2 c1 c2).
                                                +++++ apply: h'_G6_inj; rewrite /=; try by done.
                                                      all: try by rewrite eq_sym.
                                                      all: try by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                      ***** by move: a1_adj_d2; apply/contraTneq => <-.
                                                      ***** by move: a2_adj_c1; apply/contraTneq => <-.
                                                      ***** by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                                                      ***** by move: a1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                      ***** by move: a1_adj_a2; apply/contraTneq => ->.
                                                +++++ apply: h'_P_6_hom; rewrite /=; try by done.
                                                      all: by rewrite sg_sym.
                                          ----- have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
                                                case: (boolP (a2 -- d1)) => [a2_adj_d1 | a2_nadj_d1].
                                                +++++ have a2_neq_d1: a2 != d1 by rewrite sg_edgeNeq.
                                                      left; exists (hom_G4_def a2 a1 c1 d1).
                                                      ***** apply: h'_G4_inj; rewrite /=; try by done.
                                                            all: try by rewrite eq_sym.
                                                            ------ by move: a1_adj_d2; apply/contraTneq => ->.
                                                            ------ by move: a1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                            ------ by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                                      ***** apply: h'_claw_hom; rewrite /=; try by done.
                                                            all: by rewrite sg_sym.
                                                +++++ left; exists (hom_G4_def b1 b2 a2 d1).
                                                      ***** apply: h'_G4_inj; rewrite /=; try by done.
                                                            all: try by rewrite eq_sym.
                                                            ------ by move: a2_adj_c1; apply/contraTneq => <-.
                                                            ------ by move: a2_adj_c1; apply/contraTneq => ->; rewrite sg_sym.
                                                      ***** apply: h'_claw_hom; rewrite /=; try by done.
                                                            all: by rewrite sg_sym.
                                     **** have a2_neq_c2: a2 != c2 by rewrite sg_edgeNeq.
                                          case: (boolP (a2 -- d1)) => [a2_adj_d1 | a2_nadj_d1].
                                          ----- have a2_neq_d1: a2 != d1 by rewrite sg_edgeNeq.
                                                left; exists (hom_G4_def a2 a1 c1 d1).
                                                +++++ apply: h'_G4_inj; rewrite /=; try by done.
                                                      all: try by rewrite eq_sym.
                                                      ***** by move: a1_adj_d2; apply/contraTneq => ->.
                                                      ***** by move: a1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                      ***** by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                                +++++ apply: h'_claw_hom; rewrite /=; try by done.
                                                      all: by rewrite sg_sym.
                                          ----- case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1].
                                                +++++ have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
                                                      left; exists (hom_G4_def b1 b2 a2 d1).
                                                      ***** apply: h'_G4_inj; rewrite /=; try by done.
                                                            all: try by rewrite eq_sym.
                                                            ------ by move: a2_adj_c1; apply/contraTneq => <-.
                                                            ------ by move: a2_adj_c1; apply/contraTneq => ->; rewrite sg_sym.
                                                      ***** apply: h'_claw_hom; rewrite /=; try by done.
                                                            all: by rewrite sg_sym.
                                                +++++ case: (boolP (a2 -- d2)) => [a2_adj_d2 | a2_nadj_d2].
                                                      ***** have a2_neq_d2: a2 != d2 by rewrite sg_edgeNeq.
                                                            right; left; exists (hom_G5_def c1 d1 a2 d2 a1).
                                                            ------ apply: h'_G5_inj; rewrite /=; try by done.
                                                                   all: try by rewrite eq_sym.
                                                                   ++++++ by move: d1_adj_d2; apply/contraTneq => <-.
                                                                   ++++++ by move: c1_adj_c2; apply/contraTneq => ->.
                                                                   ++++++ by move: a1_adj_a2; apply/contraTneq => <-.
                                                                   ++++++ by move: b1_adj_d1; apply/contraTneq => ->; rewrite sg_sym.
                                                            ------ apply: h'_bull_hom; rewrite /=; try by done.
                                                                   all: by rewrite sg_sym.
                                                      ***** right; left; exists (hom_G5_def a2 d1 a1 d2 b2).
                                                            ------ apply: h'_G5_inj; rewrite /=; try by done.
                                                                   all: try by rewrite eq_sym.
                                                                   ++++++ by move: b1_adj_d1; apply/contraTneq => <-; rewrite sg_sym.
                                                                   ++++++ by move: b2_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
                                                                   ++++++ by move: b1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
                                                                   ++++++ by move: b1_adj_d1; apply/contraTneq => ->; rewrite sg_sym.
                                                            ------ apply: h'_bull_hom; rewrite /=; try by done.
                                                                   all: by rewrite sg_sym.
                                ++++ have a2_neq_b2: a2 != b2 by rewrite sg_edgeNeq.
                                     case: (boolP (a2 -- d1)) => [a2_adj_d1 | a2_nadj_d1].
                                     **** have a2_neq_d1: a2 != d1 by rewrite sg_edgeNeq.
                                          left; exists (hom_G4_def a2 b2 c1 d1).
                                          ----- apply: h'_G4_inj; rewrite /=; try by done.
                                                all: try by rewrite eq_sym.
                                                by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                          ----- by apply: h'_claw_hom.
                                     **** case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1]; last first.
                                          ----- right; left; exists (hom_G5_def b1 c1 b2 a2 a1).
                                                +++++ apply: h'_G5_inj; rewrite /=; try by done.
                                                      all: try by rewrite eq_sym.
                                                      ***** by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                      ***** by move: a1_adj_a2; apply/contraTneq => <-.
                                                      ***** by move: a1_adj_d2; apply/contraTneq => <-.
                                                      ***** by move: c1_adj_c2; apply/contraTneq => ->.
                                                +++++ apply: h'_bull_hom; rewrite /=; try by done.
                                                      all: by rewrite sg_sym.
                                          ----- have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
                                                right; left; exists (hom_G5_def c1 d1 a2 b1 b2).
                                                +++++ apply: h'_G5_inj; rewrite /=; try by done.
                                                      all: try by rewrite eq_sym.
                                                      ***** by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                                      ***** by move: b1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
                                                      ***** by move: a1_adj_a2; apply/contraTneq => <-.
                                                +++++ apply: h'_bull_hom; rewrite /=; try by done.
                                                      all: by rewrite sg_sym.
               --- have a1_neq_d1: a1 != d1 by rewrite sg_edgeNeq.
                   case: (boolP (a2 -- b2)) => [a2_adj_b2 | a2_nadj_b2]; last first.
                   +++ case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
                       *** case: (boolP (a2 -- d1)) => [a2_adj_d1 | a2_nadj_d1].
                           ---- have a2_neq_d1: a2 != d1 by rewrite sg_edgeNeq.
                                right; left; exists (hom_G5_def b2 c1 a1 a2 d1).
                                ++++ apply: h'_G5_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     **** by move: a2_adj_c1; apply/contraTneq => <-.
                                     **** by move: a1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
                                     **** by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                ++++ apply: h'_bull_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
                           ---- left; exists (hom_G4_def a1 a2 b2 d1).
                                ++++ apply: h'_G4_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     **** by move: a2_adj_c1; apply/contraTneq => ->.
                                     **** by move: a2_adj_c1; apply/contraTneq => ->; rewrite sg_sym.
                                ++++ apply: h'_claw_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
                       *** have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
                           case: (boolP (a2 -- d1)) => [a2_adj_d1 | a2_nadj_d1]; last first.
                           ---- case: (boolP (a2 -- c2)) => [a2_adj_c2 | a2_nadj_c2].
                                ++++ have a2_neq_c2: a2 != c2 by rewrite sg_edgeNeq.
                                     left; exists (hom_G4_def a1 a2 b2 d1).
                                     **** apply: h'_G4_inj; rewrite /=; try by done.
                                          all: try by rewrite eq_sym.
                                          ----- by move: a2_adj_c1; apply/contraTneq => ->.
                                          ----- by move: a2_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                     **** apply: h'_claw_hom; rewrite /=; try by done.
                                          all: by rewrite sg_sym.
                                ++++ case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1]; last first.
                                     **** case: (boolP (b1 -- c1)) => [b1_adj_c1 | b1_nadj_c1].
                                          ----- have b1_neq_c1: b1 != c1 by rewrite sg_edgeNeq.
                                                left; exists (hom_G4_def c1 a2 b1 c2).
                                                +++++ apply: h'_G4_inj; rewrite /=; try by done.
                                                      all: try by rewrite eq_sym.
                                                      ***** by move: b1_adj_b2; apply/contraTneq => <-.
                                                      ***** by move: a1_adj_a2; apply/contraTneq => ->.
                                                +++++ apply: h'_claw_hom; rewrite /=; try by done.
                                                      all: by rewrite sg_sym.
                                          ----- right; right; left; exists (hom_G6_def b1 b2 a1 a2 c1 c2).
                                                +++++ apply: h'_G6_inj; rewrite /=; try by done.
                                                      all: try by rewrite eq_sym.
                                                      all: try by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                      ***** by move: a1_adj_d2; apply/contraTneq => <-.
                                                      ***** by move: a2_adj_c1; apply/contraTneq => <-.
                                                      ***** by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                                                      ***** by move: a1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                      ***** by move: a1_adj_a2; apply/contraTneq => ->.
                                                +++++ apply: h'_P_6_hom; rewrite /=; try by done.
                                                      all: by rewrite sg_sym.
                                     **** have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
                                          case: (boolP (b1 -- c1)) => [b1_adj_c1 | b1_nadj_c1]; last first.
                                          ----- left; exists (hom_G4_def a2 a1 b1 c1).
                                                +++++ apply: h'_G4_inj; rewrite /=; try by done.
                                                      all: try by rewrite eq_sym.
                                                      ***** by move: a1_adj_d2; apply/contraTneq => ->.
                                                      ***** by move: a1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                      ***** by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                +++++ apply: h'_claw_hom; rewrite /=; try by done.
                                                      all: by rewrite sg_sym.
                                          ----- have b1_neq_c1: b1 != c1 by rewrite sg_edgeNeq.
                                                right; left; exists (hom_G5_def b2 c2 b1 c1 a2).
                                                +++++ apply: h'_G5_inj; rewrite /=; try by done.
                                                      all: try by rewrite eq_sym.
                                                      ***** by move: b1_adj_b2; apply/contraTneq => ->.
                                                      ***** by move: a2_adj_c1; apply/contraTneq => <-.
                                                      ***** by move: a2_adj_b1; apply/contraTneq => <-; rewrite sg_sym.
                                                +++++ apply: h'_bull_hom; rewrite /=; try by done.
                                                      all: by rewrite sg_sym.
                           ---- have a2_neq_d1: a2 != d1 by rewrite sg_edgeNeq.
                                case: (boolP (a2 -- c2)) => [a2_adj_c2 | a2_nadj_c2].
                                ++++ have a2_neq_c2: a2 != c2 by rewrite sg_edgeNeq.
                                     right; left; exists (hom_G5_def b2 c2 a1 a2 d1).
                                     **** apply: h'_G5_inj; rewrite /=; try by done.
                                          all: try by rewrite eq_sym.
                                          ----- by move: a1_adj_b2; apply/contraTneq => ->.
                                          ----- by move: a2_adj_c1; apply/contraTneq => <-.
                                     **** apply: h'_bull_hom; rewrite /=; try by done.
                                          all: by rewrite sg_sym.
                                ++++ case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1]; last first.
                                     **** case: (boolP (b1 -- c1)) => [b1_adj_c1 | b1_nadj_c1].
                                          ----- have b1_neq_c1: b1 != c1 by rewrite sg_edgeNeq.
                                                left; exists (hom_G4_def c1 a2 b1 c2).
                                                +++++ apply: h'_G4_inj; rewrite /=; try by done.
                                                      all: try by rewrite eq_sym.
                                                      ***** by move: b1_adj_b2; apply/contraTneq => <-.
                                                      ***** by move: a1_adj_a2; apply/contraTneq => ->.
                                                +++++ apply: h'_claw_hom; rewrite /=; try by done.
                                                      all: by rewrite sg_sym.
                                          ----- right; right; left; exists (hom_G6_def b1 b2 a1 a2 c1 c2).
                                                +++++ apply: h'_G6_inj; rewrite /=; try by done.
                                                      all: try by rewrite eq_sym.
                                                      all: try by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                      ***** by move: a1_adj_d2; apply/contraTneq => <-.
                                                      ***** by move: a2_adj_c1; apply/contraTneq => <-.
                                                      ***** by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                                                      ***** by move: a1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                      ***** by move: a1_adj_a2; apply/contraTneq => ->.
                                                +++++ apply: h'_P_6_hom; rewrite /=; try by done.
                                                      all: by rewrite sg_sym.
                                     **** have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
                                          case: (boolP (b1 -- c1)) => [b1_adj_c1 | b1_nadj_c1].
                                          ----- have b1_neq_c1: b1 != c1 by rewrite sg_edgeNeq.
                                                right; left; exists (hom_G5_def b2 c2 b1 c1 a2).
                                                +++++ apply: h'_G5_inj; rewrite /=; try by done.
                                                      all: try by rewrite eq_sym.
                                                      ***** by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                                                      ***** by move: a2_adj_c1; apply/contraTneq => <-.
                                                      ***** by move: a2_adj_b1; apply/contraTneq => <-; rewrite sg_sym. 
                                                +++++ apply: h'_bull_hom; rewrite /=; try by done.
                                                      all: by rewrite sg_sym.
                                          ----- left; exists (hom_G4_def a2 a1 b1 c1).
                                                +++++ apply: h'_G4_inj; rewrite /=; try by done.
                                                      all: try by rewrite eq_sym.
                                                      ***** by move: a1_adj_d2; apply/contraTneq => ->.
                                                      ***** by move: c1_adj_c2; apply/contraTneq => <-.
                                                      ***** by move: c1_adj_c2; apply/contraTneq => <-.
                                                +++++ apply: h'_claw_hom; rewrite /=; try by done.
                                                      all: by rewrite sg_sym.
                   +++ have a2_neq_b2: a2 != b2 by rewrite sg_edgeNeq.
                       case: (boolP (a2 -- d1)) => [a2_adj_d1 | a2_nadj_d1]; last first.
                       *** case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
                           ---- right; left; exists (hom_G5_def c1 d1 a2 a1 b2).
                                ++++ apply: h'_G5_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     **** by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                     **** by move: c1_adj_c2; apply/contraTneq => ->.
                                     **** by move: a2_adj_b2; apply/contraTneq => <-; rewrite sg_sym. 
                                ++++ apply: h'_bull_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
                           ---- have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
                                case: (boolP (b1 -- c1)) => [b1_adj_c1 | b1_nadj_c1].
                                ++++ have b1_neq_c1: b1 != c1 by rewrite sg_edgeNeq.
                                     case: (boolP (b1 -- d1)) => [b1_adj_d1 | b1_nadj_d1]; last first.
                                     **** left; exists (hom_G4_def c1 b1 c2 d1).
                                          ----- apply: h'_G4_inj; rewrite /=; try by done.
                                                all: try by rewrite eq_sym.
                                                by move: d1_adj_d2; apply/contraTneq => <-.
                                          ----- apply: h'_claw_hom; rewrite /=; try by done.
                                                all: by rewrite sg_sym.
                                     **** have b1_neq_d1: b1 != d1 by rewrite sg_edgeNeq.
                                          right; left; exists (hom_G5_def b2 c2 b1 c1 d1).
                                          ----- apply: h'_G5_inj; rewrite /=; try by done.
                                                all: try by rewrite eq_sym.
                                                by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                                          ----- apply: h'_bull_hom; rewrite /=; try by done.
                                                all: by rewrite sg_sym.
                                ++++ case: (boolP (a2 -- c2)) => [a2_adj_c2 | a2_nadj_c2]; last first.
                                     **** left; exists (hom_G4_def c1 a2 c2 d1).
                                          ----- apply: h'_G4_inj; rewrite /=; try by done.
                                                all: try by rewrite eq_sym.
                                                +++++ by move: a1_adj_a2; apply/contraTneq => ->.
                                                +++++ by move: a2_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                          ----- apply: h'_claw_hom; rewrite /=; try by done.
                                                all: by rewrite sg_sym.
                                     **** have a2_neq_c2: a2 != c2 by rewrite sg_edgeNeq.
                                          right; left; exists (hom_G5_def b2 d1 a2 c1 c2).
                                          ----- apply: h'_G5_inj; rewrite /=; try by done.
                                                all: try by rewrite eq_sym.
                                                +++++ by move: b1_adj_b2; apply/contraTneq => ->.
                                                +++++ by move: a2_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
                                          ----- apply: h'_bull_hom; rewrite /=; try by done.
                                                all: by rewrite sg_sym.
                       *** have a2_neq_d1: a2 != d1 by rewrite sg_edgeNeq.
                           case: (boolP (b1 -- c1)) => [b1_adj_c1 | b1_nadj_c1]; last first.
                           ---- case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1]; last first.
                                ++++ right; left; exists (hom_G5_def b1 c1 b2 a2 a1).
                                     **** apply: h'_G5_inj; rewrite /=; try by done.
                                          all: try by rewrite eq_sym.
                                          ----- by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                          ----- by move: a1_adj_a2; apply/contraTneq => <-.
                                          ----- by move: a1_adj_a2; apply/contraTneq => <-; rewrite sg_sym.
                                          ----- by move: c1_adj_c2; apply/contraTneq => ->.
                                     **** apply: h'_bull_hom; rewrite /=; try by done.
                                          all: by rewrite sg_sym.
                                ++++ have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
                                     case: (boolP (a2 -- d2)) => [a2_adj_d2 | a2_nadj_d2].
                                     **** have a2_neq_d2: a2 != d2 by rewrite sg_edgeNeq.
                                          left; exists (hom_G4_def a2 b1 c1 d2).
                                          ----- apply: h'_G4_inj; rewrite /=; try by done.
                                                all: try by rewrite eq_sym.
                                                by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                          ----- apply: h'_claw_hom; rewrite /=; try by done.
                                                all: by rewrite sg_sym.
                                     **** right; left; exists (hom_G5_def c1 d2 a2 b2 b1).
                                          ----- apply: h'_G5_inj; rewrite /=; try by done.
                                                all: try by rewrite eq_sym.
                                                +++++ by move: b1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
                                                +++++ by move: a2_adj_b1; apply/contraTneq => <-; rewrite sg_sym. 
                                          ----- apply: h'_bull_hom; rewrite /=; try by done.
                                                all: by rewrite sg_sym.
                           ---- have b1_neq_c1: b1 != c1 by rewrite sg_edgeNeq.
                                case: (boolP (b1 -- d1)) => [b1_adj_d1 | b1_nadj_d1].
                                ++++ have b1_neq_d1: b1 != d1 by rewrite sg_edgeNeq.
                                     case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
                                     **** left; exists (hom_G4_def b1 b2 c1 d1).
                                          ----- apply: h'_G4_inj; rewrite /=; try by done.
                                                all: try by rewrite eq_sym.
                                                by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                          ----- apply: h'_claw_hom; rewrite /=; try by done.
                                                all: by rewrite sg_sym.
                                     **** have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
                                          right; left; exists (hom_G5_def b2 c2 b1 c1 d1).
                                          ----- apply: h'_G5_inj; rewrite /=; try by done.
                                                all: try by rewrite eq_sym.
                                                by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                                          ----- apply: h'_bull_hom; rewrite /=; try by done.
                                                all: by rewrite sg_sym.
                                ++++ case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1].
                                     **** have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
                                          left; exists (hom_G4_def c1 b1 c2 d1).
                                          ----- apply: h'_G4_inj; rewrite /=; try by done.
                                                all: try by rewrite eq_sym.
                                                by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                          ----- apply: h'_claw_hom; rewrite /=; try by done.
                                                all: by rewrite sg_sym.
                                     **** left; exists (hom_G4_def a2 b2 c1 d1).
                                          ----- apply: h'_G4_inj; rewrite /=; try by done.
                                                all: try by rewrite eq_sym.
                                                by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                          ----- apply: h'_claw_hom; rewrite /=; try by done.
                                                all: by rewrite sg_sym.
         ++ have a1_neq_b1: a1 != b1 by rewrite sg_edgeNeq.
            case: (boolP (a1 -- c2)) => [a1_adj_c2 | a1_nadj_c2].
            ** have a1_neq_c2: a1 != c2 by rewrite sg_edgeNeq.
               case: (boolP (a1 -- d1)) => [a1_adj_d1 | a1_nadj_d1]; last first.
               --- right; left; exists (hom_G5_def c2 d1 a1 d2 b2).
                   +++ apply: h'_G5_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       *** by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
                       *** by move: b1_adj_b2; apply/contraTneq => <-.
                       *** by move: a1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
                   +++ apply: h'_bull_hom; rewrite /=; try by done.
                       all: by rewrite sg_sym.
               --- have a1_neq_d1: a1 != d1 by rewrite sg_edgeNeq.
                   left; exists (hom_G4_def a1 b2 c2 d1).
                   +++ apply: h'_G4_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                   +++ apply: h'_claw_hom; rewrite /=; try by done.
                       all: by rewrite sg_sym.
            ** have a1_neq_c2: a1 != c2 by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
               have a2_neq_c1: a2 != c1 by move: a1_adj_a2; apply/contraTneq => ->.
               have a2_adj_c1: a2 -- c1 by rewrite (negbTE a1_neq_c2) (negbTE a2_neq_c1) (negbTE a1_nadj_c2) in a1c2a2c1.
               case: (boolP (a1 -- d1)) => [a1_adj_d1 | a1_nadj_d1]; last first.
               --- case: (boolP (a2 -- c2)) => [a2_adj_c2 | a2_nadj_c2].
                   +++ have a2_neq_c2: a2 != c2 by rewrite sg_edgeNeq.
                       case: (boolP (a2 -- d1)) => [a2_adj_d1 | a2_nadj_d1].
                       *** have a2_neq_d1: a2 != d1 by rewrite sg_edgeNeq.
                           left; exists (hom_G4_def a2 a1 c2 d1).
                           ---- apply: h'_G4_inj; rewrite /=; try by done.
                                all: try by rewrite eq_sym.
                                by move: a1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                           ---- apply: h'_claw_hom; rewrite /=; try by done.
                                all: by rewrite sg_sym.
                       *** case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1].
                           ---- have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
                                right; left; exists (hom_G5_def a1 d1 a2 c1 c2).
                                ++++ apply: h'_G5_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     **** by move: a1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                     **** by move: c1_adj_c2; apply/contraTneq => <-.
                                     **** by move: a1_adj_a2; apply/contraTneq => <-.
                                ++++ apply: h'_bull_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
                           ---- case: (boolP (a2 -- d2)) => [a2_adj_d2 | a2_nadj_d2].
                                ++++ have a2_neq_d2: a2 != d2 by rewrite sg_edgeNeq.
                                     right; left; exists (hom_G5_def c1 d1 a2 d2 a1).
                                     **** apply: h'_G5_inj; rewrite /=; try by done.
                                          all: try by rewrite eq_sym.
                                          ----- by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                          ----- by move: c1_adj_c2; apply/contraTneq => ->.
                                          ----- by move: a1_adj_a2; apply/contraTneq => <-.
                                          ----- by move: a1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
                                     **** apply: h'_bull_hom; rewrite /=; try by done.
                                          all: by rewrite sg_sym.
                                ++++ case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1]; last first.
                                     **** left; exists (hom_G4_def a1 a2 b1 d2).
                                          ----- apply: h'_G4_inj; rewrite /=; try by done.
                                                all: try by rewrite eq_sym.
                                                +++++ by move: a2_adj_c2; apply/contraTneq => ->.
                                                +++++ by move: a2_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                          ----- apply: h'_claw_hom; rewrite /=; try by done.
                                                all: by rewrite sg_sym.
                                     **** have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
                                          right; left; exists (hom_G5_def c2 d2 a2 a1 b1).
                                          ----- apply: h'_G5_inj; rewrite /=; try by done.
                                                all: try by rewrite eq_sym.
                                                +++++ by move: c1_adj_c2; apply/contraTneq => ->.
                                                +++++ by move: a2_adj_b1; apply/contraTneq => <-; rewrite sg_sym.
                                          ----- apply: h'_bull_hom; rewrite /=; try by done.
                                                all: by rewrite sg_sym.
                   +++ case: (boolP (a2 -- d1)) => [a2_adj_d1 | a2_nadj_d1].
                       *** have a2_neq_d1: a2 != d1 by rewrite sg_edgeNeq.
                           case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
                           ---- left; exists (hom_G4_def a2 a1 c1 d1).
                                ++++ apply: h'_G4_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     **** by move: c1_adj_c2; apply/contraTneq => <-.
                                     **** by move: a1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                     **** by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                ++++ apply: h'_claw_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
                           ---- have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
                                right; left; exists (hom_G5_def a1 c2 a2 c1 d1).
                                ++++ apply: h'_G5_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     **** by move: c1_adj_c2; apply/contraTneq => <-.
                                     **** by move: a1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                     **** by move: a2_adj_d1; apply/contraTneq => <-.
                                ++++ apply: h'_bull_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
                       *** case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1].
                           ---- have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
                                left; exists (hom_G4_def c1 a2 c2 d1).
                                ++++ apply: h'_G4_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     **** by move: a1_adj_a2; apply/contraTneq => ->.
                                     **** by move: a1_adj_a2; apply/contraTneq => ->.
                                ++++ apply: h'_claw_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
                           ---- case: (boolP (a2 -- d2)) => [a2_adj_d2 | a2_nadj_d2]; last first.
                                ++++ right; right; left; exists (hom_G6_def c2 c1 a2 a1 d2 d1).
                                     **** apply: h'_G6_inj; rewrite /=; try by done.
                                          all: try by rewrite eq_sym.
                                          ----- by move: a1_adj_a2; apply/contraTneq => <-.
                                          ----- by move: b2_adj_d2; apply/contraTneq => <-.
                                          ----- by move: c1_adj_c2; apply/contraTneq => ->.
                                          ----- by move: a2_adj_c1; apply/contraTneq => ->.
                                          ----- by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
                                          ----- by move: d1_adj_d2; apply/contraTneq => <-.
                                          ----- by move: a1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                     **** apply: h'_P_6_hom; rewrite /=; try by done.
                                          all: by rewrite sg_sym.
                                ++++ have a2_neq_d2: a2 != d2 by rewrite sg_edgeNeq.
                                     right; left; exists (hom_G5_def c1 d1 a2 d2 a1).
                                     **** apply: h'_G5_inj; rewrite /=; try by done.
                                          all: try by rewrite eq_sym.
                                          ----- by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                          ----- by move: c1_adj_c2; apply/contraTneq => ->.
                                          ----- by move: a2_adj_c1; apply/contraTneq => <-; rewrite sg_sym.
                                          ----- by move: a1_adj_a2; apply/contraTneq => <-; rewrite sg_sym.
                                     **** apply: h'_bull_hom; rewrite /=; try by done.
                                          all: by rewrite sg_sym.
               --- have a1_neq_d1: a1 != d1 by rewrite sg_edgeNeq.
                   case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
                   +++ case: (boolP (b1 -- c1)) => [b1_adj_c1 | b1_nadj_c1].
                       *** have b1_neq_c1: b1 != c1 by rewrite sg_edgeNeq.
                           case: (boolP (b1 -- d1)) => [b1_adj_d1 | b1_nadj_d1].
                           ---- have b1_neq_d1: b1 != d1 by rewrite sg_edgeNeq.
                                left; exists (hom_G4_def b1 b2 c1 d1).
                                ++++ apply: h'_G4_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                ++++ apply: h'_claw_hom; rewrite /=; try by done.
                                     all: try by rewrite sg_sym.
                           ---- case: (boolP (a2 -- d1)) => [a2_adj_d1 | a2_nadj_d1]; last first.
                                ++++ case: (boolP (a2 -- b2)) => [a2_adj_b2 | a2_nadj_b2].
                                     **** have a2_neq_b2: a2 != b2 by rewrite sg_edgeNeq.
                                          right; left; exists (hom_G5_def c1 d1 a2 a1 b2).
                                          ----- apply: h'_G5_inj; rewrite /=; try by done.
                                                all: try by rewrite eq_sym.
                                                +++++ by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                                +++++ by move: c1_adj_c2; apply/contraTneq => ->.
                                                +++++ by move: a2_adj_c1; apply/contraTneq => <-; rewrite sg_sym.
                                          ----- apply: h'_bull_hom; rewrite /=; try by done.
                                                all: by rewrite sg_sym.
                                     **** left; exists (hom_G4_def a1 a2 b2 d1).
                                          ----- apply: h'_G4_inj; rewrite /=; try by done.
                                                all: try by rewrite eq_sym.
                                                +++++ by move: a2_adj_c1; apply/contraTneq => ->.
                                                +++++ by move: a2_adj_c1; apply/contraTneq => ->; rewrite sg_sym.
                                          ----- apply: h'_claw_hom; rewrite /=; try by done.
                                                all: by rewrite sg_sym.
                                ++++ have a2_neq_d1: a2 != d1 by rewrite sg_edgeNeq.
                                     case: (boolP (a2 -- b2)) => [a2_adj_b2 | a2_nadj_b2].
                                     **** have a2_neq_b2: a2 != b2 by rewrite sg_edgeNeq.
                                          left; exists (hom_G4_def a2 b2 c1 d1).
                                          ----- apply: h'_G4_inj; rewrite /=; try by done.
                                                all: try by rewrite eq_sym.
                                                by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                          ----- apply: h'_claw_hom; rewrite /=; try by done.
                                                all: by rewrite sg_sym.
                                     **** right; left; exists (hom_G5_def b2 c1 a1 a2 d1).
                                          ----- apply: h'_G5_inj; rewrite /=; try by done.
                                                all: try by rewrite eq_sym.
                                                +++++ by move: a2_adj_c1; apply/contraTneq => <-.
                                                +++++ by move: c1_adj_c2; apply/contraTneq => ->.
                                                +++++ by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                          ----- apply: h'_bull_hom; rewrite /=; try by done.
                                                all: by rewrite sg_sym.
                       *** case: (boolP (a2 -- b2)) => [a2_adj_b2 | a2_nadj_b2]; last first. 
                           ---- case: (boolP (a2 -- d1)) => [a2_adj_d1 | a2_nadj_d1].
                                ++++ have a2_neq_d1: a2 != d1 by rewrite sg_edgeNeq.
                                     right; left; exists (hom_G5_def b2 c1 a1 a2 d1).
                                     **** apply: h'_G5_inj; rewrite /=; try by done.
                                          all: try by rewrite eq_sym.
                                          ----- by move: a2_adj_c1; apply/contraTneq => <-.
                                          ----- by move: c1_adj_c2; apply/contraTneq => ->.
                                          ----- by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                     **** apply: h'_bull_hom; rewrite /=; try by done.
                                          all: by rewrite sg_sym.
                                ++++ left; exists (hom_G4_def a1 a2 b2 d1).
                                     **** apply: h'_G4_inj; rewrite /=; try by done.
                                          all: try by rewrite eq_sym.
                                          ----- by move: a2_adj_c1; apply/contraTneq => ->.
                                          ----- by move: a2_adj_c1; apply/contraTneq => ->; rewrite sg_sym.
                                     **** apply: h'_claw_hom; rewrite /=; try by done.
                                          all: by rewrite sg_sym.
                           ---- have a2_neq_b2: a2 != b2 by rewrite sg_edgeNeq.
                                case: (boolP (a2 -- d1)) => [a2_adj_d1 | a2_nadj_d1]; last first.
                                ++++ right; left; exists (hom_G5_def c1 d1 a2 a1 b2).
                                     **** apply: h'_G5_inj; rewrite /=; try by done.
                                          all: try by rewrite eq_sym.
                                          ----- by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                          ----- by move: c1_adj_c2; apply/contraTneq => ->.
                                          ----- by move: a2_adj_c1; apply/contraTneq => <-; rewrite sg_sym.
                                     **** apply: h'_bull_hom; rewrite /=; try by done.
                                          all: by rewrite sg_sym.
                                ++++ have a2_neq_d1: a2 != d1 by rewrite sg_edgeNeq.
                                     left; exists (hom_G4_def a2 b2 c1 d1).
                                     **** apply: h'_G4_inj; rewrite /=; try by done.
                                          all: try by rewrite eq_sym.
                                          by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                     **** apply: h'_claw_hom; rewrite /=; try by done.
                                          all: by rewrite sg_sym.
                   +++ have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
                       case: (boolP (b1 -- d1)) => [b1_adj_d1 | b1_nadj_d1]; last first.
                       *** case: (boolP (b1 -- c1)) => [b1_adj_c1 | b1_nadj_c1]; last first.
                           ---- right; left; exists (hom_G5_def b1 c1 a1 d1 d2).
                                ++++ apply: h'_G5_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     **** by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                     **** by move: d1_adj_d2; apply/contraTneq => <-.
                                     **** by move: c1_adj_c2; apply/contraTneq => ->.
                                ++++ apply: h'_bull_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
                           ---- have b1_neq_c1: b1 != c1 by rewrite sg_edgeNeq.
                                case: (boolP (a2 -- b2)) => [a2_adj_b2 | a2_nadj_b2]; last first.
                                ++++ case: (boolP (a2 -- c2)) => [a2_adj_c2 | a2_nadj_c2]; last first.
                                     **** case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1]; last first.
                                          ----- left; exists (hom_G4_def c1 a2 b1 c2).
                                                +++++ apply: h'_G4_inj; rewrite /=; try by done.
                                                      all: try by rewrite eq_sym.
                                                      ***** by move: b1_adj_b2; apply/contraTneq => <-.
                                                      ***** by move: a1_adj_a2; apply/contraTneq => ->.
                                                +++++ apply: h'_claw_hom; rewrite /=; try by done.
                                                      all: by rewrite sg_sym.
                                          ----- have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
                                                right; left; exists (hom_G5_def b2 c2 b1 c1 a2).
                                                +++++ apply: h'_G5_inj; rewrite /=; try by done.
                                                      all: try by rewrite eq_sym.
                                                      ***** by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                                                      ***** by move: a2_adj_c1; apply/contraTneq => <-.
                                                      ***** by move: a2_adj_b1; apply/contraTneq => <-; rewrite sg_sym.
                                                +++++ apply: h'_bull_hom; rewrite /=; try by done.
                                                      all: by rewrite sg_sym.
                                     **** have a2_neq_c2: a2 != c2 by rewrite sg_edgeNeq.
                                          case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1]; last first.
                                          ----- case: (boolP (a2 -- d2)) => [a2_adj_d2 | a2_nadj_d2].
                                                +++++ have a2_neq_d2: a2 != d2 by rewrite sg_edgeNeq.
                                                      right; left; exists (hom_G5_def b1 d2 c1 a2 c2).
                                                      ***** apply: h'_G5_inj; rewrite /=; try by done.
                                                            all: try by rewrite eq_sym.
                                                            ------ by move: b1_adj_b2; apply/contraTneq => ->.
                                                            ------ by move: d1_adj_d2; apply/contraTneq => ->; rewrite sg_sym.
                                                      ***** apply: h'_bull_hom; rewrite /=; try by done.
                                                            all: by rewrite sg_sym.
                                                +++++ left; exists (hom_G4_def a1 a2 b1 d2).
                                                      ***** apply: h'_G4_inj; rewrite /=; try by done.
                                                            all: try by rewrite eq_sym.
                                                            ------ by move: b1_adj_b2; apply/contraTneq => <-.
                                                            ------ by move: a2_adj_c1; apply/contraTneq => ->; rewrite sg_sym.
                                                      ***** apply: h'_claw_hom; rewrite /=; try by done.
                                                            all: by rewrite sg_sym.
                                          ----- have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
                                                case: (boolP (a2 -- d1)) => [a2_adj_d1 | a2_nadj_d1]; last first.
                                                +++++ right; left; exists (hom_G5_def c2 d1 a2 a1 b1).
                                                      ***** apply: h'_G5_inj; rewrite /=; try by done.
                                                            all: try by rewrite eq_sym.
                                                            ------ by move: a2_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                                                            ------ by move: d1_adj_d2; apply/contraTneq => ->.
                                                      ***** apply: h'_bull_hom; rewrite /=; try by done.
                                                            all: by rewrite sg_sym.
                                                +++++ have a2_neq_d1: a2 != d1 by rewrite sg_edgeNeq.
                                                      left; exists (hom_G4_def a2 b1 c2 d1).
                                                      ***** apply: h'_G4_inj; rewrite /=; try by done.
                                                            all: try by rewrite eq_sym.
                                                            by move: d1_adj_d2; apply/contraTneq => <-.
                                                      ***** apply: h'_claw_hom; rewrite /=; try by done.
                                                            all: by rewrite sg_sym.
                                ++++ have a2_neq_b2: a2 != b2 by rewrite sg_edgeNeq.
                                     case: (boolP (a2 -- d1)) => [a2_adj_d1 | a2_nadj_d1]; last first.
                                     **** case: (boolP (a2 -- c2)) => [a2_adj_c2 | a2_nadj_c2].
                                          ----- have a2_neq_c2: a2 != c2 by rewrite sg_edgeNeq.
                                                right; left; exists (hom_G5_def c2 d1 a2 a1 b2).
                                                +++++ apply: h'_G5_inj; rewrite /=; try by done.
                                                      all: try by rewrite eq_sym.
                                                      ***** by move: b1_adj_b2; apply/contraTneq => <-.
                                                      ***** by move: a2_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                                                +++++ apply: h'_bull_hom; rewrite /=; try by done.
                                                      all: by rewrite sg_sym.
                                          ----- left; exists (hom_G4_def c1 a2 c2 d1).
                                                +++++ apply: h'_G4_inj; rewrite /=; try by done.
                                                      all: try by rewrite eq_sym.
                                                      all: by move: a2_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                +++++ apply: h'_claw_hom; rewrite /=; try by done.
                                                      all: by rewrite sg_sym.
                                     **** have a2_neq_d1: a2 != d1 by rewrite sg_edgeNeq.
                                          case: (boolP (a2 -- c2)) => [a2_adj_c2 | a2_nadj_c2]; last first.
                                          ----- right; left; exists (hom_G5_def b2 c2 a2 c1 d1).
                                                +++++ apply: h'_G5_inj; rewrite /=; try by done.
                                                      all: try by rewrite eq_sym.
                                                      ***** by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                                                      ***** by move: a2_adj_d1; apply/contraTneq => <-.
                                                +++++ apply: h'_bull_hom; rewrite /=; try by done.
                                                      all: by rewrite sg_sym.
                                          ----- have a2_neq_c2: a2 != c2 by rewrite sg_edgeNeq.
                                                left; exists (hom_G4_def a2 b2 c2 d1).
                                                +++++ apply: h'_G4_inj; rewrite /=; try by done.
                                                      all: try by rewrite eq_sym.
                                                      by move: b1_adj_b2; apply/contraTneq => ->.
                                                +++++ apply: h'_claw_hom; rewrite /=; try by done.
                                                      all: by rewrite sg_sym.
                       *** have b1_neq_d1: b1 != d1 by rewrite sg_edgeNeq.
                           case: (boolP (a2 -- c2)) => [a2_adj_c2 | a2_nadj_c2].
                           ---- have a2_neq_c2: a2 != c2 by rewrite sg_edgeNeq.
                                case: (boolP (a2 -- b2)) => [a2_adj_b2 | a2_nadj_b2]; last first.
                                ++++ case: (boolP (a2 -- d1)) => [a2_adj_d1 | a2_nadj_d1]; last first.
                                     **** left; exists (hom_G4_def a1 a2 b2 d1).
                                          ----- apply: h'_G4_inj; rewrite /=; try by done.
                                                all: try by rewrite eq_sym.
                                                +++++ by move: a2_adj_c1; apply/contraTneq => ->.
                                                +++++ by move: a2_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                          ----- apply: h'_claw_hom; rewrite /=; try by done.
                                                all: by rewrite sg_sym.
                                     **** have a2_neq_d1: a2 != d1 by rewrite sg_edgeNeq.
                                          right; left; exists (hom_G5_def b2 c2 a1 a2 d1).
                                          ----- apply: h'_G5_inj; rewrite /=; try by done.
                                                all: try by rewrite eq_sym.
                                                +++++ by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                                                +++++ by move: a2_adj_d1; apply/contraTneq => <-.
                                          ----- apply: h'_bull_hom; rewrite /=; try by done.
                                                all: by rewrite sg_sym.
                                ++++ have a2_neq_b2: a2 != b2 by rewrite sg_edgeNeq.
                                     case: (boolP (a2 -- d1)) => [a2_adj_d1 | a2_nadj_d1].
                                     **** have a2_neq_d1: a2 != d1 by rewrite sg_edgeNeq.
                                          left; exists (hom_G4_def a2 b2 c2 d1).
                                          ----- apply: h'_G4_inj; rewrite /=; try by done.
                                                all: try by rewrite eq_sym.
                                                by move: b1_adj_b2; apply/contraTneq => ->.
                                          ----- apply: h'_claw_hom; rewrite /=; try by done.
                                                all: by rewrite sg_sym.
                                     **** right; left; exists (hom_G5_def b2 d1 a2 c1 c2).
                                          ----- apply: h'_G5_inj; rewrite /=; try by done.
                                                all: try by rewrite eq_sym.
                                                +++++ by move: b1_adj_b2; apply/contraTneq => ->.
                                                +++++ by move: a2_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                                          ----- apply: h'_bull_hom; rewrite /=; try by done.
                                                all: by rewrite sg_sym.
                           ---- case: (boolP (a2 -- d1)) => [a2_adj_d1 | a2_nadj_d1]; last first.
                                ++++ case: (boolP (a2 -- b2)) => [a2_adj_b2 | a2_nadj_b2].
                                     **** have a2_neq_b2: a2 != b2 by rewrite sg_edgeNeq.
                                          left; exists (hom_G4_def c1 a2 c2 d1).
                                          ----- apply: h'_G4_inj; rewrite /=; try by done.
                                                all: try by rewrite eq_sym.
                                                +++++ by move: a1_adj_a2; apply/contraTneq => ->.
                                                +++++ by move: a2_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                          ----- apply: h'_claw_hom; rewrite /=; try by done.
                                                all: by rewrite sg_sym.
                                     **** case: (boolP (a2 -- d2)) => [a2_adj_d2 | a2_nadj_d2]; last first.
                                          ----- left; exists (hom_G4_def a1 a2 b2 d1).
                                                +++++ apply: h'_G4_inj; rewrite /=; try by done.
                                                      all: try by rewrite eq_sym.
                                                      ***** by move: b2_adj_d2; apply/contraTneq => <-.
                                                      ***** by move: d1_adj_d2; apply/contraTneq => <-.
                                                +++++ apply: h'_claw_hom; rewrite /=; try by done.
                                                      all: by rewrite sg_sym.
                                          ----- have a2_neq_d2: a2 != d2 by rewrite sg_edgeNeq.
                                                case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1]; last first.
                                                +++++ left; exists (hom_G4_def d2 a2 b2 d1).
                                                      ***** apply: h'_G4_inj; rewrite /=; try by done.
                                                            all: try by rewrite eq_sym.
                                                            ------ by move: a2_adj_c1; apply/contraTneq => ->.
                                                            ------ by move: b1_adj_d1; apply/contraTneq => <-; rewrite sg_sym.
                                                      ***** apply: h'_claw_hom; rewrite /=; try by done.
                                                            all: by rewrite sg_sym.
                                                +++++ case: (boolP (b1 -- c1)) => [b1_adj_c1 | b1_nadj_c1].
                                                      ***** have b1_neq_c1: b1 != c1 by rewrite sg_edgeNeq.
                                                            right; left; exists (hom_G5_def c2 d2 c1 d1 b1).
                                                            ------ apply: h'_G5_inj; rewrite /=; try by done.
                                                                   all: try by rewrite eq_sym.
                                                                   by move: c1_adj_c2; apply/contraTneq => ->.
                                                            ------ apply: h'_bull_hom; rewrite /=; try by done.
                                                                   all: by rewrite sg_sym.
                                                      ***** left; exists (hom_G4_def a2 b1 c1 d2).
                                                            ------ apply: h'_G4_inj; rewrite /=; try by done.
                                                                   all: try by rewrite eq_sym.
                                                                   ++++++ by move: a2_adj_d2; apply/contraTneq => ->.
                                                                   ++++++ by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                            ------ apply: h'_claw_hom; rewrite /=; try by done.
                                                                   all: by rewrite sg_sym.
                                ++++ have a2_neq_d1: a2 != d1 by rewrite sg_edgeNeq.
                                     case: (boolP (a2 -- b2)) => [a2_adj_b2 | a2_nadj_b2].
                                     **** have a2_neq_b2: a2 != b2 by rewrite sg_edgeNeq.
                                          right; left; exists (hom_G5_def b2 c2 a2 c1 d1).
                                          ----- apply: h'_G5_inj; rewrite /=; try by done.
                                                all: try by rewrite eq_sym.
                                                +++++ by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                                                +++++ by move: a1_adj_a2; apply/contraTneq => <-.
                                          ----- apply: h'_bull_hom; rewrite /=; try by done.
                                                all: by rewrite sg_sym.
                                     **** case: (boolP (b1 -- c1)) => [b1_adj_c1 | b1_nadj_c1].
                                          ----- have b1_neq_c1: b1 != c1 by rewrite sg_edgeNeq.
                                                right; left; exists (hom_G5_def c2 d2 c1 d1 b1).
                                                +++++ apply: h'_G5_inj; rewrite /=; try by done.
                                                      all: try by rewrite eq_sym.
                                                      by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
                                                +++++ apply: h'_bull_hom; rewrite /=; try by done.
                                                      all: by rewrite sg_sym.
                                          ----- case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1]; last first.
                                                +++++ right; left; exists (hom_G5_def b1 c2 d1 c1 a2).
                                                      ***** apply: h'_G5_inj; rewrite /=; try by done.
                                                            all: try by rewrite eq_sym.
                                                            ------ by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                            ------ by move: b1_adj_b2; apply/contraTneq => ->.
                                                            ------ by move: a1_adj_a2; apply/contraTneq => <-.
                                                      ***** apply: h'_bull_hom; rewrite /=; try by done.
                                                            all: by rewrite sg_sym.
                                                +++++ have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
                                                      case: (boolP (a2 -- d2)) => [a2_adj_d2 | a2_nadj_d2].
                                                      ***** have a2_neq_d2: a2 != d2 by rewrite sg_edgeNeq.
                                                            left; exists (hom_G4_def a2 b1 c1 d2).
                                                            ------ apply: h'_G4_inj; rewrite /=; try by done.
                                                                   all: try by rewrite eq_sym.
                                                                   by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                            ------ apply: h'_claw_hom; rewrite /=; try by done.
                                                                   all: by rewrite sg_sym.
                                                      ***** right; left; exists (hom_G5_def c1 d2 a2 a1 b1).
                                                            ------ apply: h'_G5_inj; rewrite /=; try by done.
                                                                   all: try by rewrite eq_sym.
                                                                   ++++++ by move: c1_adj_c2; apply/contraTneq => ->.
                                                                   ++++++ by move: b1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
                                                                   ++++++ by move: a2_adj_b1; apply/contraTneq => <-; rewrite sg_sym.
                                                            ------ apply: h'_bull_hom; rewrite /=; try by done.
                                                                   all: by rewrite sg_sym.
    * have c2_neq_d2: c2 != d2 by rewrite sg_edgeNeq.
      case: (boolP (a1 -- c2)) => [a1_adj_c2 | a1_nadj_c2]; last first.
      -- have a1_neq_c2: a1 != c2 by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
         have a2_neq_c1: a2 != c1 by move: a1_adj_a2; apply/contraTneq => ->.
         have a2_adj_c1: a2 -- c1 by rewrite (negbTE a1_neq_c2) (negbTE a2_neq_c1) (negbTE a1_nadj_c2) in a1c2a2c1.
         case: (boolP (a1 -- d1)) => [a1_adj_d1 | a1_nadj_d1]; last first.
         ++ left; exists (hom_G4_def d2 a1 c2 d1).
            ** apply: h'_G4_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               by move: a1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
            ** apply: h'_claw_hom; rewrite /=; try by done.
               all: by rewrite sg_sym.
         ++ have a1_neq_d1: a1 != d1 by rewrite sg_edgeNeq.
            case: (boolP (b2 -- c2)) => [b2_adj_c2 | b2_nadj_c2]; last first.
            ** left; exists (hom_G4_def d2 b2 c2 d1).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   by move: b1_adj_b2; apply/contraTneq => ->.
               --- apply: h'_claw_hom; rewrite /=; try by done.
                   all: by rewrite sg_sym.
            ** have b2_neq_c2: b2 != c2 by rewrite sg_edgeNeq.
               case: (boolP (b1 -- c1)) => [b1_adj_c1 | b1_nadj_c1]; last first.
               --- right; left; exists (hom_G5_def b1 c1 b2 c2 d2).
                   +++ apply: h'_G5_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                   +++ apply: h'_bull_hom; rewrite /=; try by done.
                       all: by rewrite sg_sym.
               --- have b1_neq_c1: b1 != c1 by rewrite sg_edgeNeq.
                   case: (boolP (a1 -- b1)) => [a1_adj_b1 | a1_nadj_b1]; last first.
                   +++ left; exists (hom_G4_def b2 a1 b1 c2).
                       *** apply: h'_G4_inj; rewrite /=; try by done.
                           all: try by rewrite eq_sym.
                           by move: a1_adj_d2; apply/contraTneq => ->.
                       *** apply: h'_claw_hom; rewrite /=; try by done.
                           all: by rewrite sg_sym.
                   +++ have a1_neq_b1: a1 != b1 by rewrite sg_edgeNeq.
                       case: (boolP (b1 -- d1)) => [b1_adj_d1 | b1_nadj_d1]; last first.
                       *** right; left; exists (hom_G5_def c2 d1 b2 a1 b1).
                           ---- apply: h'_G5_inj; rewrite /=; try by done.
                                all: try by rewrite eq_sym.
                                by move: d1_adj_d2; apply/contraTneq => ->.
                           ---- apply: h'_bull_hom; rewrite /=; try by done.
                                all: by rewrite sg_sym.
                       *** have b1_neq_d1: b1 != d1 by rewrite sg_edgeNeq.
                           case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
                           ---- left; exists (hom_G4_def b1 b2 c1 d1).
                                ++++ apply: h'_G4_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                ++++ apply: h'_claw_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
                           ---- have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
                                right; right; right; exists (hom_G6_def b1 c2 d1 b2 c1 d2).
                                ++++ apply: h'_G6_inj; rewrite /=; try by done.
                                     all: by rewrite eq_sym.
                                ++++ apply: h'_CC_6_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
      -- have a1_neq_c2: a1 != c2 by rewrite sg_edgeNeq.
         case: (boolP (a1 -- d1)) => [a1_adj_d1 | a1_nadj_d1].
         ++ have a1_neq_d1: a1 != d1 by rewrite sg_edgeNeq.
            case: (boolP (b2 -- c2)) => [b2_adj_c2 | b2_nadj_c2]; last first.
            ** left; exists (hom_G4_def a1 b2 c2 d1).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   by move: b1_adj_b2; apply/contraTneq => ->.
               --- by apply: h'_claw_hom.
            ** have b2_neq_c2: b2 != c2 by rewrite sg_edgeNeq.
               case: (boolP (b1 -- c1)) => [b1_adj_c1 | b1_nadj_c1]; last first.
               --- right; left; exists (hom_G5_def b1 c1 b2 c2 d2).
                   +++ apply: h'_G5_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                   +++ apply: h'_bull_hom; rewrite /=; try by done.
                       all: by rewrite sg_sym.
               --- have b1_neq_c1: b1 != c1 by rewrite sg_edgeNeq.
                   case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1].
                   +++ have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
                       case: (boolP (b1 -- d1)) => [b1_adj_d1 | b1_nadj_d1]; last first.
                       *** left; exists (hom_G4_def c1 b1 d1 c2).
                           ---- apply: h'_G4_inj; rewrite /=; try by done.
                                all: try by rewrite eq_sym.
                                by move: d1_adj_d2; apply/contraTneq => <-.
                           ---- apply: h'_claw_hom; rewrite /=; try by done.
                                all: by rewrite sg_sym.
                       *** have b1_neq_d1: b1 != d1 by rewrite sg_edgeNeq.
                           right; right; right; exists (hom_G6_def b1 c2 d1 b2 c1 d2).
                           ---- apply: h'_G6_inj; rewrite /=; try by done.
                                all: by rewrite eq_sym.
                           ---- apply: h'_CC_6_hom; rewrite /=; try by done.
                                all: by rewrite sg_sym.
                   +++ case: (boolP (b1 -- d1)) => [b1_adj_d1 | b1_nadj_d1].
                       *** have b1_neq_d1: b1 != d1 by rewrite sg_edgeNeq.
                           left; exists (hom_G4_def b1 b2 c1 d1).
                           ---- apply: h'_G4_inj; rewrite /=; try by done.
                                all: try by rewrite eq_sym.
                                by move: d1_adj_d2; apply/contraTneq => <-.
                           ---- apply: h'_claw_hom; rewrite /=; try by done.
                                all: by rewrite sg_sym.
                       *** case: (boolP (a1 -- b1)) => [a1_adj_b1 | a1_nadj_b1].
                           ---- right; left; exists (hom_G5_def c1 d1 b1 a1 b2).
                                ++++ apply: h'_G5_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     **** by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                     **** by move: a1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
                                     **** by move: d1_adj_d2; apply/contraTneq => ->.
                                     **** by move: a1_adj_d2; apply/contraTneq => <-.
                                ++++ apply: h'_bull_hom; rewrite /=; try by done.
                                     all: try by rewrite sg_sym.
                           ---- right; left; exists (hom_G5_def b1 d1 b2 a1 c2).
                                ++++ apply: h'_G5_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     **** by move: d1_adj_d2; apply/contraTneq => <-.
                                     **** by move: a1_adj_d2; apply/contraTneq => <-.
                                ++++ apply: h'_bull_hom; rewrite /=; try by done.
                                     all: try by rewrite sg_sym.
         ++ case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
            ** right; left; exists (hom_G5_def c1 d1 c2 d2 a1).
               --- apply: h'_G5_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   +++ by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                   +++ by move: a1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
                   +++ by move: a1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
               --- apply: h'_bull_hom; rewrite /=; try by done.
                   all: by rewrite sg_sym.
            ** have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
               case: (boolP (b2 -- c2)) => [b2_adj_c2 | b2_nadj_c2]; last first.
               --- left; exists (hom_G4_def d2 b2 c2 d1).
                   +++ apply: h'_G4_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                   +++ apply: h'_claw_hom; rewrite /=; try by done.
                       all: by rewrite sg_sym.
               --- have b2_neq_c2: b2 != c2 by rewrite sg_edgeNeq.
                   case: (boolP (b1 -- c1)) => [b1_adj_c1 | b1_nadj_c1]; last first.
                   +++ right; left; exists (hom_G5_def b1 c1 b2 c2 d2).
                       *** apply: h'_G5_inj; rewrite /=; try by done.
                           all: try by rewrite eq_sym.
                           by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                       *** apply: h'_bull_hom; rewrite /=; try by done.
                           all: by rewrite sg_sym.
                   +++ have b1_neq_c1: b1 != c1 by rewrite sg_edgeNeq.
                       case: (boolP (b1 -- d1)) => [b1_adj_d1 | b1_nadj_d1]; last first.
                       *** left; exists (hom_G4_def c1 b1 c2 d1).
                           ---- apply: h'_G4_inj; rewrite /=; try by done.
                                all: try by rewrite eq_sym.
                                by move: d1_adj_d2; apply/contraTneq => <-.
                           ---- apply: h'_claw_hom; rewrite /=; try by done.
                                all: by rewrite sg_sym.
                       *** have b1_neq_d1: b1 != d1 by rewrite sg_edgeNeq.
                           right; right; right; exists (hom_G6_def b1 c2 d1 b2 c1 d2).
                           ---- apply: h'_G6_inj; rewrite /=; try by done.
                                all: by rewrite eq_sym.
                           ---- apply: h'_CC_6_hom; rewrite /=; try by done.
                                all: by rewrite sg_sym.
Qed.

Lemma subcase2_a1a2_b1b2_c1c2_d1d22_with_a1_adj_b2 (h : claw -> trfgraph G) (a1 a2 b1 b2 c1 c2 d1 d2 : G) :
  b1 != c2 ->
  ~~ b1 -- c2 ->
  b2 != c1 ->
  ~~ b2 -- c1 ->
  b1 != d2 ->
  ~~ b1 -- d2 ->
  b2 != d1 ->
  ~~ b2 -- d1 ->
  c1 != d2 ->
  ~~ c1 -- d2 ->
  c2 != d1 ->
  ~~ c2 -- d1 ->
  a1 -- a2 ->
  b1 -- b2 ->
  c1 -- c2 ->
  d1 -- d2 ->
  a1 -- b2 ->
  ~~ a1 -- d2 ->
  ~~ a2 -- c1 ->
  ~~ a1 -- c2 ->
  a2 -- d1 ->
  ~~ a2 -- b1 ->
  a2 = c1 ->
    ((exists2 h0 : claw -> G, injective h0 & induced_hom h0) \/
    (exists2 h0 : bull -> G, injective h0 & induced_hom h0) \/
    (exists2 h0 : 'P_6 -> G, injective h0 & induced_hom h0) \/
    (exists2 h0 : 'CC_6 -> G, injective h0 & induced_hom h0)).
Proof.
move => ? ? ? ? ? ? ? ? ? ? ? ? a1_adj_a2 b1_adj_b2 c1_adj_c2 d1_adj_d2 a1_adj_b2 a1_nadj_d2 a2_nadj_c1 a1_nadj_c2 a2_adj_d1 a2_nadj_b1 a2_eq_c1.
have a1_neq_a2: a1 != a2 by rewrite sg_edgeNeq.
have b1_neq_b2: b1 != b2 by rewrite sg_edgeNeq.
have c1_neq_c2: c1 != c2 by rewrite sg_edgeNeq.
have d1_neq_d2: d1 != d2 by rewrite sg_edgeNeq.
have a1_neq_b2: a1 != b2 by rewrite sg_edgeNeq.
have a2_neq_d1: a2 != d1 by rewrite sg_edgeNeq.
case: (boolP (b2 -- c2)) => [b2_adj_c2 | b2_nadj_c2]; last first.
- case: (boolP (a1 -- d1)) => [a1_adj_d1 | a1_nadj_d1]; last first.
  + left; exists (hom_G4_def a2 a1 c2 d1).
    * apply: h'_G4_inj; rewrite /=; try by done.
      all: try by rewrite eq_sym.
      all: try by move: a1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
      by rewrite a2_eq_c1.
    * apply: h'_claw_hom; rewrite /=; try by done.
      all: try by rewrite sg_sym.
      by rewrite a2_eq_c1.
  + have a1_neq_d1: a1 != d1 by rewrite sg_edgeNeq.
    right; left; exists (hom_G5_def b2 c2 a1 a2 d1).
    * apply: h'_G5_inj; rewrite /=; try by done.
      all: try by rewrite eq_sym.
      -- by move: a1_adj_b2; apply/contraTneq => ->.
      -- by rewrite a2_eq_c1.
      -- by move: a1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
      -- by rewrite a2_eq_c1 eq_sym.
    * apply: h'_bull_hom; rewrite /=; try by done.
      all: try by rewrite sg_sym.
      -- by rewrite a2_eq_c1 sg_sym.
      -- by rewrite a2_eq_c1.
- have b2_neq_c2: b2 != c2 by rewrite sg_edgeNeq.
  case: (boolP (a1 -- d1)) => [a1_adj_d1 | a1_nadj_d1].
  + have a1_neq_d1: a1 != d1 by rewrite sg_edgeNeq.
    case: (boolP (a1 -- b1)) => [a1_adj_b1 | a1_nadj_b1]; last first.
    * left; exists (hom_G4_def b2 a1 b1 c2).
      -- apply: h'_G4_inj; rewrite /=; try by done.
         all: try by rewrite eq_sym.
         ++ by move: a1_adj_a2; apply/contraTneq => ->; rewrite sg_sym.
         ++ by move: a1_adj_d1; apply/contraTneq => ->.
      -- apply: h'_claw_hom; rewrite /=; try by done.
         all: try by rewrite sg_sym.
    * have a1_neq_b1: a1 != b1 by rewrite sg_edgeNeq.
      case: (boolP (b2 -- d2)) => [b2_adj_d2 | b2_nadj_d2]; last first.
      -- right; left; exists (hom_G5_def b2 d2 a1 d1 a2).
         ++ apply: h'_G5_inj; rewrite /=; try by done.
            all: try by rewrite eq_sym.
            ** by move: a1_adj_b2; apply/contraTneq => ->.
            ** by rewrite a2_eq_c1.
            ** by move: a1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
            ** by rewrite a2_eq_c1 eq_sym.
         ++ apply: h'_bull_hom; rewrite /=; try by done.
            all: try by rewrite sg_sym.
            ** by rewrite a2_eq_c1.
            ** by rewrite a2_eq_c1 sg_sym.
      -- have b2_neq_d2: b2 != d2 by rewrite sg_edgeNeq.
         case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2]; last first.
         ++ left; exists (hom_G4_def b2 a1 c2 d2).
            ** apply: h'_G4_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               --- by move: a1_adj_d1; apply/contraTneq => ->.
               --- by move: a1_adj_b1; apply/contraTneq => ->; rewrite sg_sym.
               --- by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
            ** apply: h'_claw_hom; rewrite /=; try by done.
               all: try by rewrite sg_sym.
         ++ have c2_neq_d2: c2 != d2 by rewrite sg_edgeNeq.
            right; left; exists (hom_G5_def a2 b1 c2 b2 d2).
            ** apply: h'_G5_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               all: try by rewrite a2_eq_c1.
               --- by move: b1_adj_b2; apply/contraTneq => <-; rewrite a2_eq_c1 sg_sym.
               --- by move: b1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
            ** apply: h'_bull_hom; rewrite /=; try by done.
               all: try by rewrite sg_sym.
               all: try by rewrite a2_eq_c1.
               by rewrite a2_eq_c1 sg_sym.
  + case: (boolP (a1 -- b1)) => [a1_adj_b1 | a1_nadj_b1].
    * have a1_neq_b1: a1 != b1 by rewrite sg_edgeNeq.
      left; exists (hom_G4_def a2 a1 c2 d1).
      -- apply: h'_G4_inj; rewrite /=; try by done.
         all: try by rewrite eq_sym.
         ++ by rewrite a2_eq_c1.
         ++ by move: a1_adj_b1; apply/contraTneq => ->; rewrite sg_sym.
         ++ by move: a1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
      -- apply: h'_claw_hom; rewrite /=; try by done.
         all: try by rewrite sg_sym.
         by rewrite a2_eq_c1.
    * case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2].
      -- have c2_neq_d2: c2 != d2 by rewrite sg_edgeNeq.
         left; exists (hom_G4_def a2 a1 c2 d1).
         ++ apply: h'_G4_inj; rewrite /=; try by done.
            all: try by rewrite eq_sym.
            ** by rewrite a2_eq_c1.
            ** by move: c2_adj_d2; apply/contraTneq => <-.
            ** by move: a1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
         ++ apply: h'_claw_hom; rewrite /=; try by done.
            all: try by rewrite sg_sym.
            by rewrite a2_eq_c1.
      -- case: (boolP (b2 -- d2)) => [b2_adj_d2 | b2_nadj_d2].
         ++ have b2_neq_d2: b2 != d2 by rewrite sg_edgeNeq.
            left; exists (hom_G4_def b2 a1 b1 d2).
            ** apply: h'_G4_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               --- by move: a1_adj_a2; apply/contraTneq => ->; rewrite sg_sym.
               --- by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
            ** apply: h'_claw_hom; rewrite /=; try by done.
               all: by rewrite sg_sym.
         ++ case: (boolP (b1 -- d1)) => [b1_adj_d1 | b1_nadj_d1].
            ** have b1_neq_d1: b1 != d1 by rewrite sg_edgeNeq.
               left; exists (hom_G4_def d1 a2 b1 d2).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   +++ by move: a1_adj_a2; apply/contraTneq => ->.
                   +++ by rewrite a2_eq_c1.
               --- apply: h'_claw_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   by rewrite a2_eq_c1.
            ** right; right; left; exists (hom_G6_def b1 b2 a1 a2 d1 d2).
               --- apply: h'_G6_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   +++ by move: a1_adj_a2; apply/contraTneq => <-; rewrite sg_sym.
                   +++ by move: a1_adj_a2; apply/contraTneq => <-.
                   +++ by move: d1_adj_d2; apply/contraTneq => <-.
                   +++ by rewrite a2_eq_c1.
                   +++ by move: b1_adj_b2; apply/contraTneq => ->.
                   +++ by move: d1_adj_d2; apply/contraTneq => <-.
                   +++ by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
                   +++ by move: a1_adj_a2; apply/contraTneq => ->.
               --- apply: h'_P_6_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   all: by rewrite a2_eq_c1.
Qed.

Lemma case_a1a2_b1b2_c1c2_d1d2_with_a1_adj_b2 (h : claw -> trfgraph G) (a1 a2 b1 b2 c1 c2 d1 d2 : G) :
  (a1 == b2) || a1 -- b2 || (a2 == b1) || a2 -- b1 ->
  (a1 == c2) || a1 -- c2 || (a2 == c1) || a2 -- c1 ->
  (a1 == d2) || a1 -- d2 || (a2 == d1) || a2 -- d1 ->
  b1 != c2 ->
  ~~ b1 -- c2 ->
  b2 != c1 ->
  ~~ b2 -- c1 ->
  b1 != d2 ->
  ~~ b1 -- d2 ->
  b2 != d1 ->
  ~~ b2 -- d1 ->
  c1 != d2 ->
  ~~ c1 -- d2 ->
  c2 != d1 ->
  ~~ c2 -- d1 ->
  a1 -- a2 ->
  b1 -- b2 ->
  c1 -- c2 ->
  d1 -- d2 ->
  a1 -- b2 ->
    ((exists2 h0 : claw -> G, injective h0 & induced_hom h0) \/
    (exists2 h0 : bull -> G, injective h0 & induced_hom h0) \/
    (exists2 h0 : 'P_6 -> G, injective h0 & induced_hom h0) \/
    (exists2 h0 : 'CC_6 -> G, injective h0 & induced_hom h0)).
Proof.
move => a1b2a2b1 a1c2a2c1 a1d2a2d1 ? ? ? ? ? ? ? ? ? ? ? ? a1_adj_a2 b1_adj_b2 c1_adj_c2 d1_adj_d2 a1_adj_b2.
have a1_neq_a2: a1 != a2 by rewrite sg_edgeNeq.
have b1_neq_b2: b1 != b2 by rewrite sg_edgeNeq.
have c1_neq_c2: c1 != c2 by rewrite sg_edgeNeq.
have d1_neq_d2: d1 != d2 by rewrite sg_edgeNeq.
have a1_neq_b2: a1 != b2 by rewrite sg_edgeNeq.
case: (boolP (a1 -- d2)) => [a1_adj_d2 | a1_nadj_d2].
- by apply: (@subcase1_a1a2_b1b2_c1c2_d1d22_with_a1_adj_b2 h a1 a2 b1 b2 c1 c2 d1 d2).
- case: (boolP (a2 -- c1)) => [a2_adj_c1 | a2_nadj_c1].
  + have a2_neq_c1: a2 != c1 by rewrite sg_edgeNeq.
    case: (boolP (a2 -- d1)) => [a2_adj_d1 | a2_nadj_d1].
    * have a2_neq_d1: a2 != d1 by rewrite sg_edgeNeq.
      apply: (@subcase1_a1a2_b1b2_c1c2_d1d22_with_a1_adj_b2 h a2 a1 c2 c1 b2 b1 d2 d1); try by done.
      all: try by rewrite eq_sym.
      all: try by rewrite sg_sym.
      all: by rewrite orbC orbA orbC orbA orbA.
    * case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1].
      -- have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
         apply: (@subcase1_a1a2_b1b2_c1c2_d1d22_with_a1_adj_b2 h a2 a1 b2 b1 d2 d1 c2 c1); try by done.
         all: try by rewrite eq_sym.
         all: try by rewrite sg_sym.
         all: try by rewrite orbC orbA orbC orbA orbA.
      -- case: (boolP (a1 -- c2)) => [a1_adj_c2 | a1_nadj_c2].
         ++ have a1_neq_c2: a1 != c2 by rewrite sg_edgeNeq.
            apply: (@subcase1_a1a2_b1b2_c1c2_d1d22_with_a1_adj_b2 h a1 a2 b1 b2 d1 d2 c1 c2); try by done.
            all: try by rewrite eq_sym.
            all: try by rewrite sg_sym.
         ++ case: (boolP (a1 -- b1)) => [a1_adj_b1 | a1_nadj_b1]; last first.
            ** case: (boolP (b2 -- d2)) => [b2_adj_d2 | b2_nadj_d2].
               --- have b2_neq_d2: b2 != d2 by rewrite sg_edgeNeq.
                   case: (boolP (a1 -- d1)) => [a1_adj_d1 | a1_nadj_d1]; last first.
                   +++ left; exists (hom_G4_def b2 a1 b1 d2).
                       *** apply: h'_G4_inj; rewrite /=; try by done.
                           all: try by rewrite eq_sym.
                           ---- by move: a1_adj_a2; apply/contraTneq => ->; rewrite sg_sym.
                           ---- by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
                       *** apply: h'_claw_hom; rewrite /=; try by done.
                           all: by rewrite sg_sym.
                   +++ have a1_neq_d1: a1 != d1 by rewrite sg_edgeNeq.
                       case: (boolP (a2 -- d2)) => [a2_adj_d2 | a2_nadj_d2]; last first.
                       *** left; exists (hom_G4_def b2 a1 b1 d2).
                           ---- apply: h'_G4_inj; rewrite /=; try by done.
                                all: try by rewrite eq_sym.
                                all: by move: a1_adj_a2; apply/contraTneq => ->; rewrite sg_sym.
                           ---- apply: h'_claw_hom; rewrite /=; try by done.
                                all: by rewrite sg_sym.
                       *** have a2_neq_d2: a2 != d2 by rewrite sg_edgeNeq.
                           case: (boolP (b2 -- c2)) => [b2_adj_c2 | b2_nadj_c2].
                           ---- have b2_neq_c2: b2 != c2 by rewrite sg_edgeNeq.
                                left; exists (hom_G4_def b2 a1 b1 c2).
                                ++++ apply: h'_G4_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     **** by move: a1_adj_a2; apply/contraTneq => ->; rewrite sg_sym.
                                     **** by move: a1_adj_d1; apply/contraTneq => ->.
                                ++++ apply: h'_claw_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
                           ---- case: (boolP (a2 -- c2)) => [a2_adj_c2 | a2_nadj_c2]; last first.
                                ++++ case: (boolP (b1 -- c1)) => [b1_adj_c1 | b1_nadj_c1].
                                     **** have b1_neq_c1: b1 != c1 by rewrite sg_edgeNeq.
                                          left; exists (hom_G4_def c1 b1 a2 c2).
                                          ----- apply: h'_G4_inj; rewrite /=; try by done.
                                                all: try by rewrite eq_sym.
                                                +++++ by move: a1_adj_a2; apply/contraTneq => <-.
                                                +++++ by move: a1_adj_a2; apply/contraTneq => ->.
                                          ----- apply: h'_claw_hom; rewrite /=; try by done.
                                                all: by rewrite sg_sym.
                                     **** case: (boolP (a2 -- b2)) => [a2_adj_b2 | a2_nadj_b2]; last first.
                                          ----- case: (boolP (a1 -- c1)) => [a1_adj_c1 | a1_nadj_c1].
                                                +++++ have a1_neq_c1: a1 != c1 by rewrite sg_edgeNeq.
                                                      right; left; exists (hom_G5_def b2 c2 a1 c1 a2).
                                                      ***** apply: h'_G5_inj; rewrite /=; try by done.
                                                            all: try by rewrite eq_sym.
                                                            ------ by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                                                            ------ by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                            ------ by move: a1_adj_a2; apply/contraTneq => <-; rewrite sg_sym.
                                                            ------ by move: a1_adj_a2; apply/contraTneq => <-.
                                                      ***** apply: h'_bull_hom; rewrite /=; try by done.
                                                            all: by rewrite sg_sym.
                                                +++++ right; right; left; exists (hom_G6_def b1 b2 a1 a2 c1 c2).
                                                      ***** apply: h'_G6_inj; rewrite /=; try by done.
                                                            all: try by rewrite eq_sym.
                                                            all: try by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                            ------ by move: a1_adj_a2; apply/contraTneq => <-; rewrite sg_sym.
                                                            ------ by move: a2_adj_c1; apply/contraTneq => <-.
                                                            ------ by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                                                            ------ by move: a1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                            ------ by move: a1_adj_a2; apply/contraTneq => ->; rewrite sg_sym.
                                                            ------ by move: a1_adj_a2; apply/contraTneq => ->.
                                                      ***** apply: h'_P_6_hom; rewrite /=; try by done.
                                                            all: by rewrite sg_sym.
                                          ----- have a2_neq_b2: a2 != b2 by rewrite sg_edgeNeq.
                                                right; left; exists (hom_G5_def b1 c1 b2 a2 d2).
                                                +++++ apply: h'_G5_inj; rewrite /=; try by done.
                                                      all: try by rewrite eq_sym.
                                                      ***** by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                      ***** by move: a1_adj_a2; apply/contraTneq => <-.
                                                +++++ apply: h'_bull_hom; rewrite /=; try by done.
                                                      all: by rewrite sg_sym.
                                ++++ have a2_neq_c2: a2 != c2 by rewrite sg_edgeNeq.
                                     case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2].
                                     **** have c2_neq_d2: c2 != d2 by rewrite sg_edgeNeq.
                                          left; exists (hom_G4_def b2 a1 b1 d2).
                                          ----- apply: h'_G4_inj; rewrite /=; try by done.
                                                all: try by rewrite eq_sym.
                                                +++++ by move: a1_adj_a2; apply/contraTneq => ->; rewrite sg_sym.
                                                +++++ by move: c2_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
                                          ----- apply: h'_claw_hom; rewrite /=; try by done.
                                                all: by rewrite sg_sym.
                                     **** case: (boolP (a1 -- c1)) => [a1_adj_c1 | a1_nadj_c1].
                                          ----- have a1_neq_c1: a1 != c1 by rewrite sg_edgeNeq.
                                                left; exists (hom_G4_def a2 a1 c2 d2).
                                                +++++ apply: h'_G4_inj; rewrite /=; try by done.
                                                      all: try by rewrite eq_sym.
                                                      ***** by move: a1_adj_d1; apply/contraTneq => ->.
                                                      ***** by move: a1_adj_c1; apply/contraTneq => ->; rewrite sg_sym.
                                                      ***** by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
                                                +++++ apply: h'_claw_hom; rewrite /=; try by done.
                                                      all: by rewrite sg_sym.
                                          ----- case: (boolP (b1 -- c1)) => [b1_adj_c1 | b1_nadj_c1].
                                                +++++ have b1_neq_c1: b1 != c1 by rewrite sg_edgeNeq.
                                                      right; left; exists (hom_G5_def a1 b1 a2 c1 c2).
                                                      ***** apply: h'_G5_inj; rewrite /=; try by done.
                                                            all: try by rewrite eq_sym.
                                                            ------ by move: a1_adj_a2; apply/contraTneq => ->; rewrite sg_sym.
                                                            ------ by move: c1_adj_c2; apply/contraTneq => <-.
                                                            ------ by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                                                            ------ by move: a1_adj_a2; apply/contraTneq => <-.
                                                      ***** apply: h'_bull_hom; rewrite /=; try by done.
                                                            all: by rewrite sg_sym.
                                                +++++ case: (boolP (a2 -- b2)) => [a2_adj_b2 | a2_nadj_b2]; last first.
                                                      ***** left; exists (hom_G4_def a1 a2 b2 d1).
                                                            ------ apply: h'_G4_inj; rewrite /=; try by done.
                                                                   all: try by rewrite eq_sym.
                                                                   ++++++ by move: b1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
                                                                   ++++++ by move: a2_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                                            ------ apply: h'_claw_hom; rewrite /=; try by done.
                                                                   all: by rewrite sg_sym.
                                                      ***** have a2_neq_b2: a2 != b2 by rewrite sg_edgeNeq.
                                                            right; left; exists (hom_G5_def b1 c1 b2 a2 d2).
                                                            ------ apply: h'_G5_inj; rewrite /=; try by done.
                                                                   all: try by rewrite eq_sym.
                                                                   ++++++ by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                                   ++++++ by move: a1_adj_a2; apply/contraTneq => <-.
                                                            ------ apply: h'_bull_hom; rewrite /=; try by done.
                                                                   all: by rewrite sg_sym.
               --- case: (boolP (a2 -- c2)) => [a2_adj_c2 | a2_nadj_c2]; last first.
                   +++ case: (boolP (b2 -- c2)) => [b2_adj_c2 | b2_nadj_c2].
                       *** have b2_neq_c2: b2 != c2 by rewrite sg_edgeNeq.
                           left; exists (hom_G4_def b2 a1 b1 c2).
                           ---- apply: h'_G4_inj; rewrite /=; try by done.
                                all: try by rewrite eq_sym.
                                all: by move: a1_adj_a2; apply/contraTneq => ->; rewrite sg_sym.
                           ---- apply: h'_claw_hom; rewrite /=; try by done.
                                all: by rewrite sg_sym.
                       *** case: (boolP (b1 -- c1)) => [b1_adj_c1 | b1_nadj_c1].
                           ---- have b1_neq_c1: b1 != c1 by rewrite sg_edgeNeq.
                                left; exists (hom_G4_def c1 a2 b1 c2).
                                ++++ apply: h'_G4_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     all: by move: a1_adj_a2; apply/contraTneq => ->.
                                ++++ apply: h'_claw_hom; rewrite /=; try by done.
                                     all: by rewrite sg_sym.
                           ---- case: (boolP (a2 -- b2)) => [a2_adj_b2 | a2_nadj_b2]; last first.
                                ++++ case: (boolP (a1 -- c1)) => [a1_adj_c1 | a1_nadj_c1].
                                     **** have a1_neq_c1: a1 != c1 by rewrite sg_edgeNeq.
                                          right; left; exists (hom_G5_def b2 c2 a1 c1 a2).
                                          ----- apply: h'_G5_inj; rewrite /=; try by done.
                                                all: try by rewrite eq_sym.
                                                +++++ by move: b1_adj_b2; apply/contraTneq => ->.
                                                +++++ by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                +++++ by move: a1_adj_a2; apply/contraTneq => <-; rewrite sg_sym.
                                                +++++ by move: a1_adj_a2; apply/contraTneq => <-.
                                          ----- apply: h'_bull_hom; rewrite /=; try by done.
                                                all: try by rewrite sg_sym.
                                     **** right; right; left; exists (hom_G6_def b1 b2 a1 a2 c1 c2).
                                          ----- apply: h'_G6_inj; rewrite /=; try by done.
                                                all: try by rewrite eq_sym.
                                                +++++ by move: a1_adj_a2; apply/contraTneq => <-; rewrite sg_sym.
                                                +++++ by move: a2_adj_c1; apply/contraTneq => <-.
                                                +++++ by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                +++++ by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                +++++ by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                                                +++++ by move: a1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                +++++ by move: a1_adj_a2; apply/contraTneq => ->; rewrite sg_sym.
                                                +++++ by move: a1_adj_a2; apply/contraTneq => ->.
                                          ----- apply: h'_P_6_hom; rewrite /=; try by done.
                                                all: by rewrite sg_sym.
                                ++++ have a2_neq_b2: a2 != b2 by rewrite sg_edgeNeq.
                                     case: (boolP (a1 -- c1)) => [a1_adj_c1 | a1_nadj_c1]; last first.
                                     **** right; left; exists (hom_G5_def b1 c1 b2 a2 a1).
                                          ----- apply: h'_G5_inj; rewrite /=; try by done.
                                                all: try by rewrite eq_sym.
                                                +++++ by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                                +++++ by move: a1_adj_a2; apply/contraTneq => <-.
                                                +++++ by move: a1_adj_a2; apply/contraTneq => <-; rewrite sg_sym.
                                                +++++ by move: a1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
                                          ----- apply: h'_bull_hom; rewrite /=; try by done.
                                                all: by rewrite sg_sym.
                                     **** have a1_neq_c1: a1 != c1 by rewrite sg_edgeNeq.
                                          have a2_neq_d1: a2 != d1 by move: a2_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                          have a1_neq_d2: a1 != d2 by move: a1_adj_c1; apply/contraTneq => ->; rewrite sg_sym.
                                          by rewrite (negbTE a1_neq_d2) (negbTE a2_neq_d1) (negbTE a1_nadj_d2) (negbTE a2_nadj_d1) in a1d2a2d1.
                   +++ have a2_neq_c2: a2 != c2 by rewrite sg_edgeNeq.
                       have a2_neq_d1: a2 != d1 by move: a2_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                       have a1_neq_d2: a1 != d2 by move: a1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                       by rewrite (negbTE a1_neq_d2) (negbTE a2_neq_d1) (negbTE a1_nadj_d2) (negbTE a2_nadj_d1) in a1d2a2d1.
            ** have a1_neq_b1: a1 != b1 by rewrite sg_edgeNeq.
               have a1_neq_d2: a1 != d2 by move: a1_adj_b1; apply/contraTneq => ->; rewrite sg_sym.
               have a2_eq_d1: a2 = d1 by apply/eqP; rewrite (negbTE a1_neq_d2) (negbTE a1_nadj_d2) (negbTE a2_nadj_d1) orbC /= in a1d2a2d1.
               case: (boolP (a1 -- c1)) => [a1_adj_c1 | a1_nadj_c1]; last first.
               --- left; exists (hom_G4_def a2 a1 c1 d2).
                   +++ apply: h'_G4_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       *** by rewrite a2_eq_d1.
                       *** by move: a1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                   +++ apply: h'_claw_hom; rewrite /=; try by done.
                       all: try by rewrite sg_sym.
                       by rewrite a2_eq_d1.
               --- have a1_neq_c1: a1 != c1 by rewrite sg_edgeNeq.
                   case: (boolP (b2 -- d2)) => [b2_adj_d2 | b2_nadj_d2]; last first.
                   +++ right; left; exists (hom_G5_def b2 d2 a1 a2 c1).
                       *** apply: h'_G5_inj; rewrite /=; try by done.
                           all: try by rewrite eq_sym.
                           ---- by move: b1_adj_b2; apply/contraTneq => ->.
                           ---- by move: a2_adj_c1; apply/contraTneq => <-.
                           ---- by rewrite a2_eq_d1 eq_sym.
                       *** apply: h'_bull_hom; rewrite /=; try by done.
                           all: try by rewrite sg_sym.
                           ---- by rewrite a2_eq_d1 sg_sym.
                           ---- by rewrite a2_eq_d1.
                   +++ have b2_neq_d2: b2 != d2 by rewrite sg_edgeNeq.
                       case: (boolP (b2 -- c2)) => [b2_adj_c2 | b2_nadj_c2]; last first.
                       *** right; left; exists (hom_G5_def b2 c2 a1 c1 a2).
                           ---- apply: h'_G5_inj; rewrite /=; try by done.
                                all: try by rewrite eq_sym.
                                ++++ by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                                ++++ by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                                ++++ by move: a1_adj_b1; apply/contraTneq => <-; rewrite sg_sym.
                                ++++ by rewrite a2_eq_d1.
                           ---- apply: h'_bull_hom; rewrite /=; try by done.
                                all: try by rewrite sg_sym.
                                all: by rewrite a2_eq_d1.
                       *** have b2_neq_c2: b2 != c2 by rewrite sg_edgeNeq.
                           case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2]; last first.
                           ---- right; left; exists (hom_G5_def c2 d2 c1 a2 a1).
                                ++++ apply: h'_G5_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     **** by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
                                     **** by rewrite a2_eq_d1.
                                     **** by move: a1_adj_b1; apply/contraTneq => <-; rewrite sg_sym.
                                     **** by rewrite a2_eq_d1 eq_sym.
                                ++++ apply: h'_bull_hom; rewrite /=; try by done.
                                     all: try by rewrite sg_sym.
                                     **** by rewrite a2_eq_d1 sg_sym.
                                     **** by rewrite a2_eq_d1.
                           ---- have c2_neq_d2: c2 != d2 by rewrite sg_edgeNeq.
                                right; right; right; exists (hom_G6_def a1 c2 a2 b2 c1 d2).
                                ++++ apply: h'_G6_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     all: try by rewrite a2_eq_d1.
                                     **** by move: a1_adj_b1; apply/contraTneq => ->; rewrite sg_sym.
                                     **** by rewrite a2_eq_d1 eq_sym.
                                ++++ apply: h'_CC_6_hom; rewrite /=; try by done.
                                     all: try by rewrite sg_sym.
                                     all: try by rewrite a2_eq_d1.
                                     by rewrite a2_eq_d1 sg_sym.
  + case: (boolP (a1 -- c2)) => [a1_adj_c2 | a1_nadj_c2].
    * have a1_neq_c2: a1 != c2 by rewrite sg_edgeNeq.
      apply: (@subcase1_a1a2_b1b2_c1c2_d1d22_with_a1_adj_b2 h a1 a2 b1 b2 d1 d2 c1 c2); try by done.
      all: try by rewrite eq_sym.
      all: by rewrite sg_sym.
    * case: (boolP (a2 -- d1)) => [a2_adj_d1 | a2_nadj_d1].
      -- have a2_neq_d1: a2 != d1 by rewrite sg_edgeNeq.
         case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1].
         ++ apply: (@subcase1_a1a2_b1b2_c1c2_d1d22_with_a1_adj_b2 h a2 a1 d2 d1 c2 c1 b2 b1); try by done.
            all: try by rewrite eq_sym.
            all: try by rewrite sg_sym.
            all: by rewrite orbC orbA orbC orbA orbA.
         ++ rewrite (negbTE a2_nadj_c1) (negbTE a1_nadj_c2) orbC /= -orbA orbC /= in a1c2a2c1.
            case: (orP a1c2a2c1) => [/eqP a2_eq_c1 | /eqP a1_eq_c2].
            ** by apply: (@subcase2_a1a2_b1b2_c1c2_d1d22_with_a1_adj_b2 h a1 a2 b1 b2 c1 c2 d1 d2).
            ** apply: (@subcase2_a1a2_b1b2_c1c2_d1d22_with_a1_adj_b2 h a2 a1 d2 d1 c2 c1 b2 b1); try by done.
               all: try by rewrite eq_sym.
               all: by rewrite sg_sym.
      -- rewrite (negbTE a2_nadj_c1) (negbTE a1_nadj_c2) orbC /= -orbA orbC /= in a1c2a2c1.
         case: (orP a1c2a2c1) => [/eqP a2_eq_c1 | /eqP a1_eq_c2].
         ++ case: (boolP (a1 -- d1)) => [a1_adj_d1 | a1_nadj_d1].
            ** have a1_neq_d1: a1 != d1 by rewrite sg_edgeNeq.
               left; exists (hom_G4_def a1 b2 c1 d1).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   +++ by rewrite -a2_eq_c1.
                   +++ by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
               --- apply: h'_claw_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   all: by rewrite -a2_eq_c1.
            ** case: (boolP (a1 == c2)) => [/eqP a1_eq_c2 | a1_neq_c2].
               --- case: (boolP (b1 -- d1)) => [b1_adj_d1 | b1_nadj_d1].
                   +++ have b1_neq_d1: b1 != d1 by rewrite sg_edgeNeq.
                       case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1].
                       *** have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
                           left; exists (hom_G4_def b1 a2 b2 d1).
                           ---- apply: h'_G4_inj; rewrite /=; try by done.
                                all: try by rewrite eq_sym.
                                ++++ by rewrite a2_eq_c1 eq_sym.
                                ++++ by move: a1_adj_a2; apply/contraTneq => ->.
                           ---- apply: h'_claw_hom; rewrite /=; try by done.
                                all: try by rewrite sg_sym.
                                by rewrite a2_eq_c1 sg_sym.
                       *** case: (boolP (b2 -- d2)) => [b2_adj_d2 | b2_nadj_d2].
                           ---- have b2_neq_d2: b2 != d2 by rewrite sg_edgeNeq.
                                left; exists (hom_G4_def b2 a1 b1 d2).
                                ++++ apply: h'_G4_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     **** by rewrite a1_eq_c2 eq_sym.
                                     **** by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
                                ++++ apply: h'_claw_hom; rewrite /=; try by done.
                                     all: try by rewrite sg_sym.
                                     by rewrite a1_eq_c2 sg_sym.
                           ---- right; right; left; exists (hom_G6_def a2 a1 b2 b1 d1 d2).
                                ++++ apply: h'_G6_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     **** by rewrite a2_eq_c1 eq_sym.
                                     **** by move: a1_adj_a2; apply/contraTneq => ->; rewrite sg_sym a1_eq_c2.
                                     **** by move: a1_adj_a2; apply/contraTneq => ->.
                                     **** by rewrite a2_eq_c1.
                                     **** by rewrite a1_eq_c2 eq_sym.
                                     **** by rewrite a1_eq_c2.
                                     **** by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
                                     **** by move: b1_adj_b2; apply/contraTneq => ->.
                                ++++ apply: h'_P_6_hom; rewrite /=; try by done.
                                     all: try by rewrite sg_sym.
                                     **** by rewrite a2_eq_c1 sg_sym.
                                     **** by rewrite a2_eq_c1.
                                     **** by rewrite a1_eq_c2 sg_sym.
                   +++ have a1_neq_d2: a1 != d2 by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
                       have a2_neq_d1: a2 != d1 by move: a1_adj_a2; apply/contraTneq => ->.
                       by rewrite (negbTE a2_nadj_d1) (negbTE a1_nadj_d2)  (negbTE a2_neq_d1) (negbTE a1_neq_d2) in a1d2a2d1.
               --- have a1_neq_d2: a1 != d2 by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
                   have a2_neq_d1: a2 != d1 by move: a1_adj_a2; apply/contraTneq => ->.
                   by rewrite (negbTE a2_nadj_d1) (negbTE a1_nadj_d2)  (negbTE a2_neq_d1) (negbTE a1_neq_d2) in a1d2a2d1.
         ++ have a1_neq_d2: a1 != d2 by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_sym a1_eq_c2.
            have a2_neq_d1: a2 != d1 by move: a1_adj_a2; apply/contraTneq => ->; rewrite a1_eq_c2.
            by rewrite (negbTE a2_nadj_d1) (negbTE a1_nadj_d2) (negbTE a2_neq_d1) (negbTE a1_neq_d2) in a1d2a2d1.
Qed.

Lemma case_a1a2_b1b2_c1c2_d1d2_with_a1_eq_b2 (h : claw -> trfgraph G) (a1 a2 b1 b2 c1 c2 d1 d2 : G) :
  (a1 == c2) || a1 -- c2 || (a2 == c1) || a2 -- c1 ->
  (a1 == d2) || a1 -- d2 || (a2 == d1) || a2 -- d1 ->
  b1 != c2 ->
  ~~ b1 -- c2 ->
  b2 != c1 ->
  ~~ b2 -- c1 ->
  b1 != d2 ->
  ~~ b1 -- d2 ->
  b2 != d1 ->
  ~~ b2 -- d1 ->
  c1 != d2 ->
  ~~ c1 -- d2 ->
  c2 != d1 ->
  ~~ c2 -- d1 ->
  a1 -- a2 ->
  b1 -- b2 ->
  c1 -- c2 ->
  d1 -- d2 ->
  a1 = b2 ->
    ((exists2 h0 : claw -> G, injective h0 & induced_hom h0) \/
    (exists2 h0 : bull -> G, injective h0 & induced_hom h0) \/
    (exists2 h0 : 'P_6 -> G, injective h0 & induced_hom h0) \/
    (exists2 h0 : 'CC_6 -> G, injective h0 & induced_hom h0)).
Proof.
move => a1c2a2c1 a1d2a2d1 ? ? ? ? ? ? ? ? ? ? ? ? a1_adj_a2 b1_adj_b2 c1_adj_c2 d1_adj_d2 a1_eq_b2.
have a1_neq_a2: a1 != a2 by rewrite sg_edgeNeq.
have b1_neq_b2: b1 != b2 by rewrite sg_edgeNeq.
have c1_neq_c2: c1 != c2 by rewrite sg_edgeNeq.
have d1_neq_d2: d1 != d2 by rewrite sg_edgeNeq.
case: (boolP (a1 -- d2)) => [a1_adj_d2 | a1_nadj_d2].
- have a1_neq_d2: a1 != d2 by rewrite sg_edgeNeq.
  case: (boolP (a1 -- c2)) => [a1_adj_c2 | a1_nadj_c2].
  + have a1_neq_c2: a1 != c2 by rewrite sg_edgeNeq.
    case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2]; last first.
    * left; exists (hom_G4_def a1 b1 c2 d2).
      -- apply: h'_G4_inj; rewrite /=; try by done.
         all: try by rewrite eq_sym.
         ++ by move: a1_adj_d2; apply/contraTneq => ->.
         ++ by move: c1_adj_c2; apply/contraTneq => ->.
      -- apply: h'_claw_hom; rewrite /=; try by done.
         all: try by rewrite sg_sym.
         by rewrite a1_eq_b2 sg_sym.
    * have c2_neq_d2: c2 != d2 by rewrite sg_edgeNeq.
      case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
      -- right; left; exists (hom_G5_def c1 d1 c2 d2 a1).
         ++ apply: h'_G5_inj; rewrite /=; try by done.
            all: try by rewrite eq_sym.
            ** by move: d1_adj_d2; apply/contraTneq => <-.
            ** by move: a1_adj_d2; apply/contraTneq => <-.
            ** by move: a1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
         ++ apply: h'_bull_hom; rewrite /=; try by done.
            all: try by rewrite sg_sym.
            all: by rewrite a1_eq_b2 sg_sym.
      -- have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
         case: (boolP (b1 -- d1)) => [b1_adj_d1 | b1_nadj_d1]; last first.
         ++ right; left; exists (hom_G5_def b1 d1 a1 d2 c2).
            ** apply: h'_G5_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               --- by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
               --- by rewrite a1_eq_b2.
               --- by move: c1_adj_d1; apply/contraTneq => ->; rewrite a1_eq_b2 sg_sym.
            ** apply: h'_bull_hom; rewrite /=; try by done.
               all: try by rewrite sg_sym.
               --- by rewrite a1_eq_b2.
               --- by rewrite a1_eq_b2 sg_sym.
         ++ have b1_neq_d1: b1 != d1 by rewrite sg_edgeNeq.
            case: (boolP (b1 -- c1)) => [b1_adj_c1 | b1_nadj_c1]; last first.
            ** left; exists (hom_G4_def d1 b1 c1 d2).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
               --- apply: h'_claw_hom; rewrite /=; try by done.
                   all: by rewrite sg_sym.
            ** have b1_neq_c1: b1 != c1 by rewrite sg_edgeNeq.
               right; right; right; exists (hom_G6_def a1 c1 d2 b1 c2 d1).
               --- apply: h'_G6_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   +++ by rewrite a1_eq_b2.
                   +++ by rewrite a1_eq_b2 eq_sym.
                   +++ by rewrite a1_eq_b2.
               --- apply: h'_CC_6_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   +++ by rewrite a1_eq_b2 sg_sym.
                   +++ by rewrite a1_eq_b2.
                   +++ by rewrite a1_eq_b2.
  + have a1_neq_c2: a1 != c2 by move: c1_adj_c2; apply/contraTneq => <-; rewrite a1_eq_b2 sg_sym.
    have a2_neq_c1: a2 != c1 by move: a1_adj_a2; apply/contraTneq => ->; rewrite a1_eq_b2.
    have a2_adj_c1: a2 -- c1 by rewrite (negbTE a1_neq_c2) (negbTE a2_neq_c1) (negbTE a1_nadj_c2) in a1c2a2c1.
    case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2].
    * have c2_neq_d2: c2 != d2 by rewrite sg_edgeNeq.
      left; exists (hom_G4_def d2 a1 c2 d1).
      -- apply: h'_G4_inj; rewrite /=; try by done.
         all: try by rewrite eq_sym.
         by rewrite a1_eq_b2.
      -- apply: h'_claw_hom; rewrite /=; try by done.
         all: try by rewrite sg_sym.
         by rewrite a1_eq_b2.
    * case: (boolP (a2 -- c2)) => [a2_adj_c2 | a2_nadj_c2].
      -- have a2_neq_c2: a2 != c2 by rewrite sg_edgeNeq.
         case: (boolP (a2 -- d1)) => [a2_adj_d1 | a2_nadj_d1].
         ++ have a2_neq_d1: a2 != d1 by rewrite sg_edgeNeq.
            left; exists (hom_G4_def a2 a1 c2 d1).
            ** apply: h'_G4_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               by rewrite a1_eq_b2.
            ** apply: h'_claw_hom; rewrite /=; try by done.
               all: try by rewrite sg_sym.
               by rewrite a1_eq_b2.
         ++ case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1].
            ** have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
               right; left; exists (hom_G5_def a1 d1 a2 c1 c2).
               --- apply: h'_G5_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   all: try by rewrite a1_eq_b2.
                   by move: a1_adj_a2; apply/contraTneq => <-; rewrite a1_eq_b2.
               --- apply: h'_bull_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   all: by rewrite a1_eq_b2.
            ** case: (boolP (a2 -- d2)) => [a2_adj_d2 | a2_nadj_d2].
               --- have a2_neq_d2: a2 != d2 by rewrite sg_edgeNeq.
                   right; left; exists (hom_G5_def c1 d1 a2 d2 a1).
                   +++ apply: h'_G5_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       all: try by rewrite a1_eq_b2 eq_sym.
                       *** by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                       *** by move: a1_adj_a2; apply/contraTneq => <-; rewrite a1_eq_b2.
                   +++ apply: h'_bull_hom; rewrite /=; try by done.
                       all: try by rewrite sg_sym.
                       all: by rewrite a1_eq_b2 sg_sym.
               --- case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1]; last first.
                   +++ left; exists (hom_G4_def a1 a2 b1 d2).
                       *** apply: h'_G4_inj; rewrite /=; try by done.
                           all: try by rewrite eq_sym.
                           ---- by rewrite a1_eq_b2 eq_sym.
                           ---- by move: a2_adj_c2; apply/contraTneq => ->.
                           ---- by move: a2_adj_c1; apply/contraTneq => ->; rewrite sg_sym.
                       *** apply: h'_claw_hom; rewrite /=; try by done.
                           all: try by rewrite sg_sym.
                           by rewrite a1_eq_b2 sg_sym.
                   +++ have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
                       right; left; exists (hom_G5_def c2 d2 a2 a1 b1).
                       *** apply: h'_G5_inj; rewrite /=; try by done.
                           all: try by rewrite eq_sym.
                           ---- by move: c1_adj_c2; apply/contraTneq => ->.
                           ---- by move: a2_adj_c1; apply/contraTneq => <-; rewrite sg_sym.
                           ---- by rewrite a1_eq_b2 eq_sym.
                       *** apply: h'_bull_hom; rewrite /=; try by done.
                           all: try by rewrite sg_sym.
                           by rewrite a1_eq_b2 sg_sym.
      -- case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
         ++ case: (boolP (a2 -- d1)) => [a2_adj_d1 | a2_nadj_d1].
            ** have a2_neq_d1: a2 != d1 by rewrite sg_edgeNeq.
               left; exists (hom_G4_def a2 a1 c1 d1).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   all: try by rewrite a1_eq_b2.
                   by move: d1_adj_d2; apply/contraTneq => <-.
               --- apply: h'_claw_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   all: by rewrite a1_eq_b2.
            ** case: (boolP (a2 -- d2)) => [a2_adj_d2 | a2_nadj_d2].
               --- have a2_neq_d2: a2 != d2 by rewrite sg_edgeNeq.
                   right; left; exists (hom_G5_def c1 d1 a2 d2 a1).
                   +++ apply: h'_G5_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       all: try by rewrite a1_eq_b2 eq_sym.
                       *** by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                       *** by move: a1_adj_a2; apply/contraTneq => <-; rewrite a1_eq_b2.
                   +++ apply: h'_bull_hom; rewrite /=; try by done.
                       all: try by rewrite sg_sym.
                       all: by rewrite a1_eq_b2 sg_sym.
               --- right; right; left; exists (hom_G6_def c2 c1 a2 a1 d2 d1).
                   +++ apply: h'_G6_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       *** by move: a1_adj_a2; apply/contraTneq => <-.
                       *** by move: c1_adj_c2; apply/contraTneq => ->.
                       *** by rewrite a1_eq_b2 eq_sym.
                       *** by move: d1_adj_d2; apply/contraTneq => <-.
                       *** by move: d1_adj_d2; apply/contraTneq => <-; rewrite sg_sym.
                       *** by move: a1_adj_a2; apply/contraTneq => ->; rewrite a1_eq_b2.
                       *** by rewrite a1_eq_b2.
                   +++ apply: h'_P_6_hom; rewrite /=; try by done.
                       all: try by rewrite sg_sym.
                       *** by rewrite a1_eq_b2 sg_sym.
                       *** by rewrite a1_eq_b2.
         ++ have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
            case: (boolP (a2 -- d1)) => [a2_adj_d1 | a2_nadj_d1]; last first.
            ** left; exists (hom_G4_def c1 a2 c2 d1).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   +++ by move: a1_adj_a2; apply/contraTneq => ->.
                   +++ by move: a1_adj_a2; apply/contraTneq => ->; rewrite a1_eq_b2.
               --- apply: h'_claw_hom; rewrite /=; try by done.
                   all: by rewrite sg_sym.
            ** have a2_neq_d1: a2 != d1 by rewrite sg_edgeNeq.
               right; left; exists (hom_G5_def c2 a1 c1 a2 d1).
               --- apply: h'_G5_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   all: try by rewrite a1_eq_b2.
                   by move: a1_adj_a2; apply/contraTneq => <-.
               --- apply: h'_bull_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   all: by rewrite a1_eq_b2.
- have a2_neq_d1: a2 != d1 by move: a1_adj_a2; apply/contraTneq => ->; rewrite a1_eq_b2.
  have a1_neq_d2: a1 != d2 by rewrite a1_eq_b2; move: b1_adj_b2; apply/contraTneq => ->.
  have a2_adj_d1: a2 -- d1 by rewrite (negbTE a1_nadj_d2) (negbTE a2_neq_d1) (negbTE a1_neq_d2) in a1d2a2d1.
  case: (boolP (b1 -- c1)) => [b1_adj_c1 | b1_nadj_c1].
  + have b1_neq_c1: b1 != c1 by rewrite sg_edgeNeq.
    case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1].
    * have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
      case: (boolP (b1 -- d1)) => [b1_adj_d1 | b1_nadj_d1]; last first.
      -- left; exists (hom_G4_def c1 b1 c2 d1).
         ++ apply: h'_G4_inj; rewrite /=; try by done.
            all: try by rewrite eq_sym.
            by move: d1_adj_d2; apply/contraTneq => <-.
         ++ apply: h'_claw_hom; rewrite /=; try by done.
            all: by rewrite sg_sym.
      -- have b1_neq_d1: b1 != d1 by rewrite sg_edgeNeq.
         right; left; exists (hom_G5_def a1 d2 b1 d1 c1).
         ++ apply: h'_G5_inj; rewrite /=; try by done.
            all: try by rewrite eq_sym.
            all: try by rewrite a1_eq_b2.
            by rewrite a1_eq_b2 eq_sym.
         ++ apply: h'_bull_hom; rewrite /=; try by done.
            all: try by rewrite sg_sym.
            all: try by rewrite a1_eq_b2.
            by rewrite a1_eq_b2 sg_sym.
    * case: (boolP (b1 -- d1)) => [b1_adj_d1 | b1_nadj_d1].
      -- have b1_neq_d1: b1 != d1 by rewrite sg_edgeNeq.
         left; exists (hom_G4_def b1 b2 c1 d1).
         ++ apply: h'_G4_inj; rewrite /=; try by done.
            all: try by rewrite eq_sym.
            by move: d1_adj_d2; apply/contraTneq => <-.
         ++ apply: h'_claw_hom; rewrite /=; try by done.
            all: by rewrite sg_sym.
      -- case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2].
         ++ have c2_neq_d2: c2 != d2 by rewrite sg_edgeNeq.
            case: (boolP (b2 -- c2)) => [b2_adj_c2 | b2_nadj_c2].
            ** have b2_neq_c2: b2 != c2 by rewrite sg_edgeNeq.
               left; exists (hom_G4_def c2 b2 c1 d2).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   by move: b1_adj_b2; apply/contraTneq => ->.
               --- apply: h'_claw_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   by rewrite -a1_eq_b2.
            ** right; right; left; exists (hom_G6_def b2 b1 c1 c2 d2 d1).
               --- apply: h'_G6_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   all: try by move: b1_adj_b2; apply/contraTneq => ->.
                   +++ by move: b1_adj_b2; apply/contraTneq => ->; rewrite sg_sym.
                   +++ by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
               --- apply: h'_P_6_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   by rewrite -a1_eq_b2.
         ++ case: (boolP (a2 -- c1)) => [a2_adj_c1 | a2_nadj_c1].
            ** have a2_neq_c1: a2 != c1 by rewrite sg_edgeNeq.
               left; exists (hom_G4_def a2 a1 c1 d1).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   all: try by rewrite a1_eq_b2.
                   by move: d1_adj_d2; apply/contraTneq => <-.
               --- apply: h'_claw_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   all: by rewrite a1_eq_b2.
            ** have a2_neq_c1: a2 != c1 by move: a1_adj_a2; apply/contraTneq => ->; rewrite a1_eq_b2.
               have a1_neq_c2: a1 != c2 by rewrite a1_eq_b2; move: b1_adj_b2; apply/contraTneq => ->.
               have a1_adj_c2: a1 -- c2 by rewrite (negbTE a2_nadj_c1) (negbTE a2_neq_c1) (negbTE a1_neq_c2) /= orbC /= orbC /= in a1c2a2c1.
               case: (boolP (a2 -- c2)) => [a2_adj_c2 | a2_nadj_c2].
               --- have a2_neq_c2: a2 != c2 by rewrite sg_edgeNeq.
                   right; left; exists (hom_G5_def c1 d1 c2 a2 a1).
                   +++ apply: h'_G5_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       *** by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                       *** by move: a1_adj_a2; apply/contraTneq => <-; rewrite sg_sym.
                       *** by move: d1_adj_d2; apply/contraTneq => ->.
                   +++ apply: h'_bull_hom; rewrite /=; try by done.
                       all: try by rewrite sg_sym.
                       all: by rewrite a1_eq_b2 sg_sym.
               --- case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1]; last first.
                   +++ left; exists (hom_G4_def a1 a2 b1 c2).
                       *** apply: h'_G4_inj; rewrite /=; try by done.
                           all: try by rewrite eq_sym.
                           ---- by rewrite a1_eq_b2 eq_sym.
                           ---- by move: a2_adj_d1; apply/contraTneq => ->.
                           ---- by move: a2_adj_d1; apply/contraTneq => ->.
                       *** apply: h'_claw_hom; rewrite /=; try by done.
                           all: try by rewrite sg_sym.
                           by rewrite a1_eq_b2 sg_sym.
                   +++ have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
                       right; left; exists (hom_G5_def c1 d1 b1 a2 b2).
                       *** apply: h'_G5_inj; rewrite /=; try by done.
                           all: try by rewrite eq_sym.
                           ---- by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                           ---- by move: b1_adj_b2; apply/contraTneq => <-; rewrite sg_sym.
                           ----  by rewrite -a1_eq_b2 eq_sym.
                       *** apply: h'_bull_hom; rewrite /=; try by done.
                           all: try by rewrite sg_sym.
                           by rewrite -a1_eq_b2 sg_sym.
  + case: (boolP (a1 -- c2)) => [a1_adj_c2 | a1_nadj_c2]; last first.
    * have a2_neq_c1: a2 != c1 by move: a1_adj_a2; apply/contraTneq => ->; rewrite a1_eq_b2.
      have a1_neq_c2: a1 != c2 by rewrite a1_eq_b2; move: b1_adj_b2; apply/contraTneq => ->.
      have a2_adj_c1: a2 -- c1 by rewrite (negbTE a1_nadj_c2) (negbTE a2_neq_c1) (negbTE a1_neq_c2) in a1c2a2c1.
      case: (boolP (a2 -- c2)) => [a2_adj_c2 | a2_nadj_c2].
      -- have a2_neq_c2: a2 != c2 by rewrite sg_edgeNeq.
         left; exists (hom_G4_def a2 a1 c2 d1).
         ++ apply: h'_G4_inj; rewrite /=; try by done.
            all: try by rewrite eq_sym.
            by rewrite a1_eq_b2.
         ++ apply: h'_claw_hom; rewrite /=; try by done.
            all: try by rewrite sg_sym.
            by rewrite a1_eq_b2.
      -- case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1].
         ++ have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
            case: (boolP (a1 -- c1)) => [a1_adj_c1 | a1_nadj_c1].
            ** have a1_neq_c1: a1 != c1 by rewrite sg_edgeNeq.
               left; exists (hom_G4_def c1 a1 c2 d1).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   by rewrite a1_eq_b2.
               --- apply: h'_claw_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   by rewrite a1_eq_b2.
            ** right; left; exists (hom_G5_def a1 c2 a2 c1 d1).
               --- apply: h'_G5_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   all: try by rewrite a1_eq_b2.
                   by move: a2_adj_d1; apply/contraTneq => <-.
               --- apply: h'_bull_hom; rewrite /=; try by done.
                   all: try by rewrite sg_sym.
                   by rewrite a1_eq_b2.
         ++ left; exists (hom_G4_def a2 a1 c1 d1).
            ** apply: h'_G4_inj; rewrite /=; try by done.
               all: try by rewrite eq_sym.
               all: try by rewrite a1_eq_b2.
               by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
            ** apply: h'_claw_hom; rewrite /=; try by done.
               all: try by rewrite sg_sym.
               all: by rewrite a1_eq_b2.
    * have a1_neq_c2: a1 != c2 by rewrite sg_edgeNeq.
      case: (boolP (c2 -- d2)) => [c2_adj_d2 | c2_nadj_d2].
      -- have c2_neq_d2: c2 != d2 by rewrite sg_edgeNeq.
         left; exists (hom_G4_def c2 c1 a1 d2).
         ++ apply: h'_G4_inj; rewrite /=; try by done.
            all: try by rewrite eq_sym.
            by rewrite a1_eq_b2 eq_sym.
         ++ apply: h'_claw_hom; rewrite /=; try by done.
            all: try by rewrite sg_sym.
            by rewrite a1_eq_b2 sg_sym.
      -- case: (boolP (b1 -- d1)) => [d1_adj_d1 | b1_nadj_d1].
         ++ have b1_neq_d1: b1 != d1 by rewrite sg_edgeNeq.
            case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1].
            ** have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
               left; exists (hom_G4_def d1 b1 c1 d2).
               --- apply: h'_G4_inj; rewrite /=; try by done.
                   all: try by rewrite eq_sym.
                   by move: c1_adj_c2; apply/contraTneq => <-.
               --- apply: h'_claw_hom; rewrite /=; try by done.
                   all: by rewrite sg_sym.
            ** case: (boolP (a2 -- c1)) => [a2_adj_c1 | a2_nadj_c1].
               --- have a2_neq_c1: a2 != c1 by rewrite sg_edgeNeq.
                   left; exists (hom_G4_def a2 a1 c1 d1).
                   +++ apply: h'_G4_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       all: try by rewrite a1_eq_b2.
                       by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                   +++ apply: h'_claw_hom; rewrite /=; try by done.
                       all: try by rewrite sg_sym.
                       all: by rewrite a1_eq_b2.
               --- case: (boolP (a2 -- c2)) => [a2_adj_c2 | a2_nadj_c2].
                   +++ have a2_neq_c2: a2 != c2 by rewrite sg_edgeNeq.
                       right; left; exists (hom_G5_def c1 d1 c2 a2 a1).
                       *** apply: h'_G5_inj; rewrite /=; try by done.
                           all: try by rewrite eq_sym.
                           all: try by rewrite a1_eq_b2 eq_sym.
                           ---- by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                           ---- by move: a2_adj_d1; apply/contraTneq => <-.
                       *** apply: h'_bull_hom; rewrite /=; try by done.
                           all: try by rewrite sg_sym.
                           all: by rewrite a1_eq_b2 sg_sym.
                   +++ case: (boolP (a2 -- d2)) => [a2_adj_d2 | a2_nadj_d2]; last first.
                       *** right; right; left; exists (hom_G6_def c1 c2 a1 a2 d1 d2).
                           ---- apply: h'_G6_inj; rewrite /=; try by done.
                                all: try by rewrite eq_sym.
                                all: try by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                all: try by move: c1_adj_c2; apply/contraTneq => ->.
                                ++++ by rewrite a1_eq_b2 eq_sym.
                                ++++ by rewrite a1_eq_b2.
                                ++++ by move: a1_adj_a2; apply/contraTneq => ->.
                           ---- apply: h'_P_6_hom; rewrite /=; try by done.
                                all: try by rewrite sg_sym.
                                ++++ by rewrite a1_eq_b2 sg_sym.
                                ++++ by rewrite a1_eq_b2.
                       *** have a2_neq_d2: a2 != d2 by rewrite sg_edgeNeq.
                           case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1].
                           ---- have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
                                right; left; exists (hom_G5_def c2 d2 a1 a2 b1).
                                ++++ apply: h'_G5_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     **** by move: c1_adj_c2; apply/contraTneq => ->.
                                     **** by move: a2_adj_d1; apply/contraTneq => <-.
                                     **** by rewrite a1_eq_b2 eq_sym.
                                ++++ apply: h'_bull_hom; rewrite /=; try by done.
                                     all: try by rewrite sg_sym.
                                     by rewrite a1_eq_b2 sg_sym.
                           ---- left; exists (hom_G4_def a1 a2 b1 c2).
                                ++++ apply: h'_G4_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     **** by rewrite a1_eq_b2 eq_sym.
                                     **** by move: a2_adj_d2; apply/contraTneq => ->.
                                     **** by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                                ++++ apply: h'_claw_hom; rewrite /=; try by done.
                                     all: try by rewrite sg_sym.
                                     by rewrite a1_eq_b2 sg_sym.
         ++ case: (boolP (c1 -- d1)) => [c1_adj_d1 | c1_nadj_d1]; last first.
            ** case: (boolP (a2 -- c1)) => [a2_adj_c1 | a2_nadj_c1].
               --- have a2_neq_c1: a2 != c1 by rewrite sg_edgeNeq.
                   left; exists (hom_G4_def a2 a1 c1 d1).
                   +++ apply: h'_G4_inj; rewrite /=; try by done.
                       all: try by rewrite eq_sym.
                       all: try by rewrite a1_eq_b2.
                       by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                   +++ apply: h'_claw_hom; rewrite /=; try by done.
                       all: try by rewrite sg_sym.
                       all: try by rewrite a1_eq_b2.
               --- case: (boolP (a2 -- c2)) => [a2_adj_c2 | a2_nadj_c2].
                   +++ have a2_neq_c2: a2 != c2 by rewrite sg_edgeNeq.
                       right; left; exists (hom_G5_def c1 d1 c2 a2 a1).
                       *** apply: h'_G5_inj; rewrite /=; try by done.
                           all: try by rewrite eq_sym.
                           all: try by rewrite a1_eq_b2 eq_sym.
                           ---- by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                           ---- by move: a2_adj_d1; apply/contraTneq => <-.
                       *** apply: h'_bull_hom; rewrite /=; try by done.
                           all: try by rewrite sg_sym.
                           all: by rewrite a1_eq_b2 sg_sym.
                   +++ case: (boolP (a2 -- d2)) => [a2_adj_d2 | a2_nadj_d2]; last first.
                       *** right; right; left; exists (hom_G6_def c1 c2 a1 a2 d1 d2).
                           ---- apply: h'_G6_inj; rewrite /=; try by done.
                                all: try by rewrite eq_sym.
                                all: try by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                all: try by move: c1_adj_c2; apply/contraTneq => ->.
                                ++++ by rewrite a1_eq_b2 eq_sym.
                                ++++ by rewrite a1_eq_b2.
                                ++++ by move: a1_adj_a2; apply/contraTneq => ->.
                           ---- apply: h'_P_6_hom; rewrite /=; try by done.
                                all: try by rewrite sg_sym.
                                ++++ by rewrite a1_eq_b2 sg_sym.
                                ++++ by rewrite a1_eq_b2.
                       *** have a2_neq_d2: a2 != d2 by rewrite sg_edgeNeq.
                           case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1].
                           ---- have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
                                right; left; exists (hom_G5_def c2 d1 a1 a2 b1).
                                ++++ apply: h'_G5_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     all: try by rewrite a1_eq_b2 eq_sym.
                                     **** by move: c1_adj_c2; apply/contraTneq => ->; rewrite sg_sym.
                                     **** by move: d1_adj_d2; apply/contraTneq => ->.
                                ++++ apply: h'_bull_hom; rewrite /=; try by done.
                                     all: try by rewrite sg_sym.
                                     all: by rewrite a1_eq_b2 sg_sym.
                           ---- left; exists (hom_G4_def a1 a2 b1 c2).
                                ++++ apply: h'_G4_inj; rewrite /=; try by done.
                                     all: try by rewrite eq_sym.
                                     **** by rewrite a1_eq_b2 eq_sym.
                                     **** by move: a2_adj_d2; apply/contraTneq => ->.
                                     **** by move: c1_adj_c2; apply/contraTneq => <-; rewrite sg_sym.
                                ++++ apply: h'_claw_hom; rewrite /=; try by done.
                                     all: try by rewrite sg_sym.
                                     by rewrite a1_eq_b2 sg_sym.
            ** have c1_neq_d1: c1 != d1 by rewrite sg_edgeNeq.
               case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1].
               --- have a2_neq_b1: a2 != b1 by rewrite sg_edgeNeq.
                   case: (boolP (a2 -- c2)) => [a2_adj_c2 | a2_nadj_c2]; last first.
                   +++ right; left; exists (hom_G5_def c2 d1 a1 a2 b1).
                       *** apply: h'_G5_inj; rewrite /=; try by done.
                           all: try by rewrite eq_sym.
                           all: try by rewrite a1_eq_b2 eq_sym.
                           ---- by move: a2_adj_d1; apply/contraTneq => <-.
                           ---- by move: d1_adj_d2; apply/contraTneq => ->.
                       *** apply: h'_bull_hom; rewrite /=; try by done.
                           all: try by rewrite sg_sym.
                           all: by rewrite a1_eq_b2 sg_sym.
                   +++ have a2_neq_c2: a2 != c2 by rewrite sg_edgeNeq.
                       left; exists (hom_G4_def a2 b1 c2 d1).
                       *** apply: h'_G4_inj; rewrite /=; try by done.
                           by move: d1_adj_d2; apply/contraTneq => <-.
                       *** by apply: h'_claw_hom.
               --- case: (boolP (a2 -- c2)) => [a2_adj_c2 | a2_nadj_c2].
                   +++ have a2_neq_c2: a2 != c2 by rewrite sg_edgeNeq.
                       right; left; exists (hom_G5_def b1 d1 a1 a2 c2).
                       *** apply: h'_G5_inj; rewrite /=; try by done.
                           all: try by rewrite eq_sym.
                           ---- by move: d1_adj_d2; apply/contraTneq => <-.
                           ---- by rewrite a1_eq_b2.
                           ---- by move: a2_adj_d1; apply/contraTneq => <-.
                           ---- by rewrite a1_eq_b2 eq_sym.
                       *** apply: h'_bull_hom; rewrite /=; try by done.
                           all: try by rewrite sg_sym.
                           ---- by rewrite a1_eq_b2.
                           ---- by rewrite a1_eq_b2 sg_sym.
                   +++ left; exists (hom_G4_def a1 a2 b1 c2).
                       *** apply: h'_G4_inj; rewrite /=; try by done.
                           all: try by rewrite eq_sym.
                           all: try by move: a2_adj_d1; apply/contraTneq => ->.
                           by rewrite a1_eq_b2 eq_sym.
                       *** apply: h'_claw_hom; rewrite /=; try by done.
                           by rewrite a1_eq_b2 sg_sym.
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
  move: b1c2b2c1 => /andP [/andP [/andP [b1_neq_c2 b1_nadj_c2] b2_neq_c1] b2_nadj_c1].
  have b1d2b2d1 : (b1 != d2) && (~~ b1 -- d2) && (b2 != d1) && (~~ b2 -- d1)
    by t_x1y2x2y1 b1 b2 d1 d2 'v1@4 'v3@4 h h_hom.
  move: b1d2b2d1 => /andP [/andP [/andP [b1_neq_d2 b1_nadj_d2] b2_neq_d1] b2_nadj_d1].
  have c1d2c2d1 : (c1 != d2) && (~~ c1 -- d2) && (c2 != d1) && (~~ c2 -- d1)
    by t_x1y2x2y1 c1 c2 d1 d2 'v2@4 'v3@4 h h_hom.
  move: c1d2c2d1 => /andP [/andP [/andP [c1_neq_d2 c1_nadj_d2] c2_neq_d1] c2_nadj_d1].

  (* Start separation in cases... *)
case/orP: a1a2 => [/eqP a1_eq_a2 | a1_adj_a2].
- case/orP: b1b2 => [/eqP b1_eq_b2 | b1_adj_b2].
  + have a1_adj_b1: a1 -- b1.
      case: (orP a1b2a2b1) => [/orP H | ]; last by rewrite a1_eq_a2.
      case: H => [/orP H' | /eqP a2_eq_b1]; last by rewrite -b1_eq_b2 a1_eq_a2 a2_eq_b1 eq_refl in a1a2b1b2.
      case: H' => [/eqP a1_eq_b2 | ]; last by rewrite b1_eq_b2.
      by rewrite  b1_eq_b2 -a1_eq_a2 a1_eq_b2 eq_refl in a1a2b1b2.
    have a1_neq_b1: a1 != b1 by rewrite sg_edgeNeq.
    case/orP: c1c2 => [/eqP c1_eq_c2 | c1_adj_c2 ].
    * case/orP: d1d2 => [/eqP d1_eq_d2 | d1_adj_d2 ].
      (* b b --- a a --- c c *)
      (*         d d         *)
      -- left; exists (hom_G4_def a1 b1 c1 d1).
         ++ apply: h'_G4_inj; rewrite /=; try by done.
            ** by move: a1a2c1c2 ; rewrite a1_eq_a2 c1_eq_c2 orbb.
            ** by move: a1a2d1d2 ; rewrite a1_eq_a2 d1_eq_d2 orbb.
            ** by move: b1b2c1c2 ; rewrite b1_eq_b2 c1_eq_c2 orbb.
            ** by move: b1b2d1d2 ; rewrite b1_eq_b2 d1_eq_d2 orbb.
            ** by move: c1c2d1d2 ; rewrite c1_eq_c2 d1_eq_d2 orbb.
         ++ apply: h'_claw_hom; rewrite /=; try by done.
            ** move: a1a2c1c2 ; rewrite a1_eq_a2 c1_eq_c2 orbb.
               move: a1c2a2c1 ; rewrite a1_eq_a2 c1_eq_c2 -orbA orbb.
               case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by done].
            ** move: a1a2d1d2 ; rewrite a1_eq_a2 d1_eq_d2 orbb.
               move: a1d2a2d1 ; rewrite a1_eq_a2 d1_eq_d2 -orbA orbb.
               case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by done].
            ** by rewrite b1_eq_b2.
            ** by rewrite b1_eq_b2.
            ** by rewrite c1_eq_c2.
      (* b b --- a a --- c c *)
      (*        d1 d2        *)
      -- have d1_neq_d2: d1 != d2 by rewrite sg_edgeNeq.
         left ; pose h' (v : claw) :=
                match v with
                | Ordinal 0 _ => a1
                | Ordinal 1 _ => b1
                | Ordinal 2 _ => c1
                | Ordinal _ _ => if (a1 -- d1) then d1 else d2
                end.
         exists h'.
         ++ apply: h'_G4_inj; rewrite /=; try by done.
            ** by move: a1a2c1c2 ; rewrite a1_eq_a2 c1_eq_c2 orbb.
            ** rewrite (fun_if (fun d => a1 != d)) ; case: (boolP (a1 -- d1)).
               --- by apply: contraL ; move/eqP-> ; rewrite sg_irrefl.
               --- by apply: contra ; move/eqP-> ; rewrite sg_sym.
            ** by move: b1b2c1c2 ; rewrite b1_eq_b2 c1_eq_c2 orbb.
            ** rewrite (fun_if (fun d => b1 != d)) ; case: (boolP (a1 -- d1)).
               --- by rewrite b1_eq_b2.
               --- by done.
            ** rewrite (fun_if (fun d => c1 != d)) ; case: (boolP (a1 -- d1)).
               --- by rewrite c1_eq_c2.
               --- by done.
         ++ apply: h'_claw_hom; rewrite /=; try by done.
            ** move: a1a2c1c2 ; rewrite a1_eq_a2 c1_eq_c2 orbb.
               move: a1c2a2c1 ; rewrite a1_eq_a2 c1_eq_c2 -orbA orbb.
               case/orP ; [move/eqP=> ? ; move/eqP ; contradiction | by []].
            ** rewrite (fun_if (fun d => a1 -- d)) ; case: (boolP (a1 -- d1)).
               --- by move=> _.
               --- move: a1d2a2d1 ; rewrite a1_eq_a2; case/orP; last
                     by move=> ? /negP ; contradiction.
                   case/orP ; last by move/eqP->.
                   case/orP ; last by done.
                   by move/eqP-> ; apply: contraR ; rewrite sg_sym.
            ** by rewrite b1_eq_b2.
            ** rewrite (fun_if (fun d => b1 -- d)) ; case: (boolP (a1 -- d1)).
               --- by rewrite b1_eq_b2.
               --- by done.
            ** rewrite (fun_if (fun d => c1 -- d)) ; case: (boolP (a1 -- d1)).
               --- by rewrite c1_eq_c2.
               --- by done.
    * by apply:(@case_aa_bb_c1c2_d1d2 h a1 a2 b1 b2 c1 c2 d1 d2).
  + have b1_neq_b2: b1 != b2 by rewrite sg_edgeNeq.
    case/orP: c1c2 => [/eqP c1_eq_c2 | c1_adj_c2].
    * apply:(@case_aa_bb_c1c2_d1d2 h a1 a2 c1 c2 b1 b2 d1 d2); try by done.
      all: try by rewrite eq_sym.
      all: by rewrite sg_sym.
    * have c1_neq_c2: c1 != c2 by rewrite sg_edgeNeq.
      case/orP: d1d2 => [/eqP d1_eq_d2 | d1_adj_d2].
      -- apply:(@case_aa_bb_c1c2_d1d2 h a1 a2 d1 d2 b1 b2 c1 c2); try by done.
         all: try by rewrite eq_sym.
         all: try by rewrite sg_sym.
         by apply/orP; right.
      -- have d1_neq_d2: d1 != d2 by rewrite sg_edgeNeq.
         case: (boolP (a2 -- b1)) => [a2_adj_b1 | a2_nadj_b1].
         ++ by apply: (@case_aa_b1b2_c1c2_d1d2 h a1 a2 b1 b2 c1 c2 d1 d2).
         ++ have a1_neq_b2: a1 != b2 by move: b1_adj_b2; apply/contraTneq => <-; rewrite sg_sym a1_eq_a2.
            case: (boolP (a1 -- b2)) => [a1_adj_b2 | a1_nadj_b2].
            ** apply: (@case_aa_b1b2_c1c2_d1d2 h a2 a1 b2 b1 c2 c1 d2 d1); try by done.
               all: try by rewrite sg_sym.
               all: by rewrite orbC orbA orbC orbA orbA.
            ** have a2_neq_b1: a2 != b1 by move: b1_adj_b2; apply/contraTneq => <-; rewrite -a1_eq_a2.
               by rewrite (negbTE a2_neq_b1) (negbTE a1_neq_b2) (negbTE a2_nadj_b1) (negbTE a1_nadj_b2) in a1b2a2b1.
- have a1_neq_a2: a1 != a2 by rewrite sg_edgeNeq.
  case/orP: b1b2 => [/eqP b1_eq_b2 | b1_adj_b2].
  + case/orP: c1c2 => [/eqP c1_eq_c2 | c1_adj_c2]; last first.
    * have c1_neq_c2: c1 != c2 by rewrite sg_edgeNeq.
      case/orP: d1d2 => [/eqP d1_eq_d2 | d1_adj_d2]; last first.
      -- have d1_neq_d2: d1 != d2 by rewrite sg_edgeNeq.
         case: (boolP (a1 -- b1)) => [a1_adj_b1 | a1_nadj_b1].
         ++ by apply: (@case_a1a2_bb_c1c2_d1d2 h a1 a2 b1 b2 c1 c2 d1 d2).
         ++ apply: (@case_a1a2_bb_c1c2_d1d2 h a2 a1 b2 b1 c2 c1 d2 d1); try by done.
            all: try by rewrite sg_sym.
            all: try by rewrite orbC orbA orbC orbA orbA.
            have a2_neq_b1: a2 != b1 by move: a1_adj_a2; apply/contraTneq => ->.
            rewrite -b1_eq_b2; apply: contraT => a2_nadj_b1.
            have a1_neq_b2: a1 != b2 by move: a1_adj_a2; apply/contraTneq => ->; rewrite -b1_eq_b2 sg_sym.
            rewrite b1_eq_b2 in a1_nadj_b1.
            by rewrite (negbTE a2_neq_b1) (negbTE a1_neq_b2) (negbTE a2_nadj_b1) (negbTE a1_nadj_b1) in a1b2a2b1.
      -- by apply: (@case_a1a2_bb_c1c2_dd h a1 a2 b1 b2 c1 c2 d1 d2).
    * case/orP: d1d2 => [/eqP d1_eq_d2 | d1_adj_d2]; last first.
      -- apply: (@case_a1a2_bb_c1c2_dd h a1 a2 b1 b2 d1 d2 c1 c2); try by done.
         all: try by rewrite eq_sym.
         all: by rewrite sg_sym.
      -- case: (boolP (a1 -- b2)) => [a1_adj_b2 | a1_nadj_b2].
         ++ by apply: (@case_a1a2_bb_cc_dd h a1 a2 b1 b2 c1 c2 d1 d2).
         ++ have a2_neq_b1: a2 != b1 by move: a1_adj_a2; apply/contraTneq => ->; rewrite b1_eq_b2.
            have a2_adj_b1: a2 -- b1.
              apply: contraT => a2_nadj_b1.
              have a1_neq_b2: a1 != b2 by move: a1_adj_a2; apply/contraTneq => ->; rewrite sg_sym -b1_eq_b2.
              by rewrite (negbTE a2_neq_b1) (negbTE a1_neq_b2) (negbTE a1_nadj_b2) (negbTE a2_nadj_b1) in a1b2a2b1.
            apply: (@case_a1a2_bb_cc_dd h a2 a1 b2 b1 c2 c1 d2 d1); try by done.
            all: try by rewrite orbC orbA orbC orbA orbA.
            by rewrite sg_sym.
  + have b1_neq_b2: b1 != b2 by rewrite sg_edgeNeq.
    case/orP: c1c2 => [/eqP c1_eq_c2 | c1_adj_c2]; last first.
    * have c1_neq_c2: c1 != c2 by rewrite sg_edgeNeq.
      case/orP: d1d2 => [/eqP d1_eq_d2 | d1_adj_d2]; last first.
      -- have d1_neq_d2: d1 != d2 by rewrite sg_edgeNeq.
         case: (orP a1b2a2b1) => [/orP H | a2_adj_b1].
         ++ case: H => [/orP H' | /eqP a2_eq_b1].
            ** case: H' => [/eqP a1_eq_b2 | a1_adj_b2].
               --- by apply: (@case_a1a2_b1b2_c1c2_d1d2_with_a1_eq_b2 h a1 a2 b1 b2 c1 c2 d1 d2).
               --- by apply: (@case_a1a2_b1b2_c1c2_d1d2_with_a1_adj_b2 h a1 a2 b1 b2 c1 c2 d1 d2).
            ** apply: (@case_a1a2_b1b2_c1c2_d1d2_with_a1_eq_b2 h a2 a1 b2 b1 c2 c1 d2 d1); try by done.
               all: try by rewrite sg_sym.
               all: by rewrite orbC orbA orbC orbA orbA.
         ++ apply: (@case_a1a2_b1b2_c1c2_d1d2_with_a1_adj_b2 h a2 a1 b2 b1 c2 c1 d2 d1); try by done.
            all: try by rewrite sg_sym.
            all: by rewrite orbC orbA orbC orbA orbA.
      -- case: (boolP (a1 -- d2)) => [a1_adj_d2 | a1_nadj_d2].
         ++ apply: (@case_a1a2_bb_c1c2_d1d2 h a1 a2 d1 d2 b1 b2 c1 c2); try by done.
            all: try by rewrite eq_sym.
            all: try by rewrite sg_sym.
            all: try by rewrite orbC orbA orbC orbA orbA.
            by rewrite d1_eq_d2.
         ++ apply: (@case_a1a2_bb_c1c2_d1d2 h a2 a1 d2 d1 b2 b1 c2 c1); try by done.
            all: try by rewrite eq_sym.
            all: try by rewrite sg_sym.
            all: try by rewrite orbC orbA orbC orbA orbA.
            have a2_neq_d1: a2 != d1 by move: a1_adj_a2; apply/contraTneq => ->; rewrite d1_eq_d2.
            rewrite -d1_eq_d2; apply: contraT => a2_nadj_d1.
            have a1_neq_d2: a1 != d2 by move: a1_adj_a2; apply/contraTneq => ->; rewrite -d1_eq_d2 sg_sym.
            by rewrite (negbTE a2_neq_d1) (negbTE a1_neq_d2) (negbTE a2_nadj_d1) (negbTE a1_nadj_d2) in a1d2a2d1.
    * (* b1 b2 --- a1 a2 --- c c *)
      (*           d1 d2         *)
      case/orP: d1d2 => [/eqP d1_eq_d2 | d1_adj_d2]; last first.
      -- have d1_neq_d2: d1 != d2 by rewrite sg_edgeNeq.
         case: (boolP (a1 -- c2)) => [a1_adj_c2 | a1_nadj_c2].
         ++ apply: (@case_a1a2_bb_c1c2_d1d2 h a1 a2 c1 c2 d1 d2 b1 b2); try by done.
            all: try by rewrite eq_sym.
            all: try by rewrite sg_sym.
            all: try by rewrite orbC orbA orbC orbA orbA.
            by rewrite c1_eq_c2.
         ++ apply: (@case_a1a2_bb_c1c2_d1d2 h a2 a1 c2 c1 d2 d1 b2 b1); try by done.
            all: try by rewrite eq_sym.
            all: try by rewrite sg_sym.
            all: try by rewrite orbC orbA orbC orbA orbA.
            have a2_neq_c1: a2 != c1 by move: a1_adj_a2; apply/contraTneq => ->; rewrite c1_eq_c2.
            rewrite -c1_eq_c2; apply: contraT => a2_nadj_c1.
            have a1_neq_c2: a1 != c2 by move: a1_adj_a2; apply/contraTneq => ->; rewrite -c1_eq_c2 sg_sym.
            by rewrite (negbTE a2_neq_c1) (negbTE a1_neq_c2) (negbTE a2_nadj_c1) (negbTE a1_nadj_c2) in a1c2a2c1.
      -- apply: (@case_a1a2_bb_c1c2_dd h a1 a2 c1 c2 b1 b2 d1 d2); try by done.
         all: try by rewrite eq_sym.
         all: by rewrite sg_sym.
Qed.

(* The characterization of co-paw-free graphs *)
Variables Gcopaw GG7_1 GG7_2 : sgraph.
Hypothesis G_is_copaw : isomorphic Gcopaw copaw.
Hypothesis G_is_G7_1 : isomorphic GG7_1 G7_1.
Hypothesis G_is_G7_2 : isomorphic GG7_2 G7_2.

Corollary copawfree_char : Gcopaw \subgraph G \/ GG7_1 \subgraph G \/
                         GG7_2 \subgraph G <-> Gcopaw \subgraph G'.
Proof.
  rewrite /iff ; split.
  - case.
    { move=> /(subgraph_trans (sub_G2_G1 G_is_copaw)) copawsubG.
      apply: (subgraph_trans (sub_G1_G2 G_is_copaw)).
      by apply: G'copawfree ; left. }
    case.
    + move=> /(subgraph_trans (sub_G2_G1 G_is_G7_1)) G7_1subG.
      apply: (subgraph_trans (sub_G1_G2 G_is_copaw)).
      by apply: G'copawfree ; right ; left.
    + move=> /(subgraph_trans (sub_G2_G1 G_is_G7_2)) G7_2subG.
      apply: (subgraph_trans (sub_G1_G2 G_is_copaw)).
      by apply: G'copawfree ; right ; right.
  - move=> /(subgraph_trans (sub_G2_G1 G_is_copaw)) copawsubG'.
    move: (G'copawfree_rev copawsubG') ; case.
    { by left ; apply: (subgraph_trans (sub_G1_G2 G_is_copaw)). }
    case.
    + by right ; left ; apply: (subgraph_trans (sub_G1_G2 G_is_G7_1)).
    + by right ; right ; apply: (subgraph_trans (sub_G1_G2 G_is_G7_2)).
Qed.

(* The characterization of claw-free graphs *)
Variables Gclaw Gbull GP6 GCC6 : sgraph.
Hypothesis G_is_claw : isomorphic Gclaw claw.
Hypothesis G_is_bull : isomorphic Gbull bull.
Hypothesis G_is_P6 : isomorphic GP6 'P_6.
Hypothesis G_is_CC6 : isomorphic GCC6 'CC_6.

Corollary clawfree_char : Gclaw \subgraph G \/ Gbull \subgraph G \/
                          GP6 \subgraph G \/ GCC6 \subgraph G <-> Gclaw \subgraph G'.
Proof.
  rewrite /iff ; split.
  - case.
    { move=> /(subgraph_trans (sub_G2_G1 G_is_claw)) clawsubG.
      apply: (subgraph_trans (sub_G1_G2 G_is_claw)).
      by apply: G'clawfree ; left. }
    case.
    { move=> /(subgraph_trans (sub_G2_G1 G_is_bull)) bullsubG.
      apply: (subgraph_trans (sub_G1_G2 G_is_claw)).
      by apply: G'clawfree ; right ; left. }
    case.
    + move=> /(subgraph_trans (sub_G2_G1 G_is_P6)) P6subG.
      apply: (subgraph_trans (sub_G1_G2 G_is_claw)).
      by apply: G'clawfree ; right ; right ; left.
    + move=> /(subgraph_trans (sub_G2_G1 G_is_CC6)) CC6subG.
      apply: (subgraph_trans (sub_G1_G2 G_is_claw)).
      by apply: G'clawfree ; right ; right ; right.
  - move=> /(subgraph_trans (sub_G2_G1 G_is_claw)) clawsubG'.
    move: (G'clawfree_rev clawsubG') ; case.
    { by left ; apply: (subgraph_trans (sub_G1_G2 G_is_claw)). }
    case.
    { by right ; left ; apply: (subgraph_trans (sub_G1_G2 G_is_bull)). }
    case.
    + by right ; right ; left ; apply: (subgraph_trans (sub_G1_G2 G_is_P6)).
    + by right ; right ; right ; apply: (subgraph_trans (sub_G1_G2 G_is_CC6)).
Qed.

End Upper_Weighted_Irredundant_Properties.
