From mathcomp Require Import all_ssreflect.
Require Import preliminaries digraph sgraph dom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(**********************************************************************************)
(** * Graph Coloring                                                          *)
(**********************************************************************************)

(** ** Definitions of coloring as partitions and maps, k-coloring and chromatic number *)
Section ColoringBasics.

Variable G : sgraph.

(* Colorings as maps *)
Section fColoring.
  Variable C : finType.
  Variable f : {ffun G -> C}. (* the map that assigns a vertex to a color *)

  Definition is_coloring : bool := [forall u, forall v, u -- v ==> (f u != f v)].

  Definition number_of_colors : nat := #|f @: setT|.

  Definition is_kcoloring (k : nat) : bool :=  is_coloring && (number_of_colors <= k).

  Proposition is_coloringP : reflect (forall u v : G, u -- v -> (f u != f v)) is_coloring.
  Proof.
    rewrite /is_coloring ; apply: (iffP forallP).
    - by move=> P x y ; move/forallP: (P x) ; move=> /(_ y) /implyP.
    - by move=> P x ; apply/forallP=> y ; apply/implyP ; move: (P x y).
  Qed.
End fColoring.


(* Colorings as partitions *)
Section pColoring.
  Variable R : rel G.   (* the relation that tells if two vertices share the same color *)

  Definition part_p := equivalence_partition R setT.

  Definition is_coloring_p : bool := [forall S in part_p, stable S].

  Definition number_of_colors_p : nat := #|part_p|.

  Proposition is_coloring_pP :
    reflect (forall S : {set G}, S \in part_p -> {in S&, forall u v, ~~ u -- v}) is_coloring_p.
(* Daniel: I tried to put "{in part_p, forall S, {...}}" but it doesn't checktype, don't know why *)
  Proof.
    rewrite /is_coloring_p ; apply: (iffP forallP).
    - move=> P S Sinpart u v uinS vinS.
      by move: (P S) ; rewrite Sinpart implyTb ; move/stableP ; move=> /(_ u v uinS vinS).
    - move=> P S ; apply /implyP=> Sinpart ; apply/stableP=> u v uinS vinS.
      by move: (P S Sinpart u v uinS vinS).
  Qed.
End pColoring.


(* Conversion between one and the another *)
Definition f_to_R (C : finType) (f : {ffun G -> C}) := [rel x y | f x == f y].

Definition f_to_part (C : finType) (f : {ffun G -> C}) := part_p (f_to_R f).

Lemma f_to_part_is_partition (C : finType) (f : {ffun G -> C}) : partition (f_to_part f) setT.
Proof. rewrite /f_to_part ; exact: preim_partitionP. Qed.

Lemma f_to_part_is_coloring (C : finType) (f : {ffun G -> C}) :
  is_coloring f -> is_coloring_p (f_to_R f).
Proof.
  move/is_coloringP=> P ; apply/is_coloring_pP=> S Sinpart u v uinS vinS.
  rewrite (contra (P u v)) // negbK.
  move: (f_to_part_is_partition f) => /andP [_ /andP [dsj _]].

Check @pblock_equivalence_partition _ (f_to_R f) _ _ u v uinS vinS.

  move: (@same_pblock _ (part_p (f_to_R f)) u v dsj).
  set Tu := pblock (part_p (f_to_R f)) u.
  set Tv := pblock (part_p (f_to_R f)) v.
  apply: contraPT => funeqfv TuisTv.
  move: (@def_pblock _ (part_p (f_to_R f)) S u dsj Sinpart uinS).
  rewrite -/Tu.

def_pblock P B x : trivIset P -> B \in P -> x \in B -> pblock P x = B.

Print partition.

Lemma trivIsetP P :
  reflect {in P &, forall A B, A != B -> [disjoint A & B]} (trivIset P).

Check @arg_min (rel G).

Definition chi : nat := is_coloring f && (#|f @: setT| <= k).


Check mem_pred {ffun G -> C}.




End ColoringBasics.