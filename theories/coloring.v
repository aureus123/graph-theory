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

  Definition card_coloring : nat := #|f @: setT|.

  Definition is_kcoloring (k : nat) : bool :=  is_coloring && (card_coloring <= k).

  Proposition is_coloringP : reflect (forall u v : G, u -- v -> (f u != f v)) is_coloring.
  Proof.
    rewrite /is_coloring ; apply: (iffP forallP).
    - by move=> P x y ; move/forallP: (P x) ; move=> /(_ y) /implyP.
    - by move=> P x ; apply/forallP=> y ; apply/implyP ; move: (P x y).
  Qed.
End fColoring.


(* Colorings as partitions *)
Section pColoring.
  Variable P : {set {set G}}.

  Definition is_coloring_p : bool := partition P setT && [forall S in P, stable S].

  Definition card_coloring_p := #|P|.

  Proposition is_coloring_pP : reflect
    (forall S : {set G}, S \in P -> {in S&, forall u v, ~~ u -- v}) [forall S in P, stable S].
(* Daniel: I tried to put "{in part_p, forall S, {...}}" but it doesn't checktype, don't know why *)
  Proof.
    apply: (iffP forallP).
    - move=> H S Sinpart u v uinS vinS.
      by move: (H S) ; rewrite Sinpart implyTb ; move/stableP ; move=> /(_ u v uinS vinS).
    - move=> H S ; apply/implyP=> Sinpart ; apply/stableP=> u v uinS vinS.
      by move: (H S Sinpart u v uinS vinS).
  Qed.
End pColoring.


(* Conversion between one and the another *)
Section f_to_pColoring.
  Variable C : finType.
  Variable f : {ffun G -> C}.

  Definition f_to_part := preim_partition f setT.
  Let P := f_to_part.

  Lemma f_to_part_is_coloring : is_coloring f -> is_coloring_p P.
  Proof.
    set R := [rel x y | f x == f y].
    have P_is_part : partition P setT by rewrite /f_to_part ; exact: preim_partitionP.
    move/is_coloringP=> H ; rewrite /is_coloring_p ; apply/andP ; split ; first exact: P_is_part.
    apply/is_coloring_pP ; move=> S Sinpart u v uinS vinS.
    rewrite (contra (H u v)) // negbK.
    move: P_is_part => /andP [_ /andP [dsj _]].
    move: vinS ; rewrite -(@def_pblock _ P S u dsj Sinpart uinS).
    have eqiR : {in setT & &, equivalence_rel R} by split=> //= /eqP->.
    by rewrite (@pblock_equivalence_partition _ R setT eqiR u v (in_setT u) (in_setT v)).
  Qed.

  Lemma f_to_part_same_card : is_coloring f -> card_coloring f = #|P|.
  Admitted.
End f_to_pColoring.


(* A trivial coloring: a partition where each set is a singleton with diff. vertices *)
Definition singl_part := [set [set x] | x in G].

Lemma stable1 (x : G) : stable [set x].
Proof. by apply/stableP=> u v ; rewrite !in_set1 ; move/eqP-> ; move/eqP-> ; rewrite sg_irrefl. Qed.

Lemma singl_part_is_coloring : is_coloring_p singl_part.
Proof.
  rewrite /is_coloring_p ; apply/andP ; split.
  - rewrite /partition ; apply/and3P ; split.
    + rewrite /cover eqEsubset ; apply/andP ; split ; first exact: subsetT.
      apply/subsetP=> x _ ; apply/bigcupP ; rewrite /singl_part.
      exists [set x] ; last by rewrite in_set1.
      apply/imsetP ; exists x ; by [].
    + apply/trivIsetP=> A B Asin Bsin AneqB ; apply/disjointP=> x ; move: AneqB.
      move: Asin ; rewrite /singl_part ; move/imsetP=> [x' _] ; move->.
      move: Bsin ; rewrite /singl_part ; move/imsetP=> [x'' _] ; move->.
      rewrite !in_set1 ; move=> x'neqx'' /eqP xeqx' /eqP xeqx''.
      by move: x'neqx'' ; rewrite -xeqx' -xeqx'' eqxx.
    + rewrite /singl_part ; apply/imsetP=> [[x _ H]].
      by move: (set10 x) ; rewrite H ; move/eqP.
  - apply/forall_inP=> S ; rewrite /singl_part ; move/imsetP=> [x _] ->.
    exact: stable1.
Qed.

Lemma singl_part_card : #|singl_part| = #|G|.
Admitted.

Definition chi : nat := #|arg_min singl_part is_coloring_p card_coloring_p|.

Fact chi_min P : is_coloring_p P -> chi <= #|P|.
Proof.
  rewrite /chi.
  case: (arg_minP card_coloring_p singl_part_is_coloring) => A _ ; apply.
Qed.

Fact chi_witness : exists2 P, is_coloring_p P & #|P| = chi.
Proof.
  rewrite /chi.
  case: (arg_minP card_coloring_p singl_part_is_coloring) => D.
  by exists D.
Qed.

Fact chi_minset P : is_coloring_p P -> #|P| = chi -> minset is_coloring_p P.
Admitted.





End ColoringBasics.