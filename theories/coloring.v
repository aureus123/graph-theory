From mathcomp Require Import all_ssreflect.
Require Import preliminaries digraph sgraph dom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


(**********************************************************************************)
(** * Graph Coloring                                                              *)
(**********************************************************************************)
Section GraphColoring.

Variable G : sgraph.
Hypothesis Gnotempty : 0 < #|G|.

Fact somev_exists : exists v : G, v \in G.
Proof. by move: Gnotempty ; rewrite -cardsT card_gt0 ; move/set0Pn=> [x _] ; exists x. Qed.

Let somev : G := xchoose somev_exists.


(** ** Definition of clique number *)
Section CliqueNumber.

Let W1 : ({set G} -> nat) := (fun A => #|A|).

Let setv := [set somev].

Let setv1 : cliqueb setv.
Proof. apply/cliqueP ; rewrite /setv ; apply: clique1. Qed.

Definition omega : nat := #|arg_max setv (@cliqueb G) W1|.

Fact omega_max S : @cliqueb G S -> #|S| <= omega.
Proof. by move: S ; rewrite /omega ; case: (arg_maxnP W1 setv1). Qed.

Fact omega_witness : exists2 S, cliqueb S & W1 S = omega.
Proof. by rewrite /omega; case: (arg_maxnP W1 setv1) => A; exists A. Qed.

Fact omega_maxset S : cliqueb S -> W1 S = omega -> maxset (@cliqueb G) S.
Proof.
  move=> ? Somega ; apply/maxset_properP ; split ; first by [].
  move=> F ; apply/contraL=> Fclq ; move: (omega_max Fclq) ; rewrite -Somega.
  by apply/contraL ; rewrite properEcard ltnNge ; move/andP=> [_].
Qed.


(* TO DO:
     define complement of a graph, e.g. complement : sgraph -> sgraph
     prove that a clique in G is a stable in (complement G)
     prove that omega G = alpha (complement G) *)
End CliqueNumber.



(** ** Definitions of coloring as partitions and maps, k-coloring and chromatic number *)
Section ColoringBasics.

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

  Definition is_kcoloring_p (k : nat) : bool :=  is_coloring_p && (card_coloring_p <= k).

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

  Proposition card_coloring_p_gte_1 : is_coloring_p -> #|P| >= 1.
  Proof.
    rewrite /is_coloring_p => /andP [Ppart _].
    move: Gnotempty ; move: (card_partition Ppart) ; rewrite cardsT ; move->.
    rewrite !ltnNge ; apply/contraNN ; rewrite leqn0 cards_eq0 ; move/eqP->.
    by rewrite big_set0.
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

  Lemma f_to_part_same_kcom (k : nat) :
    is_coloring f -> (is_kcoloring f k) = (is_kcoloring_p P k).
  Proof.
    move=> fcol.
    rewrite /is_kcoloring /is_kcoloring_p fcol (f_to_part_is_coloring fcol) !andTb.
    by rewrite (f_to_part_same_card fcol) /card_coloring_p.
  Qed.
End f_to_pColoring.


(* A trivial coloring: a partition where each set is a singleton with diff. vertices *)
Definition singl_part := [set [set x] | x in G].

Lemma stable1 (x : G) : stable [set x].
Proof. by apply/stableP=> u v ; rewrite !in_set1 ; move/eqP-> ; move/eqP-> ; rewrite sg_irrefl. Qed.

Lemma singl_part_is_partition : partition singl_part setT.
Proof.
  rewrite /partition ; apply/and3P ; split.
  - rewrite /cover eqEsubset ; apply/andP ; split ; first exact: subsetT.
    apply/subsetP=> x _ ; apply/bigcupP ; rewrite /singl_part.
    exists [set x] ; last by rewrite in_set1.
    apply/imsetP ; exists x ; by [].
  - apply/trivIsetP=> A B Asin Bsin AneqB ; apply/disjointP=> x ; move: AneqB.
    move: Asin ; rewrite /singl_part ; move/imsetP=> [x' _] ; move->.
    move: Bsin ; rewrite /singl_part ; move/imsetP=> [x'' _] ; move->.
    rewrite !in_set1 ; move=> x'neqx'' /eqP xeqx' /eqP xeqx''.
    by move: x'neqx'' ; rewrite -xeqx' -xeqx'' eqxx.
  - rewrite /singl_part ; apply/imsetP=> [[x _ H]].
    by move: (set10 x) ; rewrite H ; move/eqP.
Qed.

Lemma singl_part_is_coloring : is_coloring_p singl_part.
Proof.
  rewrite /is_coloring_p ; apply/andP ; split.
  - exact: singl_part_is_partition.
  - apply/forall_inP=> S ; rewrite /singl_part ; move/imsetP=> [x _] ->.
    exact: stable1.
Qed.

Lemma singl_part_card : #|singl_part| = #|G|.
Proof.
  suff P1 : {in singl_part, forall A : {set G}, #|A| = 1}.
  { move: (@card_uniform_partition _ 1 singl_part setT P1 singl_part_is_partition).
    by rewrite cardsT ; move-> ; rewrite muln1. }
  by move=> A /imsetP=> [[x _]]-> ; rewrite cards1.
Qed.

(* Definition of chromatic number and some basic properties *)
Definition chi : nat := #|arg_min singl_part is_coloring_p card_coloring_p|.

Fact chi_min P : is_coloring_p P -> chi <= #|P|.
Proof.
  rewrite /chi.
  case: (arg_minnP card_coloring_p singl_part_is_coloring) => A _ ; apply.
Qed.

Fact chi_witness : exists2 P, is_coloring_p P & #|P| = chi.
Proof.
  rewrite /chi.
  case: (arg_minnP card_coloring_p singl_part_is_coloring) => D.
  by exists D.
Qed.

Fact chi_minset P : is_coloring_p P -> #|P| = chi -> minset is_coloring_p P.
Proof.
  move=> ? Pchi ; apply/minset_properP ; split ; first by [].
  move=> F ; apply/contraL=> Fcol ; move: (chi_min Fcol) ; rewrite -Pchi.
  by apply/contraL ; rewrite properEcard ltnNge ; move/andP=> [_].
Qed.

Fact chi_lte_n : chi <= #|G|.
Proof. by move: (chi_min singl_part_is_coloring) ; rewrite singl_part_card. Qed.

Fact chi_gte_1 : chi >= 1.
Proof. move: chi_witness=> [P Pcol] <- ; exact: card_coloring_p_gte_1. Qed.

End ColoringBasics.


(* A main result of graph colorings *)
Theorem omega_leq_chi : omega <= chi.
Admitted.

End GraphColoring.
