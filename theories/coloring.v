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

Fact omega_max (Q : {set G}) : cliqueb Q -> #|Q| <= omega.
Proof. by move: Q ; rewrite /omega ; case: (arg_maxnP W1 setv1). Qed.

Fact omega_witness : exists2 Q, cliqueb Q & W1 Q = omega.
Proof. by rewrite /omega; case: (arg_maxnP W1 setv1) => A; exists A. Qed.

Fact omega_maxset (Q : {set G}) : cliqueb Q -> W1 Q = omega -> maxset (@cliqueb G) Q.
Proof.
  move=> ? Qomega ; apply/maxset_properP ; split ; first by [].
  move=> F ; apply/contraL=> Fclq ; move: (omega_max Fclq) ; rewrite -Qomega.
  by apply/contraL ; rewrite properEcard ltnNge ; move/andP=> [_].
Qed.


(* TO DO:
     define complement of a graph, e.g. complement : sgraph -> sgraph
     prove that a clique in G is a stable in (complement G)
     prove that omega G = alpha (complement G) *)
End CliqueNumber.



(** ** Definitions of coloring as partitions and maps, k-coloring and chromatic number *)
Section ColoringBasics.

(* Colorings as partitions of stable sets *)
Section pColoring.
  Variable P : {set {set G}}.

  Definition is_stablepart : bool := partition P setT && [forall S in P, stable S].

  Definition card_stablepart := #|P|.

  Proposition is_stablepartP : reflect
    (forall S : {set G}, S \in P -> {in S&, forall u v, ~~ u -- v}) [forall S in P, stable S].
  Proof.
    apply: (iffP forallP).
    - move=> H S Sinpart u v uinS vinS.
      by move: (H S) ; rewrite Sinpart implyTb ; move/stableP ; move=> /(_ u v uinS vinS).
    - move=> H S ; apply/implyP=> Sinpart ; apply/stableP=> u v uinS vinS.
      by move: (H S Sinpart u v uinS vinS).
  Qed.

  Proposition card_stablepart_gte_1 : is_stablepart -> #|P| >= 1.
  Proof.
    rewrite /is_stablepart => /andP [Ppart _].
    move: Gnotempty ; move: (card_partition Ppart) ; rewrite cardsT ; move->.
    rewrite !ltnNge ; apply/contraNN ; rewrite leqn0 cards_eq0 ; move/eqP->.
    by rewrite big_set0.
  Qed.

  (* repr_class gives a "representative vertex" of the same color than v,
     while repr_coll gives the collection of all representatives *)
  Definition repr_coll := transversal P setT.
  Definition repr_class (v : G) : G := transversal_repr somev repr_coll (pblock P v).

  Proposition repr_coll_card : is_stablepart -> #|repr_coll| = #|P|.
  Proof. 
    rewrite /is_stablepart => /andP [Ppart _].
    move: (transversalP Ppart) ; rewrite -/repr_coll ; exact: card_transversal.
  Qed.

  Proposition repr_class_in_coll v : is_stablepart -> repr_class v \in repr_coll.
  Proof.
    rewrite /is_stablepart => /andP [Ppart _].
    move: (transversalP Ppart) ; rewrite -/repr_coll => repr_coll_is_transv.
    apply: (repr_mem_transversal repr_coll_is_transv).
    have vincoverP: v \in cover P by move: Ppart => /and3P [/eqP-coverT _ _] ; rewrite coverT.
    by move: (pblock_mem vincoverP).
  Qed.

  Proposition repr_same_class v : is_stablepart -> pblock P v == pblock P (repr_class v).
  Proof.
    rewrite /is_stablepart => /andP [Ppart _].
    have vincoverP: v \in cover P by move: Ppart => /and3P [/eqP-coverT _ _] ; rewrite coverT.
    move: (pblock_mem vincoverP) => vclassinP.
    move: (repr_mem_pblock (transversalP Ppart) somev vclassinP) => rcinvclass.
    move: Ppart => /andP [_ /andP [dsj _]].
    by rewrite -(same_pblock dsj rcinvclass).
  Qed.

  Proposition repr_not_adj u v : is_stablepart -> repr_class u = repr_class v -> ~~ u -- v.
  Proof.
    move=> isstp rcueqrcv.
    move/eqP: (repr_same_class u isstp).
    move/eqP: (repr_same_class v isstp).
    rewrite rcueqrcv ; move<- => uclasseqvclass.
    move: isstp ; rewrite /is_stablepart => /andP [Ppart /is_stablepartP-Pstab].
    have vincoverP: v \in cover P by move: Ppart => /and3P [/eqP-coverT _ _] ; rewrite coverT.
    move: (pblock_mem vincoverP) => vclassinP.
    set S := pblock P v.
    move: vincoverP ; rewrite -mem_pblock => vinS.
    have uincoverP: u \in cover P by move: Ppart => /and3P [/eqP-coverT _ _] ; rewrite coverT.
    move: uincoverP ; rewrite -mem_pblock uclasseqvclass => uinS.
    by move: (Pstab S vclassinP u v uinS vinS).
  Qed.
End pColoring.

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

Lemma singl_part_is_stablepart : is_stablepart singl_part.
Proof.
  rewrite /is_stablepart ; apply/andP ; split.
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
Definition chi : nat := #|arg_min singl_part is_stablepart card_stablepart|.

Fact chi_min P : is_stablepart P -> chi <= #|P|.
Proof.
  rewrite /chi.
  case: (arg_minnP card_stablepart singl_part_is_stablepart) => A _ ; apply.
Qed.

Fact chi_witness : exists2 P, is_stablepart P & #|P| = chi.
Proof.
  rewrite /chi.
  case: (arg_minnP card_stablepart singl_part_is_stablepart) => D.
  by exists D.
Qed.

Fact chi_minset P : is_stablepart P -> #|P| = chi -> minset is_stablepart P.
Proof.
  move=> ? Pchi ; apply/minset_properP ; split ; first by [].
  move=> F ; apply/contraL=> Fcol ; move: (chi_min Fcol) ; rewrite -Pchi.
  by apply/contraL ; rewrite properEcard ltnNge ; move/andP=> [_].
Qed.

Fact chi_lte_n : chi <= #|G|.
Proof. by move: (chi_min singl_part_is_stablepart) ; rewrite singl_part_card. Qed.

Fact chi_gte_1 : chi >= 1.
Proof. move: chi_witness=> [P Pstab] <- ; exact: card_stablepart_gte_1. Qed.

(* A main result of graph colorings *)
Theorem clique_leq_coloring (Q : {set G}) (P : {set {set G}}) :
  cliqueb Q -> is_stablepart P -> #|Q| <= #|P|.
Proof.
  move=> /cliqueP-Qclq isstp.
  (* QQ is the representative vertices of the vertices of Q *)
  set QQ := [set (repr_class P x) | x in Q].
  have QQsubRC: QQ \subset repr_coll P.
  { apply/subsetP=> x ; rewrite /QQ ; move/imsetP => [y _].
    move-> ; exact: repr_class_in_coll. }
  suff QeqQQ : #|Q| = #|QQ|.
  { by rewrite QeqQQ -repr_coll_card ; move: (subset_leq_card QQsubRC). }
  rewrite /QQ card_in_imset ; first by [].
  rewrite /injective => x1 x2 x1inQ x2inQ rc1eqrc2.
  apply/eqP.
  move: (repr_not_adj isstp rc1eqrc2).
  apply: contraLR.
  rewrite negbK.
  (* now, we use the fact that Q is a clique *)
  exact: (Qclq x1 x2 x1inQ x2inQ).
Qed.

Corollary omega_leq_chi : omega <= chi.
Proof.
  move: chi_witness=> [P Pstab] <-.
  move: omega_witness=> [Q Qclq] <-.
  exact: clique_leq_coloring.
Qed.

(* Colorings as maps *)
Section fColoring.
  Variable C : finType.
  Variable f : {ffun G -> C}. (* the map that assigns a vertex to a color *)

  Definition is_coloring : bool := [forall u, forall v, u -- v ==> (f u != f v)].

  Definition card_coloring : nat := #|f @: setT|.

  Definition kcoloring (k : nat) : bool :=  is_coloring && (card_coloring <= k).

  Proposition is_coloringP : reflect (forall u v : G, u -- v -> (f u != f v)) is_coloring.
  Proof.
    rewrite /is_coloring ; apply: (iffP forallP).
    - by move=> P x y ; move/forallP: (P x) ; move=> /(_ y) /implyP.
    - by move=> P x ; apply/forallP=> y ; apply/implyP ; move: (P x y).
  Qed.

  Definition col_to_part := preim_partition f setT.
  Let P := col_to_part.

  Lemma col_to_part_is_stablepart : is_coloring -> is_stablepart P.
  Proof.
    set R := [rel x y | f x == f y].
    have Ppart : partition P setT by rewrite /col_to_part ; exact: preim_partitionP.
    move/is_coloringP=> H ; rewrite /is_stablepart ; apply/andP ; split ; first exact: Ppart.
    apply/is_stablepartP ; move=> S Sinpart u v uinS vinS.
    rewrite (contra (H u v)) // negbK.
    move: Ppart => /andP [_ /andP [dsj _]].
    move: vinS ; rewrite -(@def_pblock _ P S u dsj Sinpart uinS).
    have eqiR : {in setT & &, equivalence_rel R} by split=> //= /eqP->.
    by rewrite (@pblock_equivalence_partition _ R setT eqiR u v (in_setT u) (in_setT v)).
  Qed.

  Proposition leq_preimset (aT rT : finType) (g : aT -> rT) (A : {set rT}) :
    A \subset g @: setT -> #|A| <= #|g @^-1: A|.
  (* this result should be obvious, but I didn't find it in the math-comp  :S  *)
  Proof.
    suff: forall (n : nat) (X : {set rT}), X \subset g @: setT -> #|X| = n -> n <= #|g @^-1: X|
     by move/(_ #|A| A _ erefl).
    move=> n ; elim/nat_ind: n.
    - by move=> ? _ ; move/cards0_eq-> ; rewrite preimset0 cards0.
    - move=> n IHn X Xsubim Xeqn1 ; move: (ltn0Sn n) ; rewrite -{1}Xeqn1.
      move/card_gt0P=> [x xinX].
      set Y := X :\ x.
      move: (cardsD1 x X) ; rewrite xinX //= add1n Xeqn1 ; move/eqP.
      rewrite eqSS -/Y eq_sym ; move/eqP=> Yeqn.
      move: (subset_trans (subsetDl X [set x]) Xsubim) ; rewrite -/Y => Ysubim.
      move: (IHn Y Ysubim Yeqn).
      move: (cardsD (g @^-1: X) (g @^-1: [set x])).
      rewrite -preimsetI => H1.
      rewrite /Y (preimsetD g X [set x]) H1.
      have sxinX: [set x] \subset X.
        by apply/subsetP=> y ; rewrite in_set1 ; move/eqP->.
      move: (setIidPr sxinX)->.
      have H2: #|g @^-1: [set x]| <= #|g @^-1: X|.
        by rewrite subset_leq_card // (preimsetS g sxinX).
      rewrite (leq_subRL n H2).
      have H3: 0 < #|g @^-1: [set x]|.
      { rewrite card_gt0 ; apply/set0Pn.
        move: (subsetP Xsubim x xinX) ; move/imsetP => [z _ xeqgz].
        by exists z ; rewrite /preimset in_set -xeqgz set11. }
      rewrite -(prednK H3) addSn.
      have H4: n <= #|g @^-1: [set x]|.-1 + n by exact: leq_addl.
      exact: (leq_ltn_trans H4).  
  Qed.

  Lemma col_to_part_same_card : is_coloring -> card_coloring = #|P|.
  Proof.
    move=> fcol ; apply/eqP.
    move: (col_to_part_is_stablepart fcol) => isstp.
    set cols := f @: setT.
    rewrite -(repr_coll_card isstp) eqn_leq /card_coloring -/cols.
    apply/andP ; split.
    - set verts := f @^-1: cols.
      set repr_verts := [set (repr_class P x) | x in verts].
      have rvsubRC: repr_verts \subset repr_coll P.
      { apply/subsetP=> x ; rewrite /repr_verts ; move/imsetP => [y _].
        move-> ; move: isstp ; exact: repr_class_in_coll. }
      move: (subset_leq_card rvsubRC).
      have: #|cols| <= #|verts| by rewrite /verts ; exact: leq_preimset.
      suff: #|verts| = #|repr_verts| by move-> ; exact: leq_trans.
      rewrite /repr_verts card_in_imset ; first by [].
      rewrite /injective => x1 x2 x1inve x2inve rc1eqrc2.
      admit.
    - admit.
  Admitted.

  Corollary clique_leq_kcoloring (k : nat) (Q : {set G}) :
    cliqueb Q -> kcoloring k -> #|Q| <= k.
  Proof.
    rewrite /kcoloring ; move=> Qclq /andP[fcol].
    move: (clique_leq_coloring Qclq (col_to_part_is_stablepart fcol)).
    move: (col_to_part_same_card fcol)-> ; exact: leq_trans.
  Qed.

  Corollary chi_leq_kcoloring (k : nat) : kcoloring k -> chi <= k.
  Proof.
    rewrite /kcoloring ; move=> /andP[fcol].
    move: (chi_min (col_to_part_is_stablepart fcol)).
    move: (col_to_part_same_card fcol)-> ; exact: leq_trans.
  Qed.
End fColoring.

End ColoringBasics.

End GraphColoring.
