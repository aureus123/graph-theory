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

  Proposition repr_class_rev v : is_stablepart -> v \in repr_coll -> v = repr_class v.
  Proof.
    move=> isstp vinrc.
    move: (isstp) ; rewrite /is_stablepart => /andP [Ppart _].
    move/eqP: (repr_same_class v isstp).
    move: (pblock_inj (transversalP Ppart)) ; rewrite /injective.
    by move=> /(_ v (repr_class v) vinrc (repr_class_in_coll v isstp)).
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
    suff: forall (n : nat) (X : {set rT}), X \subset g @: setT -> #|X| = n -> n <= #|g @^-1: X|.
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
    move=> fcol ; move: (col_to_part_is_stablepart fcol) => isstp.
    set cols := f @: setT.
    set repr_verts := [set (repr_class P x) | x in (f @^-1: cols)].
    have cols_eq_repr_verts: #|cols| = #|repr_verts|.
    { 
      rewrite /repr_verts.
      suff: forall (n : nat) (X : {set C}), X \subset f @: setT -> #|X| = n ->
        #|[set repr_class P x | x in f @^-1: X]| = n
        by move/(_ #|cols| cols (subxx cols) erefl).
      move=> n. elim/nat_ind: n.
      - move=> ? _ ; move/cards0_eq-> ; rewrite preimset0 eq_card0 //=.
        by move=> ? ; rewrite inE imset0 in_set0.
      - move=> n IHn X Xsubim Xeqn1 ; move: (ltn0Sn n) ; rewrite -{1}Xeqn1.
        move/card_gt0P=> [x xinX].
        set Y := X :\ x.
        move: (cardsD1 x X) ; rewrite xinX //= add1n Xeqn1 ; move/eqP.
        rewrite eqSS -/Y eq_sym ; move/eqP=> Yeqn.
        move: (subset_trans (subsetDl X [set x]) Xsubim) ; rewrite -/Y => Ysubim.
        move: (IHn Y Ysubim Yeqn)<-.
        have XeqYx: X = x |: Y by rewrite /Y setD1K.
        rewrite XeqYx preimsetU imsetU cardsU addnC -addn1 -addnBA.
        + apply/eqP ; rewrite eqn_add2l.
          have xincols: [set x] \subset cols.
          { move: Xsubim ; apply: subset_trans ; apply/subsetP => w.
            by rewrite in_set1 ; move/eqP->. }
          move: (leq_preimset xincols) ; rewrite cards1.
          move/card_gt0P=> [z zinpreim].
          have zpreimx: [set repr_class P z0 | z0 in f @^-1: [set x]] = [set repr_class P z].
          { apply/eqP ; rewrite eqEsubset ; apply/andP ; split.
            * apply/subsetP=> z' ; move/imsetP=> [z'' z''inpreim].
              rewrite in_set. move->.
              set R := [rel x y | f x == f y].
              have eqiR : {in setT & &, equivalence_rel R} by split=> //= /eqP->.
              have H1: z'' \in pblock (equivalence_partition R [set: G]) z.
              { rewrite (@pblock_equivalence_partition _ R setT eqiR z z'' (in_setT z) (in_setT z'')).
                rewrite /R //=.
                move: zinpreim ; rewrite in_set in_set1 ; move/eqP->.
                by move: z''inpreim ; rewrite in_set in_set1 ; move/eqP->. }
              move: (isstp) ; rewrite /is_stablepart ; move/andP=>[ /and3P [_ dsj _] _].
              by rewrite /repr_class (same_pblock dsj H1).
            * apply/subsetP=> z' ; rewrite in_set1 ; move/eqP-> ; apply/imsetP.
              by exists z. }
          have: #|[set repr_class P z0 | z0 in f @^-1: [set x]]| = 1
            by apply/eqP/cards1P ; exists (repr_class P z).
          move->.
          have: #|[set repr_class P z0 | z0 in f @^-1: [set x]]
                :&: [set repr_class P z0 | z0 in f @^-1: Y]| = 0.
          { apply/eqP ; rewrite cards_eq0 -subset0 zpreimx ; apply/subsetP=> z'.
            rewrite in_setI ; move/andP=> [].
            rewrite in_set ; move/eqP-> ; move/imsetP=> [z''].
            move: zinpreim ; rewrite in_set in_set1 in_set in_set in_set1. move/eqP<-.
            move=> /andP[fzz''neqfz _].
            apply: contra_eqT=> _ ; move: fzz''neqfz ; apply: contra => rczeqrcz''.
            set R := [rel x y | f x == f y].
            have eqiR : {in setT & &, equivalence_rel R} by split=> //= /eqP->.
            suff: z'' \in pblock P z.
            rewrite (@pblock_equivalence_partition _ R setT eqiR z z'' (in_setT z) (in_setT z'')).
            by rewrite /R //= eq_sym.
            move: isstp ; rewrite /is_stablepart ; move/andP=> [Ppart _].
            move: (Ppart) ; move/and3P=> [/eqP-coverT dsj _].
            have zincoverP: z \in cover P by rewrite coverT.
            rewrite -(@eq_pblock _ P z z'' dsj zincoverP).
            move: rczeqrcz''.
            rewrite /repr_class.
            have pzinP : pblock P z \in P by apply: pblock_mem.
            move: (transversal_reprK (transversalP Ppart) somev pzinP) => pteqpz.
            have z''incoverP: z'' \in cover P by rewrite coverT.
            have pz''inP : pblock P z'' \in P by apply: pblock_mem.
            move: (transversal_reprK (transversalP Ppart) somev pz''inP) => pteqpz''.
            rewrite -{2}pteqpz -{2}pteqpz''.
            by move/eqP->.
          }
          by move->.
        + rewrite subset_leq_card //= ; apply/subsetP=> z.
          by rewrite in_setI => /andP [? _].
    }
    rewrite -(repr_coll_card isstp) /card_coloring -/cols cols_eq_repr_verts.
    suff: repr_verts == repr_coll P by move/eqP->.
    rewrite eqEsubset ; apply/andP ; split.
    - apply/subsetP=> x ; rewrite /repr_verts ; move/imsetP => [y _].
      move-> ; move: isstp ; exact: repr_class_in_coll.
    - apply/subsetP=> x xinrc ; rewrite /repr_verts ; apply/imsetP.
      exists x ; [ by rewrite in_set /cols mem_imset | exact: repr_class_rev ].
  Qed.

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

(** ** Definition of coloring from Christian Dockzal *)

(* TOTHINK: do we need that [hereditary] is a boolean predicate? *)
Lemma sub_stable (B A : {set G}) : 
  A \subset B -> stable B -> stable A.
Proof.
move => subAB stB. exact: (hereditaryP _ (st_hereditary G) _ _ subAB).
Qed.

Lemma set_mem (T : finType) (A : {set T}) : [set x in mem A] = A.
Proof. by apply/setP => ?; rewrite inE. Qed.

Section partition.
Variable (T : finType) (P : {set {set T}}) (D : {set T}).
Implicit Types (A B : {set T}).

Lemma partition_set0 B : partition P D -> B \in P -> B != set0.
Proof. by move=> partP; apply: contraTneq => ->; rewrite (partition0 D). Qed.

Lemma partition_subset B : partition P D -> B \in P -> B \subset D.
Proof. 
by move=> partP BP; rewrite -(cover_partition partP); apply: bigcup_max BP _.
Qed.

(* TOTHINK: an alternative definition would be [[set B :&: A | B in P]:\ set0]. 
   Then one has to prove the partition properties, but the lemmas below 
   are simpler to prove. *)
Definition sub_partition A : {set {set T}} := 
  preim_partition (pblock P) A.

Lemma sub_partitionP A : partition (sub_partition A) A.
Proof. exact: preim_partitionP. Qed.

Lemma sub_partition_sub A : 
  partition P D -> A \subset D -> sub_partition A \subset [set B :&: A | B in P].
Proof.
move=> partP /subsetP subAD; apply/subsetP => B; case/imsetP => [x xA ->].
have ? : x \in cover P by rewrite (cover_partition partP) subAD.
apply/imsetP; exists (pblock P x); first by rewrite pblock_mem.
by apply/setP => y; rewrite !inE eq_pblock 1?andbC //; case/and3P: partP.
Qed.

Lemma card_sub_partition A : 
  partition P D -> A \subset D -> #|sub_partition A| <= #|P|.
Proof. 
move=> partP subAD; apply: leq_trans (leq_imset_card (fun B => B :&: A) _).
apply: subset_leq_card. exact: sub_partition_sub. 
Qed.

End partition.

(** chromatic number *)

Definition coloring (P : {set {set G}}) (D : {set G}) :=
  partition P D && [forall S in P, stable S].

Definition trivial_coloring (A : {set G}) := 
  [set [set x] | x in A].

Lemma trivial_coloringP (A : {set G}) :
  coloring (trivial_coloring A) A.
Proof.
apply/andP; split; last by apply/forall_inP=> ? /imsetP[x xA ->]; exact: stable1.
suff -> : trivial_coloring A = preim_partition id A by apply: preim_partitionP.
have E x : x \in A -> [set x] = [set y in A | x == y].
  by move=> xA; apply/setP => y; rewrite !inE eq_sym andb_idl // => /eqP<-.
by apply/setP => P; apply/imsetP/imsetP => -[x xA ->]; exists x => //; rewrite E.
Qed.
Arguments trivial_coloringP {A}.

(*
Fact x_in_part (P : {set {set G}}) (D : {set G}) (x : G) (xD : x \in D) (colP : coloring P D):
  exists C : {set G}, (C \in P) && (x \in C).
Admitted.

Let induced_col' (P : {set {set G}}) (D : {set G}) (x : G) (xD : x \in D) (colP : coloring P D)
    := xchoose (x_in_part xD colP).

Definition induced_col (P : {set {set G}}) (D : {set G}) (x : G) (colP : coloring P D)
    := if @idP (x \in D) is ReflectT p then induced_col' p colP else set0.
*)

Definition induced_col (P : {set {set G}}) (D : {set G}) (x : G) (colP : coloring P D) := pblock P x.

Definition chi_mem (A : mem_pred G) := 
  #|[arg min_(P < trivial_coloring [set x in A] | coloring P [set x in A]) #|P|]|.

Notation "χ( A )" := (chi_mem (mem A)) (format "χ( A )").

Lemma chi_gives_part (D : {set G}) (n : nat) : χ(D) == n -> exists P : {set {set G}},
    coloring P D && (#|P| == n).
Admitted.

Section Basics.

Implicit Types (P : {set {set G}}) (A B C : {set G}).

(** the [sub_partition] is actually a sub_coloring *)
Lemma sub_coloring P D A :
  coloring P D -> A \subset D -> coloring (sub_partition P A) A.
Proof.
case/andP => partP /forall_inP/= stabP subAD; apply/andP;split.
  exact: sub_partitionP.
have/subsetP sub := sub_partition_sub partP subAD.
apply/forall_inP => S {}/sub /imsetP [B BP ->]. 
by apply: sub_stable (stabP _ BP); apply: subsetIl.
Qed.

Variant chi_spec A : nat -> Prop :=
  ChiSpec P of coloring P A & (forall P', coloring P' A -> #|P| <= #|P'|) 
  : chi_spec A #|P|.

(** We can always replace [χ(A)] with [#|P|] for some optimal coloring [P]. *)
Lemma chiP A : chi_spec A χ(A).
Proof.
rewrite /chi_mem; case: arg_minnP; first exact: trivial_coloringP.
by move=> P; rewrite set_mem => ? ?; apply: ChiSpec.
Qed.

Lemma color_bound P A : coloring P A -> χ(A) <= #|P|.
Proof. by move => col_P; case: chiP => P' _ /(_ _ col_P). Qed.

Lemma leq_chi A : χ(A) <= #|A|.
Proof. 
case: chiP => C col_C /(_ _ (@trivial_coloringP A)).
rewrite /trivial_coloring card_imset //. exact: set1_inj.
Qed.

Lemma chi_mono A B : A \subset B -> χ(A) <= χ(B).
Proof.
move=> subAB; case: (chiP B) => P col_P opt_P.
have col_S := sub_coloring col_P subAB.
apply: leq_trans (color_bound col_S) (card_sub_partition _ subAB).
by case/andP : col_P.
Qed.

End Basics.

(** ** End of definition from Christian Dockzal *)


(** ** Definition and Proof of Brook's Theorem from Mauricio Salichs *)


(* Algunos teoremas auxiliares que pueden resultar útiles.
   Ver si ya estan definidos en otro lado y/o reubicar. *)

Lemma chi_components (A : {set G}) : χ(A) = \max_(B in components A) χ(B).
Admitted.

Lemma aux1 (A : {set G}) (x : G) : χ(A :\ x) < χ(A) -> χ(A :\ x) + 1 = χ(A).
Admitted.

Lemma aux2 (a b c : nat) : a + 1 = b -> a <= c -> c < b -> c + 1 = b.
Admitted.

Lemma aux3 : induced [set: G] = G.
Admitted.

(* Fin de teoremas auxiliares *)

Let induced_col_2 (P : {set {set G}}) (D : {set G}) (x y : G) (colP : coloring P D)
    := induced_col x colP :|: induced_col y colP.

Definition is_neigh (S : {set G}) : bool := [exists v : G, N(v) == S].

Definition delta_mem (A : mem_pred G) := 
  #|[arg max_(S > N(somev) | is_neigh S) #|S|]|.

Notation "Δ( A )" := (delta_mem (mem A)) (format "Δ( A )").

Fact delta_max : forall v : G, #|N(v)| <= Δ(G).
Proof.
  rewrite /delta_mem; case: arg_maxnP.
  by apply/existsP; exists somev.
  move=> Nw NwisNeigh Nv v.
  have NvisNeigh: is_neigh N(v) by apply/existsP; exists v.
  by move: (Nv N(v) NvisNeigh).
Qed.

Theorem chi_leq_delta_sub (n : nat) :   (* Brook's Theorem for Subgraphs *)
  (forall A : {set G}, n = #|A| -> (* Tuve que hacer esto para que me saliera la inducción *)
  connected A -> (* G is connected *)
  (exists u v : (induced A), (u != v) /\ ~ (u -- v)) /\  (* G is not a complete graph *)
  ~ (odd #|A| /\ forall v : (induced A), #|N(v)| == 2) -> (* G is not an odd cycle *)
  χ(A) <= Δ(A)).
Proof.
  elim/nat_ind: n. move=> A.
  (* Caso Base *)
  move/eqP; rewrite eq_sym; move/eqP/cards0_eq -> => _ _.
  have aux1: [set x in mem set0] = set0. { admit. }
  have aux2: [set [set x] | x in set0] = set0. { admit. }
  have aux3: [arg min_(P < set0 | coloring P set0) #|P|] = set0. { admit. }
  rewrite /chi_mem aux1 /trivial_coloring aux2 aux3 cards0 //=.
  (*  Paso Inductivo  *)
  move=> n HI J J1; move: (ltn0Sn n); rewrite J1 card_gt0; move/set0Pn=> [x xJ].
  set H := J :\ x.
  move: (cardsD1 x J); rewrite xJ -J1; move/eqP; rewrite add1n eqSS; move/eqP; rewrite -/H=> Hn.
  move: (HI H Hn)=> HI2 connJ [not_complete not_oddcycle].
  rewrite leqNgt; apply/contraT; move/negPn=> CR.
  set compH := components H.
  (* Para cada componente conexa de H, su numero cromatico es menor al delta de J *)
  have chiH'_leq_deltaJ : forall H' : {set G}, H' \in compH -> χ(H') <= Δ(J). {admit. }
  (* El numero cromatico de H es menor al delta de J *)
  have chiH_leq_deltaJ : χ(H) <= Δ(J). {admit. }
  (* Si el numero cromatico aumenta agregando el vertice x, entonces deg(x) = Δ(J) *)
  have degx_eq_delta : χ(J :\ x) < χ(J) -> #|N(x)| = Δ(J). {
    move/aux1=> chiH_leq_chiJ. move: (aux2 chiH_leq_chiJ chiH_leq_deltaJ CR).  }
  (* Y con esto podemos afirmar que #|N(x)| = Δ(J) *)
  move: (degx_eq_delta (leq_ltn_trans chiH_leq_deltaJ CR)).

  (* Arranca la parte difícil... *)

  (* Vamos a trabajar con este coloreo *)
  move: (chi_gives_part (eqxx χ(H))) => [P /andP [colPH card_PH]].
  (* induced_col_2 toma dos vértices y devuelve el subgrafo inducido por
   * los vertices coloreados igual a esos dos vértices. *)

  (* 1. Para todos dos vértices vecinos de x, estos recaen en la misma componente
   * conexa de Hij, donde Hij = induced_col_2 i j *)
  have ij_conn (i j : G) : i \in N(x) -> j \in N(x) ->
    connect (restrict (induced_col_2 i j colPH) sedge) i j.
    (*exists C : {set G}, C \subset (induced_col_2 i j colPH) ->
    i \in C /\ j \in C /\ connected C.*) {admit. }

  (* Acá habría que buscar la manera de obtener un objeto Cij para i,j
   * podríamos caracterizar con "induced_comp i j" a este conjunto.
   * Falta arreglar los dos sublemas que siguen.... *)

  (* 2. Esta componente conexa es un path entre i y j *)
  have ij_conn (i j : G) : 
    {in (induced_comp i j colPH)&,
     forall a b, nodes (Path a b) = nodes (Path i j)} . {admit. }

  (* 3. Para vertices i,j,k, los paths Cij y Cik solo coinciden en i *)
  have ijk_join_i (i j k : G) : i \in N(x) -> j \in N(x) -> k \in N(x) ->
    (induced_comp i j colPH) :&: (induced_comp i k colPH) = [set i].
Admitted.

Theorem chi_leq_delta :   (* Brook's Theorem *)
  connected [set: G] -> (* G is connected *)
  ~ (clique [set: G]) /\  (* G is not a complete graph *)
  ~ (odd #|G| /\ forall v : G, #|N(v)| == 2) -> (* G is not an odd cycle *)
  χ(G) <= Δ(G).
Proof.
  move: (@chi_leq_delta_sub #|[set: G]| [set: G] (erefl #|[set: G]|)).
  rewrite aux3. (* Falta demostrar que χ(G) = χ([set: G]) (análogo Δ) *)
Admitted.

(** ** End of Brook's Theorem from Mauricio Salichs *)

End ColoringBasics.

End GraphColoring.
