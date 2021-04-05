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

Definition chi_mem (A : mem_pred G) := 
  #|[arg min_(P < trivial_coloring [set x in A] | coloring P [set x in A]) #|P|]|.

Notation "χ( A )" := (chi_mem (mem A)) (format "χ( A )").

Lemma chi_gives_part (D : {set G}) (n : nat) : χ(D) == n -> exists P : {set {set G}},
    coloring P D /\ (#|P| == n) /\ forall P' : {set {set G}}, coloring P' D -> #|P| <= #|P'|.
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

(* Esto debería estar en sgraph *)

Definition component_of' (A : {set G}) (x : G) := pblock (components A) x.

Lemma in_component_of' (A : {set G}) (x : G) : x \in A -> x \in component_of' A x.
Proof. move=> xA. rewrite mem_pblock. Admitted.

Lemma component_of_components' (A : {set G}) (x : G) : x \in A ->
  component_of' A x \in components A.
Proof. move=> xA. rewrite pblock_mem //. Admitted.

Lemma connected_component_of' (A : {set G}) (x : G) : connected (component_of' A x).
Admitted.

Lemma in_component_sub (A : {set G}) (x y : G) :
   y \in (component_of' A x) -> y \in A.
Admitted.

(* Algunas definiciones y teoremas auxiliares que pueden resultar útiles.
   Ver si ya estan definidos en otro lado y/o reubicar. *)

Lemma col_neigh (P : {set {set G}}) (A : {set G}) (x y : G) :
  coloring P A -> y \in N(x) -> y \notin pblock P x.
Admitted.

Lemma col_neigh' (P : {set {set G}}) (A : {set G}) (x y z : G) : (* Ver de descartar y usar solo el de arriba *)
  coloring P A -> y \in N(x) -> x \in pblock P z -> y \notin pblock P z.
Admitted.

Definition is_path_of (S : {set G}) (x y : G) :=
  unique (fun p : Path x y => (S \subset p) /\ (p \subset S)).

Definition same_col (A : {set G}) (P : {set {set G}}) (x y : G) (colPA : coloring P A) :=
  y \in pblock P x.

(* change_col debe intercambiar de subconjunto en la partición a todos los elementos de C.  
 * En C habrá vértices que corresponderán a DOS subconjuntos de la partición P.
 * Deben intercambiarse entre ellos en P y devolver una nueva partición.
 * Averiguar si es necesario definir esta operación. *)


Let ch_part_v (P : {set {set G}}) (A : {set G}) (x y : G) :=
(* Movemos x de su conjunto dentro de la partición, y lo colocamos en el mismo que y *)
  (pblock P x :\ x) |: ((x |: pblock P y) |: (P :\ (pblock P x) :\ (pblock P y))).

Fact ch_part_1 (A : {set G}) (P : {set {set G}}) (x y : G) (xA : x \in A) (yA : y \in A) :
  partition P A -> partition (ch_part_v P A x y) A.
Admitted.

Fact ch_part_2 (A : {set G}) (P : {set {set G}}) (x y : G) (xA : x \in A) (yA : y \in A) :
    partition P A -> x \in pblock (ch_part_v P A x y) y.
Admitted.

Fact ch_part_3 (A : {set G}) (P : {set {set G}}) (x y : G) :
    [forall S in P, stable S] -> [forall y' in pblock P y, ~~ (x -- y')]
    -> [forall S in (ch_part_v P A x y), stable S].
Admitted.

Let nds (A B : {set G}) := (A :&: B == set0) || (A \subset B).
Let dif_sym' (A B : {set G}) := if (nds A B) then B else (A :\: B) :|: (B :\: A).
Definition change_part (P : {set {set G}}) (C : {set G}) := (*map (dif_sym' C) *)P.
(*seq_sub (map (dif_sym C) (enum P))*)

Fact ch_part_C_1 (P : {set {set G}}) (A : {set G}) (partPA : partition P A) (C : {set G}) (x y z : G) :
  x \in A -> y \in A -> z \in A -> x \in C -> y \in C -> z \notin C ->
  pblock P x != pblock P y -> pblock P y == pblock P z -> x \in pblock (change_part P C) z.
Admitted. (* Un poco rebuscado *)

Fact ch_part_C_2 (P : {set {set G}}) (A : {set G}) (partPA : partition P A) (C : {set G}) (x y : G) :
  x \notin C -> y \notin C -> y \in pblock P x -> y \in pblock (change_part P C) x.
Admitted.

Lemma chi_components (A B : {set G}) : χ(A) = \max_(B in components A) χ(B).
Admitted.

Lemma components_def (X Y : {set G}):
  Y \in components X -> Y \subset X /\ connected Y.
Admitted.

Lemma components_sub_v (A : {set G}) (v : G) : connected A -> v \in A ->
    forall B : {set G}, B \in components (A :\ v) -> exists2 w : G, w \in B & w -- v.
Admitted.

Lemma chi_del_x (A : {set G}) (x : G) : χ(A :\ x) < χ(A) -> χ(A :\ x).+1 = χ(A).
Admitted.

Lemma conn_dif (A : {set G}) (x y : G) : connected A -> x \in A -> y \in A ->
    x != y -> ~~ (x -- y) -> [exists z in A, x -- z && (z != y)].
Admitted.

Lemma ind_G : induced [set: G] = G. (*  Este lema no funciona   *)
Admitted.

Lemma strong_ind (P : nat -> Prop) :
  P 0 -> (forall k, (forall l, (l <= k) -> P l) -> P (S k)) -> (forall n, P n).
Admitted.

Lemma max_leq_n (T : finType) (n : nat) (A : {set {set T}}) (F : {set T} -> nat) :
    \max_(x in A) F x <= n <-> forall x : {set T}, x \in A -> F x <= n.
Admitted.

Lemma setISP (T : finType) (X Y Z : {set T}) : 
   (exists2 x : T, x \in Z :&: Y & x \notin X) -> X \proper Y -> Z :&: X \proper Z :&: Y.
Admitted.

Lemma aux (a b c : nat) : a.+1 = b -> a <= c -> c < b -> c.+1 = b.
Proof.
  move <-; rewrite ltnS=> ? ?; have: a <= c <= a by apply/andP; split.
  by rewrite -eqn_leq; move/eqP ->.
Qed.

Lemma set2cond (T : finType) (a b : T) (P : T -> T -> bool):
  P a b /\ P b a -> [forall x in [set a; b], forall y in [set a; b], (x != y) ==> P x y].
Proof.
  move=> [Pab Pba]. 
  apply/forallP=> x; apply/implyP. rewrite in_set2; move/orP; case; move/eqP ->.
  all: (apply/forallP=> y; apply/implyP; rewrite in_set2; move/orP; case; move/eqP ->).
  all: by apply/implyP; move/negP.
Qed.

Lemma aux1 (m n : nat) : m < n -> 0 < n.
Admitted.

Lemma aux2 (n m : nat) : 0 < n -> 0 < m -> n < m -> n.-1 < m.-1.
Admitted.

Lemma cards_n (T : finType) (C : {set T}) (n : nat) :
    0 < n -> n < #|C| -> exists2 x : T, x \in C & (n.-1) < #|C :\ x|.
Proof.
  move=> ng0 cAgn. move: (ltn_trans ng0 cAgn); rewrite card_gt0; move/set0Pn.
  elim=> [x xC]. exists x. by []. move: cAgn. rewrite (cardsD1 x C) addnC xC addn1 //=.
  by move: (aux2 ng0 (ltn0Sn #|C :\ x|)).
Qed.

Lemma cards_n_sub (T : finType) (C : {set T}) (n : nat) (x : T) :
    0 < n -> n < #|C| -> x \in C -> (n.-1) < #|C :\ x|.
Admitted.

Lemma in_comp (A : {set G}) (x : G) : x \in A ->
  (pblock (components A) x) != [set x] -> exists y : G, y \in A /\ y -- x.
Proof.
  (* x \in A  <-> (pblock (components A) x) != set0 *)
Admitted.

Lemma in_comp_N (A : {set G}) (x : G) : x \in A ->
  (pblock (components A) x) == [set x] -> forall y : G, y \in A -> ~~ (x -- y).
Admitted.

Lemma in_comp_2 (A : {set G}) (x y : G) : x \in A -> y \in A -> y -- x ->
  y \in pblock (components A) x.
Admitted.

Lemma dif_col (P : {set {set G}}) (A : {set G}) (col : coloring P A) (x y : G) :
    x \in A -> y \in A -> y -- x -> pblock P x != pblock P y.
Admitted.

Lemma cover_comp (A : {set G}) : cover (components A) = A.
Admitted.

Lemma in_part_pblock (P : {set {set G}}) (A : {set G}) (x y : G) :
    partition P A -> x \in pblock P y -> x \in A.
(* preim_partition_pblock. *)
Admitted.

Lemma in_2_pblock (P : {set {set G}}) (x y : G) :
    trivIset P -> y != x -> pblock P x :&: pblock P y = set0.
Admitted.

Lemma union_bij_proofR (A B : {set G}) (x : G) : x \in A -> x \in B :|: A.
Proof. apply/subsetP. exact: subsetUr. Qed.

Lemma trans_pblock (P : {set {set G}}) (x y z : G) :
    x \in pblock P z -> y \in pblock P z -> x \in pblock P y.
Admitted.

Lemma trans_n_pblock (P : {set {set G}}) (x y z : G) :
    x \in pblock P z -> y \notin pblock P z -> x \notin pblock P z.
Admitted.

Lemma xxx (T : finType) (x y : T) : (x == y) = false -> x != y. (* Esto ya debería existir... *)
Proof. move=> H. apply/contraT. by rewrite negbK H. Qed.

Lemma yyy (T : finType) (x y : T) : (x != y -> false) -> x == y.
Proof. move=> H. apply/contraT. by []. Qed.

(* Fin de teoremas auxiliares *)



(* Definción de Delta sobre un conjunto de vértices. *)

Definition sub_neigh (A : {set G}) (v : G) := N(v) :&: A.

Fact sub_neigh_compl (A : {set G}) (v : G) : N(v) = sub_neigh A v :|: sub_neigh (~: A) v.
Admitted.

Definition has_neigh (A : {set G}) (S : {set G}) : bool := [exists v : G, (sub_neigh A v) == S].

Definition delta_mem (A : {set G}) := 
  #|[arg max_(S > set0 | has_neigh A S) #|S|]|.

Notation "Δ( A )" := (delta_mem A) (format "Δ( A )").

Lemma leq_delta C : Δ(C) <= #|C|. (* Esto vale? *)
Admitted.

Fact delta_max (A : {set G}) : forall v : G, v \in A -> #|sub_neigh A v| <= Δ(A).
Admitted.

Fact delta_sub (A : {set G}) : forall B : {set G}, B \subset A -> Δ(B) <= Δ(A).
Admitted.

Lemma chi_set0 : χ(set0) = 0.
Proof. apply/eqP; move: (leq_chi set0); by rewrite cards0 leqn0. Qed.

Lemma delta_set0 : Δ(set0) = 0.
Proof. apply/eqP; move: (leq_delta set0); by rewrite cards0 leqn0. Qed.

Lemma clique_delta (A : {set G}) (x : G) : connected A -> cliqueb (sub_neigh A x) ->
  #|(sub_neigh A x)| = Δ(A) -> cliqueb A.
Admitted.

Lemma neigh_chi (A : {set G}) (x : G) : #|sub_neigh A x| < χ(A :\ x) -> χ(A) = χ(A :\ x).
Admitted.

Lemma chi_neigh (A : {set G}) (x : G) : χ(A :\ x) < χ(A) -> #|sub_neigh A x| = χ(A :\ x) ->
   forall P : {set {set G}}, coloring P (A :\ x) ->
  (forall y z : G, y != z -> y \in sub_neigh A x -> z \in sub_neigh A x -> y \notin pblock P z).
Admitted.

Lemma conn0 (A : {set G}) : connected A -> Δ(A) = 0 -> A = set0.
Admitted.

Lemma conn1 (A : {set G}) : connected A -> Δ(A) = 1 -> exists x y : G, A = [set x;y] /\ (x -- y).
Admitted.

Lemma sn_1 (A: {set G}) : forall z : G, connected A -> (exists x y : G, x != y /\
  x \in A /\ y \in A) -> 0 < #|sub_neigh A z|.
Admitted.

Lemma sn_2 (A: {set G}) (x : G) : #|sub_neigh A x| == 2 -> exists y z : G, y != z /\
    y \in sub_neigh A x /\ z \in sub_neigh A x.
Admitted.

(* Sublemas y definiciones preliminares el Teorema de Brooks *)

Lemma neq_cols (P : {set {set G}}) (A : {set G}) (x y : G) (partPA : partition P A) :
    (x \in pblock P y) -> (repr_class P x == repr_class P y).
Proof. by move/andP: partPA=> [_ /andP [tr _]]; rewrite /repr_class; move/(same_pblock tr) ->. Qed.

Let qty_cols (P : {set {set G}}) (A : {set G}) (x : G) := \bigcup_(x in sub_neigh A x) [set (repr_class P x)].

Fact max_dif_cols (P : {set {set G}}) (A : {set G}) (colPA : coloring P A) :
    [forall x in A, #|qty_cols P A x| <= #|P|].
Admitted.

Fact ch_col_aux (P : {set {set G}}) (A : {set G}) (colPA : coloring P A) (x : G) (xA : x \in A) :
    forall x1 x2 x3 x4 : G, #|[set x1; x2; x3; x4] :&: sub_neigh A x| = 4 ->
    x1 \in pblock P x2 -> x3 \in pblock P x4 -> #|qty_cols P A x| < #|P| - 1.
Admitted.

Fact ch_col_dif (P : {set {set G}}) (A : {set G}) (colPA : coloring P A) (x : G) (xA : x \in A) :
    #|qty_cols P A x| < #|P| - 1 -> exists y : G, (y \in A) && (y \notin pblock P x)
    && (coloring (ch_part_v P A x y) A).
(* repr_class P y \notin dif_cols P A x *)
Admitted.

Let pblockU (A : {set G}) (P : {set {set G}}) (x y : G) (colP : coloring P A)
    := pblock P x :|: pblock P y.

Fact pblockU_subset (A : {set G}) (P : {set {set G}}) (x y : G) (colP : coloring P A) :
    pblockU x y colP \subset A.
Admitted.

Fact coloring_ch_col_1 (A : {set G}) (x y : G) (P : {set {set G}}) (colP: coloring P A)
                       (xA : x \in A) (yA : y \in A)  :
  [forall v in pblock P y, ~~ (v -- x)] -> coloring (ch_part_v P A x y) A.
Proof.
  move/andP: colP=> [partP stabP] stabY. apply/andP; split. apply ch_part_1.
  all: try by rewrite (cover_partition partP). by [].
Admitted.

Fact coloring_ch_col_2 (A B : {set G}) (x y : G) (P : {set {set G}}) (colP: coloring P A) :
  B \in components (pblockU x y colP) -> coloring (change_part P B) A.
Admitted.


(* Previous Lemma: if A clique, χ = Δ + 1 and every vertex has maximum degree in A *)
Lemma clique_br : forall A : {set G}, cliqueb A ->
  [forall v in A, (#|sub_neigh A v| == Δ(A))] && (χ(A) == 1 + Δ(A)).
Admitted.

(* Previous Lemma: if A odd cycle, χ = Δ + 1 and every vertex has maximum degree in A *)
Lemma odd_cycle_br (A : {set G}) : odd #|A| && [forall v in A, #|sub_neigh A v| == 2] ->
    [forall v in A, (#|sub_neigh A v| == Δ(A))] && (χ(A) == 1 + Δ(A)).
Admitted.

Lemma clique_or_odd_cycle_br (A : {set G}) : cliqueb A \/ (odd #|A| && [forall v in A, #|sub_neigh A v| == 2])
      -> [forall v in A, (#|sub_neigh A v| == Δ(A))] && (χ(A) == 1 + Δ(A)).
Proof. case. exact: clique_br. exact: odd_cycle_br. Qed.

Theorem chi_leq_delta_sub (n : nat) :   (* Brook's Theorem for Subgraphs *)
  (forall A : {set G}, n == #|A| ->
  connected A -> (* A is connected *)
  ~ (cliqueb A) ->  (* A is not a complete graph *)
  ~ (odd #|A| && [forall v in A, #|sub_neigh A v| == 2]) -> (* A is not an odd cycle *)
  χ(A) <= Δ(A)).
Proof.
  elim/strong_ind: n. move=> A.

  (* Base Step *)

  rewrite eq_sym; move/eqP/cards0_eq -> => _ _ _.
  by rewrite chi_set0 delta_set0.

  (*  Inductive Step  *)

  (* Starting definitions... *)
  move=> n HI J /eqP Jn connJ not_clique not_oddc.
  move: (ltn0Sn n); rewrite Jn card_gt0; move/set0Pn=> [x xJ].
  set H := J :\ x.
  have/subsetP NxsubH : sub_neigh J x \subset H. {
    apply/subsetP=> v; move/setIP=> [vNx vJ].
    apply/setD1P; split => [|//].
    by apply/xxx/sg_edgeNeq; rewrite sg_sym -in_opn.
  }
  move: (cardsD1 x J). rewrite xJ -Jn; move/eqP; rewrite add1n eqSS; move/eqP; rewrite -/H=> Hn.
  rewrite leqNgt; apply/contraT; move/negPn=> CR.

  (* For every H' connected component of H, χ(H') <= Δ(J) *)
  have chiH'_leq_deltaJ : forall H' : {set G}, H' \in components H -> χ(H') <= Δ(J). {
    move=> H' H'compH; move: (H'compH); move=> /components_def [H'subH connH'].
    have pH'J := sub_proper_trans H'subH (properD1 xJ).
    have H'leqH : #|H'| <= n by rewrite Hn; apply subset_leq_card.

    (* Case 1: H' is clique or odd cycle *)
    case: (boolP (cliqueb H' || odd #|H'| && [forall v in H', #|sub_neigh H' v| == 2])).
    move/orP/clique_or_odd_cycle_br/andP=> [/forallP all_delta /eqP ->].
    have [v vH' vadjx] := components_sub_v connJ xJ H'compH.
    move/implyP: (all_delta v)=> aux. move/eqP: (aux vH') <-.
    have NvinH'_l_NvinJ : 1 + #|sub_neigh H' v| <= #|sub_neigh J v|. {
      rewrite add1n; apply/proper_card.
      have NvneqH: (exists2 x : G, x \in N(v) :&: J & x \notin H').
      { exists x. apply/setIP; split=> [|//=]; by rewrite in_opn.
        apply/contraT; rewrite negbK=> xH'.
        move/subsetP: (H'subH). move=> sH'H. move: (sH'H x xH').
        by rewrite /H setD11.  }
      exact: setISP NvneqH pH'J.
    }
    move/subsetP: (proper_sub pH'J)=> sH'J.
    exact: leq_trans NvinH'_l_NvinJ (delta_max (sH'J v vH')).

    (* Case 2: H' is none of them *)
    move/norP=> [/negP not_cliqueH' /negP not_oddcH'].
    have trans_1 := (HI #|H'| H'leqH H' (eqxx #|H'|) connH' not_cliqueH' not_oddcH').
    have trans_3 := (delta_sub (subD1set J x)); rewrite -/H in trans_3.
    exact: (leq_trans (leq_trans trans_1 (delta_sub H'subH)) trans_3).
  }

  (* Some equalities and inequalities... *)
  have χH_leq_ΔJ : χ(H) <= Δ(J). rewrite chi_components. by rewrite max_leq_n. by [].
  move: (leq_ltn_trans χH_leq_ΔJ CR); move/chi_del_x=> χH_leq_χJ.
  move: (aux χH_leq_χJ χH_leq_ΔJ CR).
  rewrite -χH_leq_χJ; move/eqP; rewrite eqSS=>/eqP ΔJ_eq_χH.
  move: (leq_ltn_trans χH_leq_ΔJ CR)=> χH_l_χJ.
  (* ...to prove that #|N(x)| = Δ(J) *)
  have/eqP Nx_eq_ΔJ : #|sub_neigh J x| == Δ(J). {
    rewrite eqn_leq. apply/andP; split. by exact: delta_max xJ.
    rewrite ΔJ_eq_χH.
    apply contraT; rewrite -ltnNge. move/neigh_chi; rewrite -χH_leq_χJ -add1n.
    rewrite -[in RHS](add0n χ(J :\ x)); move/eqP; by rewrite eqn_add2r.
  } move: (ΔJ_eq_χH); rewrite -Nx_eq_ΔJ=> Nx_eq_χH.

  (* Probamos que Δ(J) >= 3 mostrando los casos para Δ(J) = 0,1,2 *)
  case (boolP (Δ(J) <= 2)).
  rewrite leq_eqVlt; move/orP; case. (* Caso para Δ(J) = 2 *)
  {admit. }
  rewrite ltnS leq_eqVlt ; move/orP; case. (* Caso para Δ(J) = 1 *)
  { move/eqP=> ΔJ1. move: (conn1 connJ ΔJ1)=> [a [b [Jab ab]]].
    move/negP: not_clique; rewrite /cliqueb. apply contraR=> _.
    by rewrite Jab; apply/set2cond; split=> [//=|]; rewrite sg_sym. }
  rewrite ltnS leq_eqVlt ; move/orP; case. (* Caso para Δ(J) = 0 *)
  { by move/eqP=> ΔJ0; rewrite (conn0 connJ ΔJ0) in_set0 in xJ. }
  by []. rewrite -ltnNge -Nx_eq_ΔJ=> NJx_geq_2.

  (* 1. Para todo coloreo en H con a,b en N(x), col(a) != col(b) *)
  have dif_col_Nx (P : {set {set G}}) (colP : coloring P H) (i j : G) (ineqj : i != j)
  (iX : i \in sub_neigh J x) (jX : j \in sub_neigh J x) := chi_neigh χH_l_χJ Nx_eq_χH colP ineqj iX jX.

  pose C (P : {set {set G}}) (colP : coloring P H) (i j : G) := component_of' (pblockU i j colP) i.

  (* 2. Para todos dos vértices vecinos de x, estos recaen en la misma componente
   * conexa de Hij, donde Hij = pblockU i j colP *)
  have ij_conn (P : {set {set G}}) (colP : coloring P H) (i j : G) (ineqj: i != j)
               (iX : i \in sub_neigh J x) (jX : j \in sub_neigh J x) : j \in C P colP i j. {
    move/andP: (colP)=> [partP stabP]. move/andP: (partP)=> [_ /andP [trivP _]].
    have jH := NxsubH i iX. have iH := NxsubH j jX.
    have iijcol : i \in pblockU i j colP. {
      rewrite in_setU; apply/orP/or_introl.
      by rewrite mem_pblock (cover_partition partP).
    }
    have xneqi : pblock (components (pblockU i j colP)) i != [set i]. {
      apply contraT; rewrite negbK=> is_sing.
      set P'H := ch_part_v P H i j.
      have colP'H : coloring P'H H. {
        apply/andP; split. by apply ch_part_1.
        apply/(ch_part_3 H stabP)/contraT.
        move/forall_inPn=> [j' j'colPHj /negbNE iadjj'].
        move/(union_bij_proofR (pblock P i)): (j'colPHj)=> j'colPHji.
        by move: (in_comp_N iijcol is_sing j'colPHji); apply contraR=> _.
      }
      move: (ch_part_2 jH iH partP)=> ?. move: (dif_col_Nx P'H colP'H i j ineqj iX jX).
      by apply contraR=> _.
    }
    move: (in_comp iijcol xneqi)=> [k [kijcol kadji]].
    have kCompi := in_comp_2 iijcol kijcol kadji. rewrite -in_opn in kadji.
    have knPi : pblock P i != pblock P k. {admit. }
      (*Check col_neigh colP kadji.*)
    have/eqP kPj : pblock P k = pblock P j.
      rewrite in_setU in kijcol. case/orP: kijcol.
      by move/(same_pblock trivP)/eqP; rewrite eq_sym; apply/contraTeq=> _.
      by apply/same_pblock.
    apply contraT=> jnPi.
    set P'H := change_part P (pblock (components (pblockU i k colP)) i).
    rewrite in_setU in kijcol.
    have kH : k \in H by case/orP: kijcol; exact: in_part_pblock partP.
    have iP' : i \in cover (components (pblockU i j colP)) by rewrite cover_comp.
    have iP'' : i \in pblock (components (pblockU i j colP)) i by rewrite mem_pblock.
    have colP'H : coloring P'H H by move: (coloring_ch_col_2 (pblock_mem iP')); rewrite //=.
    move: (ch_part_C_1 partP jH kH iH iP'' kCompi jnPi knPi kPj).
    apply contraLR=> _. exact: (dif_col_Nx P'H colP'H i j ineqj iX jX).
  }

  (* 3. Esta componente conexa es un path entre i y j *)
  have C_is_path (P : {set {set G}}) (colP : coloring P H) (i j : G) (ineqj: i != j)
                        (iX : i \in sub_neigh J x) (jX : j \in sub_neigh J x) :
    #|sub_neigh (C P colP i j) i| == 1 /\ #|sub_neigh (C P colP i j) j| == 1 /\
    forall v : G, v \in (C P colP i j) -> v != i -> v != j -> #|sub_neigh (C P colP i j) v| == 2.
  {
    split. rewrite eqn_leq; apply/andP; split. apply/contraT.
    rewrite -ltnNge. {admit. } (* Si tiene mas de un vecino, tienen el mismo color.
    Como N(i) <= Δ-1, se puede recolorear i, teniendo mismo color que j -> Absurdo. *)
    have connC : connected (C P colP i j). {admit. } (* Sale facil usando connected_component_of' *)
    apply/(sn_1 i connC).
    exists i. exists j. split. by []. split. {admit. } {admit. } (* Fáciles *)
    split. {admit. } (* Sale fácil demostrando que (C P colP i j) = (C P colP j i) *)
    move=> v vinC vneqi vneqj. rewrite eqn_leq; apply/andP; split.
    {admit. } (*Si tiene 3 vertices vecinos, todos estan coloreados iguales, .... *)
    {admit. } (* Si todos tienen solo un vecino, no hay manera de conectar i con j *)
  }

  have v_in_C2 (P : {set {set G}}) (colP : coloring P H) (i j u v : G) :
    v \in sub_neigh (C P colP i j) u -> u \in pblock P i -> v \in pblock P j.
  {
    move/setIP=> [vNu /in_component_sub vCij] uPi. move: (col_neigh' colP vNu uPi).
    rewrite in_setU in vCij. case/orP: vCij. move=> h1 /negbTE h2. 
    by rewrite h2 in h1. by move=> ? _.
  }

  (* 4. Para vertices i,j,k, los paths Cij y Cik solo coinciden en i *)
  have ijk_join_i (P : {set {set G}}) (colP : coloring P H) (i j k : G) (ineqj : i != j) (ineqk : i != k) (jneqk : j != k)
                  (iX : i \in sub_neigh J x) (jX : j \in sub_neigh J x) (kX : k \in sub_neigh J x) :
  (C P colP i j) :&: (C P colP i k) \subset [set i].
  {
    move/andP: (colP)=> [partP _]. move/andP: (partP)=> [covP /andP [trivP nP0]].
    apply/subsetP=> u. move/setIP=> [u_ij u_ik].
    rewrite in_set1; apply/contraT=> uneqi.
    (* Probamos que u es distinto que j (análogo k) *)
    have uneqj : u != j. {admit. }  have uneqk : u != k. {admit. }
    (* Probamos que u tiene mismo color que i *)
    have ucoli : u \in pblock P i. {
      move/in_component_sub: (u_ij); rewrite in_setU; case/orP. by [].
      move/in_component_sub: (u_ik); rewrite in_setU; case/orP. by [].
      move=> H1 H2. move/setIP: (conj H1 H2).
      by rewrite (in_2_pblock trivP jneqk) in_set0.
    }

    have [NCij_i [NCij_j NCij_v]] := C_is_path P colP i j ineqj iX jX.
    move/sn_2: (NCij_v u u_ij uneqi uneqj)=> [uj1 [uj2 [uj1nuj2 [uj1NCij uj2NCij]]]].
    (* Probamos que u tiene dos vecinos con color j *)
    have uj1Pj := v_in_C2 P colP i j u uj1 uj1NCij ucoli.
    have uj2Pj := v_in_C2 P colP i j u uj2 uj2NCij ucoli.

    have [NCik_i [NCik_k NCik_v]] := C_is_path P colP i k ineqk iX kX.
    move/sn_2: (NCik_v u u_ik uneqi uneqk)=> [uk1 [uk2 [uk1nuk2 [uk1NCik uk2NCik]]]].
    (* Probamos que u tiene dos vecinos con color k *)
    have uk1Pk := v_in_C2 P colP i k u uk1 uk1NCik ucoli.
    have uk2Pk := v_in_C2 P colP i k u uk2 uk2NCik ucoli.

    (* y despues... *)
    have uH : u \in H. {admit. }
    have [_ uj1Cij] := setIP uj1NCij. have [_ uj2Cij] := setIP uj2NCij.
    have [_ uk1Cik] := setIP uk1NCik. have [_ uk2Cik] := setIP uk2NCik. 
    have all_dif : #|[set uj1; uj2; uk1; uk2] :&: sub_neigh H u| = 4. {admit. }
    move: (ch_col_aux colP uH all_dif (trans_pblock uj1Pj uj2Pj) (trans_pblock uk1Pk uk2Pk))=> xd.
    move: (ch_col_dif colP uH xd)=> [y/andP[/andP[yH ynPu]colP']].
    (* Ahora demostramos que teniendo u un color disinto a i ó j, no se cumple (2) en él.
     * Es decir, tenemos que mostrar que el nuevo color de u "corta" al camino Cij. *)
    
  }


  (* 5. Existen dos vertices vecinos de x que no son adyacentes. *)
  have : ~~ cliqueb (sub_neigh J x).
  {
    apply/contraT; rewrite negbK=> cliqueNJx.
    move: (aux1 NJx_geq_2); rewrite card_gt0; move/set0Pn=> [y yNJx].
    by move: (clique_delta connJ cliqueNJx Nx_eq_ΔJ).
  }
  move/forall_inPn=> [x1 x1Hx]. move/forall_inPn=> [x2 x2Hx].
  rewrite negb_imply; move/andP=> [x1neqx2 x1nadjx2]. rewrite eq_sym in x1neqx2.
  move/setD1P: (conj x1neqx2 x2Hx)=> x2Hxsx1. rewrite eq_sym in x1neqx2.
  move: (cards_n_sub (ltn0Sn 0) (cards_n_sub (ltn0Sn 1) NJx_geq_2 x1Hx) x2Hxsx1).
  rewrite card_gt0; move/set0Pn=> [x3]. rewrite !in_setD1=> /andP [x3neqx2 /andP [x3neqx1 x3Hx]].

  (* We are going to work with this colour partitions *)
  move: (chi_gives_part (eqxx χ(J))) => [PJ [colPJ [card_PJ chi_defJ]]].
  move: (chi_gives_part (eqxx χ(H))) => [PH [colPH [card_PH chi_defH]]].
  move/andP: (colPH)=> [partPH stabP]. move/andP: (partPH)=> [_ /andP [trivP _]].

  (* Construímos el vértice u, vecino de x1 en C12, que tiene mismo color que x2 *)
  pose C12 := C PH colPH x1 x2.
  have x1C12 : x1 \in C12.
    rewrite mem_pblock cover_comp in_setU. apply/orP/or_introl.
    rewrite mem_pblock (cover_partition partPH). exact: NxsubH x1 x1Hx.
  have x2C12 := ij_conn PH colPH x1 x2 x1neqx2 x1Hx x2Hx. rewrite -/C12 in x2C12.
  have connC12 : connected C12 by exact: connected_component_of'.
  have/existsP [u /andP[uC12/andP[x1adju uneqx2]]] := conn_dif connC12 x1C12 x2C12 x1neqx2 x1nadjx2.
  rewrite -in_opn in x1adju.
  have uCx2 : u \in pblock PH x2. case/in_component_sub/setUP: (uC12).
    by move/negbTE: (col_neigh colPH x1adju) ->. by [].

  (* Definimos una nueva partición P' que da lugar a un nuevo coloreo colP'H,
   * donde solo intercambiamos de conjunto en la partición a los vértices de C{i,j} *)
  have x1_triv : x1 \in (pblockU x1 x3 colPH).
    rewrite in_setU. apply/orP/or_introl.
    rewrite mem_pblock (cover_partition partPH). exact: NxsubH x1 x1Hx.
  pose C13 := C PH colPH x1 x3.
  have C13_triv : C13 \in components (pblockU x1 x3 colPH) by exact: (component_of_components' x1_triv).
  pose P' := change_part PH C13.
  have colP'H : coloring P' H by exact: (coloring_ch_col_2 C13_triv).

  (* As a neighbour of x1 = x'3 , our vertex u now lies in C'{x2,x3} *)
  have u_inC'23 : u \in (C P' colP'H x2 x1). {
    apply/contraT; rewrite /C.
  }

  (* By (4) for P, however, the path C{1,2} - x1 retained its original colouring, so u ∈ [C{1,2} - x] ⊆ C'{1,2} *)
  have u_inC'12 : u \in (C P' colP'H x3 x2) :\ x3. {admit. }

  (* Hence u ∈ C'{2,3} ∩ C'{1,2}, contradicting (4) for P'. *)
  have: u \in (C P' colP'H x2 x3) :&: (C P' colP'H x2 x1)
    by apply/setIP; split => [|].
  rewrite (ijk_join_i P' colP'H x2 x3 x1 x2Hx x3Hx x1Hx P' colP'H) in_set1.
  by move/eqP=> ueqx1; move: uneqx1; apply/contra_neqT.
Admitted.

Theorem chi_leq_delta :   (* Brook's Theorem *)
  connected [set: G] -> (* G is connected *)
  ~ (cliqueb [set: G]) /\  (* G is not a complete graph *)
  ~ (odd #|[set: G]| /\ forall v : G, #|N(v)| == 2) -> (* G is not an odd cycle *)
  χ(G) <= Δ(G).
Proof.
  move: (@chi_leq_delta_sub #|[set: G]| [set: G] (erefl #|[set: G]|)).
  rewrite ind_G. (* Falta demostrar que χ(G) = χ([set: G]) (análogo Δ) *)
Admitted.

(** ** End of Brook's Theorem from Mauricio Salichs *)

End ColoringBasics.

End GraphColoring.
