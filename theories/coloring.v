From mathcomp Require Import all_ssreflect.
Require Import preliminaries bij digraph sgraph dom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Preliminaries *)

(** sets *)

Lemma set_mem (T : finType) (A : {set T}) : [set x in mem A] = A.
Proof. by apply/setP => ?; rewrite inE. Qed.

Lemma setDK (T : finType) (A B : {set T}) : B \subset A -> (A :\: B :|: B) = A.
Proof. 
by move => subBA; rewrite setDE setUIl (setUidPl subBA) setUC setUCr setIT.
Qed.

(* already in mathcomp, but with a longer proof *)
Lemma setD1K (T : finType) (a : T) (A : {set T}) : a \in A -> a |: A :\ a = A.
Proof. by move=> aA; rewrite setUC setDK // sub1set. Qed.

(** dom.v *)

Lemma stable1 (G : sgraph) (x : G) : stable [set x].
Proof. by apply/stableP => ? ? /set1P -> /set1P ->; rewrite sgP. Qed.

(* TOTHINK: do we need that [hereditary] is a boolean predicate? *)
Lemma sub_stable (G : sgraph) (B A : {set G}) : 
  A \subset B -> stable B -> stable A.
Proof.
move => subAB stB. exact: (hereditaryP _ (st_hereditary G) _ _ subAB).
Qed.

(** partitions and related properties *)

Section partition.
Variable (T : finType) (P : {set {set T}}) (D : {set T}).
Implicit Types (A B S : {set T}).

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

Lemma cover1 A : cover [set A] = A.
Proof. by rewrite /cover big_set1. Qed.

Lemma trivIset1 A : trivIset [set A].
Proof. by rewrite /trivIset cover1 big_set1. Qed.

Lemma trivIsetD Q : trivIset P -> trivIset (P :\: Q).
Proof. 
move/trivIsetP => tP; apply/trivIsetP => A B /setDP[TA _] /setDP[TB _]; exact: tP.
Qed.

Lemma trivIsetU Q : 
  trivIset Q -> trivIset P -> [disjoint cover Q & cover P] -> trivIset (Q :|: P).
Proof.
move => /trivIsetP tQ /trivIsetP tP dQP; apply/trivIsetP => A B.
move => /setUP[?|?] /setUP[?|?]; first [exact:tQ|exact:tP|move => _].
  by apply: disjointW dQP; rewrite bigcup_sup.
by rewrite disjoint_sym; apply: disjointW dQP; rewrite bigcup_sup.
Qed.

Lemma trivIsetU1 S : trivIset P -> [disjoint S & cover P] -> trivIset (S |: P).
Proof. by move=> tP dSP; apply: trivIsetU => //; rewrite ?cover1 ?trivIset1. Qed.

Lemma coverD1 S : trivIset P -> S \in P -> cover (P :\ S) = cover P :\: S.
Proof.
move/trivIsetP => tP SP; apply/setP => x; rewrite inE.
apply/bigcupP/idP => [[A /setD1P [ADS AP] xA]|/andP[xNS /bigcupP[A AP xA]]].
  by rewrite (disjointFr (tP _ _ _ _ ADS)) //=; apply/bigcupP; exists A.
by exists A; rewrite // !inE AP andbT; apply: contraNneq xNS => <-.
Qed.

Lemma partitionD1 S : 
  partition P D -> S \in P -> partition (P :\ S) (D :\: S).
Proof.
case/and3P => /eqP covP trivP set0P SP.
by rewrite /partition inE (negbTE set0P) trivIsetD ?coverD1 -?covP ?eqxx ?andbF.
Qed.

Lemma partitionU1 S : 
  partition P D -> S != set0 -> [disjoint S & D] -> partition (S |: P) (S :|: D).
Proof.
case/and3P => /eqP covP trivP set0P SD0 disSD.
rewrite /partition !inE (negbTE set0P) orbF [_ == S]eq_sym SD0 andbT.
rewrite /cover bigcup_setU bigcup_set1 -covP eqxx /=.
by apply: trivIsetU1 => //; rewrite covP.
Qed.

Lemma empty_partition : partition set0 (@set0 T).
Proof. by rewrite /partition inE /trivIset/cover !big_set0 cards0 !eqxx. Qed.

End partition.

(** * Clique Number and Chromatic Number *)

(** ** Clique number *)

Section Cliques.
Variables (G : sgraph).
Implicit Types (H K : {set G}).

Definition cliques H := [set K : {set G} | (K \subset H) && cliqueb K].

Lemma cliques_gt0 A : 0 < #|cliques A|. 
Proof.
apply/card_gt0P; exists set0; rewrite inE sub0set; apply/cliqueP.
by apply: small_clique; rewrite cards0.
Qed.

Definition omega_mem (A : mem_pred G) := 
  \max_(B in cliques [set x in A]) #|B|.

End Cliques.

Notation "ω( A )" := (omega_mem (mem A)) (format "ω( A )").

Definition maxcliques (G : sgraph) (H : {set G}) := 
  [set K in cliques H | ω(H) <= #|K|].

Section OmegaBasics.
Variables (G : sgraph).
Implicit Types (A K : {set G}).

Lemma clique_bound K A : K \in cliques A -> #|K| <= ω(A).
Proof. by move => clK; apply: bigmax_sup (leqnn _); rewrite set_mem. Qed.

Variant omega_spec A : nat -> Prop :=
  OmegaSpec K of K \in maxcliques A : omega_spec A #|K|.

Lemma omegaP A : omega_spec A ω(A).
Proof. 
rewrite /omega_mem set_mem. 
have [/= K clK maxK] := eq_bigmax_cond (fun A => #|A|) (cliques_gt0 A).
by rewrite maxK; apply: OmegaSpec; rewrite inE clK -maxK -{2}[A]set_mem leqnn.
Qed.

End OmegaBasics.

Lemma omega0 (G : sgraph) : ω(@set0 G) = 0.
Proof.  
by case: omegaP => K; rewrite !inE subset0 -andbA => /andP[/eqP-> _]; rewrite cards0.
Qed.

(** ** chromatic number *)

Definition coloring (G : sgraph) (P : {set {set G}}) (D : {set G}) :=
  partition P D && [forall S in P, stable S].

Definition trivial_coloring (G : sgraph) (A : {set G}) := 
  [set [set x] | x in A].

Lemma trivial_coloringP (G : sgraph) (A : {set G}) :
  coloring (trivial_coloring A) A.
Proof.
apply/andP; split; last by apply/forall_inP=> ? /imsetP[x xA ->]; exact: stable1.
suff -> : trivial_coloring A = preim_partition id A by apply: preim_partitionP.
have E x : x \in A -> [set x] = [set y in A | x == y].
  by move=> xA; apply/setP => y; rewrite !inE eq_sym andb_idl // => /eqP<-.
by apply/setP => P; apply/imsetP/imsetP => -[x xA ->]; exists x => //; rewrite E.
Qed.
Arguments trivial_coloringP {G A}.

Definition chi_mem (G : sgraph) (A : mem_pred G) := 
  #|[arg min_(P < trivial_coloring [set x in A] | coloring P [set x in A]) #|P|]|.

Notation "χ( A )" := (chi_mem (mem A)) (format "χ( A )").


Section Basics.
Variable (G : sgraph).
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

Lemma empty_coloring : coloring set0 (@set0 G).
Proof. by rewrite /coloring empty_partition; apply/forall_inP => S; rewrite inE. Qed.

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

Lemma chi0 : χ(@set0 G) = 0.
Proof. 
apply/eqP; rewrite -leqn0; apply: leq_trans (color_bound empty_coloring) _.
by rewrite cards0.
Qed.       

Lemma leq_chi A : χ(A) <= #|A|.
Proof. 
case: chiP => C col_C /(_ _ (@trivial_coloringP _ A)).
rewrite /trivial_coloring card_imset //. exact: set1_inj.
Qed.

Lemma chi_mono A B : A \subset B -> χ(A) <= χ(B).
Proof.
move=> subAB; case: (chiP B) => P col_P opt_P.
have col_S := sub_coloring col_P subAB.
apply: leq_trans (color_bound col_S) (card_sub_partition _ subAB).
by case/andP : col_P.
Qed.

Lemma cliqueIstable A C : clique C -> stable A -> #|A :&: C| <= 1.
Proof.
move => clique_C; apply: contraTT; rewrite -ltnNge.
case/card_gt1P => x [y] [/setIP[xA xC] /setIP[yA yC] xDy].
apply/stablePn; exists x, y; split => //. exact: clique_C.
Qed.

Lemma chi_clique C : clique C -> χ(C) = #|C|.
Proof.
move=> clique_C; apply/eqP; rewrite eqn_leq leq_chi /=.
have [P /andP[partP /forall_inP /= stabP] opt_P] := chiP.
suff S A : A \in P -> #|A| = 1. 
{ rewrite (card_partition partP); under eq_bigr => A ? do rewrite S //.
  by rewrite sum_nat_const muln1. }
move=> AP; apply/eqP; rewrite eqn_leq card_gt0 (partition_set0 partP) //. 
rewrite andbT -(@setIidPl _ A C _) ?(partition_subset partP) //.
exact : cliqueIstable (stabP _ _).
Qed.

Lemma omega_leq_chi A : ω(A) <= χ(A).
Proof.
case: omegaP => C; rewrite !inE -andbA => /and3P[subCA /cliqueP clique_C _].
by apply: leq_trans (chi_mono subCA); rewrite chi_clique.
Qed.

End Basics.

(** * Perfection *)

Definition perfect (G : sgraph) := [forall A : {set G}, ω(A) == χ(A)].

Definition mimimally_imperfect (G : sgraph) := 
  (ω(G) != χ(G)) && [forall (A : {set G} | A \proper [set: G]), ω(A) == χ(A)].

Section PerfectBasics.
Variables (G : sgraph).
Implicit Types (A B H : {set G}) (P : {set {set G}}).

Lemma card_maxclique K H : K \in maxcliques H -> #|K| = ω(H).
Proof. 
rewrite inE => /andP[clK ltK]; apply/eqP; rewrite eqn_leq ltK andbT.
exact: clique_bound.
Qed.

Definition optimal P H := forall P', coloring P' H -> #|P| <= #|P'|.

Lemma optimal_coloring H : exists2 P, coloring P H & optimal P H.
Proof. by case: chiP (erefl χ(H)) => P; exists P. Qed.

Lemma coloringD1 P S H : coloring P H -> S \in P -> coloring (P :\ S) (H :\: S).
Proof. 
move=> /andP[partP stabP] SP; apply/andP; split; first exact: partitionD1.
by apply/forall_inP => A /setD1P[_ /(forall_inP stabP)].
Qed.

Lemma coloringU1 P S H : 
  stable S -> S != set0 -> coloring P H -> [disjoint S & H] -> coloring (S |: P) (S :|: H).
Proof.
move=> stS SD0 /andP[partP stabP] disHS; apply/andP; split; first exact: partitionU1.
by apply/forall_inP => A /setU1P[-> //|/(forall_inP stabP)].
Qed.

Lemma chiD1 H S : stable S -> S \subset H -> χ(H) <= χ(H :\: S).+1.
Proof.
have [->|SD0] := eqVneq S set0; first by rewrite setD0.
move=> stabS subSH; case: (chiP (H :\: S)) => P colP _. 
have := coloringU1 stabS SD0 colP. 
rewrite disjoint_sym disjoints_subset subsetDr [S :|: _]setUC setDK // => /(_ isT) => colP'.
by apply: leq_trans (color_bound colP') _; rewrite cardsU1; case (_ \in _).
Qed.

Lemma cliquesD K H S : K \in cliques (H :\: S) -> K \in cliques H.
Proof. by rewrite !inE subsetD -andbA => /and3P[-> _ ->]. Qed.

(** TODO: if [stable S], the difference is exactly 1 *)
Lemma omega_cut H S : 
  {in maxcliques H, forall K, S :&: K != set0} -> ω(H :\: S) < ω(H).
Proof.
move/forall_inP; rewrite ltnNge; apply: contraTN; rewrite negb_forall_in.
have [/= K maxK geH] := omegaP (H :\: S).
move: maxK; rewrite inE => /andP[clK cardK].
apply/exists_inP; exists K; first by rewrite inE geH (cliquesD clK).
by move: clK; rewrite !inE subsetD negbK setI_eq0 disjoint_sym -andbA => /and3P[_ -> _].
Qed.

Lemma perfectEstrong (H : {set G}) (v : G) :
  perfect G -> v \in H -> 
  exists S, [/\ stable S, S \subset H, v \in S & [forall K in maxcliques H, S :&: K != set0]].
Proof.
move=> perfG vH; have/eqP := forallP perfG H. case: chiP => P /andP[partP stabP] optP E.
pose S := pblock P v. 
have vP : v \in cover P by rewrite (cover_partition partP) vH.
have SP : S \in P by rewrite pblock_mem // vP.
have SH : S \subset H by rewrite -(cover_partition partP); apply: bigcup_sup SP.
exists S; rewrite SH mem_pblock vP (forall_inP stabP) //; split => //.
apply: contra_eqT (E) => /forall_inPn/= [K maxK]; rewrite negbK setI_eq0 => disjK.
have colP' : coloring (P :\ S) (H :\: S) by apply: coloringD1 => //; apply/andP;split.
rewrite eqn_leq negb_and -!ltnNge; apply/orP;right.
have ωH : ω(H) <= ω(H :\: S). 
{ rewrite -(card_maxclique maxK) clique_bound //. 
  move: maxK; rewrite !inE -andbA => /and3P[K1 -> _]. 
  by rewrite subsetD K1 disjoint_sym disjK. }
apply: leq_ltn_trans ωH _. apply: leq_ltn_trans (omega_leq_chi _) _.
by apply: leq_ltn_trans (color_bound colP') _; rewrite [#|P|](cardsD1 S) SP.
Qed.

Lemma perfectIweak : 
  (forall H : {set G}, H != set0 ->
   exists S : {set G}, [/\ stable S, S \subset H & [forall K in maxcliques H, S :&: K != set0]]) 
  -> perfect G.
Proof.
move=> ex_stable; apply/forallP => /= H.
elim/card_ind : H => H IH.
have [->|[HD0]] := eqVneq H set0; first by rewrite omega0 chi0.
have [S [stabS subSH /forall_inP cutS]] := ex_stable H HD0.
rewrite eqn_leq omega_leq_chi /=. 
case: {-}_ /(omegaP H) => /= K maxK.
have cardHS : #|H :\: S| < #|H|. 
{ rewrite cardsDS // ltn_subrL; move/set0Pn : (cutS K maxK) => [x /setIP[xS _]].
  by apply/andP; split; apply/card_gt0P; exists x => //; apply: (subsetP subSH). }
apply: leq_trans (chiD1 stabS subSH) _; rewrite -(eqP (IH _ _)) //.
exact: omega_cut. 
Qed.

(* TOTHINK: do we want perfect to be a property of subsets as well, or
do we want to lift lemmas using induced subgraphs? *)
Definition perfects (U : {set G}) := perfect (induced U).

End PerfectBasics.


Definition in_induced (G : sgraph) (U H : {set G}) : {set induced U} := 
  [set x | val x \in H].
Arguments in_induced [G U] H, [G] U H.

Lemma perfectsEstrong (G : sgraph) (U : {set G}) (H : {set G}) (v : G) :
  perfects U -> v \in H -> H \subset U -> 
  exists S, [/\ stable S, S \subset H, v \in S & [forall K in maxcliques H, S :&: K != set0]].
Proof.
move=> perfU vH subHU. have vU : v \in U by apply: (subsetP subHU).
have vH' : Sub v vU \in in_induced U H by rewrite inE.
have := @perfectEstrong (induced U) (in_induced H) (Sub v vU) perfU vH'.
move => [S] [S1 S2 S3 S4]; exists (val @: S).
(* BORING *)
Admitted.

Section Iso.
Variables (F G : sgraph) (i : diso F G).
Implicit Types (A : {set F}).

Lemma diso_stable A : stable A = stable (i @: A).
Admitted.

Lemma diso_omega A : ω(A) = ω(i @: A).
Admitted.

Lemma diso_chi A : χ(A) = χ(i @: A).
Admitted.

Lemma diso_perfect_aux : perfect G -> perfect F.
Proof. 
by move/forallP => perfP; apply/forallP => H; rewrite diso_omega diso_chi.
Qed.

End Iso.

Lemma diso_perfect (F G : sgraph) (i : diso F G) : perfect F = perfect G.
Proof. by apply/idP/idP; apply: diso_perfect_aux; first apply: diso_sym. Qed.

Definition replicate (G : sgraph) (v : G) := add_node G N[v].

Lemma replication (G : sgraph) (v : G) : perfect G -> perfect (replicate v).
Proof.
move => perfG; apply: perfectIweak => H inhH.
have [NsubvNH|subvNH] := boolP ([set Some v; None] \subset H); last first.
- (* induced H is isomorphic to induced H' (in G), and hence H is perfect *) 
  admit. 
- admit.
Abort.


Section LovaszGraph.
Variables (G : sgraph) (m : G -> nat).

Definition LovaszRel (u v : Σ x : G, 'I_(m x)) := 
  if tag u == tag v then u != v else tag u -- tag v.

Lemma LovaszRel_sym : symmetric LovaszRel.
Proof.
by move=> u v; rewrite /LovaszRel [tag u == _]eq_sym [u == v]eq_sym sgP.
Qed.

Lemma LovaszRel_irrefl : irreflexive LovaszRel.
Proof. by move => [x i]; rewrite /LovaszRel/= !eqxx. Qed.

Definition Lovasz := SGraph LovaszRel_sym LovaszRel_irrefl.

Lemma Lovasz_perfect : perfect G -> perfect Lovasz.
Abort. 
(* for m x > 1, this is replication, for m x = 0, this is deletion, for all x *)

End LovaszGraph.
