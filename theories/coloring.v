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

Lemma inj_imsetS (aT rT : finType) (f : aT -> rT) (A B : {pred aT}) : 
  injective f -> (f @: A \subset f @: B) = (A \subset B).
Proof.
move=> inj_f; apply/subsetP/subsetP => [/= subAB x xA|subAB ? /imsetP[x xA ->]]. 
  by move: (subAB (f x)); rewrite !(mem_imset_eq _ _ inj_f); apply.
by rewrite (mem_imset_eq _ _ inj_f); apply: subAB.
Qed.

Lemma val_subset (T: finType) (H : {set T}) (A B : {set sig [eta mem H]}) :
  (val @: A \subset val @: B) = (A \subset B).
Proof. by rewrite inj_imsetS //; exact: val_inj. Qed.

(** dom.v *)

Lemma stable1 (G : sgraph) (x : G) : stable [set x].
Proof. by apply/stableP => ? ? /set1P -> /set1P ->; rewrite sgP. Qed.

(* TOTHINK: do we need that [hereditary] is a boolean predicate? *)
Lemma sub_stable (G : sgraph) (B A : {set G}) : 
  A \subset B -> stable B -> stable A.
Proof.
move => subAB stB. exact: (hereditaryP _ (st_hereditary G) _ _ subAB).
Qed.

(** isomorphisms *)

(* TODO: scope ... *)
Notation "F ≃ G" := (diso F G) (at level 79).

Lemma diso_add_nodeK (G : sgraph) (A : {set G}) : 
  G ≃ @induced (add_node G A) [set~ None].
Proof.
set H := induced _. (* todo: factor out the bijetion *)
have h_proof (x : G) : Some x \in [set~ None] by rewrite !inE.
pose h (x : G) : H := Sub (Some x) (h_proof x).
have default (x : H) : G by case: x => -[x//|]; rewrite !inE eqxx.
pose g (x : H) : G := if val x is Some z then z else default x.
have can_h : cancel h g by [].
have can_g : cancel g h. 
  move => [[x|] p]; [exact: val_inj|by exfalso; rewrite !inE eqxx in p].
exact: Diso' can_h can_g _.
Defined.


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

(* name clash *)
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

Section Image.
Variables (T' : finType) (f : T -> T') (inj_f : injective f).
Let fP := [set f @: (S : {set T}) | S in P].

Lemma imset_inj : injective (fun A : {set T} => f @: A).
Proof. 
move => A B => /setP E; apply/setP => x. 
by rewrite -(mem_imset_eq (mem A) x inj_f) E mem_imset_eq.
Qed.

Lemma imset_disjoint (A B : {pred T}) :
  [disjoint f @: A & f @: B] = [disjoint A & B].
Proof.
apply/pred0Pn/pred0Pn => /= [[? /andP[/imsetP[x xA ->]] xB]|].
  by exists x; rewrite xA -(mem_imset_eq (mem B) x inj_f).
by move => [x /andP[xA xB]]; exists (f x); rewrite !mem_imset_eq ?xA.
Qed.

Lemma imset_trivIset : trivIset P = trivIset fP.
Proof.
apply/trivIsetP/trivIsetP.
- move=> trivP ? ? /imsetP[A AP ->] /imsetP[B BP ->].
  by rewrite (inj_eq imset_inj) imset_disjoint; apply: trivP.
- move=> trivP A B AP BP; rewrite -imset_disjoint -(inj_eq imset_inj).
  by apply: trivP; rewrite imset_f.
Qed.

Lemma imset0mem : (set0 \in fP) = (set0 \in P).
Proof. 
apply/imsetP/idP => [[A AP /esym/eqP]|P0]; last by exists set0; rewrite ?imset0.
by rewrite imset_eq0 => /eqP<-.
Qed.

Lemma bigcup_imset:
  \bigcup_(i in P) [set f x | x in i] = [set f x | x in cover P].
Proof.
apply/setP=> y; apply/bigcupP/imsetP => [[A AP /imsetP[x xA ->]]|].
  by exists x => //; apply/bigcupP; exists A.
by move=> [x /bigcupP[A AP xA] ->]; exists A => //; rewrite imset_f.
Qed.  

Lemma imset_partition : partition P D = partition fP (f @: D).
Proof.
suff cov: (cover fP == f @:D) = (cover P == D).
  by rewrite /partition -imset_trivIset imset0mem cov.
by rewrite /fP cover_imset bigcup_imset (inj_eq imset_inj).
Qed.
End Image.

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

Lemma cliquesW (A B K : {set G}) : A \subset B -> K \in cliques A -> K \in cliques B.
Proof. 
by move=> subAB; rewrite !inE => /andP[subKA ->]; rewrite (subset_trans subKA). 
Qed.

Lemma sub_cliques (A K K' : {set G}) : K' \subset K -> K \in cliques A -> K' \in cliques A.
Admitted.

Lemma cliques_subset (A K : {set G}) : K \in cliques A -> K \subset A.
Proof. by rewrite !inE => /andP[-> _]. Qed.

Lemma cliqueU1 x K : K \subset N(x) -> clique K -> clique (x |: K).
Proof. 
move => /subsetP subKNx clK u v /setU1P[-> {u}|uK] /setU1P[-> {v}|vK].
- by rewrite eqxx.
- by move/subKNx : vK; rewrite inE.
- by move/subKNx : uK; rewrite inE sgP.
- exact: clK.
Qed.

Lemma sub_clique K K' : K' \subset K -> clique K -> clique K'.
Proof. by move=> /subsetP subK clK x y /subK xK /subK yK; exact: clK. Qed.

Lemma cliqueD K H : clique K -> clique (K :\: H).
Proof. by move => clK x y /setDP[xK _] /setDP[yK _]; exact: clK. Qed.

Definition omega_mem (A : mem_pred G) := 
  \max_(B in cliques [set x in A]) #|B|.

End Cliques.

Notation "ω( A )" := (omega_mem (mem A)) (format "ω( A )").

Definition maxcliques (G : sgraph) (H : {set G}) := 
  [set K in cliques H | ω(H) <= #|K|].

Section OmegaBasics.
Variables (G : sgraph).
Implicit Types (A B K H : {set G}).

Variant omega_spec A : nat -> Prop :=
  OmegaSpec K of K \in maxcliques A : omega_spec A #|K|.

Lemma omegaP A : omega_spec A ω(A).
Proof. 
rewrite /omega_mem set_mem. 
have [/= K clK maxK] := eq_bigmax_cond (fun A => #|A|) (cliques_gt0 A).
by rewrite maxK; apply: OmegaSpec; rewrite inE clK -maxK -{2}[A]set_mem leqnn.
Qed.

Lemma clique_bound K A : K \in cliques A -> #|K| <= ω(A).
Proof. by move => clK; apply: bigmax_sup (leqnn _); rewrite set_mem. Qed.

Lemma card_maxclique K H : K \in maxcliques H -> #|K| = ω(H).
Proof. 
rewrite inE => /andP[clK ltK]; apply/eqP; rewrite eqn_leq ltK andbT.
exact: clique_bound.
Qed.

Lemma maxclique_edge K H x y : x \in K -> y \in K -> K \in maxcliques H -> x != y -> x -- y.
Proof.
by move=> xK yK; rewrite !inE -andbA => /and3P[_ /cliqueP clK _]; apply: clK.
Qed.

Lemma sub_omega A B : A \subset B -> ω(A) <= ω(B).
Proof.
move=> subAB; have [K] := omegaP A; rewrite inE => /andP[clA _]. 
exact/clique_bound/(cliquesW subAB).
Qed.

Lemma maxclique_disjoint K H A : 
  K \in maxcliques H -> [disjoint K & A] -> K \in maxcliques (H :\: A).
Proof.
rewrite !inE -!andbA subsetD => /and3P[-> -> maxK] -> /=. 
apply: leq_trans (sub_omega _) maxK. exact: subsetDl.
Qed.

Lemma maxclique_opn H K v : 
  v \in H -> K \in maxcliques H -> K \subset N(v) -> v \in K.
Proof.
rewrite !inE -andbA => vH /and3P[subKH /cliqueP clK maxK] subNvK.
have/cliqueP clvK : clique (v |: K) by apply: cliqueU1.
apply: contraTT maxK => vNK ; rewrite -ltnNge.
rewrite -add1n -[1 + _]/(true + #|K|) -vNK -cardsU1; apply: clique_bound.
by rewrite !inE clvK subUset sub1set vH subKH.
Qed.

Lemma omega0 : ω(@set0 G) = 0.
Proof.  
by case: omegaP => K; rewrite !inE subset0 -andbA => /andP[/eqP-> _]; rewrite cards0.
Qed.

End OmegaBasics.

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

Definition perfect_mem (G : sgraph) (U : mem_pred G) := 
  [forall (A : {set G} | A \subset U), ω(A) == χ(A)].

Notation perfect U := (perfect_mem (mem U)).

(** relativize as well *)
Definition mimimally_imperfect (G : sgraph) := 
  (ω(G) != χ(G)) && [forall (A : {set G} | A \proper [set: G]), ω(A) == χ(A)].

Section PerfectBasics.
Variables (G : sgraph).
Implicit Types (A B H : {set G}) (P : {set {set G}}).

Lemma sub_perfect A B : A \subset B -> perfect B -> perfect A.
Proof. 
move=> subAB /forall_inP perfB; apply/forall_inP => C subCA. 
apply: perfB. exact: subset_trans _ subAB.
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

Lemma perfectEstrong (U H : {set G}) (v : G) :
  perfect U -> H \subset U -> v \in H -> 
  exists S, [/\ stable S, S \subset H, v \in S & [forall K in maxcliques H, S :&: K != set0]].
Proof.
move=> perfG subHU vH. have/eqP := forall_inP perfG _ subHU. 
case: chiP => P /andP[partP stabP] optP E. pose S := pblock P v. 
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

Lemma perfectIweak (U : {set G}) : 
  (forall H : {set G}, H \subset U -> H != set0 -> 
   exists S : {set G}, [/\ stable S, S \subset H & [forall K in maxcliques H, S :&: K != set0]]) 
  -> perfect U.
Proof.
move=> ex_stable; apply/forall_inP => /= H.
elim/card_ind : H => H IH subHU.
have [->|HD0] := eqVneq H set0; first by rewrite omega0 chi0.
have [S [stabS subSH /forall_inP cutS]] := ex_stable H subHU HD0.
rewrite eqn_leq omega_leq_chi /=. 
case: {-}_ /(omegaP H) => /= K maxK.
have cardHS : #|H :\: S| < #|H|. 
{ rewrite cardsDS // ltn_subrL; move/set0Pn : (cutS K maxK) => [x /setIP[xS _]].
  by apply/andP; split; apply/card_gt0P; exists x => //; apply: (subsetP subSH). }
apply: leq_trans (chiD1 stabS subSH) _.
rewrite -(eqP (IH _ _ _)) //; first exact: omega_cut. 
by rewrite subDset subsetU // subHU orbT.
Qed.


Let setG : [set x in mem [set: G]] = [set x in mem G]. 
Proof. by apply/setP => x; rewrite !inE. Qed.

Lemma chiT : χ([set: G]) = χ(G).
Proof. by rewrite /chi_mem setG. Qed.

Lemma omegaT : ω([set: G]) = ω(G). 
Proof. by rewrite /omega_mem setG. Qed.

Lemma perfectT : perfect([set: G]) = perfect(G). 
Proof. by apply: eq_forallb => A; rewrite subsetT subset_predT. Qed.

End PerfectBasics.

Notation sval := (@sval _ _).

Definition in_induced (G : sgraph) (U H : {set G}) : {set induced U} := 
  [set x | val x \in H].
Arguments in_induced [G U] H, [G] U H.

Lemma val_in_induced (G : sgraph) (H A : {set G}) : 
  val @: in_induced H A = A :&: H.
Proof. 
apply/setP => x; apply/imsetP/idP => [/= [y yH ->]|/= /setIP[xA xH]]. 
  by move: yH; rewrite !inE (svalP y) andbT.
exists (Sub x xH) => //; by rewrite inE.
Qed.

Lemma val_in_induced' (G : sgraph) (H A : {set G}) : 
  (A \subset H) -> val @: in_induced H A = A.
Proof. by move => subAH; rewrite val_in_induced (setIidPl subAH). Qed.

Lemma in_induced_val (G : sgraph) (H : {set G}) (A : {set induced H}) : 
  in_induced H (val @: A) = A.
Proof. by apply/setP => x; rewrite !inE mem_imset_eq //; apply: val_inj. Qed.

Lemma in_inducedT (G : sgraph) (H : {set G}) : 
  in_induced H H = [set: induced H].
Proof. by apply/setP => x; rewrite !inE (valP x). Qed.  

Lemma card_in_induced (G : sgraph) (H A : {set G}) : 
  A \subset H -> #|in_induced H A| = #|A|.
Proof. by move => subAH; rewrite -(card_imset _ val_inj) val_in_induced'. Qed.
Arguments card_in_induced [G] H [A].

Lemma sub_induced (G : sgraph) (H : {set G}) (A : {set induced H}) : 
  val @: A \subset H.
Proof. by apply/subsetP => ? /imsetP[x xH ->]; apply: valP. Qed.

Lemma forall_imset (aT rT : finType) (f : aT -> rT) (p : {pred aT}) (q : {pred rT}) :
  [forall x in [set f z | z in p], q x] = [forall x in p, q (f x)].
Proof.
apply/forall_inP/forall_inP=>[allQ x xp|]; first by apply: allQ; rewrite imset_f.
by move => allQ ? /imsetP[z zp ->]; apply: allQ.
Qed.

Lemma forall2_imset (aT rT : finType) (f g : aT -> rT) (p : {pred aT}) (q : rel rT) :
  [forall x in [set f z | z in p], forall y in [set g z | z in p], q x y] = 
  [forall x in p, forall y in p, q (f x) (g y)].
Proof.
by rewrite forall_imset; under eq_forallb => y do rewrite forall_imset.
Qed.

Lemma eq_forall_in (T : finType) (A P1 P2 : {pred T}) : 
  {in A, P1 =1 P2} -> [forall x in A, P1 x] = [forall x in A, P2 x].
Proof. move=> eqP. apply/eq_forallb => x; case xA: (x \in A) => //=. exact: eqP. Qed.

Lemma induced_edge (G : sgraph) (A : {set G}) (x y : induced A) : 
  (x -- y) = (val x -- val y).
Proof. by move: x y => [x xA] [y yA]. Qed.


(* better statement *)
Lemma Diso' [F G : diGraph] [f : F -> G] [g : G -> F] : 
  cancel f g -> cancel g f -> {mono f : x y / x -- y} -> F ≃ G.
Proof. 
move => can_f can_g mono_f; apply: Diso' can_f can_g _.
abstract (by move => x y; apply/Bool.eq_iff_eq_true).
Defined.

(** [G] contains [F] as an induced subgraph *)
Record isubgraph (F G : diGraph) := 
  ISubgraph { isubgraph_fun :> F -> G ; 
              isubgraph_inj : injective isubgraph_fun ; 
              isubgraph_mono : {mono isubgraph_fun : x y / x -- y} }.
Arguments isubgraph_inj [F G] i.
Notation "F ⇀ G" := (isubgraph F G) (at level 30).

Lemma induced_isubgraph (G : sgraph) (A : {set G}) : induced A ⇀ G.
Proof.
pose f (x : induced A) : G := val x.
have : {mono f : x y / x -- y} by abstract by move => x y; rewrite induced_edge.
apply: ISubgraph; exact: val_inj.
Defined.

Lemma isubgraph_induced (F G : sgraph) (i : F ⇀ G) : 
  F ≃ induced [set x in codom i].
Proof.
set A := [set _ in _].
have jP (x : induced A) : val x \in codom i. 
  abstract by move: (valP x); rewrite inE.
pose j (x : induced A) : F := iinv (jP x).
have iP (x : F) : i x \in A by abstract by rewrite inE codom_f.
pose i' (x : F) : induced A := Sub (i x) (iP x).
have can_i : cancel i' j. 
  abstract by move=> x; apply: (isubgraph_inj i); rewrite f_iinv.
have can_j : cancel j i'. 
  abstract by move => [x xA]; apply: val_inj; rewrite /j/=f_iinv.
apply: Diso' can_i can_j _. 
  abstract by move => x y; rewrite induced_edge /= isubgraph_mono.
Defined.

Lemma isubgraph_iso (F G : diGraph) (i : F ⇀ G) : #|G| <= #|F| -> F ≃ G.
Proof.
move => leqGF. apply: Diso' (isubgraph_mono i).
Abort.

Lemma isubgraph_comp (F G H : diGraph) (i : F ⇀ G) (j : G ⇀ H) : F ⇀ H.
Proof.
apply: ISubgraph (j \o i) _ _. 
exact: inj_comp (isubgraph_inj j) (isubgraph_inj i).
abstract by move=> x y /=; rewrite !isubgraph_mono.
Defined.

Section Induced.
Variables (F G : sgraph) (i : F ⇀ G).

Lemma cliqueb_induced (K : {set F}) : cliqueb K = cliqueb (i @: K).
Proof.
rewrite /cliqueb (@forall2_imset _ _ i i).
apply: eq_forall_in => x xK; apply: eq_forall_in => y yK.
by rewrite (inj_eq (isubgraph_inj i)) isubgraph_mono.
Qed.

Lemma stable_induced (S  : {set F}) : stable S = stable (i @: S).
Proof.
rewrite !stableEedge (@forall2_imset _ _ i i).
apply: eq_forall_in => x xS; apply: eq_forall_in => y yS.
by rewrite isubgraph_mono.
Qed.

Lemma coloring_induced (P : {set {set F}}) (D : {set F}) : 
  coloring P D = @coloring G [set i @: (S : {set F}) | S in P] (i @: D).
Proof.
rewrite /coloring -imset_partition; last exact: isubgraph_inj.
by rewrite forall_imset; under [in RHS]eq_forallb => S do rewrite -stable_induced.
Qed.

Lemma can_preimset (f : F -> G) (A : {set G}) : 
  A \subset codom f -> [set f x | x in f @^-1: A] = A.
Proof. 
move/subsetP => subAi; apply/setP => z; apply/imsetP/idP => [[x]|zA].
  by rewrite inE => ? ->.
by exists (iinv (subAi _ zA)); rewrite ?inE f_iinv.
Qed.

Let i_inj := isubgraph_inj i.

(* also relies on injectivity *)
Lemma inj_card_preimset (A : {set G}) : A \subset codom i -> #|i @^-1: A| = #|A|.
Proof. 
move/subsetP => subAi.
have [->|[y yA]] := set_0Vmem A; first by rewrite preimset0 !cards0.
have x0 : F := (iinv (subAi _ yA)).
pose j (x : G) : F := if @idP (x \in codom i) is ReflectT p then iinv p else x0.
apply: on_card_preimset; exists j. 
- move => x /subAi; rewrite /j. case E : {1}_ / idP => //. by rewrite iinv_f.
- move => x /subAi; rewrite /j. case E : {1}_ / idP => //. by rewrite f_iinv.
Qed.

Lemma imset_codom (f : F -> G) (A : {set F}) : 
  [set f x | x in A] \subset codom f.
Proof. apply/subsetP => ? /imsetP[x xA ->]; exact: codom_f. Qed.

Lemma preim_coloring (P : {set {set G}}) (D : {set F}) : 
  coloring P (i @: D) -> coloring [set i @^-1: (B : {set G}) | B in P] D.
Proof.
move => colP; rewrite coloring_induced -imset_comp /comp /=.
have coB B : B \in P -> B \subset codom i. 
{ case/andP: colP => partP _; move/(partition_subset partP) => sub.
  apply: subset_trans sub _. exact: imset_codom. }
under [X in coloring X _]eq_in_imset => B BP. 
  rewrite (@can_preimset i) ?coB //; over. 
by rewrite imset_id.
Qed.

Lemma chi_induced (A : {set F}) : χ(A) = χ(i @: A).
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- case: (chiP (i @: A)) => P /preim_coloring colP minP.
  exact: leq_trans (color_bound colP) (leq_imset_card _ _).
- case: (chiP A) => P colP minP.
  rewrite coloring_induced in colP; apply: leq_trans (color_bound colP) _.
  by rewrite card_imset //; apply/imset_inj/isubgraph_inj.
Qed.

Lemma induced_cliques (B K : {set F}) : 
  (K \in cliques B) = (i @: K \in cliques (i @: B)).
Proof. by rewrite !inE inj_imsetS // -cliqueb_induced. Qed.

Lemma clique_to_induced (K A : {set G}) : 
  K \in cliques A -> i @^-1: K \in cliques (i @^-1: A).
Proof.
rewrite !inE => /andP[subKA /cliqueP clK]. 
rewrite preimsetS //= cliqueb_induced; apply/cliqueP.
by apply: sub_clique clK; rewrite sub_imset_pre preimsetS.
Qed.

Lemma can_inj_imset (A : {set F}) : i @^-1: (i @: A) = A.
Proof. by apply/setP => x; rewrite !inE (mem_imset_eq). Qed.

Lemma omega_induced (B : {set F}) : ω(B) = ω(i @: B).
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- have [K] := omegaP B. 
  rewrite inE induced_cliques => /andP[ckK _]; rewrite -(card_imset _ i_inj).
  exact: clique_bound.
- have [K] := omegaP; rewrite inE => /andP[clK].
  move/clique_to_induced : (clK). rewrite can_inj_imset => clK' _. 
  apply: leq_trans (clique_bound clK'). rewrite inj_card_preimset //.
  exact: subset_trans (cliques_subset clK) (imset_codom _ _).
Qed.

Lemma perfect_imset (A : {set F}) : perfect A = perfect(i @: A).
Proof.
apply/idP/idP.
- move/forall_inP => perfIA; apply/forall_inP => B subBA.
  have subBi : B \subset codom i by apply: subset_trans subBA (imset_codom _ _).
  rewrite -[B](@can_preimset i) //  -omega_induced -chi_induced; apply perfIA. 
  by rewrite -(@inj_imsetS _ _ i) // can_preimset.
- move/forall_inP => perfA; apply/forall_inP => B ?.
  by rewrite omega_induced chi_induced; apply/perfA/imsetS.
Qed.

End Induced.

Lemma perfect_induced (G : sgraph) (A : {set G}) : 
  perfect (induced A) = perfect A.
Proof.
pose i := induced_isubgraph A.
by rewrite -perfectT (perfect_imset i) /= imset_valT set_mem.
Qed.

Arguments perfect_imset [F G] i A.

(** Graph Properties - useful? *)
Section GProp.
Variable (rT : eqType).

Definition gprop (P : sgraph -> rT) := 
  forall F G : sgraph, F ≃ G -> P F = P G.

Definition gset_prop (P : forall (G : sgraph), {set G} -> rT) :=
  forall (F G : sgraph) (i : F ⇀ G) (A : {set F}), P F A = P G (i @: A).

Lemma gset_prop_induced P (G : sgraph) (H : {set G}) (A : {set induced H}) :
  gset_prop P -> P (induced H) A = P G (val @: A).
Proof. by move/(_ _ _ (induced_isubgraph H)); apply. Qed.

End GProp.

Lemma gset_cliqueb : gset_prop cliqueb. 
Proof. exact: cliqueb_induced. Qed.



Module Legacy. (* should be subsumed *)
Section Induced.
Variables (G : sgraph).
Implicit Types (A B H : {set G}).

Lemma cliqueb_induced H (K : {set induced H}) : 
  cliqueb K = cliqueb (val @: K).
Proof.
rewrite /cliqueb forall2_imset.
apply: eq_forall_in => -[x xH] xK; apply: eq_forall_in => -[y yH] yK.
by rewrite -val_eqE /= induced_edge.
Qed.

Lemma induced_cliques H (B K : {set induced H}) : 
  (K \in cliques B) = (val @: K \in cliques (val @: B)).
Proof. by rewrite !inE val_subset -cliqueb_induced. Qed.

Lemma clique_to_induced H (K A : {set G}) : 
  K \in cliques A -> in_induced H K \in cliques (in_induced H A).
Proof.
rewrite !inE => /andP[subKA /cliqueP clK]. 
rewrite -val_subset cliqueb_induced !val_in_induced setISS //.
by apply/cliqueP; apply: sub_clique clK; apply: subIset; rewrite subxx.
Qed.

Lemma omega_induced A (B : {set induced A}) : ω(B) = ω(val @: B).
Proof.
apply/eqP; rewrite eqn_leq; apply/andP; split.
- have [K] := omegaP B. 
  rewrite inE induced_cliques => /andP[ckK _]; rewrite -(card_imset _ val_inj).
  exact: clique_bound.
- have [K] := omegaP; rewrite inE => /andP[clK].
  move/clique_to_induced : (clK) => /(_ A); rewrite in_induced_val => clK' _.
  rewrite -(card_in_induced A); first exact: clique_bound clK'.
  exact: subset_trans (cliques_subset clK) (sub_induced _).
Qed.

Lemma omega_inducedT A : ω(induced A) = ω(A).
Proof. by rewrite -omegaT omega_induced -in_inducedT val_in_induced setIid. Qed.

Lemma stable_induced H (S : {set induced H}) : 
  stable S = stable (val @: S).
Proof.
rewrite !stableEedge forall2_imset.
apply: eq_forall_in => -[x xH] xS; apply: eq_forall_in => -[y yH] yS.
by rewrite induced_edge.
Qed.

(* Lemma perfect_induced A : perfect(induced A) = perfect(A). *)
(* Proof. *)
(* apply/idP/idP. *)
(* - move/forall_inP => perfIA; apply/forall_inP => B subBA. *)
(*   rewrite -[B](val_in_induced' subBA) -omega_induced -chi_induced.  *)
(*   apply: perfIA. by rewrite subset_predT. *)
(* - move/forall_inP => perfA; apply/forall_inP => B _. *)
(*   rewrite omega_induced chi_induced; exact/perfA/sub_induced. *)
(* Qed. *)

End Induced.
End Legacy.


Lemma imset_bijT (aT rT : finType) (i : bij aT rT) : i @: setT = setT.
Proof. 
apply/setP => x; rewrite inE; apply/imsetP; exists (i^-1 x) => //.
by rewrite bijK'.
Qed.

Section Iso.
Variables (F G : sgraph) (i : diso F G).
Implicit Types (A : {set F}).

Let i_mono : {mono i : x y / x -- y}.
Proof. by move => x y; rewrite edge_diso. Qed.

Let i_inj : injective i.
Proof. by apply: (can_inj (g := i^-1)) => x; rewrite bijK. Qed.

Definition i' : F ⇀ G := ISubgraph i_inj i_mono.

Lemma diso_stable A : stable A = stable (i @: A).
Admitted.

Lemma diso_clique A : cliqueb A = cliqueb (i @: A).
Admitted.

Lemma diso_omega A : ω(A) = ω(i @: A).
Admitted.

Lemma diso_chi A : χ(A) = χ(i @: A).
Admitted.

Lemma diso_perfect A : perfect A = perfect (i @: A).
Proof. by rewrite (perfect_imset i'). Qed.

Lemma diso_perfectT : perfect F = perfect G.
Proof. by rewrite -!perfectT diso_perfect imset_bijT. Qed.

End Iso.

Lemma diso_perfect_induced (G : sgraph) (U V : {set G}) : 
  induced U ≃ induced V -> perfect U -> perfect V.
Proof. 
move => i; rewrite -perfect_induced -perfectT (diso_perfect i).
have -> : i @: [set: induced U] = [set: induced V].
{ by apply/setP => x; rewrite !inE -[x](bijK' i) imset_f. }
by rewrite perfectT perfect_induced.
Qed.

Definition replicate (G : sgraph) (v : G) := add_node G N[v].

Lemma diso_replicate (G : sgraph) (v : G) : 
  G ≃ @induced (replicate v) [set~ None].
Proof. exact: diso_add_nodeK. Qed.

Arguments val : simpl never.
Arguments Sub : simpl never.

Lemma cln_eq (G : sgraph) (x x' y : G) : 
  N[x] = N[x'] -> y != x -> y != x' -> x -- y = x' -- y.
Proof.
by move/setP=> /(_ y); rewrite !inE; case: (eqVneq x y); case: (eqVneq x' y).
Qed.

(* [v -- v'] is not necessary, as it follows from [v != v'] and the
case for [v == v'] is trivial. But we have it at the only point of use *)
Lemma eq_cln_iso (G : sgraph) (v v' : G) : 
  v -- v' -> N[v] = N[v'] -> induced [set~ v'] ≃ induced [set~ v].
Proof.
move=> vv' Nvv'.
set Hv := induced [set~ v']; set Hv' := induced _.
have [vI v'I] : v \in [set~ v'] /\ v' \in [set~ v] by rewrite !inE [v' == _]eq_sym (sg_edgeNeq vv').
pose f (x : Hv) : Hv' := insubd (Sub v' v'I) (val x).
pose g (x : Hv') : Hv := insubd (Sub v vI) (val x).
have can_f : cancel f g. (* TODO: merge induced subgraphs from wagner branch *)
{ move => x. apply: val_inj. rewrite /f/g/= !val_insubd !inE !SubK. 
  have [/= ->|/=] := eqVneq (val x) v; rewrite ?eqxx // ifT // -in_set1 -in_setC. exact (valP x). }
have can_g : cancel g f. 
{ move => x. apply: val_inj. rewrite /f/g/= !val_insubd !inE !SubK. 
  have [/= ->|/=] := eqVneq (val x) v'; rewrite ?eqxx // ifT // -in_set1 -in_setC. exact (valP x). }
apply: Diso' can_f can_g _.
move => [x px] [y py]; rewrite /f/=. rewrite /edge_rel/= !val_insubd !SubK !inE.
rewrite !inE in px py. 
have [?/=|/=] := eqVneq x v; subst.
  have [->|/= yDv] := eqVneq y v; [by rewrite !sgP | by rewrite (cln_eq Nvv')].
by have [->/= xDv|//] := eqVneq y v; rewrite [RHS]sgP (cln_eq Nvv') // sgP.
Qed.

Lemma opn_cln (G : sgraph) (x : G) : N(x) = N[x] :\ x.
Proof. by apply/setP => y; rewrite !inE; case: (eqVneq x y) => //= ->; rewrite sgP. Qed.

(* [v != v'] would suffice *)
Lemma replication_aux (G : sgraph) (v v' : G) : 
  v -- v' -> N[v] = N[v'] -> perfect [set~ v'] -> perfect G.
Proof.
move => vv' Nvv' perfNv'; rewrite -perfectT; apply: perfectIweak => H _ /set0Pn [z zH].
have [vv'_H|] := boolP ([set v;v'] \subset H); last first.
- have perfNv : perfect [set~ v]. 
  { apply: diso_perfect_induced perfNv'. exact: eq_cln_iso. }
  rewrite subUset !sub1set negb_and => vNH. 
  wlog vNH : v v' vv' {Nvv'} {perfNv'} perfNv {vNH} / v \notin H. 
    by case/orP: vNH => [vNH /(_ v v') |v'NH /(_ v' v)]; apply; rewrite // sgP.
  have [|S [S1 S2 _ S3]] := @perfectEstrong _ [set~ v] H z perfNv _ zH.
    by rewrite subsetC sub1set inE.
  by exists S. 
- have Hvv' : H :\ v' \subset [set~ v'] by rewrite subDset setUCr subsetT.
  have vHv' : v \in H :\ v' by rewrite !inE (sg_edgeNeq vv') (subsetP vv'_H) // !inE eqxx.
  have perfHv : perfect (H :\ v') by apply: sub_perfect perfNv'. 
  have := @perfectEstrong _ [set~ v'] (H :\ v')  v perfNv' Hvv' vHv'.
  move => [S] [stabS subSH vS cutS]; exists S; split => //. 
    exact: subset_trans subSH (subsetDl _ _).
  apply/forall_inP => K maxK. 
  have [v'K|v'NK] := boolP (v' \in K).
  - (* a maximal clique contains every vertex total to it *)
    suff vK : v \in K by apply/set0Pn; exists v; rewrite inE vS vK.
    apply: wlog_neg => v'NK.
    apply: maxclique_opn (maxK) _ ; first by case/setD1P : vHv'.
    apply/subsetP => x xK; case: (eqVneq x v) => [xv|xDv]; first by rewrite -xv xK in v'NK.
    rewrite opn_cln Nvv' !inE xDv -implyNb sgP; apply/implyP.
    exact: maxclique_edge maxK.
  - suff: K \in maxcliques (H :\ v') by move/(forall_inP cutS).
    by apply: maxclique_disjoint => //; rewrite disjoint_sym disjoints1.
Qed.

Lemma replication (G : sgraph) (v : G) : perfect G -> perfect (replicate v).
Proof.
move => perfG; apply: (@replication_aux (replicate v) (Some v) None).
- by rewrite /edge_rel/= v_in_clneigh. (* fixme: name! *)
- by apply/setP => -[x|] ; rewrite !inE /edge_rel//= ?v_in_clneigh ?Some_eqE ?in_cln 1?eq_sym.
- by rewrite -perfect_induced -(diso_perfectT (diso_replicate v)).
Qed.

Print Assumptions replication.

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
