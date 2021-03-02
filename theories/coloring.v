From mathcomp Require Import all_ssreflect.
Require Import preliminaries digraph sgraph dom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Preliminaries *)

Lemma stable1 (G : sgraph) (x : G) : stable [set x].
Proof. by apply/stableP => ? ? /set1P -> /set1P ->; rewrite sgP. Qed.

(* TOTHINK: do we need that [hereditary] is a boolean predicate? *)
Lemma sub_stable (G : sgraph) (B A : {set G}) : 
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

(** clique number *)

Definition omega_mem (G : sgraph) (A : mem_pred G) := 
  \max_(B : {set G} | (B \subset A) && cliqueb B) #|B|.

Notation "ω( A )" := (omega_mem (mem A)) (format "ω( A )").

(** chromatic number *)

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
apply/bigmax_leqP => C /andP[subCA /cliqueP clique_C].
apply: leq_trans (chi_mono subCA). by rewrite chi_clique.
Qed.

End Basics.

Definition perfect (G : sgraph) := [forall A : {set G}, ω(A) == χ(A)].

Definition mimimally_imperfect (G : sgraph) := 
  (ω(G) != χ(G)) && [forall (A : {set G} | A \proper [set: G]), ω(A) == χ(A)].

Fact omegaT : forall G : sgraph, ω(G) = ω([set: G]). 
Proof. by move => G; apply: eq_bigl => B; rewrite subsetT subset_predT. Qed.

Fact omega_induced (G : sgraph) (A : {set G}) : ω(induced A) = ω(A).
Abort.

