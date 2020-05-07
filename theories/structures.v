Require Import RelationClasses Morphisms Relation_Definitions.
From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Setoids and Label Structures *)


(*  
TODO: packed classes? (does not seem to be problematic for now)
but we should at least understand the current hack in rewriting.v for setoid_of_bisetoid
*)


(* Note on Equivalences and Morphisms: This development mixes both
rewriting in Prop (e.g., 2pdom algebras) and rewriting in Type (e.g.,
iso). To facilitate this, we import the Prop versions and introduce
notations for the Type versions. This leads to the follwing usage
patterns: 

- Morphisms and Relation classes should be imported as needed.
- CMorhisms and CRelationClasses should be Required but never imported.
- There are notations CEquivalence and CProper that refer to the Type versions.
- The "_ ==> ..." argumentof CProper is parsed using the respectful from CMorphisms.
*)

Notation CEquivalence := CRelationClasses.Equivalence.
Notation CProper := CMorphisms.Proper.
(* Declare Scope csignature. compat:coq-8.9*)
Delimit Scope csignature with C.
Notation "A ==> B" := (@CMorphisms.respectful _ _ (A%C) (B%C)) : csignature.
Arguments CMorphisms.Proper [A] _%C _.

Section CProper.
Variables A B C: Type.
Notation i R := (fun x y => inhabited (R x y)). 
Variable R: A -> A -> Type.
Variable S: B -> B -> Type.
Variable T: C -> C -> Type.
Variable f: A -> B.
Hypothesis Hf: CProper (R ==> S) f.
Lemma CProper1: Proper (i R ==> i S) f.
Proof. intros x y [H]. exists. by apply Hf. Qed.
Variable g: A -> B -> C.
Hypothesis Hg: CProper (R ==> S ==> T) g.
Lemma CProper2: Proper (i R ==> i S ==> i T) g.
Proof. intros x y [E] u v [F]. exists. by apply Hg. Qed.
End CProper.

(** ** setoids *)
Structure setoid :=
  Setoid {
      car:> Type;
      eqv: relation car;
      Eqv: Equivalence eqv
    }.
Arguments eqv {_} : simpl never. 
Infix "≡" := eqv (at level 79).
Global Existing Instance Eqv.

Definition eq_setoid (X: Type): setoid := Setoid (@eq_equivalence X).

Lemma eqvxx (X : setoid) (x : X) : x ≡ x. reflexivity. Qed.
Arguments eqvxx {X x}.

(** ** label structures (Definition 4.1) *)
(* ingredients required to label graphs
   - eqv' x y = eqv x y° (when we have an involution _°)
   - eqv' _ _ = False    (otherwise)
 *)

Class monoidLaws {X : setoid} (mon0 : X) (mon2 : X -> X -> X) :=
  MonoidLaws {
      mon_eqv: Proper (eqv ==> eqv ==> eqv) mon2;
      monA: forall x y z, mon2 x (mon2 y z) ≡ mon2 (mon2 x y) z;
      monC: forall x y, mon2 x y ≡ mon2 y x;
      monU: forall x, mon2 x mon0 ≡ x
    }.
Global Existing Instance mon_eqv.  

Record labels :=
  Labels {
      lv: setoid;
      mon0: lv;
      mon2: lv -> lv -> lv;
      lv_monoid: monoidLaws mon0 mon2;
      le: setoid;
      eqv': relation le;
      Eqv'_sym: Symmetric eqv';
      eqv01: forall x y z, eqv  x y -> eqv' y z -> eqv' x z;
      eqv11: forall x y z, eqv' x y -> eqv' y z -> eqv  x z;
    }.
Global Existing Instance lv_monoid.
Arguments mon0 {_}: simpl never.
Arguments mon2 {_}: simpl never.
Arguments eqv' {_}.
Infix "≡'" := eqv' (at level 79).

Lemma eqv10 (l : labels) (x y z : le l) : eqv' x y -> eqv  y z -> eqv' x z.
Proof. move => /Eqv'_sym A B. apply: Eqv'_sym. apply: eqv01 A. by symmetry. Qed.

(* switch between [≡] and [≡'] based on a Boolean (useful for defining potentially edge swapping homomorphisms) *)
Definition eqv_ (X: labels) (b: bool) (x y: le X) := if b then x ≡' y else x ≡ y.
Notation "x ≡[ b ] y" := (eqv_ b x y) (at level 79).
Global Instance eqv_sym {X: labels} {b}: Symmetric (@eqv_ X b).
Proof. case b=> x y/=. apply Eqv'_sym. by symmetry. Qed.

Lemma eqvb_trans (X : labels) (u v w : le X) (b1 b2 : bool) : 
  u ≡[b1] v -> v ≡[b2] w -> u ≡[b1 (+) b2] w.
Proof. 
  case: b1; case: b2 => //=; eauto using eqv10, eqv01, eqv11. 
  by transitivity v.
Qed.

(* variants of the above that are more useful for backward chaining *)
Lemma eqvb_transR (X : labels) b b' (u v v' : le X) : 
  u ≡[b (+) b'] v' ->  v' ≡[b'] v ->  u ≡[b] v.
Proof. move => A B. move:(eqvb_trans A B). by rewrite -addbA addbb addbF. Qed.

Lemma eqvb_transL (X : labels) b b' (u u' v : le X) : 
  u' ≡[b (+) b'] v ->  u ≡[b'] u' ->  u ≡[b] v.
Proof. move => A B. move:(eqvb_trans B A). by rewrite addbC -addbA addbb addbF. Qed.

Global Instance eqv_morphim (X: labels) : 
  Proper (eq ==> eqv ==> eqv ==> iff) (@eqv_ X).
Proof. 
  move => b ? <- x x' xx y y' yy. 
  change (x ≡[false] x') in xx. change (y ≡[false] y') in yy. split => H. 
  - symmetry in xx. apply: eqvb_transR yy. apply: eqvb_transL xx. by rewrite !addbF.
  - symmetry in yy. apply: eqvb_transR yy. apply: eqvb_transL xx. by rewrite !addbF.
Qed.

Lemma eq_unit (a b: unit): a = b.
Proof. by case a; case b. Qed.
Hint Resolve eq_unit: core.

(* label structure for letter-labeled graphs (Definition 4.2) *)
Definition flat_labels (X: Type): labels.
  refine (@Labels (eq_setoid unit) tt (fun _ _ => tt) _ (eq_setoid X) (fun _ _ => False) _ _ _).
  abstract by split.
  all: abstract by []. 
Defined.
  

(* notations for vertex labels *)
(* Declare Scope labels. compat:coq-8.9*)
Bind Scope labels with lv.
Delimit Scope labels with lbl.
Infix "⊗" := mon2 (left associativity, at level 25): labels.
Notation "1" := mon0: labels.

(** ** BigOps over the label monoid *)

Section Theory.
Variables (X : setoid) (mon0 : X) (mon2 : X -> X -> X).
Context {X_laws : monoidLaws mon0 mon2}.
Notation "1" := mon0.
Infix "⊗" := mon2 (left associativity, at level 25).

Lemma monUl (x : X) : 1 ⊗ x ≡ x. by rewrite monC monU. Qed.

Lemma big_mkcond (I : eqType) (r : seq I) (P : pred I) (F : I -> X) :
  \big[mon2/1]_(i <- r | P i) F i ≡ \big[mon2/1]_(i <- r) (if P i then F i else 1).
Proof. rewrite unlock. elim: r => //= i r H. by case P; rewrite H ?monUl. Qed.

Lemma big_cat (I : eqType) (r1 r2 : seq I) (P : pred I) (F : I -> X) :
      \big[mon2/1]_(i <- (r1 ++ r2) | P i) F i ≡
      (\big[mon2/1]_(i <- r1 | P i) F i) ⊗ (\big[mon2/1]_(i <- r2 | P i) F i).
Proof.
rewrite !(big_mkcond _ P). elim: r1 => /= [|i r1 IH]; first by rewrite big_nil monUl.
by rewrite !big_cons IH monA.
Qed.

Lemma perm_big (I : eqType) r1 r2 (P : pred I) (F : I -> X) :
  perm_eq r1 r2 ->
  \big[mon2/1]_(i <- r1 | P i) F i ≡ \big[mon2/1]_(i <- r2 | P i) F i.
Proof.
move/permP; rewrite !(big_mkcond _ P).
elim: r1 r2 => [|i r1 IHr1] r2 eq_r12.
  by case: r2 eq_r12 => // i r2; move/(_ (pred1 i)); rewrite /= eqxx.
have r2i: i \in r2 by rewrite -has_pred1 has_count -eq_r12 /= eqxx.
case/splitPr: r2 / r2i => [r3 r4] in eq_r12 *. rewrite big_cat /= !big_cons.
rewrite monA [_ ⊗ if _ then _ else _]monC -monA. rewrite -big_cat. 
rewrite (IHr1 (r3 ++ r4)) //.  move => a. move/(_ a) : eq_r12. 
rewrite !count_cat /= addnCA. apply: addnI.
Qed.

Lemma eqv_map (I1 I2 : finType) (r1 : seq I1) (P1 : pred I1) (P2 : pred I2) 
  (f : I1 -> I2) (F1 : I1 -> X) (F2 : I2 -> X) :
   (forall x, P1 x = P2 (f x)) -> (forall i : I1, P1 i -> F1 i ≡ F2 (f i)) -> 
   \big[mon2/1]_(i <- r1 | P1 i) F1 i ≡ \big[mon2/1]_(i <- map f r1 | P2 i) F2 i.
Proof.
  
  move => HP HF. elim r1 => [|k r2 IH]; first by rewrite !big_nil.
  rewrite /= !big_cons -HP. case: (boolP (P1 k)) => [Pk|_]; by rewrite -?HF ?IH.
Qed.

Lemma eqv_big_bij (I1 I2 : finType) (f : I1 -> I2) 
   (r1 : seq I1) (r2 : seq I2) (P1 : pred I1) (P2 : pred I2) (F1 : I1 -> X) (F2 : I2 -> X) :
   perm_eq r2 (map f r1) -> (forall x, P1 x = P2 (f x)) -> (forall i : I1, P1 i -> F1 i ≡ F2 (f i)) -> 
   \big[mon2/1]_(i <- r1 | P1 i) F1 i ≡ \big[mon2/1]_(i <- r2 | P2 i) F2 i.
Proof. move => pr HP HF. rewrite (perm_big _ _ pr). exact: eqv_map. Qed.

Lemma big_split I r (P : pred I) (F1 F2 : I -> X) :
  \big[mon2/1]_(i <- r | P i) (F1 i ⊗ F2 i) ≡
  (\big[mon2/1]_(i <- r | P i) F1 i) ⊗ \big[mon2/1]_(i <- r | P i) F2 i.
Proof.
  elim/big_rec3 : _ => [|i x y z Pi ->]; rewrite ?monU //.
  rewrite -!monA. apply: mon_eqv => //. by rewrite monA [_ ⊗ y]monC monA.
Qed.

Lemma eqv_bigr (I : Type) (r : seq I) (P : pred I) (F1 F2 : I -> X) :
    (forall i : I, P i -> F1 i ≡ F2 i) -> \big[mon2/1]_(i <- r | P i) F1 i ≡ \big[mon2/1]_(i <- r | P i) F2 i.
Proof. elim/big_rec2 : _ => // i x y Pi H1 H2. by rewrite H2 ?H1. Qed.

Lemma eqv_bigl I r (P1 P2 : pred I) (F : I -> X) :
  P1 =1 P2 ->
  \big[mon2/1]_(i <- r | P1 i) F i ≡ \big[mon2/1]_(i <- r | P2 i) F i.
Proof. by move=> eqP12; rewrite -!(big_filter r) (eq_filter eqP12). Qed.

Lemma bigID (I:eqType) r (a P : pred I) (F : I -> X) :
  \big[mon2/1]_(i <- r | P i) F i ≡
  (\big[mon2/1]_(i <- r | P i && a i) F i) ⊗ \big[mon2/1]_(i <- r | P i && ~~ a i) F i.
Proof.
  rewrite !(@big_mkcond I r _ F) -big_split. 
  apply: eqv_bigr => i; case: (a i); by rewrite /= ?andbT ?andbF ?monU ?monUl.
Qed.
Arguments bigID [I r] a P F.

Lemma big_seq1 (I : Type) (i : I) (F : I -> X) : \big[mon2/1]_(j <- [:: i]) F j ≡ F i.
Proof. by rewrite big_cons big_nil monU. Qed.

Lemma big_pred1_eq (I : finType) (i : I) (F : I -> X) :
  \big[mon2/1]_(j | j == i) F j ≡ F i.
Proof. 
  rewrite -big_filter filter_pred1_uniq //; first by rewrite big_seq1.
  solve [by rewrite /index_enum -?enumT ?enum_uniq (* mathcomp-1.9.0 *)
        |exact: index_enum_uniq].                  (* mathcomp-1.10.0 *)
Qed.

Lemma big_pred1 (I : finType) i (P : pred I) (F : I -> X) :
  P =1 pred1 i -> \big[mon2/1]_(j | P j) F j ≡ F i.
Proof.  move/(eq_bigl _ _)->; apply: big_pred1_eq. Qed.

Lemma bigD1 (I : finType) j (P : pred I) (F : I -> X) : 
  P j -> \big[mon2/1]_(i | P i) F i ≡ F j ⊗ \big[mon2/1]_(i | P i && (i != j)) F i.
Proof.
  move=> Pj; rewrite (bigID (pred1 j)); apply mon_eqv => //.
  apply: big_pred1 => i /=. by rewrite /= andbC; case: eqP => // ->.
Qed.
Arguments bigD1 [I] j [P F].

Lemma reindex_onto (I J : finType) (h : J -> I) h' (P : pred I) (F : I -> X) :
   (forall i, P i -> h (h' i) = i) ->
  \big[mon2/1]_(i | P i) F i ≡
  \big[mon2/1]_(j | P (h j) && (h' (h j) == j)) F (h j).
Proof.
move=> h'K; elim: {P}_.+1 {-3}P h'K (ltnSn #|P|) => //= n IHn P h'K.
case: (pickP P) => [i Pi | P0 _]; last first.
  by rewrite !big_pred0 // => j; rewrite P0.
rewrite ltnS (cardD1x Pi); move/IHn {n IHn} => IH.
rewrite (bigD1 i Pi) (bigD1 (h' i)) h'K ?Pi ?eq_refl //=. apply: mon_eqv => //.
rewrite {}IH => [|j]; [apply: eqv_bigl => j | by case/andP; auto].
rewrite andbC -andbA (andbCA (P _)); case: eqP => //= hK; congr (_ && ~~ _).
by apply/eqP/eqP=> [<-|->] //; rewrite h'K.
Qed.
Arguments reindex_onto [I J] h h' [P F].


Lemma reindex (I J : finType) (h : J -> I) (P : pred I) (F : I -> X) :
    {on [pred i | P i], bijective h} ->
  \big[mon2/1]_(i | P i) F i ≡ \big[mon2/1]_(j | P (h j)) F (h j).
Proof.
case=> h' hK h'K; rewrite (reindex_onto h h' h'K).
by apply eqv_bigl => j; rewrite !inE; case Pi: (P _); rewrite //= hK ?eqxx.
Qed.
Arguments reindex [I J] h P F.

Lemma eqv_big I (r:seq I) (P1 P2 : pred I) (F1 F2 : I -> X) :
  P1 =1 P2 -> (forall i, P1 i -> F1 i ≡ F2 i) ->
  \big[mon2/1]_(i <- r | P1 i) F1 i ≡ \big[mon2/1]_(i <- r | P2 i) F2 i.
Proof. by move/eqv_bigl <-; move/eqv_bigr->. Qed.

Lemma partition_big (I J : finType) (P : pred I) p (Q : pred J) (F : I -> X) :
    (forall i, P i -> Q (p i)) ->
      \big[mon2/1]_(i | P i) F i ≡
         \big[mon2/1]_(j | Q j) \big[mon2/1]_(i | P i && (p i == j)) F i.
Proof.
move=> Qp; transitivity (\big[mon2/1]_(i | P i && Q (p i)) F i).
  by apply: eqv_bigl => i; case Pi: (P i); rewrite // Qp.
elim: {Q Qp}_.+1 {-2}Q (ltnSn #|Q|) => // n IHn Q.
case: (pickP Q) => [j Qj | Q0 _]; last first.
  by rewrite !big_pred0 // => i; rewrite Q0 andbF.
rewrite ltnS (cardD1x Qj) (bigD1 j) //; move/IHn=> {n IHn} <-.
rewrite (bigID (fun i => p i == j)) => /=. apply: mon_eqv; apply: eqv_bigl => i.
  case: eqP => [-> | _] ; by rewrite ?(Qj). 
by rewrite andbA.
Qed.


(* TODO: eliminate [i1] and [i2], which are only used as defaults for reindexing *)
Lemma big_sum (I1 I2 : finType) (i1 : I1) (i2 : I2) (P : pred (I1 + I2)) (F : (I1 + I2) -> X) : 
  \big[mon2/1]_(x | P x) F x ≡ 
  (\big[mon2/1]_(x | P (inl x)) F (inl x)) ⊗ (\big[mon2/1]_(x | P (inr x)) F (inr x)).
Proof.
  rewrite (bigID is_inl). apply: mon_eqv. 
  - rewrite (reindex inl). exact: eqv_bigl. 
    exists (fun x => if x is inl x then x else i1) => //. move => [x|x] //. by rewrite inE /= andbF.
  - rewrite (reindex inr). exact: eqv_bigl. 
    exists (fun x => if x is inr x then x else i2) => //. move => [x|x] //. by rewrite inE /= andbF.
Qed.
Arguments big_sum [I1 I2] i1 i2 P F.

Lemma big_unit (P : pred unit) (F : unit -> X) : 
  \big[mon2/1]_(x | P x) F x ≡ if P tt then F tt else 1.
Proof.
case Ptt : (P tt); last by rewrite big_pred0 // => -[]. 
by rewrite (@big_pred1 _ tt) //; case.
Qed.

Lemma big_inj2_eq (I1 I2 : finType) (F : I1 -> X) (f : I1 -> I2) (y : I1) :
  injective f -> \big[mon2/mon0]_(x | f x == f y) F x ≡ F y.
Proof. move => inj_f; rewrite (@big_pred1 _ y) //= => x; exact: inj_eq. Qed.

End Theory.
Arguments reindex_onto [X mon0 mon2 _ I J] h h' [P F].
Arguments reindex [X mon0 mon2 _ I J] h [P F].
Arguments bigD1 [X mon0 mon2 _ I] j [P F].
Arguments partition_big [X mon0 mon2 _ I J P] p Q [F].
Arguments big_pred1 [X mon0 mon2 _ I] i P F.