
(* Template for a certificate *)

From mathcomp Require Import all_ssreflect.
Require Import preliminaries digraph sgraph dom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


(* give_sg generate the sedge relation from a function f such that:
     f u v (with 0 <= u < v < n) is true iff (u,v) is an edge of G *)
Definition give_sg (f : nat -> nat -> bool) (n : nat) (i j : 'I_n) :=
  let u := nat_of_ord i in
    let v := nat_of_ord j in
      if (u == v) then false else
        if (u < v) then f u v else f v u.

Fact give_sg_sym (f : nat -> nat -> bool) (n : nat) : symmetric (give_sg f (n:=n)).
Proof.
  rewrite /symmetric /give_sg => u v.
  case: (boolP (u == v))=> [ | uneqv] ; first by move/eqP->.
  rewrite (ifN _ _ uneqv).
  rewrite eq_sym in uneqv.
  rewrite (ifN _ _ uneqv).
  rewrite neq_ltn in uneqv.
  by case: (orP uneqv) => ultv;
    move: (ltnW ultv) ; rewrite leqNgt => nvltu; rewrite (ifN _ _ nvltu) ultv.
Qed.

Fact give_sg_irrefl (f : nat -> nat -> bool) (n : nat) : irreflexive (give_sg f (n:=n)).
Proof. by rewrite /irreflexive /give_sg => ? ; rewrite eq_refl. Qed.


Definition n := 5.

(**********************************************************************************)
Section Instance.
  Let inst_vert := 'I_n.
  Let inst_adj(u v : nat) :=
    match u, v with
    | 0, 2 => true
    | 1, 3 => true
    | 2, 3 => true
    | 2, 4 => true
    | 3, 4 => true
    | _, _ => false
  end.

  Let inst_rel := [ rel u v : inst_vert | give_sg inst_adj u v ].
  Let inst_sym : symmetric inst_rel. Proof. exact: give_sg_sym. Qed.
  Let inst_irrefl : irreflexive inst_rel. Proof. exact: give_sg_irrefl. Qed.
  Definition inst := SGraph inst_sym inst_irrefl.
End Instance.

Notation "''v' m" := (@Ordinal n m isT) (at level 0, m at level 8, format "''v' m").

(* UNWEIGHTED CASE *)

(**********************************************************************************)
Section Certificate.
  Let inst_set := [set 'v0; 'v1; 'v4].

  Fact inst_set_is_irr : @irredundant inst inst_set.
  Proof.
    apply/irredundantP.
    move=> [v vltn] ; do 5 try destruct v.
    (* first, discard all the cases where v is not in inst_set *)
    all : try ( rewrite (bool_irrelevance vltn isT);
                by apply: contraLR => _ ; rewrite /inst_set !inE ).
    (* for the remaining cases, provide a private vertex *)
    - rewrite (bool_irrelevance vltn isT) => _.
      apply/set0Pn ; exists 'v0 ; apply/privateP ; split=> //.
      move=> [u ultn] ; do 5 try destruct u.
      all : try by rewrite (bool_irrelevance ultn isT).
      all : try ( rewrite (bool_irrelevance ultn isT) => H _;
                  by move: H ; apply: contraPeq => _ ; rewrite /inst_set !inE ).
      suff: ~ (u.+1.+4 < n) by contradiction.
      by apply/negP ; rewrite /=.
    - rewrite (bool_irrelevance vltn isT) => _.
      apply/set0Pn ; exists 'v1 ; apply/privateP ; split=> //.
      move=> [u ultn] ; do 5 try destruct u.
      all : try by rewrite (bool_irrelevance ultn isT).
      all : try ( rewrite (bool_irrelevance ultn isT) => H _;
                  by move: H ; apply: contraPeq => _ ; rewrite /inst_set !inE ).
      suff: ~ (u.+1.+4 < n) by contradiction.
      by apply/negP ; rewrite /=.
    - rewrite (bool_irrelevance vltn isT) => _.
      apply/set0Pn ; exists 'v4 ; apply/privateP ; split=> //.
      move=> [u ultn] ; do 5 try destruct u.
      all : try by rewrite (bool_irrelevance ultn isT).
      all : try ( rewrite (bool_irrelevance ultn isT) => H _;
                  by move: H ; apply: contraPeq => _ ; rewrite /inst_set !inE ).
      suff: ~ (u.+1.+4 < n) by contradiction.
      by apply/negP ; rewrite /=.
    - suff: ~ (v.+1.+4 < n) by contradiction.
      by apply/negP ; rewrite /=.
  Qed.

  Fact IR_lb : IR inst >= 3.
  Proof.
    rewrite eq_IR_IR1.
    suff: weight_set (@ones inst) inst_set = 3.
    move<- ; apply: IR_max ; exact: inst_set_is_irr.
    by rewrite -cardwset1 /inst_set -!setUA !cardsU1 !inE negb_or cards1.
  Qed.


End Certificate.

(* WEIGHTED CASE *)

Lemma weightsU1 (G : sgraph) (a : G) (A : {set G}) (weight : G -> nat):
  weight_set weight (a |: A) = (weight a) * (a \notin A) + weight_set weight A.
Proof.
  rewrite /weight_set.
  case: (boolP (a \notin A)) => [H | H].
  - by rewrite (big_setU1 _ H) /= muln1.
  - rewrite muln0 add0n.
    suff iden : a |: A = A by under eq_bigl => x do rewrite iden.
    apply/eqP ; rewrite eqEsubset ; apply/andP ; split.
    + apply/subsetP => x ; rewrite in_setU1 ; case/orP=> //.
      by move/eqP-> ; move: H ; apply: contraR.
    + apply/subsetP => ? ; exact: setU1r.
Qed.

(**********************************************************************************)
Section Instance.
  Definition weight (v : inst) := match v with
      | Ordinal 0 _ => 1
      | Ordinal 1 _ => 1
      | Ordinal 2 _ => 2
      | Ordinal 3 _ => 2
      | Ordinal _ _ => 1
      end.
End Instance.

(**********************************************************************************)
Section Certificate.
  Let inst_set := [set 'v2; 'v3].

  Fact inst_set_is_irr' : @irredundant inst inst_set.
    apply/irredundantP.
    move=> [v vltn] ; do 5 try destruct v.
    (* first, discard all the cases where v is not in inst_set *)
    all : try ( rewrite (bool_irrelevance vltn isT);
                by apply: contraLR => _ ; rewrite /inst_set !inE ).
    (* for the remaining cases, provide a private vertex *)
    - rewrite (bool_irrelevance vltn isT) => _.
      apply/set0Pn ; exists 'v0 ; apply/privateP ; split=> //.
      move=> [u ultn] ; do 5 try destruct u.
      all : try by rewrite (bool_irrelevance ultn isT).
      all : try ( rewrite (bool_irrelevance ultn isT) => H _;
                  by move: H ; apply: contraPeq => _ ; rewrite /inst_set !inE ).
      suff: ~ (u.+1.+4 < n) by contradiction.
      by apply/negP ; rewrite /=.
    - rewrite (bool_irrelevance vltn isT) => _.
      apply/set0Pn ; exists 'v1 ; apply/privateP ; split=> //.
      move=> [u ultn] ; do 5 try destruct u.
      all : try by rewrite (bool_irrelevance ultn isT).
      all : try ( rewrite (bool_irrelevance ultn isT) => H _;
                  by move: H ; apply: contraPeq => _ ; rewrite /inst_set !inE ).
      suff: ~ (u.+1.+4 < n) by contradiction.
      by apply/negP ; rewrite /=.
    - suff: ~ (v.+1.+4 < n) by contradiction.
      by apply/negP ; rewrite /=.
  Qed.

  Fact IR_w_lb : IR_w inst weight >= 4.
  Proof.
    suff: weight_set weight inst_set = 4.
    move<- ; apply: IR_max ; exact: inst_set_is_irr'.
(* add -!setU1 after /inst_set and negb_or after !inE
            if inst_set has 3 or more elements. *)
    by rewrite /inst_set !weightsU1 !inE /weight_set big_set1.
  Qed.

End Certificate.
