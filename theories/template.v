
(* Resolution of the Upper Weighted Irredundant Problem *)

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
  Let lb := 3.

  Fact inst_set_is_irr : @irredundant inst inst_set.
  Admitted.

  Fact inst_set_card : #|inst_set| = lb.
  Proof. by rewrite /inst_set -!setUA !cardsU1 !inE negb_or cards1. Qed.

  Fact IR_lb : IR inst >= lb.
  Proof.
    rewrite eq_IR_IR1.
    suff: weight_set (@ones inst) inst_set = lb.
    move<- ; apply: IR_max ; exact: inst_set_is_irr.
    rewrite -cardwset1 ; exact: inst_set_card.
  Qed.
End Certificate.

(* WEIGHTED CASE *)

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
  Let lb := 4.

  Fact inst_set_is_irr' : @irredundant inst inst_set.
  Admitted.

  Fact inst_set_weight : weight_set weight inst_set = lb.
  Proof. rewrite /inst_set /weight_set. Admitted.

  Fact IR_w_lb : IR_w inst weight >= lb.
  Proof. rewrite -inst_set_weight ; apply: IR_max ; exact: inst_set_is_irr'. Qed.
End Certificate.
