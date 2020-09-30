
(* Template for a certificate *)

From mathcomp Require Import all_ssreflect.
Require Import preliminaries digraph sgraph dom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


Definition n := 11.

(**********************************************************************************)
Section Instance.
  Let inst_vert := 'I_n.
  Let inst_adj(u v : nat) :=
    match u, v with
    | 0, 1 => true
    | 0, 3 => true
    | 0, 6 => true
    | 0, 8 => true
    | 1, 2 => true
    | 1, 5 => true
    | 1, 7 => true
    | 2, 4 => true
    | 2, 6 => true
    | 2, 9 => true
    | 3, 4 => true
    | 3, 5 => true
    | 3, 9 => true
    | 4, 7 => true
    | 4, 8 => true
    | 5, 10 => true
    | 6, 10 => true
    | 7, 10 => true
    | 8, 10 => true
    | 9, 10 => true
    | _, _ => false
    end.

  Let inst_rel := [ rel u v : inst_vert | give_sg inst_adj u v ].
  Let inst_sym : symmetric inst_rel. Proof. exact: give_sg_sym. Qed.
  Let inst_irrefl : irreflexive inst_rel. Proof. exact: give_sg_irrefl. Qed.
  Definition inst := SGraph inst_sym inst_irrefl.
End Instance.

Notation "''v' m" := (@Ordinal n m isT) (at level 0, m at level 8, format "''v' m").

(**********************************************************************************)
Section Certificate.
  Let inst_set := [set 'v5; 'v6; 'v7; 'v8; 'v9].

  Fact inst_set_is_irr : @irredundant inst inst_set.
  Proof.
    apply/irredundantP.
    move=> [v vltn] ; do 11 try destruct v.
    all : try ( rewrite (bool_irrelevance vltn isT);
                by apply: contraLR => _ ; rewrite /inst_set !inE ).
    - rewrite(bool_irrelevance vltn isT) => _.
      apply/set0Pn; exists 'v5 ; apply/privateP ; split=> //.
      move => [u ultn]; do 11 try destruct u.
      all : try by rewrite(bool_irrelevance ultn isT).
      all : try ( rewrite(bool_irrelevance ultn isT) => H _;
                by move: H; apply: contraPeq => _; rewrite /inst_set !inE ).
      suff : False by contradiction.
      by move: ultn; apply/negP.
    - rewrite(bool_irrelevance vltn isT) => _.
      apply/set0Pn; exists 'v6 ; apply/privateP ; split=> //.
      move => [u ultn]; do 11 try destruct u.
      all : try by rewrite(bool_irrelevance ultn isT).
      all : try ( rewrite(bool_irrelevance ultn isT) => H _;
                by move: H; apply: contraPeq => _; rewrite /inst_set !inE ).
      suff : False by contradiction.
      by move: ultn; apply/negP.
    - rewrite(bool_irrelevance vltn isT) => _.
      apply/set0Pn; exists 'v7 ; apply/privateP ; split=> //.
      move => [u ultn]; do 11 try destruct u.
      all : try by rewrite(bool_irrelevance ultn isT).
      all : try ( rewrite(bool_irrelevance ultn isT) => H _;
                by move: H; apply: contraPeq => _; rewrite /inst_set !inE ).
      suff : False by contradiction.
      by move: ultn; apply/negP.
    - rewrite(bool_irrelevance vltn isT) => _.
      apply/set0Pn; exists 'v8 ; apply/privateP ; split=> //.
      move => [u ultn]; do 11 try destruct u.
      all : try by rewrite(bool_irrelevance ultn isT).
      all : try ( rewrite(bool_irrelevance ultn isT) => H _;
                by move: H; apply: contraPeq => _; rewrite /inst_set !inE ).
      suff : False by contradiction.
      by move: ultn; apply/negP.
    - rewrite(bool_irrelevance vltn isT) => _.
      apply/set0Pn; exists 'v9 ; apply/privateP ; split=> //.
      move => [u ultn]; do 11 try destruct u.
      all : try by rewrite(bool_irrelevance ultn isT).
      all : try ( rewrite(bool_irrelevance ultn isT) => H _;
                by move: H; apply: contraPeq => _; rewrite /inst_set !inE ).
      suff : False by contradiction.
      by move: ultn; apply/negP.
    - suff: False by contradiction.
      by move: vltn ; apply/negP.
  Qed.

  Fact IR_lb : IR inst >= 5.
  Proof.
    rewrite eq_IR_IR1.
    suff: weight_set (@ones inst) inst_set = 5.
    move<- ; apply: IR_max ; exact: inst_set_is_irr.
    rewrite -cardwset1 /inst_set.
    try rewrite -!setUA.
    rewrite !cardsU1 !inE.
    try rewrite negb_or.
    by rewrite cards1.
  Qed.

End Certificate.
