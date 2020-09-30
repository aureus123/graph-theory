
(* Template for a certificate *)

From mathcomp Require Import all_ssreflect.
Require Import preliminaries digraph sgraph dom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


Definition n := 5.

(**********************************************************************************)
Section Instance.
  Let inst_vert := 'I_n.
  Let inst_adj(u v : nat) :=
    match u, v with
    | 0, 1 => true
    | 0, 4 => true
    | 1, 2 => true
    | 2, 3 => true
    | 3, 4 => true
    | _, _ => false
    end.

  Let inst_rel := [ rel u v : inst_vert | give_sg inst_adj u v ].
  Let inst_sym : symmetric inst_rel. Proof. exact: give_sg_sym. Qed.
  Let inst_irrefl : irreflexive inst_rel. Proof. exact: give_sg_irrefl. Qed.
  Definition inst := SGraph inst_sym inst_irrefl.

  Definition weight (v : inst) := match v with
      | Ordinal 0 _ => 2
      | Ordinal 1 _ => 2
      | Ordinal 2 _ => 1
      | Ordinal 3 _ => 1
      | Ordinal _ _ => 1
      end.
End Instance.

Notation "''v' m" := (@Ordinal n m isT) (at level 0, m at level 8, format "''v' m").

(**********************************************************************************)
Section Certificate.
  Let inst_set := [set 'v0; 'v1].

  Fact inst_set_is_irr' : @irredundant inst inst_set.
    apply/irredundantP.
    move=> [v vltn] ; do 5 try destruct v.
    all : try ( rewrite (bool_irrelevance vltn isT);
                by apply: contraLR => _ ; rewrite /inst_set !inE ).
    - rewrite(bool_irrelevance vltn isT) => _.
      apply/set0Pn; exists 'v4 ; apply/privateP ; split=> //.
      move => [u ultn]; do 5 try destruct u.
      all : try by rewrite(bool_irrelevance ultn isT).
      all : try ( rewrite(bool_irrelevance ultn isT) => H _;
                by move: H; apply: contraPeq => _; rewrite /inst_set !inE ).
      suff : False by contradiction.
      by move: ultn; apply/negP.
    - rewrite(bool_irrelevance vltn isT) => _.
      apply/set0Pn; exists 'v2 ; apply/privateP ; split=> //.
      move => [u ultn]; do 5 try destruct u.
      all : try by rewrite(bool_irrelevance ultn isT).
      all : try ( rewrite(bool_irrelevance ultn isT) => H _;
                by move: H; apply: contraPeq => _; rewrite /inst_set !inE ).
      suff : False by contradiction.
      by move: ultn; apply/negP.
    - suff: False by contradiction.
      by move: vltn ; apply/negP.
  Qed.

  Fact IR_w_lb : IR_w inst weight >= 4.
  Proof.
    suff: weight_set weight inst_set = 4.
    move<- ; apply: IR_max ; exact: inst_set_is_irr'.
    rewrite /inst_set.
    try rewrite -!setUA.
    rewrite !weightsU1 !inE.
    try rewrite negb_or.
    by rewrite /weight_set big_set1.
  Qed.

End Certificate.
