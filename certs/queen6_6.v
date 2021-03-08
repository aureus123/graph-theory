
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import preliminaries digraph sgraph dom.
Require Import check_ir prelim.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


Definition n := 36.

(**********************************************************************************)
Section Instance.
  Let inst_vert := 'I_n.
  Let inst_adj(u v : nat) :=
    match u, v with
    | 0, 7 => true
    | 0, 14 => true
    | 0, 21 => true
    | 0, 28 => true
    | 0, 35 => true
    | 0, 1 => true
    | 0, 2 => true
    | 0, 3 => true
    | 0, 4 => true
    | 0, 5 => true
    | 0, 6 => true
    | 0, 12 => true
    | 0, 18 => true
    | 0, 24 => true
    | 0, 30 => true
    | 1, 8 => true
    | 1, 15 => true
    | 1, 22 => true
    | 1, 29 => true
    | 1, 6 => true
    | 1, 2 => true
    | 1, 3 => true
    | 1, 4 => true
    | 1, 5 => true
    | 1, 7 => true
    | 1, 13 => true
    | 1, 19 => true
    | 1, 25 => true
    | 1, 31 => true
    | 2, 9 => true
    | 2, 16 => true
    | 2, 23 => true
    | 2, 7 => true
    | 2, 12 => true
    | 2, 3 => true
    | 2, 4 => true
    | 2, 5 => true
    | 2, 8 => true
    | 2, 14 => true
    | 2, 20 => true
    | 2, 26 => true
    | 2, 32 => true
    | 3, 10 => true
    | 3, 17 => true
    | 3, 8 => true
    | 3, 13 => true
    | 3, 18 => true
    | 3, 4 => true
    | 3, 5 => true
    | 3, 9 => true
    | 3, 15 => true
    | 3, 21 => true
    | 3, 27 => true
    | 3, 33 => true
    | 4, 11 => true
    | 4, 9 => true
    | 4, 14 => true
    | 4, 19 => true
    | 4, 24 => true
    | 4, 5 => true
    | 4, 10 => true
    | 4, 16 => true
    | 4, 22 => true
    | 4, 28 => true
    | 4, 34 => true
    | 5, 10 => true
    | 5, 15 => true
    | 5, 20 => true
    | 5, 25 => true
    | 5, 30 => true
    | 5, 11 => true
    | 5, 17 => true
    | 5, 23 => true
    | 5, 29 => true
    | 5, 35 => true
    | 6, 13 => true
    | 6, 20 => true
    | 6, 27 => true
    | 6, 34 => true
    | 6, 7 => true
    | 6, 8 => true
    | 6, 9 => true
    | 6, 10 => true
    | 6, 11 => true
    | 6, 12 => true
    | 6, 18 => true
    | 6, 24 => true
    | 6, 30 => true
    | 7, 14 => true
    | 7, 21 => true
    | 7, 28 => true
    | 7, 35 => true
    | 7, 12 => true
    | 7, 8 => true
    | 7, 9 => true
    | 7, 10 => true
    | 7, 11 => true
    | 7, 13 => true
    | 7, 19 => true
    | 7, 25 => true
    | 7, 31 => true
    | 8, 15 => true
    | 8, 22 => true
    | 8, 29 => true
    | 8, 13 => true
    | 8, 18 => true
    | 8, 9 => true
    | 8, 10 => true
    | 8, 11 => true
    | 8, 14 => true
    | 8, 20 => true
    | 8, 26 => true
    | 8, 32 => true
    | 9, 16 => true
    | 9, 23 => true
    | 9, 14 => true
    | 9, 19 => true
    | 9, 24 => true
    | 9, 10 => true
    | 9, 11 => true
    | 9, 15 => true
    | 9, 21 => true
    | 9, 27 => true
    | 9, 33 => true
    | 10, 17 => true
    | 10, 15 => true
    | 10, 20 => true
    | 10, 25 => true
    | 10, 30 => true
    | 10, 11 => true
    | 10, 16 => true
    | 10, 22 => true
    | 10, 28 => true
    | 10, 34 => true
    | 11, 16 => true
    | 11, 21 => true
    | 11, 26 => true
    | 11, 31 => true
    | 11, 17 => true
    | 11, 23 => true
    | 11, 29 => true
    | 11, 35 => true
    | 12, 19 => true
    | 12, 26 => true
    | 12, 33 => true
    | 12, 13 => true
    | 12, 14 => true
    | 12, 15 => true
    | 12, 16 => true
    | 12, 17 => true
    | 12, 18 => true
    | 12, 24 => true
    | 12, 30 => true
    | 13, 20 => true
    | 13, 27 => true
    | 13, 34 => true
    | 13, 18 => true
    | 13, 14 => true
    | 13, 15 => true
    | 13, 16 => true
    | 13, 17 => true
    | 13, 19 => true
    | 13, 25 => true
    | 13, 31 => true
    | 14, 21 => true
    | 14, 28 => true
    | 14, 35 => true
    | 14, 19 => true
    | 14, 24 => true
    | 14, 15 => true
    | 14, 16 => true
    | 14, 17 => true
    | 14, 20 => true
    | 14, 26 => true
    | 14, 32 => true
    | 15, 22 => true
    | 15, 29 => true
    | 15, 20 => true
    | 15, 25 => true
    | 15, 30 => true
    | 15, 16 => true
    | 15, 17 => true
    | 15, 21 => true
    | 15, 27 => true
    | 15, 33 => true
    | 16, 23 => true
    | 16, 21 => true
    | 16, 26 => true
    | 16, 31 => true
    | 16, 17 => true
    | 16, 22 => true
    | 16, 28 => true
    | 16, 34 => true
    | 17, 22 => true
    | 17, 27 => true
    | 17, 32 => true
    | 17, 23 => true
    | 17, 29 => true
    | 17, 35 => true
    | 18, 25 => true
    | 18, 32 => true
    | 18, 19 => true
    | 18, 20 => true
    | 18, 21 => true
    | 18, 22 => true
    | 18, 23 => true
    | 18, 24 => true
    | 18, 30 => true
    | 19, 26 => true
    | 19, 33 => true
    | 19, 24 => true
    | 19, 20 => true
    | 19, 21 => true
    | 19, 22 => true
    | 19, 23 => true
    | 19, 25 => true
    | 19, 31 => true
    | 20, 27 => true
    | 20, 34 => true
    | 20, 25 => true
    | 20, 30 => true
    | 20, 21 => true
    | 20, 22 => true
    | 20, 23 => true
    | 20, 26 => true
    | 20, 32 => true
    | 21, 28 => true
    | 21, 35 => true
    | 21, 26 => true
    | 21, 31 => true
    | 21, 22 => true
    | 21, 23 => true
    | 21, 27 => true
    | 21, 33 => true
    | 22, 29 => true
    | 22, 27 => true
    | 22, 32 => true
    | 22, 23 => true
    | 22, 28 => true
    | 22, 34 => true
    | 23, 28 => true
    | 23, 33 => true
    | 23, 29 => true
    | 23, 35 => true
    | 24, 31 => true
    | 24, 25 => true
    | 24, 26 => true
    | 24, 27 => true
    | 24, 28 => true
    | 24, 29 => true
    | 24, 30 => true
    | 25, 32 => true
    | 25, 30 => true
    | 25, 26 => true
    | 25, 27 => true
    | 25, 28 => true
    | 25, 29 => true
    | 25, 31 => true
    | 26, 33 => true
    | 26, 31 => true
    | 26, 27 => true
    | 26, 28 => true
    | 26, 29 => true
    | 26, 32 => true
    | 27, 34 => true
    | 27, 32 => true
    | 27, 28 => true
    | 27, 29 => true
    | 27, 33 => true
    | 28, 35 => true
    | 28, 33 => true
    | 28, 29 => true
    | 28, 34 => true
    | 29, 34 => true
    | 29, 35 => true
    | 30, 31 => true
    | 30, 32 => true
    | 30, 33 => true
    | 30, 34 => true
    | 30, 35 => true
    | 31, 32 => true
    | 31, 33 => true
    | 31, 34 => true
    | 31, 35 => true
    | 32, 33 => true
    | 32, 34 => true
    | 32, 35 => true
    | 33, 34 => true
    | 33, 35 => true
    | 34, 35 => true
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
  Let inst_set := [set 'v0; 'v2; 'v4; 'v6; 'v8; 'v10; 'v30].

  Section List_of_Set.
    Definition inst_list := [:: 'v0; 'v2; 'v4; 'v6; 'v8; 'v10; 'v30].

    Fact inst_list_eq_inst_set : inst_list =i inst_set.
    Proof. by move=> v ; rewrite !inE /= ; try rewrite !orbA. Qed.

    Fact inst_list_uniq : uniq inst_list.
    Proof. done. Qed.
  End List_of_Set.

  Fact inst_set_card : #|inst_set| = 7.
  Proof. by rewrite -(eq_card inst_list_eq_inst_set) (card_uniqP inst_list_uniq). Qed.

  Fact inst_set_is_irr : @irredundant inst inst_set.
  Proof.
    apply (irredundant_checkP inst inst_list (ord_enum_eqT n)).
    - exact: inst_list_uniq.
    - exact: inst_list_eq_inst_set.
    - done.
  Qed.

  Fact IR_lb : IR inst >= 7.
  Proof.
    rewrite eq_IR_IR1 ; move: inst_set_card ; rewrite (@cardwset1 inst inst_set).
    move<- ; apply: IR_max ; exact: inst_set_is_irr.
  Qed.

End Certificate.
