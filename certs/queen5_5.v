
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import preliminaries digraph sgraph dom.
Require Import check_ir prelim.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


Definition n := 25.

(**********************************************************************************)
Section Instance.
  Let inst_vert := 'I_n.
  Let inst_adj(u v : nat) :=
    match u, v with
    | 0, 6 => true
    | 0, 12 => true
    | 0, 18 => true
    | 0, 24 => true
    | 0, 1 => true
    | 0, 2 => true
    | 0, 3 => true
    | 0, 4 => true
    | 0, 5 => true
    | 0, 10 => true
    | 0, 15 => true
    | 0, 20 => true
    | 1, 7 => true
    | 1, 13 => true
    | 1, 19 => true
    | 1, 5 => true
    | 1, 2 => true
    | 1, 3 => true
    | 1, 4 => true
    | 1, 6 => true
    | 1, 11 => true
    | 1, 16 => true
    | 1, 21 => true
    | 2, 8 => true
    | 2, 14 => true
    | 2, 6 => true
    | 2, 10 => true
    | 2, 3 => true
    | 2, 4 => true
    | 2, 7 => true
    | 2, 12 => true
    | 2, 17 => true
    | 2, 22 => true
    | 3, 9 => true
    | 3, 7 => true
    | 3, 11 => true
    | 3, 15 => true
    | 3, 4 => true
    | 3, 8 => true
    | 3, 13 => true
    | 3, 18 => true
    | 3, 23 => true
    | 4, 8 => true
    | 4, 12 => true
    | 4, 16 => true
    | 4, 20 => true
    | 4, 9 => true
    | 4, 14 => true
    | 4, 19 => true
    | 4, 24 => true
    | 5, 11 => true
    | 5, 17 => true
    | 5, 23 => true
    | 5, 6 => true
    | 5, 7 => true
    | 5, 8 => true
    | 5, 9 => true
    | 5, 10 => true
    | 5, 15 => true
    | 5, 20 => true
    | 6, 12 => true
    | 6, 18 => true
    | 6, 24 => true
    | 6, 10 => true
    | 6, 7 => true
    | 6, 8 => true
    | 6, 9 => true
    | 6, 11 => true
    | 6, 16 => true
    | 6, 21 => true
    | 7, 13 => true
    | 7, 19 => true
    | 7, 11 => true
    | 7, 15 => true
    | 7, 8 => true
    | 7, 9 => true
    | 7, 12 => true
    | 7, 17 => true
    | 7, 22 => true
    | 8, 14 => true
    | 8, 12 => true
    | 8, 16 => true
    | 8, 20 => true
    | 8, 9 => true
    | 8, 13 => true
    | 8, 18 => true
    | 8, 23 => true
    | 9, 13 => true
    | 9, 17 => true
    | 9, 21 => true
    | 9, 14 => true
    | 9, 19 => true
    | 9, 24 => true
    | 10, 16 => true
    | 10, 22 => true
    | 10, 11 => true
    | 10, 12 => true
    | 10, 13 => true
    | 10, 14 => true
    | 10, 15 => true
    | 10, 20 => true
    | 11, 17 => true
    | 11, 23 => true
    | 11, 15 => true
    | 11, 12 => true
    | 11, 13 => true
    | 11, 14 => true
    | 11, 16 => true
    | 11, 21 => true
    | 12, 18 => true
    | 12, 24 => true
    | 12, 16 => true
    | 12, 20 => true
    | 12, 13 => true
    | 12, 14 => true
    | 12, 17 => true
    | 12, 22 => true
    | 13, 19 => true
    | 13, 17 => true
    | 13, 21 => true
    | 13, 14 => true
    | 13, 18 => true
    | 13, 23 => true
    | 14, 18 => true
    | 14, 22 => true
    | 14, 19 => true
    | 14, 24 => true
    | 15, 21 => true
    | 15, 16 => true
    | 15, 17 => true
    | 15, 18 => true
    | 15, 19 => true
    | 15, 20 => true
    | 16, 22 => true
    | 16, 20 => true
    | 16, 17 => true
    | 16, 18 => true
    | 16, 19 => true
    | 16, 21 => true
    | 17, 23 => true
    | 17, 21 => true
    | 17, 18 => true
    | 17, 19 => true
    | 17, 22 => true
    | 18, 24 => true
    | 18, 22 => true
    | 18, 19 => true
    | 18, 23 => true
    | 19, 23 => true
    | 19, 24 => true
    | 20, 21 => true
    | 20, 22 => true
    | 20, 23 => true
    | 20, 24 => true
    | 21, 22 => true
    | 21, 23 => true
    | 21, 24 => true
    | 22, 23 => true
    | 22, 24 => true
    | 23, 24 => true
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
  Let inst_set := [set 'v0; 'v3; 'v6; 'v9; 'v14].

  Section List_of_Set.
    Definition inst_list := [:: 'v0; 'v3; 'v6; 'v9; 'v14].

    Fact inst_list_eq_inst_set : inst_list =i inst_set.
    Proof. by move=> v ; rewrite !inE /= ; try rewrite !orbA. Qed.

    Fact inst_list_uniq : uniq inst_list.
    Proof. done. Qed.
  End List_of_Set.

  Fact inst_set_card : #|inst_set| = 5.
  Proof. by rewrite -(eq_card inst_list_eq_inst_set) (card_uniqP inst_list_uniq). Qed.

  Fact inst_set_is_irr : @irredundant inst inst_set.
  Proof.
    apply (irredundant_checkP inst inst_list (ord_enum_eqT n)).
    - exact: inst_list_uniq.
    - exact: inst_list_eq_inst_set.
    - done.
  Qed.

  Fact IR_lb : IR inst >= 5.
  Proof.
    rewrite eq_IR_IR1 ; move: inst_set_card ; rewrite (@cardwset1 inst inst_set).
    move<- ; apply: IR_max ; exact: inst_set_is_irr.
  Qed.

End Certificate.
