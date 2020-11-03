
From mathcomp Require Import all_ssreflect.
Require Import preliminaries digraph sgraph dom check_ir.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


Definition n := 37.

(**********************************************************************************)
Section Instance.
  Let inst_vert := 'I_n.
  Let inst_adj(u v : nat) :=
    match u, v with
    | 0, 1 => true
    | 0, 3 => true
    | 0, 10 => true
    | 0, 12 => true
    | 1, 2 => true
    | 1, 9 => true
    | 1, 11 => true
    | 2, 5 => true
    | 2, 10 => true
    | 2, 14 => true
    | 3, 4 => true
    | 3, 9 => true
    | 3, 13 => true
    | 4, 7 => true
    | 4, 12 => true
    | 4, 16 => true
    | 5, 6 => true
    | 5, 11 => true
    | 5, 15 => true
    | 6, 8 => true
    | 6, 14 => true
    | 6, 17 => true
    | 7, 8 => true
    | 7, 13 => true
    | 7, 17 => true
    | 8, 15 => true
    | 8, 16 => true
    | 9, 19 => true
    | 9, 21 => true
    | 10, 18 => true
    | 10, 20 => true
    | 11, 19 => true
    | 11, 23 => true
    | 12, 18 => true
    | 12, 22 => true
    | 13, 21 => true
    | 13, 25 => true
    | 14, 20 => true
    | 14, 24 => true
    | 15, 23 => true
    | 15, 26 => true
    | 16, 22 => true
    | 16, 26 => true
    | 17, 24 => true
    | 17, 25 => true
    | 18, 28 => true
    | 18, 30 => true
    | 19, 27 => true
    | 19, 29 => true
    | 20, 28 => true
    | 20, 32 => true
    | 21, 27 => true
    | 21, 31 => true
    | 22, 30 => true
    | 22, 34 => true
    | 23, 29 => true
    | 23, 33 => true
    | 24, 32 => true
    | 24, 35 => true
    | 25, 31 => true
    | 25, 35 => true
    | 26, 33 => true
    | 26, 34 => true
    | 27, 36 => true
    | 28, 36 => true
    | 29, 36 => true
    | 30, 36 => true
    | 31, 36 => true
    | 32, 36 => true
    | 33, 36 => true
    | 34, 36 => true
    | 35, 36 => true
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
  Let inst_set := [set 'v9; 'v10; 'v11; 'v12; 'v13; 'v14; 'v15; 'v16; 'v17; 'v27; 'v28; 'v29; 'v30; 'v31; 'v32; 'v33; 'v34; 'v35].

  Section List_of_Set.
    Definition inst_list := [:: 'v9; 'v10; 'v11; 'v12; 'v13; 'v14; 'v15; 'v16; 'v17; 'v27; 'v28; 'v29; 'v30; 'v31; 'v32; 'v33; 'v34; 'v35].

    Fact inst_list_eq_inst_set : inst_list =i inst_set.
    Proof. by move=> v ; rewrite !inE /= ; try rewrite !orbA. Qed.

    Fact inst_list_uniq : uniq inst_list.
    Proof. done. Qed.
  End List_of_Set.

  Fact inst_set_card : #|inst_set| = 18.
  Proof. by rewrite -(eq_card inst_list_eq_inst_set) (card_uniqP inst_list_uniq). Qed.

  Fact inst_set_is_irr : @irredundant inst inst_set.
  Proof.
    apply (irredundant_checkP inst inst_list (ord_enum_eqT n)).
    - exact: inst_list_uniq.
    - exact: inst_list_eq_inst_set.
    - done.
  Qed.

  Fact IR_lb : IR inst >= 18.
  Proof.
    rewrite eq_IR_IR1 ; move: inst_set_card ; rewrite (@cardwset1 inst inst_set).
    move<- ; apply: IR_max ; exact: inst_set_is_irr.
  Qed.

End Certificate.
