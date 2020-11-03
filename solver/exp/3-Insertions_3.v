
From mathcomp Require Import all_ssreflect.
Require Import preliminaries digraph sgraph dom check_ir.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


Definition n := 56.

(**********************************************************************************)
Section Instance.
  Let inst_vert := 'I_n.
  Let inst_adj(u v : nat) :=
    match u, v with
    | 0, 1 => true
    | 0, 3 => true
    | 0, 12 => true
    | 0, 14 => true
    | 1, 2 => true
    | 1, 11 => true
    | 1, 13 => true
    | 2, 5 => true
    | 2, 12 => true
    | 2, 16 => true
    | 3, 4 => true
    | 3, 11 => true
    | 3, 15 => true
    | 4, 7 => true
    | 4, 14 => true
    | 4, 18 => true
    | 5, 6 => true
    | 5, 13 => true
    | 5, 17 => true
    | 6, 9 => true
    | 6, 16 => true
    | 6, 20 => true
    | 7, 8 => true
    | 7, 15 => true
    | 7, 19 => true
    | 8, 10 => true
    | 8, 18 => true
    | 8, 21 => true
    | 9, 10 => true
    | 9, 17 => true
    | 9, 21 => true
    | 10, 19 => true
    | 10, 20 => true
    | 11, 23 => true
    | 11, 25 => true
    | 12, 22 => true
    | 12, 24 => true
    | 13, 23 => true
    | 13, 27 => true
    | 14, 22 => true
    | 14, 26 => true
    | 15, 25 => true
    | 15, 29 => true
    | 16, 24 => true
    | 16, 28 => true
    | 17, 27 => true
    | 17, 31 => true
    | 18, 26 => true
    | 18, 30 => true
    | 19, 29 => true
    | 19, 32 => true
    | 20, 28 => true
    | 20, 32 => true
    | 21, 30 => true
    | 21, 31 => true
    | 22, 34 => true
    | 22, 36 => true
    | 23, 33 => true
    | 23, 35 => true
    | 24, 34 => true
    | 24, 38 => true
    | 25, 33 => true
    | 25, 37 => true
    | 26, 36 => true
    | 26, 40 => true
    | 27, 35 => true
    | 27, 39 => true
    | 28, 38 => true
    | 28, 42 => true
    | 29, 37 => true
    | 29, 41 => true
    | 30, 40 => true
    | 30, 43 => true
    | 31, 39 => true
    | 31, 43 => true
    | 32, 41 => true
    | 32, 42 => true
    | 33, 45 => true
    | 33, 47 => true
    | 34, 44 => true
    | 34, 46 => true
    | 35, 45 => true
    | 35, 49 => true
    | 36, 44 => true
    | 36, 48 => true
    | 37, 47 => true
    | 37, 51 => true
    | 38, 46 => true
    | 38, 50 => true
    | 39, 49 => true
    | 39, 53 => true
    | 40, 48 => true
    | 40, 52 => true
    | 41, 51 => true
    | 41, 54 => true
    | 42, 50 => true
    | 42, 54 => true
    | 43, 52 => true
    | 43, 53 => true
    | 44, 55 => true
    | 45, 55 => true
    | 46, 55 => true
    | 47, 55 => true
    | 48, 55 => true
    | 49, 55 => true
    | 50, 55 => true
    | 51, 55 => true
    | 52, 55 => true
    | 53, 55 => true
    | 54, 55 => true
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
  Let inst_set := [set 'v2; 'v3; 'v4; 'v9; 'v10; 'v22; 'v23; 'v24; 'v25; 'v26; 'v27; 'v28; 'v29; 'v30; 'v31; 'v32; 'v44; 'v45; 'v46; 'v47; 'v48; 'v49; 'v50; 'v51; 'v52; 'v53; 'v54].

  Section List_of_Set.
    Definition inst_list := [:: 'v2; 'v3; 'v4; 'v9; 'v10; 'v22; 'v23; 'v24; 'v25; 'v26; 'v27; 'v28; 'v29; 'v30; 'v31; 'v32; 'v44; 'v45; 'v46; 'v47; 'v48; 'v49; 'v50; 'v51; 'v52; 'v53; 'v54].

    Fact inst_list_eq_inst_set : inst_list =i inst_set.
    Proof. by move=> v ; rewrite !inE /= ; try rewrite !orbA. Qed.

    Fact inst_list_uniq : uniq inst_list.
    Proof. done. Qed.
  End List_of_Set.

  Fact inst_set_card : #|inst_set| = 27.
  Proof. by rewrite -(eq_card inst_list_eq_inst_set) (card_uniqP inst_list_uniq). Qed.

  Fact inst_set_is_irr : @irredundant inst inst_set.
  Proof.
    apply (irredundant_checkP inst inst_list (ord_enum_eqT n)).
    - exact: inst_list_uniq.
    - exact: inst_list_eq_inst_set.
    - done.
  Qed.

  Fact IR_lb : IR inst >= 27.
  Proof.
    rewrite eq_IR_IR1 ; move: inst_set_card ; rewrite (@cardwset1 inst inst_set).
    move<- ; apply: IR_max ; exact: inst_set_is_irr.
  Qed.

End Certificate.
