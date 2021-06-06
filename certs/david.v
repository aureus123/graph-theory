
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import preliminaries digraph sgraph dom.
Require Import check_ir prelim.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


Definition n := 87.

(**********************************************************************************)
Section Instance.
  Let inst_vert := 'I_n.
  Let inst_adj(u v : nat) :=
    match u, v with
    | 0, 19 => true
    | 0, 13 => true
    | 0, 3 => true
    | 0, 78 => true
    | 0, 65 => true
    | 0, 82 => true
    | 1, 31 => true
    | 1, 54 => true
    | 1, 73 => true
    | 1, 45 => true
    | 1, 6 => true
    | 1, 3 => true
    | 1, 33 => true
    | 1, 71 => true
    | 1, 28 => true
    | 1, 22 => true
    | 1, 42 => true
    | 1, 41 => true
    | 1, 80 => true
    | 1, 52 => true
    | 1, 18 => true
    | 1, 38 => true
    | 1, 85 => true
    | 1, 15 => true
    | 1, 55 => true
    | 1, 86 => true
    | 1, 32 => true
    | 1, 57 => true
    | 1, 75 => true
    | 1, 66 => true
    | 1, 34 => true
    | 1, 53 => true
    | 1, 82 => true
    | 1, 78 => true
    | 1, 10 => true
    | 1, 65 => true
    | 1, 79 => true
    | 2, 21 => true
    | 2, 22 => true
    | 2, 71 => true
    | 2, 57 => true
    | 2, 86 => true
    | 2, 82 => true
    | 2, 32 => true
    | 3, 11 => true
    | 3, 86 => true
    | 3, 18 => true
    | 3, 73 => true
    | 3, 31 => true
    | 3, 54 => true
    | 3, 45 => true
    | 3, 33 => true
    | 3, 20 => true
    | 3, 17 => true
    | 3, 58 => true
    | 3, 48 => true
    | 3, 13 => true
    | 3, 19 => true
    | 3, 82 => true
    | 3, 78 => true
    | 3, 65 => true
    | 4, 30 => true
    | 4, 33 => true
    | 4, 82 => true
    | 4, 77 => true
    | 5, 46 => true
    | 5, 82 => true
    | 6, 34 => true
    | 6, 18 => true
    | 6, 86 => true
    | 6, 32 => true
    | 6, 33 => true
    | 6, 82 => true
    | 6, 57 => true
    | 7, 70 => true
    | 7, 48 => true
    | 7, 82 => true
    | 8, 10 => true
    | 8, 75 => true
    | 8, 13 => true
    | 8, 39 => true
    | 8, 82 => true
    | 8, 56 => true
    | 9, 41 => true
    | 9, 82 => true
    | 10, 39 => true
    | 10, 13 => true
    | 10, 66 => true
    | 10, 82 => true
    | 10, 75 => true
    | 11, 73 => true
    | 11, 31 => true
    | 11, 45 => true
    | 11, 33 => true
    | 11, 13 => true
    | 11, 20 => true
    | 11, 19 => true
    | 11, 67 => true
    | 11, 35 => true
    | 11, 51 => true
    | 11, 82 => true
    | 12, 42 => true
    | 12, 26 => true
    | 12, 84 => true
    | 12, 59 => true
    | 12, 18 => true
    | 13, 73 => true
    | 13, 31 => true
    | 13, 45 => true
    | 13, 33 => true
    | 13, 20 => true
    | 13, 48 => true
    | 13, 39 => true
    | 13, 75 => true
    | 13, 19 => true
    | 13, 82 => true
    | 13, 78 => true
    | 13, 65 => true
    | 14, 60 => true
    | 14, 48 => true
    | 14, 82 => true
    | 15, 66 => true
    | 15, 76 => true
    | 15, 62 => true
    | 15, 21 => true
    | 15, 41 => true
    | 15, 75 => true
    | 15, 65 => true
    | 15, 82 => true
    | 16, 36 => true
    | 16, 83 => true
    | 16, 18 => true
    | 16, 86 => true
    | 16, 57 => true
    | 16, 44 => true
    | 16, 72 => true
    | 16, 49 => true
    | 16, 82 => true
    | 17, 70 => true
    | 17, 58 => true
    | 17, 82 => true
    | 17, 48 => true
    | 18, 50 => true
    | 18, 22 => true
    | 18, 71 => true
    | 18, 54 => true
    | 18, 41 => true
    | 18, 80 => true
    | 18, 52 => true
    | 18, 42 => true
    | 18, 26 => true
    | 18, 84 => true
    | 18, 59 => true
    | 18, 31 => true
    | 18, 73 => true
    | 18, 34 => true
    | 18, 65 => true
    | 18, 70 => true
    | 18, 45 => true
    | 18, 33 => true
    | 18, 36 => true
    | 18, 83 => true
    | 18, 86 => true
    | 18, 57 => true
    | 18, 44 => true
    | 18, 72 => true
    | 18, 49 => true
    | 18, 67 => true
    | 18, 68 => true
    | 18, 51 => true
    | 18, 48 => true
    | 18, 82 => true
    | 19, 73 => true
    | 19, 31 => true
    | 19, 45 => true
    | 19, 33 => true
    | 19, 86 => true
    | 19, 58 => true
    | 19, 70 => true
    | 19, 20 => true
    | 19, 48 => true
    | 19, 82 => true
    | 19, 78 => true
    | 19, 65 => true
    | 20, 73 => true
    | 20, 31 => true
    | 20, 45 => true
    | 20, 33 => true
    | 20, 65 => true
    | 20, 82 => true
    | 20, 78 => true
    | 21, 76 => true
    | 21, 62 => true
    | 21, 41 => true
    | 21, 82 => true
    | 22, 42 => true
    | 22, 34 => true
    | 22, 86 => true
    | 22, 28 => true
    | 22, 66 => true
    | 22, 71 => true
    | 22, 82 => true
    | 22, 32 => true
    | 23, 66 => true
    | 23, 65 => true
    | 23, 79 => true
    | 23, 82 => true
    | 24, 82 => true
    | 25, 82 => true
    | 26, 42 => true
    | 26, 84 => true
    | 26, 59 => true
    | 27, 50 => true
    | 27, 68 => true
    | 27, 67 => true
    | 27, 82 => true
    | 28, 34 => true
    | 28, 86 => true
    | 28, 32 => true
    | 28, 71 => true
    | 28, 82 => true
    | 28, 66 => true
    | 29, 38 => true
    | 29, 82 => true
    | 30, 33 => true
    | 30, 66 => true
    | 30, 43 => true
    | 30, 75 => true
    | 30, 82 => true
    | 31, 65 => true
    | 31, 86 => true
    | 31, 69 => true
    | 31, 45 => true
    | 31, 73 => true
    | 31, 54 => true
    | 31, 33 => true
    | 31, 82 => true
    | 32, 66 => true
    | 32, 57 => true
    | 32, 71 => true
    | 32, 86 => true
    | 32, 82 => true
    | 33, 86 => true
    | 33, 34 => true
    | 33, 70 => true
    | 33, 57 => true
    | 33, 65 => true
    | 33, 69 => true
    | 33, 45 => true
    | 33, 73 => true
    | 33, 54 => true
    | 33, 82 => true
    | 34, 86 => true
    | 34, 57 => true
    | 34, 85 => true
    | 34, 65 => true
    | 34, 71 => true
    | 34, 55 => true
    | 34, 75 => true
    | 34, 66 => true
    | 34, 53 => true
    | 34, 82 => true
    | 35, 51 => true
    | 35, 82 => true
    | 36, 83 => true
    | 36, 86 => true
    | 36, 57 => true
    | 36, 44 => true
    | 36, 72 => true
    | 36, 49 => true
    | 36, 82 => true
    | 37, 82 => true
    | 38, 65 => true
    | 38, 82 => true
    | 39, 75 => true
    | 39, 82 => true
    | 39, 56 => true
    | 40, 82 => true
    | 41, 42 => true
    | 41, 65 => true
    | 41, 86 => true
    | 41, 80 => true
    | 41, 52 => true
    | 41, 76 => true
    | 41, 62 => true
    | 41, 66 => true
    | 41, 82 => true
    | 42, 71 => true
    | 42, 80 => true
    | 42, 52 => true
    | 42, 65 => true
    | 42, 86 => true
    | 42, 82 => true
    | 42, 84 => true
    | 42, 59 => true
    | 43, 75 => true
    | 43, 82 => true
    | 44, 83 => true
    | 44, 86 => true
    | 44, 57 => true
    | 44, 72 => true
    | 44, 49 => true
    | 44, 82 => true
    | 45, 65 => true
    | 45, 86 => true
    | 45, 70 => true
    | 45, 69 => true
    | 45, 73 => true
    | 45, 54 => true
    | 45, 82 => true
    | 46, 82 => true
    | 47, 82 => true
    | 48, 60 => true
    | 48, 65 => true
    | 48, 70 => true
    | 48, 58 => true
    | 48, 78 => true
    | 48, 67 => true
    | 48, 68 => true
    | 48, 51 => true
    | 48, 82 => true
    | 49, 83 => true
    | 49, 86 => true
    | 49, 57 => true
    | 49, 72 => true
    | 49, 82 => true
    | 50, 84 => true
    | 50, 59 => true
    | 50, 68 => true
    | 50, 67 => true
    | 50, 82 => true
    | 51, 67 => true
    | 51, 68 => true
    | 51, 82 => true
    | 52, 65 => true
    | 52, 86 => true
    | 52, 82 => true
    | 52, 80 => true
    | 53, 75 => true
    | 53, 66 => true
    | 53, 82 => true
    | 54, 65 => true
    | 54, 86 => true
    | 54, 69 => true
    | 54, 73 => true
    | 54, 82 => true
    | 55, 82 => true
    | 56, 82 => true
    | 57, 70 => true
    | 57, 68 => true
    | 57, 71 => true
    | 57, 83 => true
    | 57, 72 => true
    | 57, 86 => true
    | 57, 82 => true
    | 58, 70 => true
    | 58, 82 => true
    | 59, 84 => true
    | 60, 82 => true
    | 61, 82 => true
    | 62, 76 => true
    | 62, 82 => true
    | 63, 82 => true
    | 64, 82 => true
    | 65, 73 => true
    | 65, 80 => true
    | 65, 86 => true
    | 65, 85 => true
    | 65, 66 => true
    | 65, 75 => true
    | 65, 82 => true
    | 65, 79 => true
    | 65, 78 => true
    | 66, 86 => true
    | 66, 71 => true
    | 66, 75 => true
    | 66, 79 => true
    | 66, 82 => true
    | 67, 68 => true
    | 67, 82 => true
    | 68, 70 => true
    | 68, 82 => true
    | 69, 73 => true
    | 69, 82 => true
    | 70, 82 => true
    | 71, 86 => true
    | 71, 82 => true
    | 72, 83 => true
    | 72, 86 => true
    | 72, 82 => true
    | 73, 86 => true
    | 73, 82 => true
    | 74, 82 => true
    | 75, 79 => true
    | 75, 82 => true
    | 76, 82 => true
    | 77, 82 => true
    | 78, 82 => true
    | 79, 82 => true
    | 80, 86 => true
    | 80, 82 => true
    | 81, 82 => true
    | 82, 83 => true
    | 82, 85 => true
    | 82, 86 => true
    | 83, 86 => true
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
  Let inst_set := [set 'v0; 'v2; 'v4; 'v5; 'v6; 'v7; 'v9; 'v10; 'v14; 'v15; 'v20; 'v24; 'v25; 'v27; 'v28; 'v35; 'v36; 'v37; 'v38; 'v40; 'v43; 'v47; 'v52; 'v53; 'v55; 'v56; 'v58; 'v61; 'v63; 'v64; 'v69; 'v74; 'v79; 'v81; 'v84; 'v85].

  Section List_of_Set.
    Definition inst_list := [:: 'v0; 'v2; 'v4; 'v5; 'v6; 'v7; 'v9; 'v10; 'v14; 'v15; 'v20; 'v24; 'v25; 'v27; 'v28; 'v35; 'v36; 'v37; 'v38; 'v40; 'v43; 'v47; 'v52; 'v53; 'v55; 'v56; 'v58; 'v61; 'v63; 'v64; 'v69; 'v74; 'v79; 'v81; 'v84; 'v85].

    Fact inst_list_eq_inst_set : inst_list =i inst_set.
    Proof. by move=> v ; rewrite !inE ; try rewrite !orbA. Qed.

    Fact inst_list_uniq : uniq inst_list.
    Proof. done. Qed.
  End List_of_Set.

  Fact inst_set_card : #|inst_set| = 36.
  Proof. by rewrite -(eq_card inst_list_eq_inst_set) (card_uniqP inst_list_uniq). Qed.

  Fact inst_set_is_irr : @irredundant inst inst_set.
  Proof.
    apply (irredundant_checkP inst inst_list (ord_enum_eqT n)).
    - exact: inst_list_uniq.
    - exact: inst_list_eq_inst_set.
    - done.
  Qed.

  Fact IR_lb : IR inst >= 36.
  Proof.
    rewrite eq_IR_IR1 ; move: inst_set_card ; rewrite (@cardwset1 inst inst_set).
    move<- ; apply: IR_max ; exact: inst_set_is_irr.
  Qed.

End Certificate.
