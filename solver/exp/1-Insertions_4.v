
From mathcomp Require Import all_ssreflect.
Require Import preliminaries digraph sgraph dom check_ir.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


Definition n := 67.

(**********************************************************************************)
Section Instance.
  Let inst_vert := 'I_n.
  Let inst_adj(u v : nat) :=
    match u, v with
    | 0, 1 => true
    | 0, 3 => true
    | 0, 8 => true
    | 0, 10 => true
    | 0, 23 => true
    | 0, 25 => true
    | 0, 30 => true
    | 0, 32 => true
    | 1, 2 => true
    | 1, 7 => true
    | 1, 9 => true
    | 1, 22 => true
    | 1, 24 => true
    | 1, 29 => true
    | 1, 31 => true
    | 2, 5 => true
    | 2, 8 => true
    | 2, 12 => true
    | 2, 23 => true
    | 2, 27 => true
    | 2, 30 => true
    | 2, 34 => true
    | 3, 4 => true
    | 3, 7 => true
    | 3, 11 => true
    | 3, 22 => true
    | 3, 26 => true
    | 3, 29 => true
    | 3, 33 => true
    | 4, 6 => true
    | 4, 10 => true
    | 4, 13 => true
    | 4, 25 => true
    | 4, 28 => true
    | 4, 32 => true
    | 4, 35 => true
    | 5, 6 => true
    | 5, 9 => true
    | 5, 13 => true
    | 5, 24 => true
    | 5, 28 => true
    | 5, 31 => true
    | 5, 35 => true
    | 6, 11 => true
    | 6, 12 => true
    | 6, 26 => true
    | 6, 27 => true
    | 6, 33 => true
    | 6, 34 => true
    | 7, 15 => true
    | 7, 17 => true
    | 7, 23 => true
    | 7, 25 => true
    | 7, 37 => true
    | 7, 39 => true
    | 8, 14 => true
    | 8, 16 => true
    | 8, 22 => true
    | 8, 24 => true
    | 8, 36 => true
    | 8, 38 => true
    | 9, 15 => true
    | 9, 19 => true
    | 9, 23 => true
    | 9, 27 => true
    | 9, 37 => true
    | 9, 41 => true
    | 10, 14 => true
    | 10, 18 => true
    | 10, 22 => true
    | 10, 26 => true
    | 10, 36 => true
    | 10, 40 => true
    | 11, 17 => true
    | 11, 20 => true
    | 11, 25 => true
    | 11, 28 => true
    | 11, 39 => true
    | 11, 42 => true
    | 12, 16 => true
    | 12, 20 => true
    | 12, 24 => true
    | 12, 28 => true
    | 12, 38 => true
    | 12, 42 => true
    | 13, 18 => true
    | 13, 19 => true
    | 13, 26 => true
    | 13, 27 => true
    | 13, 40 => true
    | 13, 41 => true
    | 14, 21 => true
    | 14, 30 => true
    | 14, 32 => true
    | 14, 43 => true
    | 15, 21 => true
    | 15, 29 => true
    | 15, 31 => true
    | 15, 43 => true
    | 16, 21 => true
    | 16, 30 => true
    | 16, 34 => true
    | 16, 43 => true
    | 17, 21 => true
    | 17, 29 => true
    | 17, 33 => true
    | 17, 43 => true
    | 18, 21 => true
    | 18, 32 => true
    | 18, 35 => true
    | 18, 43 => true
    | 19, 21 => true
    | 19, 31 => true
    | 19, 35 => true
    | 19, 43 => true
    | 20, 21 => true
    | 20, 33 => true
    | 20, 34 => true
    | 20, 43 => true
    | 21, 36 => true
    | 21, 37 => true
    | 21, 38 => true
    | 21, 39 => true
    | 21, 40 => true
    | 21, 41 => true
    | 21, 42 => true
    | 22, 45 => true
    | 22, 47 => true
    | 22, 52 => true
    | 22, 54 => true
    | 23, 44 => true
    | 23, 46 => true
    | 23, 51 => true
    | 23, 53 => true
    | 24, 45 => true
    | 24, 49 => true
    | 24, 52 => true
    | 24, 56 => true
    | 25, 44 => true
    | 25, 48 => true
    | 25, 51 => true
    | 25, 55 => true
    | 26, 47 => true
    | 26, 50 => true
    | 26, 54 => true
    | 26, 57 => true
    | 27, 46 => true
    | 27, 50 => true
    | 27, 53 => true
    | 27, 57 => true
    | 28, 48 => true
    | 28, 49 => true
    | 28, 55 => true
    | 28, 56 => true
    | 29, 45 => true
    | 29, 47 => true
    | 29, 59 => true
    | 29, 61 => true
    | 30, 44 => true
    | 30, 46 => true
    | 30, 58 => true
    | 30, 60 => true
    | 31, 45 => true
    | 31, 49 => true
    | 31, 59 => true
    | 31, 63 => true
    | 32, 44 => true
    | 32, 48 => true
    | 32, 58 => true
    | 32, 62 => true
    | 33, 47 => true
    | 33, 50 => true
    | 33, 61 => true
    | 33, 64 => true
    | 34, 46 => true
    | 34, 50 => true
    | 34, 60 => true
    | 34, 64 => true
    | 35, 48 => true
    | 35, 49 => true
    | 35, 62 => true
    | 35, 63 => true
    | 36, 52 => true
    | 36, 54 => true
    | 36, 65 => true
    | 37, 51 => true
    | 37, 53 => true
    | 37, 65 => true
    | 38, 52 => true
    | 38, 56 => true
    | 38, 65 => true
    | 39, 51 => true
    | 39, 55 => true
    | 39, 65 => true
    | 40, 54 => true
    | 40, 57 => true
    | 40, 65 => true
    | 41, 53 => true
    | 41, 57 => true
    | 41, 65 => true
    | 42, 55 => true
    | 42, 56 => true
    | 42, 65 => true
    | 43, 58 => true
    | 43, 59 => true
    | 43, 60 => true
    | 43, 61 => true
    | 43, 62 => true
    | 43, 63 => true
    | 43, 64 => true
    | 44, 66 => true
    | 45, 66 => true
    | 46, 66 => true
    | 47, 66 => true
    | 48, 66 => true
    | 49, 66 => true
    | 50, 66 => true
    | 51, 66 => true
    | 52, 66 => true
    | 53, 66 => true
    | 54, 66 => true
    | 55, 66 => true
    | 56, 66 => true
    | 57, 66 => true
    | 58, 66 => true
    | 59, 66 => true
    | 60, 66 => true
    | 61, 66 => true
    | 62, 66 => true
    | 63, 66 => true
    | 64, 66 => true
    | 65, 66 => true
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
  Let inst_set := [set 'v0; 'v2; 'v6; 'v14; 'v15; 'v16; 'v17; 'v18; 'v19; 'v20; 'v44; 'v45; 'v46; 'v47; 'v48; 'v49; 'v50; 'v51; 'v52; 'v53; 'v54; 'v55; 'v56; 'v57; 'v58; 'v59; 'v60; 'v61; 'v62; 'v63; 'v64; 'v65].

  Section List_of_Set.
    Definition inst_list := [:: 'v0; 'v2; 'v6; 'v14; 'v15; 'v16; 'v17; 'v18; 'v19; 'v20; 'v44; 'v45; 'v46; 'v47; 'v48; 'v49; 'v50; 'v51; 'v52; 'v53; 'v54; 'v55; 'v56; 'v57; 'v58; 'v59; 'v60; 'v61; 'v62; 'v63; 'v64; 'v65].

    Fact inst_list_eq_inst_set : inst_list =i inst_set.
    Proof. by move=> v ; rewrite !inE /= ; try rewrite !orbA. Qed.

    Fact inst_list_uniq : uniq inst_list.
    Proof. done. Qed.
  End List_of_Set.

  Fact inst_set_card : #|inst_set| = 32.
  Proof. by rewrite -(eq_card inst_list_eq_inst_set) (card_uniqP inst_list_uniq). Qed.

  Fact inst_set_is_irr : @irredundant inst inst_set.
  Proof.
    apply (irredundant_checkP inst inst_list (ord_enum_eqT n)).
    - exact: inst_list_uniq.
    - exact: inst_list_eq_inst_set.
    - done.
  Qed.

  Fact IR_lb : IR inst >= 32.
  Proof.
    rewrite eq_IR_IR1 ; move: inst_set_card ; rewrite (@cardwset1 inst inst_set).
    move<- ; apply: IR_max ; exact: inst_set_is_irr.
  Qed.

End Certificate.
