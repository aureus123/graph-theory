
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import preliminaries digraph sgraph dom.
Require Import check_ir prelim.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


Definition n := 100.

(**********************************************************************************)
Section Instance.
  Let inst_vert := 'I_n.
  Let inst_adj(u v : nat) :=
    match u, v with
    | 0, 2 => true
    | 0, 3 => true
    | 0, 8 => true
    | 0, 22 => true
    | 1, 5 => true
    | 1, 7 => true
    | 1, 10 => true
    | 1, 31 => true
    | 2, 3 => true
    | 2, 4 => true
    | 3, 20 => true
    | 3, 21 => true
    | 4, 6 => true
    | 4, 44 => true
    | 4, 45 => true
    | 5, 17 => true
    | 5, 18 => true
    | 5, 43 => true
    | 6, 11 => true
    | 6, 12 => true
    | 6, 16 => true
    | 7, 8 => true
    | 7, 9 => true
    | 8, 9 => true
    | 9, 23 => true
    | 9, 24 => true
    | 10, 14 => true
    | 10, 40 => true
    | 10, 61 => true
    | 11, 12 => true
    | 11, 25 => true
    | 12, 63 => true
    | 12, 64 => true
    | 13, 14 => true
    | 13, 15 => true
    | 13, 52 => true
    | 13, 58 => true
    | 14, 15 => true
    | 15, 42 => true
    | 15, 46 => true
    | 16, 18 => true
    | 16, 29 => true
    | 16, 30 => true
    | 17, 28 => true
    | 17, 49 => true
    | 18, 50 => true
    | 18, 51 => true
    | 19, 20 => true
    | 19, 21 => true
    | 19, 32 => true
    | 19, 33 => true
    | 20, 21 => true
    | 22, 23 => true
    | 22, 24 => true
    | 23, 24 => true
    | 25, 26 => true
    | 25, 27 => true
    | 26, 27 => true
    | 26, 53 => true
    | 26, 54 => true
    | 27, 35 => true
    | 27, 36 => true
    | 28, 29 => true
    | 28, 30 => true
    | 29, 30 => true
    | 31, 32 => true
    | 31, 33 => true
    | 32, 33 => true
    | 34, 35 => true
    | 34, 36 => true
    | 34, 59 => true
    | 34, 60 => true
    | 35, 70 => true
    | 36, 38 => true
    | 36, 39 => true
    | 37, 38 => true
    | 37, 39 => true
    | 37, 72 => true
    | 37, 94 => true
    | 38, 39 => true
    | 40, 41 => true
    | 40, 77 => true
    | 40, 82 => true
    | 41, 42 => true
    | 41, 47 => true
    | 41, 48 => true
    | 42, 76 => true
    | 43, 45 => true
    | 43, 86 => true
    | 43, 87 => true
    | 44, 45 => true
    | 44, 85 => true
    | 46, 47 => true
    | 46, 56 => true
    | 46, 57 => true
    | 47, 48 => true
    | 48, 98 => true
    | 48, 99 => true
    | 49, 51 => true
    | 49, 92 => true
    | 49, 93 => true
    | 50, 51 => true
    | 50, 91 => true
    | 52, 53 => true
    | 52, 54 => true
    | 53, 54 => true
    | 55, 57 => true
    | 55, 68 => true
    | 55, 69 => true
    | 55, 97 => true
    | 56, 57 => true
    | 56, 67 => true
    | 58, 59 => true
    | 58, 60 => true
    | 59, 74 => true
    | 59, 75 => true
    | 60, 73 => true
    | 61, 62 => true
    | 61, 63 => true
    | 62, 63 => true
    | 62, 65 => true
    | 62, 66 => true
    | 64, 65 => true
    | 64, 66 => true
    | 65, 66 => true
    | 67, 68 => true
    | 67, 69 => true
    | 68, 69 => true
    | 70, 71 => true
    | 70, 72 => true
    | 71, 72 => true
    | 71, 95 => true
    | 71, 96 => true
    | 73, 74 => true
    | 73, 75 => true
    | 74, 75 => true
    | 76, 77 => true
    | 76, 78 => true
    | 77, 89 => true
    | 77, 90 => true
    | 78, 80 => true
    | 78, 81 => true
    | 78, 88 => true
    | 79, 80 => true
    | 79, 81 => true
    | 79, 83 => true
    | 79, 84 => true
    | 80, 81 => true
    | 82, 83 => true
    | 82, 84 => true
    | 83, 84 => true
    | 85, 86 => true
    | 85, 87 => true
    | 86, 87 => true
    | 88, 89 => true
    | 88, 90 => true
    | 89, 90 => true
    | 91, 92 => true
    | 91, 93 => true
    | 92, 93 => true
    | 94, 95 => true
    | 94, 96 => true
    | 95, 96 => true
    | 97, 98 => true
    | 97, 99 => true
    | 98, 99 => true
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
  Let inst_set := [set 'v1; 'v2; 'v4; 'v5; 'v6; 'v9; 'v10; 'v11; 'v12; 'v17; 'v19; 'v22; 'v28; 'v34; 'v35; 'v36; 'v40; 'v41; 'v48; 'v50; 'v52; 'v53; 'v55; 'v57; 'v59; 'v63; 'v68; 'v74; 'v77; 'v79; 'v80; 'v85; 'v90; 'v91; 'v94; 'v96].

  Section List_of_Set.
    Definition inst_list := [:: 'v1; 'v2; 'v4; 'v5; 'v6; 'v9; 'v10; 'v11; 'v12; 'v17; 'v19; 'v22; 'v28; 'v34; 'v35; 'v36; 'v40; 'v41; 'v48; 'v50; 'v52; 'v53; 'v55; 'v57; 'v59; 'v63; 'v68; 'v74; 'v77; 'v79; 'v80; 'v85; 'v90; 'v91; 'v94; 'v96].

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
