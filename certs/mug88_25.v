
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import preliminaries digraph sgraph dom.
Require Import check_ir prelim.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


Definition n := 88.

(**********************************************************************************)
Section Instance.
  Let inst_vert := 'I_n.
  Let inst_adj(u v : nat) :=
    match u, v with
    | 0, 2 => true
    | 0, 6 => true
    | 0, 10 => true
    | 0, 16 => true
    | 1, 4 => true
    | 1, 23 => true
    | 1, 24 => true
    | 1, 76 => true
    | 2, 3 => true
    | 2, 77 => true
    | 2, 78 => true
    | 3, 13 => true
    | 3, 25 => true
    | 3, 79 => true
    | 4, 6 => true
    | 4, 8 => true
    | 4, 9 => true
    | 5, 6 => true
    | 5, 7 => true
    | 5, 17 => true
    | 5, 18 => true
    | 7, 8 => true
    | 7, 9 => true
    | 8, 9 => true
    | 10, 12 => true
    | 10, 59 => true
    | 10, 60 => true
    | 11, 12 => true
    | 11, 15 => true
    | 11, 55 => true
    | 11, 58 => true
    | 12, 32 => true
    | 12, 33 => true
    | 13, 14 => true
    | 13, 38 => true
    | 13, 39 => true
    | 14, 20 => true
    | 14, 21 => true
    | 14, 49 => true
    | 15, 50 => true
    | 15, 51 => true
    | 15, 61 => true
    | 16, 17 => true
    | 16, 18 => true
    | 17, 18 => true
    | 19, 20 => true
    | 19, 21 => true
    | 19, 56 => true
    | 19, 57 => true
    | 20, 74 => true
    | 20, 75 => true
    | 21, 73 => true
    | 22, 23 => true
    | 22, 26 => true
    | 22, 27 => true
    | 22, 52 => true
    | 23, 29 => true
    | 23, 30 => true
    | 24, 28 => true
    | 24, 41 => true
    | 24, 42 => true
    | 25, 27 => true
    | 25, 34 => true
    | 26, 27 => true
    | 26, 35 => true
    | 26, 36 => true
    | 28, 29 => true
    | 28, 43 => true
    | 29, 30 => true
    | 30, 44 => true
    | 30, 45 => true
    | 31, 32 => true
    | 31, 33 => true
    | 31, 65 => true
    | 31, 66 => true
    | 32, 33 => true
    | 34, 35 => true
    | 34, 36 => true
    | 35, 83 => true
    | 35, 84 => true
    | 36, 82 => true
    | 37, 38 => true
    | 37, 39 => true
    | 37, 62 => true
    | 37, 70 => true
    | 38, 39 => true
    | 40, 41 => true
    | 40, 42 => true
    | 40, 53 => true
    | 40, 54 => true
    | 41, 42 => true
    | 43, 45 => true
    | 43, 46 => true
    | 44, 45 => true
    | 44, 47 => true
    | 44, 48 => true
    | 46, 47 => true
    | 46, 48 => true
    | 47, 48 => true
    | 49, 50 => true
    | 49, 51 => true
    | 50, 67 => true
    | 51, 68 => true
    | 51, 69 => true
    | 52, 53 => true
    | 52, 54 => true
    | 53, 54 => true
    | 55, 56 => true
    | 55, 57 => true
    | 56, 57 => true
    | 58, 59 => true
    | 58, 60 => true
    | 59, 60 => true
    | 61, 62 => true
    | 61, 63 => true
    | 62, 63 => true
    | 63, 71 => true
    | 63, 72 => true
    | 64, 65 => true
    | 64, 66 => true
    | 64, 80 => true
    | 64, 81 => true
    | 65, 66 => true
    | 67, 68 => true
    | 67, 69 => true
    | 68, 69 => true
    | 70, 71 => true
    | 70, 72 => true
    | 71, 72 => true
    | 73, 74 => true
    | 73, 86 => true
    | 73, 87 => true
    | 74, 75 => true
    | 75, 85 => true
    | 76, 77 => true
    | 76, 78 => true
    | 77, 78 => true
    | 79, 80 => true
    | 79, 81 => true
    | 80, 81 => true
    | 82, 83 => true
    | 82, 84 => true
    | 83, 84 => true
    | 85, 86 => true
    | 85, 87 => true
    | 86, 87 => true
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
  Let inst_set := [set 'v1; 'v3; 'v4; 'v9; 'v13; 'v14; 'v16; 'v17; 'v21; 'v23; 'v25; 'v29; 'v31; 'v34; 'v36; 'v40; 'v46; 'v47; 'v54; 'v56; 'v58; 'v60; 'v61; 'v62; 'v63; 'v65; 'v67; 'v69; 'v75; 'v76; 'v79; 'v82; 'v85].

  Section List_of_Set.
    Definition inst_list := [:: 'v1; 'v3; 'v4; 'v9; 'v13; 'v14; 'v16; 'v17; 'v21; 'v23; 'v25; 'v29; 'v31; 'v34; 'v36; 'v40; 'v46; 'v47; 'v54; 'v56; 'v58; 'v60; 'v61; 'v62; 'v63; 'v65; 'v67; 'v69; 'v75; 'v76; 'v79; 'v82; 'v85].

    Fact inst_list_eq_inst_set : inst_list =i inst_set.
    Proof. by move=> v ; rewrite !inE ; try rewrite !orbA. Qed.

    Fact inst_list_uniq : uniq inst_list.
    Proof. done. Qed.
  End List_of_Set.

  Fact inst_set_card : #|inst_set| = 33.
  Proof. by rewrite -(eq_card inst_list_eq_inst_set) (card_uniqP inst_list_uniq). Qed.

  Fact inst_set_is_irr : @irredundant inst inst_set.
  Proof.
    apply (irredundant_checkP inst inst_list (ord_enum_eqT n)).
    - exact: inst_list_uniq.
    - exact: inst_list_eq_inst_set.
    - done.
  Qed.

  Fact IR_lb : IR inst >= 33.
  Proof.
    rewrite eq_IR_IR1 ; move: inst_set_card ; rewrite (@cardwset1 inst inst_set).
    move<- ; apply: IR_max ; exact: inst_set_is_irr.
  Qed.

End Certificate.
