
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
    | 0, 1 => true
    | 0, 5 => true
    | 0, 6 => true
    | 0, 64 => true
    | 1, 3 => true
    | 1, 37 => true
    | 1, 52 => true
    | 2, 4 => true
    | 2, 7 => true
    | 2, 20 => true
    | 2, 21 => true
    | 3, 11 => true
    | 3, 12 => true
    | 3, 19 => true
    | 4, 5 => true
    | 4, 59 => true
    | 4, 60 => true
    | 5, 23 => true
    | 5, 24 => true
    | 6, 58 => true
    | 6, 77 => true
    | 6, 78 => true
    | 7, 8 => true
    | 7, 9 => true
    | 8, 9 => true
    | 8, 53 => true
    | 8, 54 => true
    | 9, 14 => true
    | 9, 16 => true
    | 10, 12 => true
    | 10, 29 => true
    | 10, 31 => true
    | 10, 43 => true
    | 11, 12 => true
    | 11, 44 => true
    | 11, 46 => true
    | 13, 14 => true
    | 13, 15 => true
    | 13, 39 => true
    | 13, 67 => true
    | 14, 15 => true
    | 15, 17 => true
    | 15, 18 => true
    | 16, 17 => true
    | 16, 18 => true
    | 17, 18 => true
    | 19, 20 => true
    | 19, 41 => true
    | 19, 42 => true
    | 20, 25 => true
    | 21, 26 => true
    | 21, 27 => true
    | 21, 40 => true
    | 22, 23 => true
    | 22, 24 => true
    | 22, 76 => true
    | 23, 24 => true
    | 25, 26 => true
    | 25, 27 => true
    | 26, 27 => true
    | 28, 29 => true
    | 28, 30 => true
    | 28, 65 => true
    | 28, 66 => true
    | 29, 30 => true
    | 30, 32 => true
    | 30, 55 => true
    | 31, 32 => true
    | 31, 33 => true
    | 32, 36 => true
    | 32, 61 => true
    | 33, 34 => true
    | 33, 56 => true
    | 33, 57 => true
    | 34, 35 => true
    | 34, 86 => true
    | 34, 87 => true
    | 35, 36 => true
    | 35, 62 => true
    | 35, 63 => true
    | 36, 85 => true
    | 37, 38 => true
    | 37, 39 => true
    | 38, 39 => true
    | 38, 68 => true
    | 38, 69 => true
    | 40, 41 => true
    | 40, 50 => true
    | 40, 51 => true
    | 41, 42 => true
    | 42, 49 => true
    | 43, 44 => true
    | 43, 45 => true
    | 44, 45 => true
    | 45, 48 => true
    | 45, 73 => true
    | 46, 47 => true
    | 46, 48 => true
    | 47, 48 => true
    | 47, 74 => true
    | 47, 75 => true
    | 49, 50 => true
    | 49, 51 => true
    | 50, 80 => true
    | 50, 81 => true
    | 51, 79 => true
    | 52, 53 => true
    | 52, 54 => true
    | 53, 70 => true
    | 54, 72 => true
    | 54, 82 => true
    | 55, 56 => true
    | 55, 57 => true
    | 56, 57 => true
    | 58, 59 => true
    | 58, 60 => true
    | 59, 60 => true
    | 61, 62 => true
    | 61, 63 => true
    | 62, 63 => true
    | 64, 65 => true
    | 64, 66 => true
    | 65, 66 => true
    | 67, 68 => true
    | 67, 69 => true
    | 68, 69 => true
    | 70, 71 => true
    | 70, 72 => true
    | 71, 72 => true
    | 71, 83 => true
    | 71, 84 => true
    | 73, 74 => true
    | 73, 75 => true
    | 74, 75 => true
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
  Let inst_set := [set 'v7; 'v8; 'v9; 'v10; 'v12; 'v16; 'v22; 'v24; 'v25; 'v27; 'v37; 'v39; 'v41; 'v42; 'v43; 'v46; 'v53; 'v55; 'v57; 'v58; 'v59; 'v61; 'v62; 'v64; 'v65; 'v68; 'v70; 'v75; 'v79; 'v81; 'v83; 'v85; 'v87].

  Section List_of_Set.
    Definition inst_list := [:: 'v7; 'v8; 'v9; 'v10; 'v12; 'v16; 'v22; 'v24; 'v25; 'v27; 'v37; 'v39; 'v41; 'v42; 'v43; 'v46; 'v53; 'v55; 'v57; 'v58; 'v59; 'v61; 'v62; 'v64; 'v65; 'v68; 'v70; 'v75; 'v79; 'v81; 'v83; 'v85; 'v87].

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
