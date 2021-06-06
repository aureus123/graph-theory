
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import preliminaries digraph sgraph dom.
Require Import check_ir prelim.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


Definition n := 80.

(**********************************************************************************)
Section Instance.
  Let inst_vert := 'I_n.
  Let inst_adj(u v : nat) :=
    match u, v with
    | 0, 13 => true
    | 1, 36 => true
    | 1, 74 => true
    | 1, 13 => true
    | 2, 53 => true
    | 2, 45 => true
    | 2, 36 => true
    | 2, 27 => true
    | 2, 4 => true
    | 2, 59 => true
    | 2, 56 => true
    | 2, 43 => true
    | 2, 62 => true
    | 2, 39 => true
    | 2, 68 => true
    | 2, 24 => true
    | 2, 26 => true
    | 2, 72 => true
    | 2, 32 => true
    | 3, 49 => true
    | 3, 78 => true
    | 3, 6 => true
    | 3, 71 => true
    | 3, 46 => true
    | 3, 18 => true
    | 3, 33 => true
    | 3, 67 => true
    | 3, 8 => true
    | 3, 65 => true
    | 4, 21 => true
    | 4, 9 => true
    | 4, 19 => true
    | 4, 38 => true
    | 4, 16 => true
    | 4, 36 => true
    | 4, 27 => true
    | 5, 56 => true
    | 5, 15 => true
    | 5, 47 => true
    | 5, 71 => true
    | 5, 36 => true
    | 5, 34 => true
    | 5, 54 => true
    | 5, 57 => true
    | 5, 27 => true
    | 6, 14 => true
    | 6, 46 => true
    | 6, 49 => true
    | 6, 78 => true
    | 6, 8 => true
    | 6, 65 => true
    | 6, 37 => true
    | 6, 33 => true
    | 6, 71 => true
    | 6, 67 => true
    | 6, 18 => true
    | 7, 71 => true
    | 7, 55 => true
    | 8, 36 => true
    | 8, 37 => true
    | 8, 34 => true
    | 8, 27 => true
    | 8, 46 => true
    | 8, 49 => true
    | 8, 18 => true
    | 8, 78 => true
    | 8, 65 => true
    | 8, 71 => true
    | 8, 67 => true
    | 8, 14 => true
    | 8, 33 => true
    | 9, 36 => true
    | 9, 21 => true
    | 9, 19 => true
    | 9, 38 => true
    | 9, 16 => true
    | 10, 41 => true
    | 10, 71 => true
    | 11, 13 => true
    | 12, 42 => true
    | 13, 36 => true
    | 13, 79 => true
    | 13, 40 => true
    | 13, 64 => true
    | 13, 31 => true
    | 13, 23 => true
    | 13, 74 => true
    | 14, 78 => true
    | 14, 71 => true
    | 14, 18 => true
    | 14, 47 => true
    | 14, 56 => true
    | 14, 32 => true
    | 14, 36 => true
    | 14, 58 => true
    | 14, 67 => true
    | 14, 33 => true
    | 14, 65 => true
    | 14, 25 => true
    | 14, 37 => true
    | 14, 75 => true
    | 14, 22 => true
    | 14, 76 => true
    | 14, 28 => true
    | 15, 34 => true
    | 15, 47 => true
    | 15, 71 => true
    | 15, 56 => true
    | 15, 54 => true
    | 15, 57 => true
    | 16, 21 => true
    | 16, 19 => true
    | 16, 38 => true
    | 16, 36 => true
    | 17, 43 => true
    | 17, 56 => true
    | 17, 47 => true
    | 18, 37 => true
    | 18, 67 => true
    | 18, 49 => true
    | 18, 78 => true
    | 18, 33 => true
    | 18, 71 => true
    | 18, 46 => true
    | 18, 65 => true
    | 19, 36 => true
    | 19, 21 => true
    | 19, 38 => true
    | 21, 36 => true
    | 21, 38 => true
    | 22, 76 => true
    | 24, 62 => true
    | 24, 39 => true
    | 24, 68 => true
    | 24, 26 => true
    | 24, 72 => true
    | 24, 32 => true
    | 25, 58 => true
    | 25, 76 => true
    | 25, 28 => true
    | 26, 62 => true
    | 26, 39 => true
    | 26, 68 => true
    | 26, 72 => true
    | 26, 32 => true
    | 27, 29 => true
    | 27, 58 => true
    | 27, 71 => true
    | 27, 34 => true
    | 27, 54 => true
    | 27, 43 => true
    | 27, 57 => true
    | 27, 63 => true
    | 27, 56 => true
    | 27, 45 => true
    | 27, 30 => true
    | 27, 36 => true
    | 27, 42 => true
    | 28, 36 => true
    | 28, 58 => true
    | 28, 76 => true
    | 28, 35 => true
    | 28, 44 => true
    | 29, 36 => true
    | 29, 58 => true
    | 30, 36 => true
    | 32, 58 => true
    | 32, 62 => true
    | 32, 39 => true
    | 32, 68 => true
    | 32, 72 => true
    | 33, 46 => true
    | 33, 49 => true
    | 33, 78 => true
    | 33, 47 => true
    | 33, 37 => true
    | 33, 71 => true
    | 33, 67 => true
    | 33, 65 => true
    | 34, 47 => true
    | 34, 43 => true
    | 34, 36 => true
    | 34, 54 => true
    | 34, 57 => true
    | 34, 56 => true
    | 36, 76 => true
    | 36, 65 => true
    | 36, 71 => true
    | 36, 54 => true
    | 36, 57 => true
    | 36, 77 => true
    | 36, 63 => true
    | 36, 56 => true
    | 36, 43 => true
    | 36, 58 => true
    | 36, 38 => true
    | 36, 60 => true
    | 36, 45 => true
    | 36, 42 => true
    | 36, 52 => true
    | 36, 69 => true
    | 36, 74 => true
    | 36, 66 => true
    | 36, 59 => true
    | 36, 61 => true
    | 37, 78 => true
    | 37, 71 => true
    | 37, 65 => true
    | 37, 67 => true
    | 37, 47 => true
    | 37, 51 => true
    | 39, 62 => true
    | 39, 68 => true
    | 39, 72 => true
    | 41, 71 => true
    | 42, 77 => true
    | 43, 73 => true
    | 43, 54 => true
    | 43, 57 => true
    | 43, 47 => true
    | 43, 58 => true
    | 43, 56 => true
    | 44, 75 => true
    | 45, 53 => true
    | 46, 71 => true
    | 46, 65 => true
    | 47, 54 => true
    | 47, 57 => true
    | 47, 56 => true
    | 49, 67 => true
    | 49, 78 => true
    | 49, 65 => true
    | 49, 71 => true
    | 50, 56 => true
    | 54, 71 => true
    | 54, 57 => true
    | 54, 56 => true
    | 56, 71 => true
    | 56, 57 => true
    | 56, 58 => true
    | 56, 75 => true
    | 57, 71 => true
    | 58, 76 => true
    | 58, 63 => true
    | 62, 68 => true
    | 62, 72 => true
    | 65, 67 => true
    | 65, 78 => true
    | 65, 71 => true
    | 67, 78 => true
    | 67, 71 => true
    | 68, 72 => true
    | 71, 78 => true
    | 73, 76 => true
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
  Let inst_set := [set 'v0; 'v1; 'v4; 'v5; 'v11; 'v12; 'v17; 'v20; 'v22; 'v23; 'v25; 'v29; 'v30; 'v31; 'v35; 'v40; 'v41; 'v45; 'v46; 'v48; 'v49; 'v50; 'v51; 'v52; 'v55; 'v59; 'v60; 'v61; 'v62; 'v63; 'v64; 'v66; 'v69; 'v70; 'v73; 'v75; 'v77; 'v79].

  Section List_of_Set.
    Definition inst_list := [:: 'v0; 'v1; 'v4; 'v5; 'v11; 'v12; 'v17; 'v20; 'v22; 'v23; 'v25; 'v29; 'v30; 'v31; 'v35; 'v40; 'v41; 'v45; 'v46; 'v48; 'v49; 'v50; 'v51; 'v52; 'v55; 'v59; 'v60; 'v61; 'v62; 'v63; 'v64; 'v66; 'v69; 'v70; 'v73; 'v75; 'v77; 'v79].

    Fact inst_list_eq_inst_set : inst_list =i inst_set.
    Proof. by move=> v ; rewrite !inE ; try rewrite !orbA. Qed.

    Fact inst_list_uniq : uniq inst_list.
    Proof. done. Qed.
  End List_of_Set.

  Fact inst_set_card : #|inst_set| = 38.
  Proof. by rewrite -(eq_card inst_list_eq_inst_set) (card_uniqP inst_list_uniq). Qed.

  Fact inst_set_is_irr : @irredundant inst inst_set.
  Proof.
    apply (irredundant_checkP inst inst_list (ord_enum_eqT n)).
    - exact: inst_list_uniq.
    - exact: inst_list_eq_inst_set.
    - done.
  Qed.

  Fact IR_lb : IR inst >= 38.
  Proof.
    rewrite eq_IR_IR1 ; move: inst_set_card ; rewrite (@cardwset1 inst inst_set).
    move<- ; apply: IR_max ; exact: inst_set_is_irr.
  Qed.

End Certificate.
