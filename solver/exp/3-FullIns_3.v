
From mathcomp Require Import all_ssreflect.
Require Import preliminaries digraph sgraph dom check_ir.

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
    | 0, 1 => true
    | 0, 3 => true
    | 0, 16 => true
    | 0, 18 => true
    | 1, 2 => true
    | 1, 15 => true
    | 1, 17 => true
    | 2, 5 => true
    | 2, 11 => true
    | 2, 16 => true
    | 2, 20 => true
    | 2, 26 => true
    | 3, 4 => true
    | 3, 11 => true
    | 3, 15 => true
    | 3, 19 => true
    | 3, 26 => true
    | 4, 7 => true
    | 4, 12 => true
    | 4, 18 => true
    | 4, 22 => true
    | 4, 27 => true
    | 5, 6 => true
    | 5, 12 => true
    | 5, 17 => true
    | 5, 21 => true
    | 5, 27 => true
    | 6, 9 => true
    | 6, 13 => true
    | 6, 20 => true
    | 6, 24 => true
    | 6, 28 => true
    | 7, 8 => true
    | 7, 13 => true
    | 7, 19 => true
    | 7, 23 => true
    | 7, 28 => true
    | 8, 10 => true
    | 8, 14 => true
    | 8, 22 => true
    | 8, 25 => true
    | 8, 29 => true
    | 9, 10 => true
    | 9, 14 => true
    | 9, 21 => true
    | 9, 25 => true
    | 9, 29 => true
    | 10, 11 => true
    | 10, 12 => true
    | 10, 13 => true
    | 10, 14 => true
    | 10, 23 => true
    | 10, 24 => true
    | 10, 26 => true
    | 10, 27 => true
    | 10, 28 => true
    | 10, 29 => true
    | 11, 12 => true
    | 11, 13 => true
    | 11, 14 => true
    | 11, 17 => true
    | 11, 18 => true
    | 11, 25 => true
    | 11, 27 => true
    | 11, 28 => true
    | 11, 29 => true
    | 12, 13 => true
    | 12, 14 => true
    | 12, 19 => true
    | 12, 20 => true
    | 12, 25 => true
    | 12, 26 => true
    | 12, 28 => true
    | 12, 29 => true
    | 13, 14 => true
    | 13, 21 => true
    | 13, 22 => true
    | 13, 25 => true
    | 13, 26 => true
    | 13, 27 => true
    | 13, 29 => true
    | 14, 23 => true
    | 14, 24 => true
    | 14, 25 => true
    | 14, 26 => true
    | 14, 27 => true
    | 14, 28 => true
    | 15, 31 => true
    | 15, 33 => true
    | 15, 76 => true
    | 16, 30 => true
    | 16, 32 => true
    | 16, 76 => true
    | 17, 31 => true
    | 17, 35 => true
    | 17, 41 => true
    | 17, 76 => true
    | 18, 30 => true
    | 18, 34 => true
    | 18, 41 => true
    | 18, 76 => true
    | 19, 33 => true
    | 19, 37 => true
    | 19, 42 => true
    | 19, 76 => true
    | 20, 32 => true
    | 20, 36 => true
    | 20, 42 => true
    | 20, 76 => true
    | 21, 35 => true
    | 21, 39 => true
    | 21, 43 => true
    | 21, 76 => true
    | 22, 34 => true
    | 22, 38 => true
    | 22, 43 => true
    | 22, 76 => true
    | 23, 37 => true
    | 23, 40 => true
    | 23, 44 => true
    | 23, 76 => true
    | 24, 36 => true
    | 24, 40 => true
    | 24, 44 => true
    | 24, 76 => true
    | 25, 38 => true
    | 25, 39 => true
    | 25, 41 => true
    | 25, 42 => true
    | 25, 43 => true
    | 25, 44 => true
    | 25, 76 => true
    | 26, 32 => true
    | 26, 33 => true
    | 26, 40 => true
    | 26, 42 => true
    | 26, 43 => true
    | 26, 44 => true
    | 26, 76 => true
    | 27, 34 => true
    | 27, 35 => true
    | 27, 40 => true
    | 27, 41 => true
    | 27, 43 => true
    | 27, 44 => true
    | 27, 76 => true
    | 28, 36 => true
    | 28, 37 => true
    | 28, 40 => true
    | 28, 41 => true
    | 28, 42 => true
    | 28, 44 => true
    | 28, 76 => true
    | 29, 38 => true
    | 29, 39 => true
    | 29, 40 => true
    | 29, 41 => true
    | 29, 42 => true
    | 29, 43 => true
    | 29, 76 => true
    | 30, 46 => true
    | 30, 48 => true
    | 30, 77 => true
    | 31, 45 => true
    | 31, 47 => true
    | 31, 77 => true
    | 32, 46 => true
    | 32, 50 => true
    | 32, 56 => true
    | 32, 77 => true
    | 33, 45 => true
    | 33, 49 => true
    | 33, 56 => true
    | 33, 77 => true
    | 34, 48 => true
    | 34, 52 => true
    | 34, 57 => true
    | 34, 77 => true
    | 35, 47 => true
    | 35, 51 => true
    | 35, 57 => true
    | 35, 77 => true
    | 36, 50 => true
    | 36, 54 => true
    | 36, 58 => true
    | 36, 77 => true
    | 37, 49 => true
    | 37, 53 => true
    | 37, 58 => true
    | 37, 77 => true
    | 38, 52 => true
    | 38, 55 => true
    | 38, 59 => true
    | 38, 77 => true
    | 39, 51 => true
    | 39, 55 => true
    | 39, 59 => true
    | 39, 77 => true
    | 40, 53 => true
    | 40, 54 => true
    | 40, 56 => true
    | 40, 57 => true
    | 40, 58 => true
    | 40, 59 => true
    | 40, 77 => true
    | 41, 47 => true
    | 41, 48 => true
    | 41, 55 => true
    | 41, 57 => true
    | 41, 58 => true
    | 41, 59 => true
    | 41, 77 => true
    | 42, 49 => true
    | 42, 50 => true
    | 42, 55 => true
    | 42, 56 => true
    | 42, 58 => true
    | 42, 59 => true
    | 42, 77 => true
    | 43, 51 => true
    | 43, 52 => true
    | 43, 55 => true
    | 43, 56 => true
    | 43, 57 => true
    | 43, 59 => true
    | 43, 77 => true
    | 44, 53 => true
    | 44, 54 => true
    | 44, 55 => true
    | 44, 56 => true
    | 44, 57 => true
    | 44, 58 => true
    | 44, 77 => true
    | 45, 61 => true
    | 45, 63 => true
    | 45, 78 => true
    | 46, 60 => true
    | 46, 62 => true
    | 46, 78 => true
    | 47, 61 => true
    | 47, 65 => true
    | 47, 71 => true
    | 47, 78 => true
    | 48, 60 => true
    | 48, 64 => true
    | 48, 71 => true
    | 48, 78 => true
    | 49, 63 => true
    | 49, 67 => true
    | 49, 72 => true
    | 49, 78 => true
    | 50, 62 => true
    | 50, 66 => true
    | 50, 72 => true
    | 50, 78 => true
    | 51, 65 => true
    | 51, 69 => true
    | 51, 73 => true
    | 51, 78 => true
    | 52, 64 => true
    | 52, 68 => true
    | 52, 73 => true
    | 52, 78 => true
    | 53, 67 => true
    | 53, 70 => true
    | 53, 74 => true
    | 53, 78 => true
    | 54, 66 => true
    | 54, 70 => true
    | 54, 74 => true
    | 54, 78 => true
    | 55, 68 => true
    | 55, 69 => true
    | 55, 71 => true
    | 55, 72 => true
    | 55, 73 => true
    | 55, 74 => true
    | 55, 78 => true
    | 56, 62 => true
    | 56, 63 => true
    | 56, 70 => true
    | 56, 72 => true
    | 56, 73 => true
    | 56, 74 => true
    | 56, 78 => true
    | 57, 64 => true
    | 57, 65 => true
    | 57, 70 => true
    | 57, 71 => true
    | 57, 73 => true
    | 57, 74 => true
    | 57, 78 => true
    | 58, 66 => true
    | 58, 67 => true
    | 58, 70 => true
    | 58, 71 => true
    | 58, 72 => true
    | 58, 74 => true
    | 58, 78 => true
    | 59, 68 => true
    | 59, 69 => true
    | 59, 70 => true
    | 59, 71 => true
    | 59, 72 => true
    | 59, 73 => true
    | 59, 78 => true
    | 60, 75 => true
    | 60, 79 => true
    | 61, 75 => true
    | 61, 79 => true
    | 62, 75 => true
    | 62, 79 => true
    | 63, 75 => true
    | 63, 79 => true
    | 64, 75 => true
    | 64, 79 => true
    | 65, 75 => true
    | 65, 79 => true
    | 66, 75 => true
    | 66, 79 => true
    | 67, 75 => true
    | 67, 79 => true
    | 68, 75 => true
    | 68, 79 => true
    | 69, 75 => true
    | 69, 79 => true
    | 70, 75 => true
    | 70, 79 => true
    | 71, 75 => true
    | 71, 79 => true
    | 72, 75 => true
    | 72, 79 => true
    | 73, 75 => true
    | 73, 79 => true
    | 74, 75 => true
    | 74, 79 => true
    | 75, 76 => true
    | 75, 77 => true
    | 75, 78 => true
    | 75, 79 => true
    | 76, 77 => true
    | 76, 78 => true
    | 76, 79 => true
    | 77, 78 => true
    | 77, 79 => true
    | 78, 79 => true
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
  Let inst_set := [set 'v1; 'v2; 'v5; 'v6; 'v7; 'v8; 'v30; 'v31; 'v32; 'v33; 'v34; 'v35; 'v36; 'v37; 'v38; 'v39; 'v40; 'v41; 'v42; 'v43; 'v44; 'v60; 'v61; 'v62; 'v63; 'v64; 'v65; 'v66; 'v67; 'v68; 'v69; 'v70; 'v71; 'v72; 'v73; 'v74; 'v78].

  Section List_of_Set.
    Definition inst_list := [:: 'v1; 'v2; 'v5; 'v6; 'v7; 'v8; 'v30; 'v31; 'v32; 'v33; 'v34; 'v35; 'v36; 'v37; 'v38; 'v39; 'v40; 'v41; 'v42; 'v43; 'v44; 'v60; 'v61; 'v62; 'v63; 'v64; 'v65; 'v66; 'v67; 'v68; 'v69; 'v70; 'v71; 'v72; 'v73; 'v74; 'v78].

    Fact inst_list_eq_inst_set : inst_list =i inst_set.
    Proof. by move=> v ; rewrite !inE /= ; try rewrite !orbA. Qed.

    Fact inst_list_uniq : uniq inst_list.
    Proof. done. Qed.
  End List_of_Set.

  Fact inst_set_card : #|inst_set| = 37.
  Proof. by rewrite -(eq_card inst_list_eq_inst_set) (card_uniqP inst_list_uniq). Qed.

  Fact inst_set_is_irr : @irredundant inst inst_set.
  Proof.
    apply (irredundant_checkP inst inst_list (ord_enum_eqT n)).
    - exact: inst_list_uniq.
    - exact: inst_list_eq_inst_set.
    - done.
  Qed.

  Fact IR_lb : IR inst >= 37.
  Proof.
    rewrite eq_IR_IR1 ; move: inst_set_card ; rewrite (@cardwset1 inst inst_set).
    move<- ; apply: IR_max ; exact: inst_set_is_irr.
  Qed.

End Certificate.
