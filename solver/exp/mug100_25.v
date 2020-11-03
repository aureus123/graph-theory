
From mathcomp Require Import all_ssreflect.
Require Import preliminaries digraph sgraph dom check_ir.

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
    | 0, 1 => true
    | 0, 3 => true
    | 0, 11 => true
    | 0, 12 => true
    | 1, 3 => true
    | 1, 32 => true
    | 1, 33 => true
    | 2, 6 => true
    | 2, 7 => true
    | 2, 10 => true
    | 2, 31 => true
    | 3, 4 => true
    | 4, 5 => true
    | 4, 47 => true
    | 4, 48 => true
    | 5, 6 => true
    | 5, 8 => true
    | 5, 9 => true
    | 6, 91 => true
    | 7, 8 => true
    | 7, 26 => true
    | 7, 61 => true
    | 8, 73 => true
    | 9, 67 => true
    | 9, 74 => true
    | 9, 75 => true
    | 10, 12 => true
    | 10, 17 => true
    | 10, 19 => true
    | 11, 22 => true
    | 11, 58 => true
    | 12, 14 => true
    | 12, 15 => true
    | 13, 14 => true
    | 13, 15 => true
    | 13, 59 => true
    | 13, 60 => true
    | 14, 34 => true
    | 14, 43 => true
    | 15, 28 => true
    | 16, 17 => true
    | 16, 18 => true
    | 16, 23 => true
    | 16, 24 => true
    | 17, 18 => true
    | 18, 20 => true
    | 18, 21 => true
    | 19, 20 => true
    | 19, 21 => true
    | 20, 21 => true
    | 22, 23 => true
    | 22, 24 => true
    | 23, 98 => true
    | 23, 99 => true
    | 24, 50 => true
    | 24, 51 => true
    | 25, 26 => true
    | 25, 27 => true
    | 25, 69 => true
    | 25, 70 => true
    | 26, 27 => true
    | 27, 63 => true
    | 27, 76 => true
    | 28, 29 => true
    | 28, 30 => true
    | 29, 30 => true
    | 29, 35 => true
    | 29, 36 => true
    | 30, 44 => true
    | 30, 45 => true
    | 31, 32 => true
    | 31, 33 => true
    | 32, 33 => true
    | 34, 36 => true
    | 34, 38 => true
    | 34, 39 => true
    | 35, 36 => true
    | 35, 88 => true
    | 37, 38 => true
    | 37, 39 => true
    | 37, 41 => true
    | 37, 42 => true
    | 38, 39 => true
    | 40, 42 => true
    | 40, 53 => true
    | 40, 54 => true
    | 40, 55 => true
    | 41, 42 => true
    | 41, 56 => true
    | 41, 57 => true
    | 43, 44 => true
    | 43, 45 => true
    | 44, 45 => true
    | 46, 47 => true
    | 46, 48 => true
    | 46, 92 => true
    | 46, 93 => true
    | 47, 48 => true
    | 49, 64 => true
    | 49, 80 => true
    | 49, 81 => true
    | 49, 97 => true
    | 50, 51 => true
    | 50, 65 => true
    | 50, 66 => true
    | 51, 79 => true
    | 52, 53 => true
    | 52, 54 => true
    | 52, 89 => true
    | 52, 90 => true
    | 53, 54 => true
    | 55, 57 => true
    | 55, 94 => true
    | 56, 57 => true
    | 56, 95 => true
    | 56, 96 => true
    | 58, 59 => true
    | 58, 60 => true
    | 59, 60 => true
    | 61, 63 => true
    | 61, 83 => true
    | 61, 84 => true
    | 62, 63 => true
    | 62, 77 => true
    | 62, 78 => true
    | 62, 82 => true
    | 64, 65 => true
    | 64, 66 => true
    | 65, 86 => true
    | 65, 87 => true
    | 66, 85 => true
    | 67, 68 => true
    | 67, 69 => true
    | 68, 69 => true
    | 68, 71 => true
    | 68, 72 => true
    | 70, 71 => true
    | 70, 72 => true
    | 71, 72 => true
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
  Let inst_set := [set 'v3; 'v5; 'v6; 'v9; 'v11; 'v12; 'v13; 'v15; 'v18; 'v20; 'v22; 'v23; 'v25; 'v26; 'v27; 'v32; 'v34; 'v35; 'v37; 'v40; 'v44; 'v47; 'v49; 'v53; 'v56; 'v64; 'v66; 'v71; 'v74; 'v76; 'v79; 'v82; 'v83; 'v85; 'v88; 'v92; 'v95].

  Section List_of_Set.
    Definition inst_list := [:: 'v3; 'v5; 'v6; 'v9; 'v11; 'v12; 'v13; 'v15; 'v18; 'v20; 'v22; 'v23; 'v25; 'v26; 'v27; 'v32; 'v34; 'v35; 'v37; 'v40; 'v44; 'v47; 'v49; 'v53; 'v56; 'v64; 'v66; 'v71; 'v74; 'v76; 'v79; 'v82; 'v83; 'v85; 'v88; 'v92; 'v95].

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
