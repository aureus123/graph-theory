
From mathcomp Require Import all_ssreflect.
Require Import preliminaries digraph sgraph dom check_ir.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


Definition n := 47.

(**********************************************************************************)
Section Instance.
  Let inst_vert := 'I_n.
  Let inst_adj(u v : nat) :=
    match u, v with
    | 0, 1 => true
    | 0, 3 => true
    | 0, 6 => true
    | 0, 8 => true
    | 0, 12 => true
    | 0, 14 => true
    | 0, 17 => true
    | 0, 19 => true
    | 0, 24 => true
    | 0, 26 => true
    | 0, 29 => true
    | 0, 31 => true
    | 0, 35 => true
    | 0, 37 => true
    | 0, 40 => true
    | 0, 42 => true
    | 1, 2 => true
    | 1, 5 => true
    | 1, 7 => true
    | 1, 11 => true
    | 1, 13 => true
    | 1, 16 => true
    | 1, 18 => true
    | 1, 23 => true
    | 1, 25 => true
    | 1, 28 => true
    | 1, 30 => true
    | 1, 34 => true
    | 1, 36 => true
    | 1, 39 => true
    | 1, 41 => true
    | 2, 4 => true
    | 2, 6 => true
    | 2, 9 => true
    | 2, 12 => true
    | 2, 15 => true
    | 2, 17 => true
    | 2, 20 => true
    | 2, 24 => true
    | 2, 27 => true
    | 2, 29 => true
    | 2, 32 => true
    | 2, 35 => true
    | 2, 38 => true
    | 2, 40 => true
    | 2, 43 => true
    | 3, 4 => true
    | 3, 5 => true
    | 3, 9 => true
    | 3, 11 => true
    | 3, 15 => true
    | 3, 16 => true
    | 3, 20 => true
    | 3, 23 => true
    | 3, 27 => true
    | 3, 28 => true
    | 3, 32 => true
    | 3, 34 => true
    | 3, 38 => true
    | 3, 39 => true
    | 3, 43 => true
    | 4, 7 => true
    | 4, 8 => true
    | 4, 13 => true
    | 4, 14 => true
    | 4, 18 => true
    | 4, 19 => true
    | 4, 25 => true
    | 4, 26 => true
    | 4, 30 => true
    | 4, 31 => true
    | 4, 36 => true
    | 4, 37 => true
    | 4, 41 => true
    | 4, 42 => true
    | 5, 10 => true
    | 5, 12 => true
    | 5, 14 => true
    | 5, 21 => true
    | 5, 24 => true
    | 5, 26 => true
    | 5, 33 => true
    | 5, 35 => true
    | 5, 37 => true
    | 5, 44 => true
    | 6, 10 => true
    | 6, 11 => true
    | 6, 13 => true
    | 6, 21 => true
    | 6, 23 => true
    | 6, 25 => true
    | 6, 33 => true
    | 6, 34 => true
    | 6, 36 => true
    | 6, 44 => true
    | 7, 10 => true
    | 7, 12 => true
    | 7, 15 => true
    | 7, 21 => true
    | 7, 24 => true
    | 7, 27 => true
    | 7, 33 => true
    | 7, 35 => true
    | 7, 38 => true
    | 7, 44 => true
    | 8, 10 => true
    | 8, 11 => true
    | 8, 15 => true
    | 8, 21 => true
    | 8, 23 => true
    | 8, 27 => true
    | 8, 33 => true
    | 8, 34 => true
    | 8, 38 => true
    | 8, 44 => true
    | 9, 10 => true
    | 9, 13 => true
    | 9, 14 => true
    | 9, 21 => true
    | 9, 25 => true
    | 9, 26 => true
    | 9, 33 => true
    | 9, 36 => true
    | 9, 37 => true
    | 9, 44 => true
    | 10, 16 => true
    | 10, 17 => true
    | 10, 18 => true
    | 10, 19 => true
    | 10, 20 => true
    | 10, 28 => true
    | 10, 29 => true
    | 10, 30 => true
    | 10, 31 => true
    | 10, 32 => true
    | 10, 39 => true
    | 10, 40 => true
    | 10, 41 => true
    | 10, 42 => true
    | 10, 43 => true
    | 11, 22 => true
    | 11, 24 => true
    | 11, 26 => true
    | 11, 29 => true
    | 11, 31 => true
    | 11, 45 => true
    | 12, 22 => true
    | 12, 23 => true
    | 12, 25 => true
    | 12, 28 => true
    | 12, 30 => true
    | 12, 45 => true
    | 13, 22 => true
    | 13, 24 => true
    | 13, 27 => true
    | 13, 29 => true
    | 13, 32 => true
    | 13, 45 => true
    | 14, 22 => true
    | 14, 23 => true
    | 14, 27 => true
    | 14, 28 => true
    | 14, 32 => true
    | 14, 45 => true
    | 15, 22 => true
    | 15, 25 => true
    | 15, 26 => true
    | 15, 30 => true
    | 15, 31 => true
    | 15, 45 => true
    | 16, 22 => true
    | 16, 24 => true
    | 16, 26 => true
    | 16, 33 => true
    | 16, 45 => true
    | 17, 22 => true
    | 17, 23 => true
    | 17, 25 => true
    | 17, 33 => true
    | 17, 45 => true
    | 18, 22 => true
    | 18, 24 => true
    | 18, 27 => true
    | 18, 33 => true
    | 18, 45 => true
    | 19, 22 => true
    | 19, 23 => true
    | 19, 27 => true
    | 19, 33 => true
    | 19, 45 => true
    | 20, 22 => true
    | 20, 25 => true
    | 20, 26 => true
    | 20, 33 => true
    | 20, 45 => true
    | 21, 22 => true
    | 21, 28 => true
    | 21, 29 => true
    | 21, 30 => true
    | 21, 31 => true
    | 21, 32 => true
    | 21, 45 => true
    | 22, 34 => true
    | 22, 35 => true
    | 22, 36 => true
    | 22, 37 => true
    | 22, 38 => true
    | 22, 39 => true
    | 22, 40 => true
    | 22, 41 => true
    | 22, 42 => true
    | 22, 43 => true
    | 22, 44 => true
    | 23, 46 => true
    | 24, 46 => true
    | 25, 46 => true
    | 26, 46 => true
    | 27, 46 => true
    | 28, 46 => true
    | 29, 46 => true
    | 30, 46 => true
    | 31, 46 => true
    | 32, 46 => true
    | 33, 46 => true
    | 34, 46 => true
    | 35, 46 => true
    | 36, 46 => true
    | 37, 46 => true
    | 38, 46 => true
    | 39, 46 => true
    | 40, 46 => true
    | 41, 46 => true
    | 42, 46 => true
    | 43, 46 => true
    | 44, 46 => true
    | 45, 46 => true
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
  Let inst_set := [set 'v23; 'v24; 'v25; 'v26; 'v27; 'v28; 'v29; 'v30; 'v31; 'v32; 'v33; 'v34; 'v35; 'v36; 'v37; 'v38; 'v39; 'v40; 'v41; 'v42; 'v43; 'v44; 'v45].

  Section List_of_Set.
    Definition inst_list := [:: 'v23; 'v24; 'v25; 'v26; 'v27; 'v28; 'v29; 'v30; 'v31; 'v32; 'v33; 'v34; 'v35; 'v36; 'v37; 'v38; 'v39; 'v40; 'v41; 'v42; 'v43; 'v44; 'v45].

    Fact inst_list_eq_inst_set : inst_list =i inst_set.
    Proof. by move=> v ; rewrite !inE /= ; try rewrite !orbA. Qed.

    Fact inst_list_uniq : uniq inst_list.
    Proof. done. Qed.
  End List_of_Set.

  Fact inst_set_card : #|inst_set| = 23.
  Proof. by rewrite -(eq_card inst_list_eq_inst_set) (card_uniqP inst_list_uniq). Qed.

  Fact inst_set_is_irr : @irredundant inst inst_set.
  Proof.
    apply (irredundant_checkP inst inst_list (ord_enum_eqT n)).
    - exact: inst_list_uniq.
    - exact: inst_list_eq_inst_set.
    - done.
  Qed.

  Fact IR_lb : IR inst >= 23.
  Proof.
    rewrite eq_IR_IR1 ; move: inst_set_card ; rewrite (@cardwset1 inst inst_set).
    move<- ; apply: IR_max ; exact: inst_set_is_irr.
  Qed.

End Certificate.
