
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import preliminaries digraph sgraph dom.
Require Import check_ir prelim.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


Definition n := 49.

(**********************************************************************************)
Section Instance.
  Let inst_vert := 'I_n.
  Let inst_adj(u v : nat) :=
    match u, v with
    | 0, 8 => true
    | 0, 16 => true
    | 0, 24 => true
    | 0, 32 => true
    | 0, 40 => true
    | 0, 48 => true
    | 0, 1 => true
    | 0, 2 => true
    | 0, 3 => true
    | 0, 4 => true
    | 0, 5 => true
    | 0, 6 => true
    | 0, 7 => true
    | 0, 14 => true
    | 0, 21 => true
    | 0, 28 => true
    | 0, 35 => true
    | 0, 42 => true
    | 1, 9 => true
    | 1, 17 => true
    | 1, 25 => true
    | 1, 33 => true
    | 1, 41 => true
    | 1, 7 => true
    | 1, 2 => true
    | 1, 3 => true
    | 1, 4 => true
    | 1, 5 => true
    | 1, 6 => true
    | 1, 8 => true
    | 1, 15 => true
    | 1, 22 => true
    | 1, 29 => true
    | 1, 36 => true
    | 1, 43 => true
    | 2, 10 => true
    | 2, 18 => true
    | 2, 26 => true
    | 2, 34 => true
    | 2, 8 => true
    | 2, 14 => true
    | 2, 3 => true
    | 2, 4 => true
    | 2, 5 => true
    | 2, 6 => true
    | 2, 9 => true
    | 2, 16 => true
    | 2, 23 => true
    | 2, 30 => true
    | 2, 37 => true
    | 2, 44 => true
    | 3, 11 => true
    | 3, 19 => true
    | 3, 27 => true
    | 3, 9 => true
    | 3, 15 => true
    | 3, 21 => true
    | 3, 4 => true
    | 3, 5 => true
    | 3, 6 => true
    | 3, 10 => true
    | 3, 17 => true
    | 3, 24 => true
    | 3, 31 => true
    | 3, 38 => true
    | 3, 45 => true
    | 4, 12 => true
    | 4, 20 => true
    | 4, 10 => true
    | 4, 16 => true
    | 4, 22 => true
    | 4, 28 => true
    | 4, 5 => true
    | 4, 6 => true
    | 4, 11 => true
    | 4, 18 => true
    | 4, 25 => true
    | 4, 32 => true
    | 4, 39 => true
    | 4, 46 => true
    | 5, 13 => true
    | 5, 11 => true
    | 5, 17 => true
    | 5, 23 => true
    | 5, 29 => true
    | 5, 35 => true
    | 5, 6 => true
    | 5, 12 => true
    | 5, 19 => true
    | 5, 26 => true
    | 5, 33 => true
    | 5, 40 => true
    | 5, 47 => true
    | 6, 12 => true
    | 6, 18 => true
    | 6, 24 => true
    | 6, 30 => true
    | 6, 36 => true
    | 6, 42 => true
    | 6, 13 => true
    | 6, 20 => true
    | 6, 27 => true
    | 6, 34 => true
    | 6, 41 => true
    | 6, 48 => true
    | 7, 15 => true
    | 7, 23 => true
    | 7, 31 => true
    | 7, 39 => true
    | 7, 47 => true
    | 7, 8 => true
    | 7, 9 => true
    | 7, 10 => true
    | 7, 11 => true
    | 7, 12 => true
    | 7, 13 => true
    | 7, 14 => true
    | 7, 21 => true
    | 7, 28 => true
    | 7, 35 => true
    | 7, 42 => true
    | 8, 16 => true
    | 8, 24 => true
    | 8, 32 => true
    | 8, 40 => true
    | 8, 48 => true
    | 8, 14 => true
    | 8, 9 => true
    | 8, 10 => true
    | 8, 11 => true
    | 8, 12 => true
    | 8, 13 => true
    | 8, 15 => true
    | 8, 22 => true
    | 8, 29 => true
    | 8, 36 => true
    | 8, 43 => true
    | 9, 17 => true
    | 9, 25 => true
    | 9, 33 => true
    | 9, 41 => true
    | 9, 15 => true
    | 9, 21 => true
    | 9, 10 => true
    | 9, 11 => true
    | 9, 12 => true
    | 9, 13 => true
    | 9, 16 => true
    | 9, 23 => true
    | 9, 30 => true
    | 9, 37 => true
    | 9, 44 => true
    | 10, 18 => true
    | 10, 26 => true
    | 10, 34 => true
    | 10, 16 => true
    | 10, 22 => true
    | 10, 28 => true
    | 10, 11 => true
    | 10, 12 => true
    | 10, 13 => true
    | 10, 17 => true
    | 10, 24 => true
    | 10, 31 => true
    | 10, 38 => true
    | 10, 45 => true
    | 11, 19 => true
    | 11, 27 => true
    | 11, 17 => true
    | 11, 23 => true
    | 11, 29 => true
    | 11, 35 => true
    | 11, 12 => true
    | 11, 13 => true
    | 11, 18 => true
    | 11, 25 => true
    | 11, 32 => true
    | 11, 39 => true
    | 11, 46 => true
    | 12, 20 => true
    | 12, 18 => true
    | 12, 24 => true
    | 12, 30 => true
    | 12, 36 => true
    | 12, 42 => true
    | 12, 13 => true
    | 12, 19 => true
    | 12, 26 => true
    | 12, 33 => true
    | 12, 40 => true
    | 12, 47 => true
    | 13, 19 => true
    | 13, 25 => true
    | 13, 31 => true
    | 13, 37 => true
    | 13, 43 => true
    | 13, 20 => true
    | 13, 27 => true
    | 13, 34 => true
    | 13, 41 => true
    | 13, 48 => true
    | 14, 22 => true
    | 14, 30 => true
    | 14, 38 => true
    | 14, 46 => true
    | 14, 15 => true
    | 14, 16 => true
    | 14, 17 => true
    | 14, 18 => true
    | 14, 19 => true
    | 14, 20 => true
    | 14, 21 => true
    | 14, 28 => true
    | 14, 35 => true
    | 14, 42 => true
    | 15, 23 => true
    | 15, 31 => true
    | 15, 39 => true
    | 15, 47 => true
    | 15, 21 => true
    | 15, 16 => true
    | 15, 17 => true
    | 15, 18 => true
    | 15, 19 => true
    | 15, 20 => true
    | 15, 22 => true
    | 15, 29 => true
    | 15, 36 => true
    | 15, 43 => true
    | 16, 24 => true
    | 16, 32 => true
    | 16, 40 => true
    | 16, 48 => true
    | 16, 22 => true
    | 16, 28 => true
    | 16, 17 => true
    | 16, 18 => true
    | 16, 19 => true
    | 16, 20 => true
    | 16, 23 => true
    | 16, 30 => true
    | 16, 37 => true
    | 16, 44 => true
    | 17, 25 => true
    | 17, 33 => true
    | 17, 41 => true
    | 17, 23 => true
    | 17, 29 => true
    | 17, 35 => true
    | 17, 18 => true
    | 17, 19 => true
    | 17, 20 => true
    | 17, 24 => true
    | 17, 31 => true
    | 17, 38 => true
    | 17, 45 => true
    | 18, 26 => true
    | 18, 34 => true
    | 18, 24 => true
    | 18, 30 => true
    | 18, 36 => true
    | 18, 42 => true
    | 18, 19 => true
    | 18, 20 => true
    | 18, 25 => true
    | 18, 32 => true
    | 18, 39 => true
    | 18, 46 => true
    | 19, 27 => true
    | 19, 25 => true
    | 19, 31 => true
    | 19, 37 => true
    | 19, 43 => true
    | 19, 20 => true
    | 19, 26 => true
    | 19, 33 => true
    | 19, 40 => true
    | 19, 47 => true
    | 20, 26 => true
    | 20, 32 => true
    | 20, 38 => true
    | 20, 44 => true
    | 20, 27 => true
    | 20, 34 => true
    | 20, 41 => true
    | 20, 48 => true
    | 21, 29 => true
    | 21, 37 => true
    | 21, 45 => true
    | 21, 22 => true
    | 21, 23 => true
    | 21, 24 => true
    | 21, 25 => true
    | 21, 26 => true
    | 21, 27 => true
    | 21, 28 => true
    | 21, 35 => true
    | 21, 42 => true
    | 22, 30 => true
    | 22, 38 => true
    | 22, 46 => true
    | 22, 28 => true
    | 22, 23 => true
    | 22, 24 => true
    | 22, 25 => true
    | 22, 26 => true
    | 22, 27 => true
    | 22, 29 => true
    | 22, 36 => true
    | 22, 43 => true
    | 23, 31 => true
    | 23, 39 => true
    | 23, 47 => true
    | 23, 29 => true
    | 23, 35 => true
    | 23, 24 => true
    | 23, 25 => true
    | 23, 26 => true
    | 23, 27 => true
    | 23, 30 => true
    | 23, 37 => true
    | 23, 44 => true
    | 24, 32 => true
    | 24, 40 => true
    | 24, 48 => true
    | 24, 30 => true
    | 24, 36 => true
    | 24, 42 => true
    | 24, 25 => true
    | 24, 26 => true
    | 24, 27 => true
    | 24, 31 => true
    | 24, 38 => true
    | 24, 45 => true
    | 25, 33 => true
    | 25, 41 => true
    | 25, 31 => true
    | 25, 37 => true
    | 25, 43 => true
    | 25, 26 => true
    | 25, 27 => true
    | 25, 32 => true
    | 25, 39 => true
    | 25, 46 => true
    | 26, 34 => true
    | 26, 32 => true
    | 26, 38 => true
    | 26, 44 => true
    | 26, 27 => true
    | 26, 33 => true
    | 26, 40 => true
    | 26, 47 => true
    | 27, 33 => true
    | 27, 39 => true
    | 27, 45 => true
    | 27, 34 => true
    | 27, 41 => true
    | 27, 48 => true
    | 28, 36 => true
    | 28, 44 => true
    | 28, 29 => true
    | 28, 30 => true
    | 28, 31 => true
    | 28, 32 => true
    | 28, 33 => true
    | 28, 34 => true
    | 28, 35 => true
    | 28, 42 => true
    | 29, 37 => true
    | 29, 45 => true
    | 29, 35 => true
    | 29, 30 => true
    | 29, 31 => true
    | 29, 32 => true
    | 29, 33 => true
    | 29, 34 => true
    | 29, 36 => true
    | 29, 43 => true
    | 30, 38 => true
    | 30, 46 => true
    | 30, 36 => true
    | 30, 42 => true
    | 30, 31 => true
    | 30, 32 => true
    | 30, 33 => true
    | 30, 34 => true
    | 30, 37 => true
    | 30, 44 => true
    | 31, 39 => true
    | 31, 47 => true
    | 31, 37 => true
    | 31, 43 => true
    | 31, 32 => true
    | 31, 33 => true
    | 31, 34 => true
    | 31, 38 => true
    | 31, 45 => true
    | 32, 40 => true
    | 32, 48 => true
    | 32, 38 => true
    | 32, 44 => true
    | 32, 33 => true
    | 32, 34 => true
    | 32, 39 => true
    | 32, 46 => true
    | 33, 41 => true
    | 33, 39 => true
    | 33, 45 => true
    | 33, 34 => true
    | 33, 40 => true
    | 33, 47 => true
    | 34, 40 => true
    | 34, 46 => true
    | 34, 41 => true
    | 34, 48 => true
    | 35, 43 => true
    | 35, 36 => true
    | 35, 37 => true
    | 35, 38 => true
    | 35, 39 => true
    | 35, 40 => true
    | 35, 41 => true
    | 35, 42 => true
    | 36, 44 => true
    | 36, 42 => true
    | 36, 37 => true
    | 36, 38 => true
    | 36, 39 => true
    | 36, 40 => true
    | 36, 41 => true
    | 36, 43 => true
    | 37, 45 => true
    | 37, 43 => true
    | 37, 38 => true
    | 37, 39 => true
    | 37, 40 => true
    | 37, 41 => true
    | 37, 44 => true
    | 38, 46 => true
    | 38, 44 => true
    | 38, 39 => true
    | 38, 40 => true
    | 38, 41 => true
    | 38, 45 => true
    | 39, 47 => true
    | 39, 45 => true
    | 39, 40 => true
    | 39, 41 => true
    | 39, 46 => true
    | 40, 48 => true
    | 40, 46 => true
    | 40, 41 => true
    | 40, 47 => true
    | 41, 47 => true
    | 41, 48 => true
    | 42, 43 => true
    | 42, 44 => true
    | 42, 45 => true
    | 42, 46 => true
    | 42, 47 => true
    | 42, 48 => true
    | 43, 44 => true
    | 43, 45 => true
    | 43, 46 => true
    | 43, 47 => true
    | 43, 48 => true
    | 44, 45 => true
    | 44, 46 => true
    | 44, 47 => true
    | 44, 48 => true
    | 45, 46 => true
    | 45, 47 => true
    | 45, 48 => true
    | 46, 47 => true
    | 46, 48 => true
    | 47, 48 => true
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
  Let inst_set := [set 'v0; 'v1; 'v2; 'v14; 'v15; 'v21; 'v35; 'v36; 'v37].

  Section List_of_Set.
    Definition inst_list := [:: 'v0; 'v1; 'v2; 'v14; 'v15; 'v21; 'v35; 'v36; 'v37].

    Fact inst_list_eq_inst_set : inst_list =i inst_set.
    Proof. by move=> v ; rewrite !inE /= ; try rewrite !orbA. Qed.

    Fact inst_list_uniq : uniq inst_list.
    Proof. done. Qed.
  End List_of_Set.

  Fact inst_set_card : #|inst_set| = 9.
  Proof. by rewrite -(eq_card inst_list_eq_inst_set) (card_uniqP inst_list_uniq). Qed.

  Fact inst_set_is_irr : @irredundant inst inst_set.
  Proof.
    apply (irredundant_checkP inst inst_list (ord_enum_eqT n)).
    - exact: inst_list_uniq.
    - exact: inst_list_eq_inst_set.
    - done.
  Qed.

  Fact IR_lb : IR inst >= 9.
  Proof.
    rewrite eq_IR_IR1 ; move: inst_set_card ; rewrite (@cardwset1 inst inst_set).
    move<- ; apply: IR_max ; exact: inst_set_is_irr.
  Qed.

End Certificate.
