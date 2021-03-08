
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import preliminaries digraph sgraph dom.
Require Import check_ir prelim.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


Definition n := 52.

(**********************************************************************************)
Section Instance.
  Let inst_vert := 'I_n.
  Let inst_adj(u v : nat) :=
    match u, v with
    | 0, 1 => true
    | 0, 3 => true
    | 0, 13 => true
    | 0, 15 => true
    | 1, 2 => true
    | 1, 12 => true
    | 1, 14 => true
    | 2, 5 => true
    | 2, 9 => true
    | 2, 13 => true
    | 2, 17 => true
    | 2, 21 => true
    | 3, 4 => true
    | 3, 9 => true
    | 3, 12 => true
    | 3, 16 => true
    | 3, 21 => true
    | 4, 7 => true
    | 4, 10 => true
    | 4, 15 => true
    | 4, 19 => true
    | 4, 22 => true
    | 5, 6 => true
    | 5, 10 => true
    | 5, 14 => true
    | 5, 18 => true
    | 5, 22 => true
    | 6, 8 => true
    | 6, 11 => true
    | 6, 17 => true
    | 6, 20 => true
    | 6, 23 => true
    | 7, 8 => true
    | 7, 11 => true
    | 7, 16 => true
    | 7, 20 => true
    | 7, 23 => true
    | 8, 9 => true
    | 8, 10 => true
    | 8, 11 => true
    | 8, 18 => true
    | 8, 19 => true
    | 8, 21 => true
    | 8, 22 => true
    | 8, 23 => true
    | 9, 10 => true
    | 9, 11 => true
    | 9, 14 => true
    | 9, 15 => true
    | 9, 20 => true
    | 9, 22 => true
    | 9, 23 => true
    | 10, 11 => true
    | 10, 16 => true
    | 10, 17 => true
    | 10, 20 => true
    | 10, 21 => true
    | 10, 23 => true
    | 11, 18 => true
    | 11, 19 => true
    | 11, 20 => true
    | 11, 21 => true
    | 11, 22 => true
    | 12, 25 => true
    | 12, 27 => true
    | 12, 49 => true
    | 13, 24 => true
    | 13, 26 => true
    | 13, 49 => true
    | 14, 25 => true
    | 14, 29 => true
    | 14, 33 => true
    | 14, 49 => true
    | 15, 24 => true
    | 15, 28 => true
    | 15, 33 => true
    | 15, 49 => true
    | 16, 27 => true
    | 16, 31 => true
    | 16, 34 => true
    | 16, 49 => true
    | 17, 26 => true
    | 17, 30 => true
    | 17, 34 => true
    | 17, 49 => true
    | 18, 29 => true
    | 18, 32 => true
    | 18, 35 => true
    | 18, 49 => true
    | 19, 28 => true
    | 19, 32 => true
    | 19, 35 => true
    | 19, 49 => true
    | 20, 30 => true
    | 20, 31 => true
    | 20, 33 => true
    | 20, 34 => true
    | 20, 35 => true
    | 20, 49 => true
    | 21, 26 => true
    | 21, 27 => true
    | 21, 32 => true
    | 21, 34 => true
    | 21, 35 => true
    | 21, 49 => true
    | 22, 28 => true
    | 22, 29 => true
    | 22, 32 => true
    | 22, 33 => true
    | 22, 35 => true
    | 22, 49 => true
    | 23, 30 => true
    | 23, 31 => true
    | 23, 32 => true
    | 23, 33 => true
    | 23, 34 => true
    | 23, 49 => true
    | 24, 37 => true
    | 24, 39 => true
    | 24, 50 => true
    | 25, 36 => true
    | 25, 38 => true
    | 25, 50 => true
    | 26, 37 => true
    | 26, 41 => true
    | 26, 45 => true
    | 26, 50 => true
    | 27, 36 => true
    | 27, 40 => true
    | 27, 45 => true
    | 27, 50 => true
    | 28, 39 => true
    | 28, 43 => true
    | 28, 46 => true
    | 28, 50 => true
    | 29, 38 => true
    | 29, 42 => true
    | 29, 46 => true
    | 29, 50 => true
    | 30, 41 => true
    | 30, 44 => true
    | 30, 47 => true
    | 30, 50 => true
    | 31, 40 => true
    | 31, 44 => true
    | 31, 47 => true
    | 31, 50 => true
    | 32, 42 => true
    | 32, 43 => true
    | 32, 45 => true
    | 32, 46 => true
    | 32, 47 => true
    | 32, 50 => true
    | 33, 38 => true
    | 33, 39 => true
    | 33, 44 => true
    | 33, 46 => true
    | 33, 47 => true
    | 33, 50 => true
    | 34, 40 => true
    | 34, 41 => true
    | 34, 44 => true
    | 34, 45 => true
    | 34, 47 => true
    | 34, 50 => true
    | 35, 42 => true
    | 35, 43 => true
    | 35, 44 => true
    | 35, 45 => true
    | 35, 46 => true
    | 35, 50 => true
    | 36, 48 => true
    | 36, 51 => true
    | 37, 48 => true
    | 37, 51 => true
    | 38, 48 => true
    | 38, 51 => true
    | 39, 48 => true
    | 39, 51 => true
    | 40, 48 => true
    | 40, 51 => true
    | 41, 48 => true
    | 41, 51 => true
    | 42, 48 => true
    | 42, 51 => true
    | 43, 48 => true
    | 43, 51 => true
    | 44, 48 => true
    | 44, 51 => true
    | 45, 48 => true
    | 45, 51 => true
    | 46, 48 => true
    | 46, 51 => true
    | 47, 48 => true
    | 47, 51 => true
    | 48, 49 => true
    | 48, 50 => true
    | 48, 51 => true
    | 49, 50 => true
    | 49, 51 => true
    | 50, 51 => true
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
  Let inst_set := [set 'v12; 'v13; 'v14; 'v15; 'v16; 'v17; 'v18; 'v19; 'v20; 'v21; 'v22; 'v23; 'v36; 'v37; 'v38; 'v39; 'v40; 'v41; 'v42; 'v43; 'v44; 'v45; 'v46; 'v47; 'v50].

  Section List_of_Set.
    Definition inst_list := [:: 'v12; 'v13; 'v14; 'v15; 'v16; 'v17; 'v18; 'v19; 'v20; 'v21; 'v22; 'v23; 'v36; 'v37; 'v38; 'v39; 'v40; 'v41; 'v42; 'v43; 'v44; 'v45; 'v46; 'v47; 'v50].

    Fact inst_list_eq_inst_set : inst_list =i inst_set.
    Proof. by move=> v ; rewrite !inE /= ; try rewrite !orbA. Qed.

    Fact inst_list_uniq : uniq inst_list.
    Proof. done. Qed.
  End List_of_Set.

  Fact inst_set_card : #|inst_set| = 25.
  Proof. by rewrite -(eq_card inst_list_eq_inst_set) (card_uniqP inst_list_uniq). Qed.

  Fact inst_set_is_irr : @irredundant inst inst_set.
  Proof.
    apply (irredundant_checkP inst inst_list (ord_enum_eqT n)).
    - exact: inst_list_uniq.
    - exact: inst_list_eq_inst_set.
    - done.
  Qed.

  Fact IR_lb : IR inst >= 25.
  Proof.
    rewrite eq_IR_IR1 ; move: inst_set_card ; rewrite (@cardwset1 inst inst_set).
    move<- ; apply: IR_max ; exact: inst_set_is_irr.
  Qed.

End Certificate.
