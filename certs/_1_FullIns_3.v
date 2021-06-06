
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import preliminaries digraph sgraph dom.
Require Import check_ir prelim.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


Definition n := 30.

(**********************************************************************************)
Section Instance.
  Let inst_vert := 'I_n.
  Let inst_adj(u v : nat) :=
    match u, v with
    | 0, 1 => true
    | 0, 3 => true
    | 0, 10 => true
    | 0, 12 => true
    | 1, 2 => true
    | 1, 9 => true
    | 1, 11 => true
    | 2, 5 => true
    | 2, 7 => true
    | 2, 10 => true
    | 2, 14 => true
    | 2, 16 => true
    | 3, 4 => true
    | 3, 7 => true
    | 3, 9 => true
    | 3, 13 => true
    | 3, 16 => true
    | 4, 6 => true
    | 4, 8 => true
    | 4, 12 => true
    | 4, 15 => true
    | 4, 17 => true
    | 5, 6 => true
    | 5, 8 => true
    | 5, 11 => true
    | 5, 15 => true
    | 5, 17 => true
    | 6, 7 => true
    | 6, 8 => true
    | 6, 13 => true
    | 6, 14 => true
    | 6, 16 => true
    | 6, 17 => true
    | 7, 8 => true
    | 7, 11 => true
    | 7, 12 => true
    | 7, 15 => true
    | 7, 17 => true
    | 8, 13 => true
    | 8, 14 => true
    | 8, 15 => true
    | 8, 16 => true
    | 9, 19 => true
    | 9, 21 => true
    | 9, 28 => true
    | 10, 18 => true
    | 10, 20 => true
    | 10, 28 => true
    | 11, 19 => true
    | 11, 23 => true
    | 11, 25 => true
    | 11, 28 => true
    | 12, 18 => true
    | 12, 22 => true
    | 12, 25 => true
    | 12, 28 => true
    | 13, 21 => true
    | 13, 24 => true
    | 13, 26 => true
    | 13, 28 => true
    | 14, 20 => true
    | 14, 24 => true
    | 14, 26 => true
    | 14, 28 => true
    | 15, 22 => true
    | 15, 23 => true
    | 15, 25 => true
    | 15, 26 => true
    | 15, 28 => true
    | 16, 20 => true
    | 16, 21 => true
    | 16, 24 => true
    | 16, 26 => true
    | 16, 28 => true
    | 17, 22 => true
    | 17, 23 => true
    | 17, 24 => true
    | 17, 25 => true
    | 17, 28 => true
    | 18, 27 => true
    | 18, 29 => true
    | 19, 27 => true
    | 19, 29 => true
    | 20, 27 => true
    | 20, 29 => true
    | 21, 27 => true
    | 21, 29 => true
    | 22, 27 => true
    | 22, 29 => true
    | 23, 27 => true
    | 23, 29 => true
    | 24, 27 => true
    | 24, 29 => true
    | 25, 27 => true
    | 25, 29 => true
    | 26, 27 => true
    | 26, 29 => true
    | 27, 28 => true
    | 27, 29 => true
    | 28, 29 => true
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
  Let inst_set := [set 'v1; 'v4; 'v5; 'v7; 'v18; 'v19; 'v20; 'v21; 'v22; 'v23; 'v24; 'v25; 'v26; 'v28].

  Section List_of_Set.
    Definition inst_list := [:: 'v1; 'v4; 'v5; 'v7; 'v18; 'v19; 'v20; 'v21; 'v22; 'v23; 'v24; 'v25; 'v26; 'v28].

    Fact inst_list_eq_inst_set : inst_list =i inst_set.
    Proof. by move=> v ; rewrite !inE ; try rewrite !orbA. Qed.

    Fact inst_list_uniq : uniq inst_list.
    Proof. done. Qed.
  End List_of_Set.

  Fact inst_set_card : #|inst_set| = 14.
  Proof. by rewrite -(eq_card inst_list_eq_inst_set) (card_uniqP inst_list_uniq). Qed.

  Fact inst_set_is_irr : @irredundant inst inst_set.
  Proof.
    apply (irredundant_checkP inst inst_list (ord_enum_eqT n)).
    - exact: inst_list_uniq.
    - exact: inst_list_eq_inst_set.
    - done.
  Qed.

  Fact IR_lb : IR inst >= 14.
  Proof.
    rewrite eq_IR_IR1 ; move: inst_set_card ; rewrite (@cardwset1 inst inst_set).
    move<- ; apply: IR_max ; exact: inst_set_is_irr.
  Qed.

End Certificate.
