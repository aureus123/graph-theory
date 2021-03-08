
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import preliminaries digraph sgraph dom.
Require Import check_ir prelim.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


Definition n := 23.

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
    | 1, 2 => true
    | 1, 5 => true
    | 1, 7 => true
    | 1, 11 => true
    | 1, 13 => true
    | 1, 16 => true
    | 1, 18 => true
    | 2, 4 => true
    | 2, 6 => true
    | 2, 9 => true
    | 2, 12 => true
    | 2, 15 => true
    | 2, 17 => true
    | 2, 20 => true
    | 3, 4 => true
    | 3, 5 => true
    | 3, 9 => true
    | 3, 11 => true
    | 3, 15 => true
    | 3, 16 => true
    | 3, 20 => true
    | 4, 7 => true
    | 4, 8 => true
    | 4, 13 => true
    | 4, 14 => true
    | 4, 18 => true
    | 4, 19 => true
    | 5, 10 => true
    | 5, 12 => true
    | 5, 14 => true
    | 5, 21 => true
    | 6, 10 => true
    | 6, 11 => true
    | 6, 13 => true
    | 6, 21 => true
    | 7, 10 => true
    | 7, 12 => true
    | 7, 15 => true
    | 7, 21 => true
    | 8, 10 => true
    | 8, 11 => true
    | 8, 15 => true
    | 8, 21 => true
    | 9, 10 => true
    | 9, 13 => true
    | 9, 14 => true
    | 9, 21 => true
    | 10, 16 => true
    | 10, 17 => true
    | 10, 18 => true
    | 10, 19 => true
    | 10, 20 => true
    | 11, 22 => true
    | 12, 22 => true
    | 13, 22 => true
    | 14, 22 => true
    | 15, 22 => true
    | 16, 22 => true
    | 17, 22 => true
    | 18, 22 => true
    | 19, 22 => true
    | 20, 22 => true
    | 21, 22 => true
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
  Let inst_set := [set 'v11; 'v12; 'v13; 'v14; 'v15; 'v16; 'v17; 'v18; 'v19; 'v20; 'v21].

  Section List_of_Set.
    Definition inst_list := [:: 'v11; 'v12; 'v13; 'v14; 'v15; 'v16; 'v17; 'v18; 'v19; 'v20; 'v21].

    Fact inst_list_eq_inst_set : inst_list =i inst_set.
    Proof. by move=> v ; rewrite !inE /= ; try rewrite !orbA. Qed.

    Fact inst_list_uniq : uniq inst_list.
    Proof. done. Qed.
  End List_of_Set.

  Fact inst_set_card : #|inst_set| = 11.
  Proof. by rewrite -(eq_card inst_list_eq_inst_set) (card_uniqP inst_list_uniq). Qed.

  Fact inst_set_is_irr : @irredundant inst inst_set.
  Proof.
    apply (irredundant_checkP inst inst_list (ord_enum_eqT n)).
    - exact: inst_list_uniq.
    - exact: inst_list_eq_inst_set.
    - done.
  Qed.

  Fact IR_lb : IR inst >= 11.
  Proof.
    rewrite eq_IR_IR1 ; move: inst_set_card ; rewrite (@cardwset1 inst inst_set).
    move<- ; apply: IR_max ; exact: inst_set_is_irr.
  Qed.

End Certificate.
