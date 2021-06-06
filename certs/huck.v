
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import preliminaries digraph sgraph dom.
Require Import check_ir prelim.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


Definition n := 79.

(**********************************************************************************)
Section Instance.
  Let inst_vert := 'I_n.
  Let inst_adj(u v : nat) :=
    match u, v with
    | 0, 1 => true
    | 0, 3 => true
    | 0, 14 => true
    | 0, 16 => true
    | 1, 2 => true
    | 1, 13 => true
    | 1, 15 => true
    | 2, 5 => true
    | 2, 14 => true
    | 2, 18 => true
    | 3, 4 => true
    | 3, 13 => true
    | 3, 17 => true
    | 4, 7 => true
    | 4, 16 => true
    | 4, 20 => true
    | 5, 6 => true
    | 5, 15 => true
    | 5, 19 => true
    | 6, 9 => true
    | 6, 18 => true
    | 6, 22 => true
    | 7, 8 => true
    | 7, 17 => true
    | 7, 21 => true
    | 8, 11 => true
    | 8, 20 => true
    | 8, 24 => true
    | 9, 10 => true
    | 9, 19 => true
    | 9, 23 => true
    | 10, 12 => true
    | 10, 22 => true
    | 10, 25 => true
    | 11, 12 => true
    | 11, 21 => true
    | 11, 25 => true
    | 12, 23 => true
    | 12, 24 => true
    | 13, 27 => true
    | 13, 29 => true
    | 14, 26 => true
    | 14, 28 => true
    | 15, 27 => true
    | 15, 31 => true
    | 16, 26 => true
    | 16, 30 => true
    | 17, 29 => true
    | 17, 33 => true
    | 18, 28 => true
    | 18, 32 => true
    | 19, 31 => true
    | 19, 35 => true
    | 20, 30 => true
    | 20, 34 => true
    | 21, 33 => true
    | 21, 37 => true
    | 22, 32 => true
    | 22, 36 => true
    | 23, 35 => true
    | 23, 38 => true
    | 24, 34 => true
    | 24, 38 => true
    | 25, 36 => true
    | 25, 37 => true
    | 26, 40 => true
    | 26, 42 => true
    | 27, 39 => true
    | 27, 41 => true
    | 28, 40 => true
    | 28, 44 => true
    | 29, 39 => true
    | 29, 43 => true
    | 30, 42 => true
    | 30, 46 => true
    | 31, 41 => true
    | 31, 45 => true
    | 32, 44 => true
    | 32, 48 => true
    | 33, 43 => true
    | 33, 47 => true
    | 34, 46 => true
    | 34, 50 => true
    | 35, 45 => true
    | 35, 49 => true
    | 36, 48 => true
    | 36, 51 => true
    | 37, 47 => true
    | 37, 51 => true
    | 38, 49 => true
    | 38, 50 => true
    | 39, 53 => true
    | 39, 55 => true
    | 40, 52 => true
    | 40, 54 => true
    | 41, 53 => true
    | 41, 57 => true
    | 42, 52 => true
    | 42, 56 => true
    | 43, 55 => true
    | 43, 59 => true
    | 44, 54 => true
    | 44, 58 => true
    | 45, 57 => true
    | 45, 61 => true
    | 46, 56 => true
    | 46, 60 => true
    | 47, 59 => true
    | 47, 63 => true
    | 48, 58 => true
    | 48, 62 => true
    | 49, 61 => true
    | 49, 64 => true
    | 50, 60 => true
    | 50, 64 => true
    | 51, 62 => true
    | 51, 63 => true
    | 52, 66 => true
    | 52, 68 => true
    | 53, 65 => true
    | 53, 67 => true
    | 54, 66 => true
    | 54, 70 => true
    | 55, 65 => true
    | 55, 69 => true
    | 56, 68 => true
    | 56, 72 => true
    | 57, 67 => true
    | 57, 71 => true
    | 58, 70 => true
    | 58, 74 => true
    | 59, 69 => true
    | 59, 73 => true
    | 60, 72 => true
    | 60, 76 => true
    | 61, 71 => true
    | 61, 75 => true
    | 62, 74 => true
    | 62, 77 => true
    | 63, 73 => true
    | 63, 77 => true
    | 64, 75 => true
    | 64, 76 => true
    | 65, 78 => true
    | 66, 78 => true
    | 67, 78 => true
    | 68, 78 => true
    | 69, 78 => true
    | 70, 78 => true
    | 71, 78 => true
    | 72, 78 => true
    | 73, 78 => true
    | 74, 78 => true
    | 75, 78 => true
    | 76, 78 => true
    | 77, 78 => true
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
  Let inst_set := [set 'v13; 'v14; 'v15; 'v16; 'v17; 'v18; 'v19; 'v20; 'v21; 'v22; 'v23; 'v24; 'v25; 'v39; 'v40; 'v41; 'v42; 'v43; 'v44; 'v45; 'v46; 'v47; 'v48; 'v49; 'v50; 'v51; 'v65; 'v66; 'v67; 'v68; 'v69; 'v70; 'v71; 'v72; 'v73; 'v74; 'v75; 'v76; 'v77].

  Section List_of_Set.
    Definition inst_list := [:: 'v13; 'v14; 'v15; 'v16; 'v17; 'v18; 'v19; 'v20; 'v21; 'v22; 'v23; 'v24; 'v25; 'v39; 'v40; 'v41; 'v42; 'v43; 'v44; 'v45; 'v46; 'v47; 'v48; 'v49; 'v50; 'v51; 'v65; 'v66; 'v67; 'v68; 'v69; 'v70; 'v71; 'v72; 'v73; 'v74; 'v75; 'v76; 'v77].

    Fact inst_list_eq_inst_set : inst_list =i inst_set.
    Proof. by move=> v ; rewrite !inE ; try rewrite !orbA. Qed.

    Fact inst_list_uniq : uniq inst_list.
    Proof. done. Qed.
  End List_of_Set.

  Fact inst_set_card : #|inst_set| = 39.
  Proof. by rewrite -(eq_card inst_list_eq_inst_set) (card_uniqP inst_list_uniq). Qed.

  Fact inst_set_is_irr : @irredundant inst inst_set.
  Proof.
    apply (irredundant_checkP inst inst_list (ord_enum_eqT n)).
    - exact: inst_list_uniq.
    - exact: inst_list_eq_inst_set.
    - done.
  Qed.

  Fact IR_lb : IR inst >= 39.
  Proof.
    rewrite eq_IR_IR1 ; move: inst_set_card ; rewrite (@cardwset1 inst inst_set).
    move<- ; apply: IR_max ; exact: inst_set_is_irr.
  Qed.

End Certificate.
