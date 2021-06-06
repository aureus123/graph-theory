
From mathcomp Require Import all_ssreflect.
From GraphTheory Require Import preliminaries digraph sgraph dom.
Require Import check_ir prelim.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


Definition n := 48.

(**********************************************************************************)
Section Instance.
  Let inst_vert := 'I_n.
  Let inst_adj(u v : nat) :=
    match u, v with
    | 0, 1 => true
    | 0, 2 => true
    | 0, 3 => true
    | 1, 2 => true
    | 1, 4 => true
    | 2, 3 => true
    | 2, 4 => true
    | 3, 4 => true
    | 3, 7 => true
    | 3, 8 => true
    | 3, 9 => true
    | 4, 5 => true
    | 4, 6 => true
    | 4, 7 => true
    | 5, 10 => true
    | 5, 11 => true
    | 6, 7 => true
    | 6, 10 => true
    | 6, 13 => true
    | 7, 8 => true
    | 7, 13 => true
    | 7, 14 => true
    | 8, 9 => true
    | 8, 14 => true
    | 9, 14 => true
    | 9, 15 => true
    | 9, 16 => true
    | 10, 11 => true
    | 10, 12 => true
    | 10, 13 => true
    | 11, 12 => true
    | 11, 18 => true
    | 11, 19 => true
    | 12, 13 => true
    | 12, 19 => true
    | 12, 20 => true
    | 12, 21 => true
    | 13, 14 => true
    | 13, 15 => true
    | 13, 21 => true
    | 14, 15 => true
    | 15, 22 => true
    | 15, 23 => true
    | 16, 17 => true
    | 16, 23 => true
    | 16, 24 => true
    | 16, 25 => true
    | 17, 25 => true
    | 17, 26 => true
    | 18, 19 => true
    | 18, 27 => true
    | 19, 20 => true
    | 19, 27 => true
    | 19, 28 => true
    | 19, 29 => true
    | 19, 30 => true
    | 20, 21 => true
    | 20, 30 => true
    | 20, 31 => true
    | 21, 22 => true
    | 21, 31 => true
    | 22, 23 => true
    | 22, 31 => true
    | 22, 32 => true
    | 22, 33 => true
    | 23, 24 => true
    | 23, 33 => true
    | 24, 25 => true
    | 24, 34 => true
    | 24, 36 => true
    | 25, 26 => true
    | 25, 36 => true
    | 26, 36 => true
    | 26, 37 => true
    | 26, 44 => true
    | 27, 28 => true
    | 27, 38 => true
    | 28, 29 => true
    | 28, 38 => true
    | 28, 39 => true
    | 28, 40 => true
    | 29, 30 => true
    | 29, 40 => true
    | 30, 31 => true
    | 30, 40 => true
    | 31, 32 => true
    | 31, 40 => true
    | 31, 46 => true
    | 32, 33 => true
    | 32, 41 => true
    | 33, 34 => true
    | 33, 41 => true
    | 33, 42 => true
    | 34, 35 => true
    | 34, 42 => true
    | 35, 36 => true
    | 35, 37 => true
    | 35, 42 => true
    | 35, 43 => true
    | 36, 37 => true
    | 37, 43 => true
    | 37, 44 => true
    | 38, 39 => true
    | 39, 40 => true
    | 39, 45 => true
    | 40, 45 => true
    | 40, 46 => true
    | 41, 42 => true
    | 41, 43 => true
    | 41, 46 => true
    | 42, 43 => true
    | 43, 44 => true
    | 45, 46 => true
    | 45, 47 => true
    | 46, 47 => true
    | _, _ => false
    end.

  Let inst_rel := [ rel u v : inst_vert | give_sg inst_adj u v ].
  Let inst_sym : symmetric inst_rel. Proof. exact: give_sg_sym. Qed.
  Let inst_irrefl : irreflexive inst_rel. Proof. exact: give_sg_irrefl. Qed.
  Definition inst := SGraph inst_sym inst_irrefl.

  Definition weight (v : inst) := match v with
      | Ordinal 0 _ => 53
      | Ordinal 1 _ => 52
      | Ordinal 2 _ => 19
      | Ordinal 3 _ => 139
      | Ordinal 4 _ => 89
      | Ordinal 5 _ => 40
      | Ordinal 6 _ => 39
      | Ordinal 7 _ => 23
      | Ordinal 8 _ => 57
      | Ordinal 9 _ => 252
      | Ordinal 10 _ => 35
      | Ordinal 11 _ => 71
      | Ordinal 12 _ => 59
      | Ordinal 13 _ => 20
      | Ordinal 14 _ => 27
      | Ordinal 15 _ => 90
      | Ordinal 16 _ => 189
      | Ordinal 17 _ => 45
      | Ordinal 18 _ => 14
      | Ordinal 19 _ => 44
      | Ordinal 20 _ => 34
      | Ordinal 21 _ => 36
      | Ordinal 22 _ => 183
      | Ordinal 23 _ => 139
      | Ordinal 24 _ => 152
      | Ordinal 25 _ => 33
      | Ordinal 26 _ => 7
      | Ordinal 27 _ => 14
      | Ordinal 28 _ => 33
      | Ordinal 29 _ => 36
      | Ordinal 30 _ => 39
      | Ordinal 31 _ => 150
      | Ordinal 32 _ => 39
      | Ordinal 33 _ => 49
      | Ordinal 34 _ => 50
      | Ordinal 35 _ => 46
      | Ordinal 36 _ => 35
      | Ordinal 37 _ => 26
      | Ordinal 38 _ => 44
      | Ordinal 39 _ => 65
      | Ordinal 40 _ => 54
      | Ordinal 41 _ => 63
      | Ordinal 42 _ => 41
      | Ordinal 43 _ => 77
      | Ordinal 44 _ => 46
      | Ordinal 45 _ => 114
      | Ordinal 46 _ => 41
      | Ordinal _ _ => 15
      end.
End Instance.

Notation "''v' m" := (@Ordinal n m isT) (at level 0, m at level 8, format "''v' m").

(**********************************************************************************)
Section Certificate.
  Let inst_set := [set 'v3; 'v4; 'v6; 'v9; 'v11; 'v16; 'v18; 'v22; 'v24; 'v31; 'v39; 'v40; 'v43; 'v44; 'v45].

  Section List_of_Set.
    Definition inst_list := [:: 'v3; 'v4; 'v6; 'v9; 'v11; 'v16; 'v18; 'v22; 'v24; 'v31; 'v39; 'v40; 'v43; 'v44; 'v45].

    Fact inst_list_eq_inst_set : inst_list =i inst_set.
    Proof. by move=> v ; rewrite !inE ; try rewrite !orbA. Qed.

    Fact inst_list_uniq : uniq inst_list.
    Proof. done. Qed.
  End List_of_Set.

  Fact inst_set_weight : weight_set weight inst_set = 1634.
  Proof.
    (* slow code, TO DO: apply the same technique as "card" *)
    rewrite /inst_set.
    try rewrite -!setUA.
    try rewrite !weightsU1 !inE.
    try rewrite negb_or.
    by rewrite /weight_set big_set1.
  Qed.

  Fact inst_set_is_irr : @irredundant inst inst_set.
  Proof.
    apply (irredundant_checkP inst inst_list (ord_enum_eqT n)).
    - exact: inst_list_uniq.
    - exact: inst_list_eq_inst_set.
    - done.
  Qed.

  Fact IR_w_lb : IR_w inst weight >= 1634.
  Proof. move: inst_set_weight <- ; apply: IR_max ; exact: inst_set_is_irr. Qed.

End Certificate.
