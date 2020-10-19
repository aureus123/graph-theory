From mathcomp Require Import all_ssreflect.
Require Import preliminaries digraph sgraph dom check_ir.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(* Certificate of bull *)
Definition n := 5.

(**********************************************************************************)
Section Instance.
  Let inst_vert := 'I_n.
  Let inst_adj(u v : nat) :=
    match u, v with
    | 0, 2 => true
    | 1, 3 => true
    | 2, 3 => true
    | 2, 4 => true
    | 3, 4 => true
    | _, _ => false
    end.
  Let inst_rel := [ rel u v : inst_vert | give_sg inst_adj u v ].
  Let inst_sym : symmetric inst_rel. Proof. exact: give_sg_sym. Qed.
  Let inst_irrefl : irreflexive inst_rel. Proof. exact: give_sg_irrefl. Qed.
  Definition inst := SGraph inst_sym inst_irrefl.

  Definition weight (v : inst) := match v with
      | Ordinal 0 _ => 1
      | Ordinal 1 _ => 1
      | Ordinal 2 _ => 2
      | Ordinal 3 _ => 2
      | Ordinal _ _ => 1
      end.
End Instance.

Notation "''v' m" := (@Ordinal n m isT) (at level 0, m at level 8, format "''v' m").

(**********************************************************************************)
Section Certificate.
  Definition inst_set := [set 'v2; 'v3].

  Section List_of_Set.
    Definition inst_list := [:: 'v2; 'v3].

    Fact inst_list_eq_inst_set : inst_list =i inst_set.
    Proof. by move=> v ; rewrite !inE /= ; try rewrite !orbA. Qed.

    Fact inst_list_uniq : uniq inst_list.
    Proof. done. Qed.
  End List_of_Set.

  Fact inst_set_weight : weight_set weight inst_set = 4.
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

  Fact IR_w_lb : IR_w inst weight >= 4.
  Proof. move: inst_set_weight <- ; apply: IR_max ; exact: inst_set_is_irr. Qed.

End Certificate.
