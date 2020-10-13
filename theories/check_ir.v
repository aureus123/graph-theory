From mathcomp Require Import all_ssreflect.
Require Import preliminaries digraph sgraph dom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(** * Computationally checking that a set is irredundant *)

Lemma eq_in_pmap (aT : eqType) rT (f1 f2 : aT -> option rT) (s : seq aT) : 
  {in s, f1 =1 f2} -> pmap f1 s = pmap f2 s.
Proof.
by elim: s => // a s IHs /all_cons [eq_a eq_s]; rewrite /= eq_a (IHs eq_s).
Qed.

(** ** Enumeration of ['I_n] that computes to a reasonable normal form *)
Section EnumI.
Variable (k : nat).

Definition ord_enum_eq : seq 'I_k := pmap (insub_eq _) (iota 0 k).

Lemma eq_ord_enum : ord_enum_eq = ord_enum k.
Proof. apply:eq_in_pmap => n _. exact: insub_eqE. Qed.

Lemma ord_enum_eqT : ord_enum_eq =i 'I_k.
Proof. by move => i; rewrite eq_ord_enum mem_ord_enum. Qed.

End EnumI.

Section CheckIR.
Variable (G : sgraph).
Implicit Types (V s : seq G) (A : {set G}).

Definition has_private (V s : seq G) (v : G) := 
  has [pred w | v -*- w && all [pred u | ~~ u -*- w] (rem v s)] V.

Lemma has_privateE V s v : 
  uniq s -> V =i G -> 
  (has_private V s v) = (private_set [set z in s] v != set0).
Proof.
move=> uniq_V eq_VG; apply/hasP/set0Pn => [[w /= W1 /andP [W2 /allP /= W3]]|].
  exists w; apply/privateP; split => // u; rewrite inE => u_s uw. 
  by apply: contraTeq uw => uDv; apply: W3; rewrite mem_rem_uniq // inE uDv.
move=> [w /privateP [vw priv_w]]; exists w; rewrite ?eq_VG //= vw /=.
apply/allP => u; rewrite mem_rem_uniq // !inE => /andP[uDv u_s]. 
by apply: contra_neqN uDv; apply: priv_w; rewrite inE.
Qed.

Definition irredundant_check (V s : seq G) := all (has_private V s) s.

Lemma irredundant_checkP V s A : 
  V =i G -> uniq s -> s =i A -> irredundant_check V s -> irredundant A.
Proof.
move=> eq_VG uniq_s  eq_As /allP chk; apply/irredundantP => v.
have -> : A = [set z in s] by apply/setP => z; rewrite inE -eq_As.
by rewrite inE => /chk; rewrite has_privateE.
Qed.

End CheckIR.

Arguments ord_enum_eqT : clear implicits.
Arguments irredundant_checkP G [V] s [A] _.

(* Christian's example *)
Example irK4 : @irredundant 'K_4 [set ord0].
Proof.
apply (irredundant_checkP 'K_4 [:: ord0] (ord_enum_eqT 4)); try done.
by move => z; rewrite !inE.
Qed.

(* Certificate of myciel3 *)
Definition n := 11.

(**********************************************************************************)
Section Instance.
  Let inst_vert := 'I_n.
  Let inst_adj(u v : nat) :=
    match u, v with
    | 0, 1 => true
    | 0, 3 => true
    | 0, 6 => true
    | 0, 8 => true
    | 1, 2 => true
    | 1, 5 => true
    | 1, 7 => true
    | 2, 4 => true
    | 2, 6 => true
    | 2, 9 => true
    | 3, 4 => true
    | 3, 5 => true
    | 3, 9 => true
    | 4, 7 => true
    | 4, 8 => true
    | 5, 10 => true
    | 6, 10 => true
    | 7, 10 => true
    | 8, 10 => true
    | 9, 10 => true
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
  Let inst_set := [set 'v5; 'v6; 'v7; 'v8; 'v9].

  Fact inst_set_is_irr : @irredundant inst inst_set.
  Proof.
    set inst_list := [:: 'v5; 'v6; 'v7; 'v8; 'v9].
    apply (irredundant_checkP inst inst_list (ord_enum_eqT n)) ; try done.
    by move=> v ; rewrite !inE /= !orbA.
  Qed.

  Fact IR_lb : IR inst >= 5.
  Proof.
    rewrite eq_IR_IR1.
    suff: weight_set (@ones inst) inst_set = 5.
    move<- ; apply: IR_max ; exact: inst_set_is_irr.
    rewrite -cardwset1 /inst_set.
    try rewrite -!setUA.
    rewrite !cardsU1 !inE.
    try rewrite negb_or.
    by rewrite cards1.
  Qed.

End Certificate.


