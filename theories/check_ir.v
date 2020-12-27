From mathcomp Require Import all_ssreflect.
Require Import preliminaries digraph sgraph dom.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


(** Function for generating graphs (used by wirred.v and solver) *)

(* give_sg generate the sedge relation from a function f such that:
     f u v (with 0 <= u < v < n) is true iff (u,v) is an edge of G *)
Definition give_sg (f : nat -> nat -> bool) (n : nat) (i j : 'I_n) :=
  let u := nat_of_ord i in
    let v := nat_of_ord j in
      if (u == v) then false else
        if (u < v) then f u v else f v u.

Fact give_sg_sym (f : nat -> nat -> bool) (n : nat) : symmetric (give_sg f (n:=n)).
Proof.
  rewrite /symmetric /give_sg => u v.
  case: (boolP (u == v))=> [ | uneqv] ; first by move/eqP->.
  rewrite (ifN _ _ uneqv).
  rewrite eq_sym in uneqv.
  rewrite (ifN _ _ uneqv).
  rewrite neq_ltn in uneqv.
  by case: (orP uneqv) => ultv;
    move: (ltnW ultv) ; rewrite leqNgt => nvltu; rewrite (ifN _ _ nvltu) ultv.
Qed.

Fact give_sg_irrefl (f : nat -> nat -> bool) (n : nat) : irreflexive (give_sg f (n:=n)).
Proof. by rewrite /irreflexive /give_sg => ? ; rewrite eq_refl. Qed.


Section Weighted_Sets.
  Variables (T : finType) (weight : T -> nat).
  Let W := weight_set weight.

  (* equivalent to cardsU1, but for weighted sets *)
  Lemma weightsU1 (a : T) (A : {set T}) :
    W (a |: A) = (weight a) * (a \notin A) + W A.
  Proof.
    rewrite /W /weight_set.
    case: (boolP (a \notin A)) => [H | H].
    - by rewrite (big_setU1 _ H) /= muln1.
    - rewrite muln0 add0n.
      suff iden : a |: A = A by under eq_bigl => x do rewrite iden.
      apply/eqP ; rewrite eqEsubset ; apply/andP ; split.
      + apply/subsetP => x ; rewrite in_setU1 ; case/orP=> //.
        by move/eqP-> ; move: H ; apply: contraR.
      + apply/subsetP => ? ; exact: setU1r.
  Qed.
End Weighted_Sets.


(** * Computationally checking that a set is irredundant *)

Lemma eq_in_pmap (aT : eqType) rT (f1 f2 : aT -> option rT) (s : seq aT) : 
  {in s, f1 =1 f2} -> pmap f1 s = pmap f2 s.
Proof. by elim: s => // a s IHs /all_cons [eq_a eq_s]; rewrite /= eq_a (IHs eq_s). Qed.

(** ** Enumeration of ['I_n] that computes to a reasonable normal form *)
Section EnumI.
  Variable (k : nat).

  Definition ord_enum_eq : seq 'I_k := pmap (insub_eq _) (iota 0 k).

  Lemma eq_ord_enum : ord_enum_eq = ord_enum k.
  Proof. apply: eq_in_pmap => n _ ; exact: insub_eqE. Qed.

  Lemma ord_enum_eqT : ord_enum_eq =i 'I_k.
  Proof. by move => i; rewrite eq_ord_enum mem_ord_enum. Qed.
End EnumI.

Section CheckIR.
  Variable (G : sgraph).
  Implicit Types (V s : seq G) (A : {set G}).

  Definition has_private (V s : seq G) (v : G) :=
    has [pred w | v -*- w && all [pred u | ~~ u -*- w] (rem v s)] V.

  Lemma has_privateE V s v : uniq s -> V =i G ->
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
