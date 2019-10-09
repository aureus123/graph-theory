Require Import Setoid CMorphisms.
Require Relation_Definitions.
From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Bijections between Types  *)

Record bij (A B: Type): Type := Bij
  { bij_fwd:> A -> B;
    bij_bwd: B -> A;
    bijK: cancel bij_fwd bij_bwd;
    bijK': cancel bij_bwd bij_fwd }.
Notation "h '^-1'" := (bij_bwd h). 

(** Facts about Bijections *)

Lemma bij_bijective A B (f : bij A B) : bijective f.
Proof. case: f => f g can_f can_g. by exists g. Qed.

Lemma bij_bijective' A B (f : bij A B) : bijective f^-1.
Proof. case: f => f g can_f can_g. by exists f. Qed.

Hint Resolve bij_bijective bij_bijective'.

Lemma bij_injective A B (f: bij A B) : injective f.
Proof. exact: bij_inj. Qed.

Lemma bij_injective' A B (f: bij A B) : injective f^-1.
Proof. exact: bij_inj. Qed.

Hint Resolve bij_injective bij_injective'.

Lemma card_bij (A B: finType) (f : bij A B) : #|A| = #|B|.
Proof. exact: (bij_card_eq (f := f)). Qed.
Arguments card_bij [A B] f.

(** Specific Bijections *)

Definition bij_id {A}: bij A A := @Bij A A id id (@erefl A) (@erefl A).

Definition bij_sym {A B}: bij A B -> bij B A.
Proof. move=>f. econstructor; apply f. Defined.

Definition bij_comp {A B C}: bij A B -> bij B C -> bij A C.
Proof.
  move=> f g.
  econstructor; apply can_comp. apply g. apply f. apply f. apply g. 
Defined.

Instance bij_Equivalence: Equivalence bij.
Proof. constructor. exact @bij_id. exact @bij_sym. exact @bij_comp. Defined.


(* bijections about [sum] *)

Definition sumf {A B C D} (f: A -> B) (g: C -> D) (x: A+C): B+D :=
  match x with inl a => inl (f a) | inr c => inr (g c) end. 

Instance sum_bij: Proper (bij ==> bij ==> bij) sum.
Proof.
  intros A A' f B B' g.
  exists (sumf f g) (sumf f^-1 g^-1); abstract (by move=>[a|b] /=; rewrite ?bijK ?bijK').
Defined.

Definition sumC {A B} (x: A + B): B + A := match x with inl x => inr x | inr x => inl x end.
Lemma bij_sumC {A B}: bij (A+B) (B+A).
Proof. exists sumC sumC; abstract by repeat case. Defined.

Definition sumA {A B C} (x: A + (B + C)): (A + B) + C :=
  match x with inl x => inl (inl x) | inr (inl x) => inl (inr x) | inr (inr x) => inr x end.
Definition sumA' {A B C} (x: (A + B) + C): A + (B + C) :=
  match x with inr x => inr (inr x) | inl (inr x) => inr (inl x) | inl (inl x) => inl x end.
Lemma bij_sumA {A B C}: bij (A+(B+C)) ((A+B)+C).
Proof. exists sumA sumA'; abstract by repeat case. Defined.

Lemma sumUx {A}: bij (void + A) A.
Proof.
  exists
    (fun x => match x with inl x => vfun x | inr a => a end)
    (fun x => inr x);
  abstract by repeat case.
Defined.
Lemma sumxU {A}: bij (A + void) A.
Proof. etransitivity. apply bij_sumC. apply sumUx. Defined.


(* bijections for [option] types *)

Definition option_bij (A B : Type) (f : bij A B) : bij (option A) (option B).
Proof.
  exists (option_map f) (option_map f^-1); abstract (case => //= x; by rewrite ?bijK ?bijK'). 
Defined.

Lemma option_sum_unit {A}: bij (option A) (A+unit).
Proof.
  exists
    (fun x => match x with Some a => inl a | None => inr tt end)
    (fun x => match x with inl a => Some a | inr _ => None end).
  all: abstract (repeat case=>//).
Defined.

(* the definitions below also follow from [option_sum_unit] and the bijections about [sum] *)
Definition option_void: bij (option void) unit.
Proof. exists (fun _ => tt) (fun _ => None); by case. Defined.

Lemma sum_option_l {A B}: bij ((option A) + B) (option (A + B)).
Proof.
  exists
    (fun x => match x with inl (Some a) => Some (inl a) | inl None => None | inr b => Some (inr b) end)
    (fun x => match x with Some (inl a) => inl (Some a) | None => inl None | Some (inr b) => inr b end).
  all: abstract (repeat case=>//).
Defined.

Lemma sum_option_r {A B}: bij (A + option B) (option (A + B)).
Proof.
  etransitivity. apply bij_sumC. 
  etransitivity. apply sum_option_l.
  apply option_bij, bij_sumC.
Defined. 

Definition option2x {A}: option (option A) -> option (option A) :=
  fun x => match x with Some (Some a) => Some (Some a) | Some None => None | None => Some None end.
Definition option2_swap {A}: bij (option (option A)) (option (option A)).
  exists option2x option2x; abstract by repeat case. 
Defined.


(* bijections for [bool] *)

Definition bool_swap: bij bool bool.
Proof. exists negb negb; by case. Defined.

Lemma bool_two: bij bool (unit+unit).
Proof.
  exists
    (fun b => if b then inr tt else inl tt)
    (fun x => match x with inl _ => false | inr _ => true end).
  all: abstract by repeat case.
Defined.  

Definition bool_option_unit: bij bool (option unit).
Proof.
  exists
    (fun b => if b then None else  Some tt)
    (fun o => if o is None then true else false);
    abstract by repeat case. 
Defined.


(** Useful to obtain bijections with good simplification properties *)
Lemma bij_same A B (f : A -> B) (f_inv : B -> A) (i : bij A B) :
  f =1 i -> f_inv =1 i^-1 -> bij A B.
Proof.
  move => Hf Hf'.
  exists f f_inv; abstract (move => x; by rewrite Hf Hf' ?bijK ?bijK').
Defined.
Arguments bij_same [A B] f f_inv i _ _.
