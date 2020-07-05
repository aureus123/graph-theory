From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section SetOfList.
Variables (T : finType).

Fixpoint set_of_list x (s : seq T) := 
  if s is y :: s then set_of_list y s :|: [set x] else [set x].

Lemma set_of_listE x (s : seq T) : set_of_list x s =i x::s.
Proof. elim: s x => //= [x|y s IHs x] z; by rewrite !inE // IHs orbC. Qed.

Lemma cards_list x (s : seq T) : uniq (x::s) -> #|set_of_list x s| = (size s).+1.
Proof.
  elim: s x => //= [x|y s IHs x]; first by rewrite cards1.
  rewrite inE negb_or -!andbA => /and4P [A B C D].
  rewrite cardsU setIC [#| _ :&: _|]eq_card0.
  + by rewrite subn0 cards1 addn1 IHs ?C.
  + move => z. rewrite !(inE,set_of_listE). 
    case: (altP (z =P x)) => // ->. by rewrite (negbTE A) (negbTE B).
Qed.
End SetOfList.

Section Graph.
Let n := 6.
Definition v0 := @Ordinal n 0 isT : 'I_n.
Definition v1 := @Ordinal n 1 isT : 'I_n.
Definition v2 := @Ordinal n 2 isT : 'I_n.
Definition v3 := @Ordinal n 3 isT : 'I_n.
Definition v4 := @Ordinal n 4 isT : 'I_n.
Definition v5 := @Ordinal n 5 isT : 'I_n.

(* NOTE: the reification part (i.e., introducting [set_of_list] could be done by a tactic) *)
Lemma foo : #|[set v1; v2; v4]| = 3.
by rewrite -!setUA !cardsU1 !inE negb_or cards1.
Qed.

Lemma foo' : #|[set v1; v2; v4]| = 3.
Proof. rewrite -[X in #|_ X|]/(set_of_list v4 [:: v2; v1]). by rewrite cards_list. Qed.

Lemma test (T : finType) (A B : {set T}) : 
  (forall x, (x \in A) (+) (x \in B)) -> ~: A = B.
Admitted.

Lemma bar : ~: [set v1; v2; v4] = [set v0; v3; v5].
Proof. apply: test. case. move => [|[|[|[|[|[|//]]]]]] p; by rewrite !inE. Qed.
  
