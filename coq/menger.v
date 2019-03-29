From mathcomp Require Import all_ssreflect.
Require Import edone preliminaries path sgraph set_tac.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

(** * Menger's Theorem *)

(** In this file we prove Menger's Theorem and some of its most
well-known and most-used corollaries. The proof follows Göring's
"Short Proof of Menger's Theorem".  The two most central notions in
the proof are those of an AB-separator and an AB-connector. *)

(** ** Separators and Connectors *)

Section SeparatorConnector.
Variables (G : diGraph).
Implicit Types (x y : G) (A B S : {set G}).

Definition separator (A B S : {set G}) :=
  forall (a b : G) (p : Path a b), a \in A -> b \in B -> exists2 s, s \in S & s \in p.

Lemma separatorI A B S : 
  (forall (a b : G) (p : Path a b), irred p -> a \in A -> b \in B -> exists2 s, s \in S & s \in p)
  -> separator A B S.
Proof. 
  move => H a b p aA bB. case: (uncycle p) => p' sub_p Ip. case: (H _ _ p') => //.
  move => s sS /sub_p sp. by exists s.
Qed.

Definition separatorb (A B S : {set G}) := 
  [forall a in A, forall b in B, forall p : IPath a b, exists s in S, s \in p].

Lemma separatorP (A B S : {set G}) : reflect (separator A B S) (separatorb A B S).
Proof.
  rewrite /separatorb. apply: (iffP forall_inP) => [H|H a aA].
  - apply: separatorI => a b p Ip aA bB. 
    move/(_ _ aA) : H => /forall_inP /(_ _ bB) /forallP /(_ (Sub p Ip)) /exists_inP [s sS in_p]. 
    by exists s.
  - apply/forall_inP => b bB. apply/forallP => [[p ?]]. apply/exists_inP. 
    case: (H a b p) => // s S1 S2. by exists s.
Qed.

Lemma separator_cap A B S : separator A B S -> A :&: B \subset S.
Proof.
  move => sepS. apply/subsetP => x /setIP [xA xB]. 
  case: (sepS _ _ (idp x)) => // s in_S. by rewrite mem_idp => /eqP <-.
Qed.

Lemma separator_min A B S : separator A B S -> #|A :&: B| <= #|S|.
Proof. move/separator_cap. exact: subset_leq_card. Qed.

(** In order to define the notion of [AB]-connector, we need to
abstract from the incices in [Path x y] *)

Definition pathS := { x : G * G & Path x.1 x.2 }.
Definition PathS x y (p : Path x y) : pathS := existT (fun x : G * G => Path x.1 x.2) (x,y) p.

Definition in_pathS (p : pathS) : collective_pred G := [pred x | x \in tagged p].
Canonical pathS_predType := Eval hnf in mkPredType (@in_pathS).
Arguments in_pathS _ /.

(** We can override fst because MathComp uses .1 *)
Definition fst (p : pathS) := (tag p).1.
Definition lst (p : pathS) := (tag p).2.
Arguments fst _ /.
Arguments lst _ /.

Lemma pathS_eta (p : pathS) : 
  p = @PathS (fst p) (lst p) (tagged p).
Proof. by case: p => [[x y] ri]. Qed.

Lemma fst_mem (p : pathS) : fst p \in p.
Proof. case: p => [[x y] p] /=. exact: path_begin. Qed.

Lemma lst_mem (p : pathS) : lst p \in p.
Proof. case: p => [[x y] p] /=. exact: path_end. Qed.

(** TOTHINK: [conn_disjoint] could also be expressed as [x \in p i -> x \in p j ->  i = j] *)
(** NOTE: Unlike the definition of Göring, we do not allow single edge paths inside [A :&: B] *)
Record connector (A B : {set G}) n (p : 'I_n -> pathS) : Prop := 
  { conn_irred    : forall i, irred (tagged (p i)); 
    conn_begin    : forall i, [set x in p i] :&: A = [set fst (p i)];
    conn_end      : forall i, [set x in p i] :&: B = [set lst (p i)];
    conn_disjoint :  forall i j, i != j -> [set x in p i] :&: [set x in p j] = set0 }.

Section ConnectorTheory.
Variables (A B : {set G}) (n : nat) (p : 'I_n -> pathS).
Hypothesis conn_p : connector A B p.

Lemma connector_fst i : fst (p i) \in A.
Proof. 
  move/setP : (conn_begin conn_p i) => /(_ (fst (p i))). 
  rewrite !inE eqxx. by case/andP.
Qed.

Lemma connector_lst i : lst (p i) \in B.
Proof. 
  move/setP : (conn_end conn_p i) => /(_ (lst (p i))). 
  rewrite !inE eqxx. by case/andP.
Qed.

Lemma connector_left i x : x \in p i -> x \in A -> x = fst (p i).
Proof.
  move => in_pi in_A. move/setP : (conn_begin conn_p i) => /(_ x). 
  rewrite !inE in_pi in_A /=. by move/esym/eqP.
Qed.

Lemma connector_right i x : x \in p i -> x \in B -> x = lst (p i).
Proof.
  move => in_pi in_B. move/setP : (conn_end conn_p i) => /(_ x). 
  rewrite !inE in_pi in_B /=. by move/esym/eqP.
Qed.

Lemma lst_idp i : lst (p i) \in A -> lst (p i) = fst (p i).
Proof.
  move => H. move/setP : (conn_begin conn_p i) => /(_ (lst (p i))).
  rewrite !inE H. by move/esym/eqP. 
Qed.

Lemma fst_idp i : fst (p i) \in B -> fst (p i) = lst (p i).
Proof.
  move => H. move/setP : (conn_end conn_p i) => /(_ (fst (p i))).
  rewrite !inE H. by move/esym/eqP. 
Qed.

Lemma connector_eq i j x : x \in p i -> x \in p j -> i = j.
Proof. 
  move => Hi Hj. apply: contraTeq isT => /(conn_disjoint conn_p)/setP/(_ x).
  by rewrite !inE Hi Hj.
Qed.

Lemma fst_lst_eq i j : fst (p i) = lst (p j) -> i = j.
Proof.
  move => E. apply: (connector_eq (x := fst (p i))); first exact: fst_mem.
  by rewrite E lst_mem.
Qed.

Lemma fst_inj : injective (fst \o p).
Proof. 
  apply/injectiveP. 
  apply: wlog_neg => /injectivePn [i] [j] /(conn_disjoint conn_p)/setP S /= H.
  move/(_ (fst (p i))) : S. by rewrite !inE /fst H fst_mem.
Qed.

Lemma lst_inj : injective (lst \o p).
Proof. 
  apply/injectiveP. 
  apply: wlog_neg => /injectivePn [i] [j] /(conn_disjoint conn_p)/setP S /= H.
  move/(_ (lst (p i))) : S. by rewrite !inE /lst H lst_mem. 
Qed.

End ConnectorTheory.

(** Concatenation on [pathS] *)

Definition castL (x' x y : G) (E : x = x') (p : Path x y) : Path x' y :=
  match E in (_ = y0) return (Path y0 y) with erefl => p end.

Definition pcatS (p1 p2 : pathS) : pathS :=
  let: (existT x p,existT y q) := (p1,p2) in
  match altP (y.1 =P x.2) with
    AltTrue E => PathS (pcat p (castL E q))
  | AltFalse _ => PathS p
  end.

Lemma pcatSE (x y z : G) (p : Path x y) (q : Path y z) : 
  pcatS (PathS p) (PathS q) = PathS (pcat p q).
Proof. 
  rewrite /pcatS /=. case: {-}_ /altP => [E|]; last by rewrite eqxx.
  rewrite /castL. by rewrite (eq_irrelevance E erefl).
Qed.


Lemma edgeLP x y z (xy : x -- y) (p : Path y z) u : 
  reflect (u = x \/ u \in p) (u \in pcat (edgep xy) p).
Proof. 
  rewrite !inE mem_edgep -orbA. apply: (iffP or3P) => [|[->|->]]; rewrite ?eqxx. 
  1: case => [/eqP->|/eqP->|->]; rewrite ?inE. all: by firstorder.
Qed.

Lemma connector_extend A B n (p : 'I_n -> pathS) x y i : 
  x \notin \bigcup_i [set z in p i] -> fst (p i) = y -> x -- y -> x \notin B ->
  connector A B p -> exists q : 'I_n -> pathS, connector (x |: (A :\ y)) B q.
Proof.
  move => Hx Hy xy xB conn_p.
  have xDy : x != y. 
  { apply: contraNneq Hx => ->. apply/bigcupP; exists i => //. by rewrite inE -Hy fst_mem. }
  set A' := _ |: _.
  pose q (j : 'I_n) := if j == i then pcatS (PathS (edgep xy)) (p j) else p j. 
  have Hj (j : 'I_n) u : j != i -> u \in tagged (p j) -> (u == y = false)*(u == x = false).
  { move => jDi u_pi. split. 
    - apply: contra_eqF (conn_disjoint conn_p jDi) => /eqP ?; subst.
      apply/set0Pn; exists (fst (p i)). by rewrite !inE u_pi.
    - apply: contraNF Hx => /eqP <-. apply/bigcupP; exists j => //. by rewrite inE. }
  exists q. split.
  - move => j. rewrite /q /=. 
    case: (altP (j =P i)) => [E|D]; last exact: (conn_irred conn_p).
    subst j. rewrite [p i]pathS_eta. subst y. rewrite pcatSE /= irred_edgeL.
    rewrite (conn_irred conn_p) andbT. apply: contraNN Hx => Hx.
    apply/bigcupP. exists i => //. by rewrite inE.
  - move => j. rewrite /q. case: (altP (j =P i)) => [E|D].
    + subst j. rewrite [p i]pathS_eta. subst y. rewrite pcatSE /=.
      apply/setP => u. rewrite [A']lock !inE -lock. apply/andP/idP.
      * rewrite !inE mem_edgep /=. case: (altP (u =P x)) => [-> //|/=].
        rewrite -/(fst (p i)). case: (altP (u =P fst (p i))) => [_ _ [_ ?] //|].
        rewrite /= -/(fst (p i)) => [H1 H2 [H3 H4]].
        by rewrite -(connector_left conn_p _ H4) ?eqxx in H1.
      * move/eqP->. by rewrite mem_edgep /= !inE eqxx.
    + rewrite -(conn_begin conn_p). 
      apply/setP => u. rewrite !inE. case e: (u \in _) => //=. by rewrite !(Hj j) /=.
  - move => j.  rewrite /q. case: (altP (j =P i)) => [E|D]; last exact: (conn_end conn_p). 
    subst j. rewrite [p i]pathS_eta. subst y. rewrite pcatSE /= -/(lst _).
    apply/setP => u. rewrite -(conn_end conn_p i) !inE -mem_pcat. case uB : (u \in B) => //.
    rewrite !andbT. apply/edgeLP/idP => /=; last by right. case => [?|//]. 
    subst. by rewrite uB in xB. 
  - move => j1 j2. rewrite /q. 
    have jP j : i != j -> [set x0 in pcatS (PathS (edgep xy)) (p i)] :&: [set x0 in p j] = set0.
    { move => jDi. rewrite [p i]pathS_eta. subst y. rewrite pcatSE. 
      apply: contra_eq (conn_disjoint conn_p jDi). case/set0Pn => u /setIP []. 
      rewrite 2!inE /=. case/edgeLP => /= [-> Hx'|Hu ?]. 
      * apply: contraNN Hx => _. apply/bigcupP; exists j => //. by rewrite inE.
      * apply/set0Pn. exists u. by rewrite !inE Hu. }
    case: (altP (j1 =P i)); case: (altP (j2 =P i)). 
    + move => -> -> . by rewrite eqxx.
    + rewrite eq_sym => Hj2 ->. exact: jP.
    + rewrite eq_sym setIC. move => -> Hj2 _. exact: jP.
    + move => _ _. exact: (conn_disjoint conn_p).
Qed.

Lemma connector_sep P A B n (p q : 'I_n -> pathS) i j x : 
  separator A B P -> connector A P p -> connector P B q -> 
  x \in p i -> x \in q j -> (x \in P) (* * (lst (p i) = fst (q j)) *).
Proof.
  move => sep_P con_p con_q x_pi x_qj. 
  case def_pi : (p i) => [[u v] /= pi]. 
  case def_qj : (q j) => [[u' v'] /= qj]. rewrite -!/(PathS _) in def_pi def_qj.
  have [x_pi' x_qj'] : x \in pi /\ x \in qj by rewrite def_pi def_qj in x_pi x_qj.
  have Ip : irred pi. { move: (conn_irred con_p i). by rewrite def_pi. }
  have Iq : irred qj. { move: (conn_irred con_q j). by rewrite def_qj. }
  case/(isplitP Ip) def_p : _ / x_pi' => {Ip} [p1 p2 Ip1 Ip2 Ip].
  case/(isplitP Iq) def_q : _ / x_qj' => {Iq} [q1 q2 Iq1 Iq2 Iq].
  case: (sep_P _ _ (pcat p1 q2)).
  - move: (connector_fst con_p i). by rewrite def_pi.
  - move: (connector_lst con_q j). by rewrite def_qj.
  - move => s in_P. rewrite inE. case/orP => [in_p1|in_q2].
    + suff ? : s = v by subst s; rewrite [v]Ip // inE in in_P.
      rewrite [s](connector_right con_p (i := i)) // def_pi //. 
      change (s \in pi). by rewrite def_p inE in_p1.
    + suff ? : s = u' by subst s; rewrite [u']Iq // inE in in_P.
      rewrite [s](connector_left con_q (i := j)) // def_qj //. 
      change (s \in qj). by rewrite def_q inE in_q2.
Qed.

Lemma connector_cat (P A B : {set G}) n (p q : 'I_n -> pathS) : 
  #|P| = n -> separator A B P ->
  connector A P p -> connector P B q -> 
  exists (r : 'I_n -> pathS), connector A B r.
Proof.
  move => card_P. subst n. move => sep_P con_p con_q. 
  (** For every [i], we can obtain some [j] such that [p i] and [q j] compose. *)
  have mtch i : { j | fst (q j) = lst (p i) }.
  { pose x := lst (p i).
    have Hx : x \in codom (fst \o q). 
    { apply: (inj_card_onto_pred (P := mem P)). 
      - exact: fst_inj con_q.
      - move => j. exact: connector_fst con_q _.
      - by rewrite card_ord.
      - exact: connector_lst con_p _. }
    exists (iinv Hx). rewrite -[fst _]/((fst \o q) (iinv Hx)). by rewrite f_iinv. }
  have mtch_inj : injective (fun i => sval (mtch i)).
  { move => i i' E. move: (svalP (mtch i')). rewrite -E (svalP (mtch i)).
    exact : (lst_inj con_p). }
  (** Compose matching paths *)
  pose pq i := pcatS (p i) (q (sval (mtch i))).
  (** Elimination lemma for pq to encapsulate dependent types reasoning *)
  have pqE i : exists j x y z (pi : Path x y) (qi : Path y z), 
      [/\ p i = PathS pi, j = sval (mtch i), q j = PathS qi & pq i = PathS (pcat pi qi) ].
  { pose j := sval (mtch i). 
    have jP := svalP (mtch i) : fst (q j) = lst (p i). 
    exists j. exists (fst (p i)). exists (lst (p i)). exists (lst (q j)). 
    exists (tagged (p i)). exists (castL jP (tagged (q j))). split => //.
    - by rewrite {1}[p i]pathS_eta. 
    - rewrite {1}[q j]pathS_eta. move: (jP). rewrite -jP => jP'.
      by rewrite (eq_irrelevance jP' erefl).
    - rewrite /pq -/j. rewrite -pcatSE -pathS_eta. move: (jP). rewrite -jP => jP'.
      by rewrite (eq_irrelevance jP' erefl) /= -pathS_eta. }
  have sepP i j x : x \in p i -> x \in q j -> x \in P.
  { exact: connector_sep sep_P con_p con_q. }
  exists pq. split. 
  - move => i. move: (pqE i) => [j] [x] [y] [z] [pi] [qj] [Ep Ej Eq ->] /=. 
    apply: irred_catI => [u u_p u_q||]. 
    + have uP : u \in P. apply: (sepP i j u); rewrite ?Ep ?Eq //.
      move: (conn_end con_p i) => /setP/(_ u). rewrite Ep !inE /= u_p uP /=. 
      by move/esym/eqP.
    + move: (conn_irred con_p i). by rewrite Ep.
    + move: (conn_irred con_q j). by rewrite Eq.
  - move => i. move: (pqE i) => [j] [x] [y] [z] [pi] [qj] [Ep Ej Eq ->] /=.
    apply/setP => u. rewrite !inE /=. apply/andP/eqP => [[/orP[u_pi|u_qj] uA]|->].
    + move/(_ i u): (connector_left con_p). rewrite Ep /= u_pi uA. by apply.
    + suff ? : u = y. 
      { subst. suff: lst (p i) = fst (p i) by rewrite Ep. 
        apply: (lst_idp con_p _). by rewrite !Ep. }
      (* y is the only element of P in qj, so if [u != y], the uz-path avoids P *) 
      have Iq : irred qj. move: (conn_irred con_q j). by rewrite Eq.
      case/(isplitP Iq) def_q : _ / u_qj => [q1 q2 _ _ I].
      have zB : z \in B. { move: (connector_lst con_q j). by rewrite Eq. } 
      case: (sep_P _ _ q2) => // s sP in_q2. 
      have ? : s = y. 
      { by rewrite [s](connector_left con_q (i := j)) // Eq // def_q mem_pcat in_q2. }
      subst s. by rewrite [y]I // inE. 
    + by rewrite inE [x](_ : _ = fst (p i)) ?(connector_fst con_p) // Ep. 
  - (* symmetric to the argument above *)
    move => i. move: (pqE i) => [j] [x] [y] [z] [pi] [qj] [Ep Ej Eq ->] /=.
    apply/setP => u. rewrite !inE /=. apply/andP/eqP => [[/orP[u_pi|u_qj] uB]|->].
    + have uz : u = y.
      { have Ip : irred pi. move: (conn_irred con_p i). by rewrite Ep.
        case/(isplitP Ip) def_p : _ / u_pi => [p1 p2 _ _ I].
        have xA : x \in A. { move: (connector_fst con_p i). by rewrite Ep. } 
        case: (sep_P _ _ p1) => // s sP in_p1. 
        have ? : s = y. 
        { by rewrite [s](connector_right con_p (i := i)) // Ep // def_p mem_pcat in_p1. }
        subst s. by rewrite [y]I // inE. }
      subst u. 
      suff: fst (q j) = lst (q j). by rewrite Eq. 
      apply: (fst_idp con_q _). by rewrite Eq. 
    + move/(_ j u): (connector_right con_q). rewrite Eq /= u_qj uB. by apply.
    + by rewrite inE [z](_ : _ = lst (q j)) ?(connector_lst con_q) // Eq.
  - move => i j iDj.
    move: (pqE i) => [i2] [x] [y] [z] [pi] [qi2] [Ep Ei Eq ->] /=. 
    move: (pqE j) => [j2] [x'] [y'] [z'] [pj] [qj2] [Ep' Ej Eq' ->] /=.
    apply/eqP. apply: wlog_neg. case/set0Pn => u. rewrite !inE => /andP[]. 
    case/orP => Hi; case/orP => Hj; case: notF.
    + move/setP/(_ u): (conn_disjoint con_p iDj). by rewrite Ep Ep' !inE Hi Hj.
    + have uP : u \in P. 
      { apply: (@connector_sep P A B _ p q i j2 u) => //; by rewrite ?Ep ?Eq'. }
      have [? ?] : y' = u /\ y = u.
      { split.
        - by rewrite {1}[u](connector_left con_q (i := j2)) ?Eq'. 
        - by rewrite {1}[u](connector_right con_p (i := i)) ?Ep. }
      subst y' y. apply: contraNT iDj => _. apply/eqP. apply: mtch_inj. 
      rewrite -Ei -Ej. apply: (connector_eq con_q (x := u)); by rewrite ?Eq ?Eq' inE.
    + have uP : u \in P. 
      { apply: (@connector_sep P A B _ p q j i2 u) => // ; by rewrite ?Ep' ?Eq. }
      have [? ?] : y' = u /\ y = u. 
      { split.
        - by rewrite {1}[u](connector_right con_p (i := j)) ?Ep'.
        - by rewrite {1}[u](connector_left con_q (i := i2)) ?Eq. }
      subst y' y. apply: contraNT iDj => _. apply/eqP. apply: mtch_inj. 
      rewrite -Ei -Ej. apply: (connector_eq con_q (x := u)); by rewrite ?Eq ?Eq' inE.
    + apply: contraNT iDj => _. apply/eqP. apply: mtch_inj. rewrite -Ei -Ej.
      apply: contraTeq isT => iDj.
      move/setP/(_ u): (conn_disjoint con_q iDj). by rewrite Eq Eq' !inE Hi Hj.
Qed.

Lemma trivial_connector A B : exists p : 'I_#|A :&: B| -> pathS, connector A B p.
Proof.
  exists (fun i => PathS (idp (enum_val i))). split.
  - move => i /=. exact: irred_idp.
  - move => i /=. case/setIP : (enum_valP i) => iA iB. apply/setP => z.
    rewrite !inE /= mem_idp. case e: (_ == _) => //. by rewrite (eqP e).
  - move => i /=. case/setIP : (enum_valP i) => iA iB. apply/setP => z.
    rewrite !inE /= mem_idp. case e: (_ == _) => //. by rewrite (eqP e).
  - move => i j. apply: contraNeq => /set0Pn [x /setIP[]]. 
    by rewrite !inE /= !mem_idp => /eqP-> /eqP /enum_val_inj->. 
Qed.

Lemma sub_connector A B n m (p : 'I_m -> pathS) : 
  n <= m -> connector A B p -> exists q : 'I_n -> pathS, connector A B q.
Proof.
  move => n_leq_m conn_p. pose W := widen_ord n_leq_m. exists (fun i => p (W i)).
  case: conn_p => C1 C2 C3 C4. split => // i j. exact:(C4 (W i) (W j)).
Qed.

End SeparatorConnector.

Lemma nat_size_ind (X : Type) (P : X -> Type) (x : X) (f : X -> nat) :
       (forall x : X, (forall y : X, f y < f x -> P y) -> P x) -> P x.
Proof. move => H. apply: nat_size_ind. exact: H. Qed.

Lemma subrel_pathp (T : finType) (e1 e2 : rel T) (x y : T) (p : seq T) :
  subrel e1 e2 -> @pathp (DiGraph e1) x y p -> @pathp (DiGraph e2) x y p.
Proof. 
  move => sub12. elim: p x => //= z p IHp x. rewrite !pathp_cons => /andP [A B].
  apply/andP;split; [exact: sub12 | exact: IHp].
Qed.

Arguments nat_size_ind [X] [P] [x] f.
Arguments separator : clear implicits.
Arguments separatorb : clear implicits.

Definition num_edges (G : diGraph) := #|[pred x : G * G | x.1 -- x.2]|.

Lemma subrelP (T : finType) (e1 e2 : rel T) : 
  reflect (subrel e1 e2) ([pred x | e1 x.1 x.2] \subset [pred x | e2 x.1 x.2]).
Proof. apply: (iffP subsetP) => [S x y /(S (x,y)) //|S [x y]]. exact: S. Qed.


Section DelEdge.

Variable (G : diGraph) (a b : G).

Definition del_rel a b := [rel x y : G | x -- y && ((x != a) || (y != b))].

Definition del_edge := DiGraph (del_rel a b).

Definition subrel_del_edge : subrel (del_rel a b) (@edge_rel G).
Proof. by move => x y /andP []. Qed.

Hypothesis ab : a -- b.

Lemma card_del_edge : num_edges del_edge < num_edges G.
Proof.
  apply: proper_card. apply/properP; split.
  - apply/subrelP. exact: subrel_del_edge. 
  - exists (a,b); by rewrite !inE //= /edge_rel /= !eqxx. 
Qed.

(** This is the fundamental case analysis for irredundant paths in [G] in
terms of paths in [del_edge a b] *)

(** TOTHINK: The proof below is a slighty messy induction on
[p]. Informally, one would simply check wether [nodes p] contains and
[a] followed by a [b] *)
Lemma del_edge_path_case (x y : G) (p : Path x y) (Ip : irred p) :
    (exists (p1 : @IPath del_edge x a) (p2 : @IPath del_edge b y), 
        [/\ nodes p = nodes p1 ++ nodes p2, a \notin p2 & b \notin p1])
  \/ (exists p1 : @IPath del_edge x y, nodes p = nodes p1).
Proof.
  pattern x, y, p. apply irred_ind => //.
  - move => {p Ip}.  
    have Ip : irred (@idp del_edge y) by apply: irred_idp. by right;exists (Sub _ Ip).
  - move => {x p Ip} x z p xz Ip xp [[p1] [p2] [A B C]|[p1] E].
    + left. 
      have xyD : (x:del_edge) -- z. 
      { rewrite /edge_rel/= xz (_ : x != a) //. apply: contraNneq xp => -> .
        by rewrite mem_path A mem_cat -(@mem_path del_edge) path_end. }
      have Iq : irred (pcat (edgep xyD) p1). 
      { rewrite irred_edgeL (valP p1) andbT. 
        rewrite mem_path A mem_cat -(@mem_path del_edge) negb_or in xp.
        by case/andP : xp. }
      exists (Sub _ Iq). exists p2. split => //. 
      * by rewrite /= !nodes_pcat A [nodes p1](nodesE) /= -catA. 
      * change (b \notin pcat (edgep xyD) p1). 
        rewrite (@mem_pcat del_edge) (negbTE C) orbF mem_edgep negb_or.
        rewrite irred_edgeL in Iq. apply/andP; split.
        -- apply: contraNneq xp => <-. 
           by rewrite mem_path A mem_cat -!(@mem_path del_edge) path_begin.
        -- apply: contraTneq Ip => ?. subst z. 
           rewrite irredE A cat_uniq [has _ _](_ : _ = true) //. 
           apply/hasP. by exists b => /=; rewrite -!(@mem_path del_edge) path_begin.
    + case: (boolP ((x : del_edge) -- z)) => [xzD|xzND].
      * right. 
        have Iq : irred (pcat (edgep xzD) p1). 
        { by rewrite irred_edgeL (valP p1) mem_path -E -(@mem_path G) xp. }
        exists (Sub _ Iq). by rewrite !nodes_pcat E. 
      * left. rewrite /edge_rel/= xz /= negb_or !negbK in xzND. 
        case/andP : xzND => /eqP ? /eqP ?. subst x. subst z. 
        have Iq : irred (@idp del_edge a) by apply: irred_idp.
        exists (Sub _ Iq). exists p1. split => //=. 
        -- by rewrite nodes_pcat E [nodes p1]nodesE /= -cat1s catA !nodesE. 
        -- by rewrite (@mem_path del_edge) -E -(@mem_path G).
        -- rewrite (@mem_path del_edge) nodesE /= inE. 
           apply: contraNneq xp => <-. 
           by rewrite mem_path E -(@mem_path del_edge) path_begin.
Qed.

End DelEdge.

Lemma del_edge_lift_proof (G : diGraph) (a b x y : G) p : 
  @pathp (del_edge a b) x y p -> @pathp G x y p.
Proof. case: G a b x y p => T e a b x y p. apply: subrel_pathp. exact: subrel_del_edge. Qed.

Definition del_edge_liftS (G : diGraph) (a b : G) (p : pathS (del_edge a b)) :=
  let: existT (x,y) p' := p in PathS (Build_Path (del_edge_lift_proof (valP p'))).

Lemma mem_del_edge_liftS (G : diGraph) (a b : G) (p : pathS (del_edge a b))  x : 
  (x \in del_edge_liftS p) = (x \in p).
Proof. by case: p => [[u v] p]. Qed.

Lemma connector_nodes (T : finType) (e1 e2 : rel T) (A B : {set T}) : 
  forall s (p : 'I_s -> pathS (DiGraph e1)) (q : 'I_s -> pathS (DiGraph e2)), 
  (forall i, nodes (tagged (p i)) = nodes (tagged (q i)) :> seq T) -> 
  @connector (DiGraph e1) A B s p -> @connector (DiGraph e2) A B s q.
Proof.
  set G1 := DiGraph e1. set G2 := DiGraph e2.
  move => s p q Epq [C1 C2 C3 C4]. 
  have Spq : forall i, [set x in p i] = [set x in q i]. 
  { move => i. apply/setP => z. by rewrite !inE !mem_path Epq. }
  split.
  - move => i /=. rewrite irredE -Epq -(@irredE G1). exact: C1.
  - move => i /=. rewrite -Spq C2. f_equal. 
    move: (Epq i). case: (p i) => [[x y] pi]. case: (q i) => [[x' y'] qi].
    rewrite /fst /=. rewrite !nodesE. by case.
  - move => i /=. rewrite -Spq C3. f_equal. 
    move: (Epq i). case: (p i) => [[x y] pi]. case: (q i) => [[x' y'] qi].
    rewrite /lst /= in pi qi *. rewrite !nodesE => [[E1 E2]]. 
    by rewrite -(path_last pi) -(path_last qi) /= E2 E1.
  - move => i j /C4. by rewrite -!Spq.
Qed.
 
Lemma del_edge_connector (G : diGraph) (a b : G) (A B : {set G}) s (p : 'I_s -> pathS (del_edge a b)) : 
  @connector (del_edge a b) A B s p -> connector A B (fun i : 'I_s => del_edge_liftS (p i)).
Proof.
  destruct G. apply: connector_nodes => i. 
  case: (p i) => [[x y] pi] /=. by rewrite !nodesE. 
Qed.

Theorem Menger (G : diGraph) (A B : {set G}) s : 
  (forall S, separator G A B S -> s <= #|S|) -> exists (p : 'I_s -> pathS G), connector A B p.
Proof.
  move: s A B. pattern G. apply: (nat_size_ind num_edges) => {G}.
  move => G IH s A B min_s. 
  case: (boolP [exists x : G, exists y : G, x -- y]) => [E|E0]; last first.
  - suff Hs : s <= #|A :&: B|. 
    { case: (trivial_connector A B) => p. exact: sub_connector. }
    apply: min_s => a b p aA bB. 
    (* If a != b then p must have an edge, contradition - Lemma? *) 
    revert aA bB. pattern a,b,p. apply Path_ind. 
    + move => bA bB. exists b; by rewrite !inE ?bA.
    + move => x y ? xy. case: notF. apply: contraNT E0 => _. 
      apply/existsP;exists x. by apply/existsP; exists y. 
  - case/existsP : E => x /existsP [y xy].
    pose G' := del_edge x y.
    have HG' : num_edges G' < num_edges G by exact: card_del_edge. 
    move/(_ _ HG' s) in IH.
    case: (boolP [exists S : {set G'}, separatorb G' A B S && (#|S| < s)]); last first.
    { move/exists_inPn => Hs. case: (IH A B) => [S sepS|p conn_p].
      - rewrite leqNgt Hs //. exact/separatorP. 
      - exists (fun i : 'I_s => del_edge_liftS (p i)). exact: del_edge_connector. }
    case/exists_inP => S /separatorP sepS ltn_s. 
    pose P := x |: S.
    have xP : x \in P by rewrite /P; set_tac.
    pose Q := y |: S.
    have yQ : y \in Q by rewrite /Q; set_tac.
    have [sep_G_P sep_G_Q] : separator G A B P /\ separator G A B Q.
    { have Hp (a b : G) (p : Path a b) : 
        irred p -> a \in A -> b \in B -> (x \in p /\ y \in p) \/ exists2 s, s \in S & s \in p.
      { move => Ip aA bB. case: (del_edge_path_case x y Ip).
        - move => [p1] [p2] [H1 H2 H3]. left. 
          rewrite !mem_path H1 !mem_cat. by rewrite -!(@mem_path G') !inE.
        - move => [p1 Ep]. right. case/sepS : (p1) => // z Z1 Z2. exists z => //.
          by rewrite (@mem_path G) Ep -(@mem_path G'). }
      split; apply: separatorI => a b p Ip aA bB. 
      all: case: (Hp _ _ _ Ip aA bB) => [[xp yp]|[s0 in_S in_p]]. 
      all: solve [by exists x | by exists y | exists s0; rewrite /P /Q; set_tac]. }
    have lift_AP T : separator G' A P T -> separator G A B T.
    { move => sepT. apply/separatorI => a b p Ip aA bB. 
      case: (del_edge_path_case x y Ip).
      - move => [p1] [p2] [E Nx Ny]. case/sepT : (p1) => // t T1 T2.  
        exists t => //. by rewrite mem_path E mem_cat -(@mem_path G') T2.
      - case. case => p' Ip' /= E. case/sep_G_P : (p) => // z zP zp. 
        have zp' : z \in p' by rewrite (@mem_path G') -E -(@mem_path G).
        case: (split_at_first (D := G') zP zp') => u [p1] [p2] [E' uP ?].
        case/sepT : (p1) => // t tT tp1. exists t => //. 
        by rewrite mem_path E -(@mem_path G') E' mem_pcat tp1. }
    have lift_QB T : separator G' Q B T -> separator G A B T.
    { (* same as above -- generalize? *) 
      move => sepT. apply/separatorI => a b p Ip aA bB. 
      case/sep_G_Q : (p) => // z zP zp. case: (del_edge_path_case x y Ip).
      - move => [p1] [p2] [E Nx Ny]. case/sepT : (p2) => // t T1 T2.  
        exists t => //. by rewrite mem_path E mem_cat -(@mem_path G') T2.
      - case. case => p' Ip' /= E. 
        have zp' : z \in p' by rewrite (@mem_path G') -E -(@mem_path G). 
        case: (split_at_first (D := G') zP zp') => u [p1] [p2] [E' uP ?].
        case/sepT : (p2) => // t tT tp1. exists t => //. 
        by rewrite mem_path E -(@mem_path G') E' mem_pcat tp1. } 
    have size_AP T : separator G' A P T -> s <= #|T|. move/lift_AP. exact: min_s.
    have size_QB T : separator G' Q B T -> s <= #|T|. move/lift_QB. exact: min_s.
    have card_S u : separator G A B (u |: S) -> u \notin S /\ s = #|u |: S|.
    { move => HS. 
      have Hu : u \notin S. 
      { apply: contraTN ltn_s => uS. by rewrite -leqNgt min_s // -(setU1_mem uS). }
      split => //. apply: esym. apply/eqP. 
      by rewrite eqn_leq min_s // andbT cardsU1 Hu /= add1n. }
    case: (IH _ _ size_AP) => X (* /del_edge_connector *) conn_X.
    case: (IH _ _ size_QB) => Y (* /del_edge_connector *) conn_Y.
    have [i Hi] : exists j, lst (X j) = x. 
    { suff : x \in codom (fun j => lst (X j)) by case/mapP => j _ ->; exists j.
      apply: inj_card_onto_pred xP. 
      - exact: lst_inj conn_X.
      - exact: connector_lst conn_X.
      - rewrite card_ord. by apply card_S. }
    have xB : x \notin B. 
    { move: (connector_fst conn_X i) => HA. 
      move: (conn_end conn_X i). rewrite Hi => HP.
      case: (card_S _ sep_G_P) => xS _. apply: contraNN xS => xB. 
      have [u U1 U2] : exists2 u, u \in S & u \in X i. 
      { rewrite -Hi in xB. case: (X i) HA xB => [[a b] /= p]. exact: sepS. }
      move/setP/(_ u)/esym : HP. by rewrite !inE U1 U2 orbT /= => /eqP <-. }
    move/del_edge_connector : (conn_X) => conn_X'.
    move/del_edge_connector : (conn_Y) => conn_Y'.
    case: (altP (x =P y)) => [?|xDy]. 
    { subst y. apply: connector_cat conn_X' conn_Y' => //. by apply esym,card_S. } 
    have [j jP] : exists i : 'I_s, fst (Y i) = y :> G. 
    { suff : y \in codom (fun j => fst (Y j)) by case/mapP => j _ ->; exists j.
      apply: inj_card_onto_pred (_ : y \in Q). 
      - exact: fst_inj conn_Y.
      - exact: connector_fst conn_Y.
      - rewrite card_ord. by apply card_S. 
      - by rewrite !inE eqxx. }
    case: (connector_extend (G := G) (i := j) _ _ xy xB conn_Y') => //. 
    + move => {j jP}.
      apply/negP => /bigcupP [j] _. rewrite inE mem_del_edge_liftS => xYj. 
      (* have [i Hi] : exists i, lst (X i) = x. admit. *)
      case EYj : (Y j) => [[u v] /= p]. rewrite -/(PathS p) in EYj.
      have Ip : irred p. { move: (conn_irred conn_Y j). by rewrite EYj. }
      have xp : x \in p by rewrite EYj in xYj.
      case/(isplitP Ip) def_p : _ / xp => [p1 p2 Ip1 Ip2 I]. 
      case EXi : (X i) => [[a x'] /= q]. rewrite -/(PathS q) in EXi.
      have ? : x' = x by rewrite -Hi EXi. subst x'.
      case: (sepS a v (pcat q p2)) => [||t t_in_S].
      * move: (connector_fst conn_X i). by rewrite EXi.
      * move: (connector_lst conn_Y j). by rewrite EYj.
      * rewrite inE. case/orP => Ht.
        -- move: (t_in_S).  
           rewrite [t](connector_right conn_X (i := i)) ?EXi ?inE ?t_in_S /lst //=.
           apply/negP. by apply card_S.
        -- move: (t_in_S). apply/negP. rewrite [t]I //; first by apply card_S.
           rewrite [t](connector_left conn_Y (i := j)) ?inE ?t_in_S //.
           ++ rewrite EYj /fst /=. by rewrite (@path_begin G').
           ++ by rewrite EYj -[_ \in _]/(t \in p) def_p inE Ht.
    + by case: (Y j) jP => [[a b] p].
    + move => Y'. rewrite [_ |: _](_ : _ = P) => [conn_xY|].
      * apply: connector_cat conn_X' conn_xY => //. by apply esym,card_S.
      * apply/setP => u. rewrite /Q setU1K //. by apply card_S.
Qed.


Section Separators.
Variable (G : diGraph).
Implicit Types (x y z u v : G) (S U V : {set G}).

Definition separates x y U := [/\ x \notin U, y \notin U & forall p : Path x y, exists2 z, z \in p & z \in U].

(** Standard trick to show decidability: quantify only over irredundant paths *)
Definition separatesb x y U := [&& x \notin U, y \notin U & [forall p : IPath x y, exists z in p, z \in U]].

Lemma separatesI x y (U : {set G}) :
  [/\ x \notin U, y \notin U & forall p : Path x y, irred p -> exists2 z, z \in p & z \in U] -> separates x y U.
Proof.
  case => S1 S2 S3. split => // p.
  case: (uncycle p) => p' sub_p Ip'. 
  case: (S3 _ Ip') => z Z1 Z2. exists z => //. exact: sub_p.
Qed.

Lemma separatesP x y U : reflect (separates x y U) (separatesb x y U).
Proof. 
  apply: (iffP and3P) => [[? ? A]|[? ? A]].
  - apply: separatesI. split => // p Ip.
    move/forallP/(_ (Build_IPath Ip)) : A. 
    case/exists_inP => z Z1 Z2. by exists z. 
  - split => //. apply/forallP => p. by move/exists_inP : (A p). 
Qed.
Arguments separatesP [x y U].

Fact separatesNeq x y U : separates x y U -> x != y.
Proof. 
  case => Hx _ Hp. apply: contraNN Hx => /eqP C. subst y. case: (Hp (idp x)).
  move => ?. by rewrite mem_idp => /eqP->. 
Qed.


Fact separates0P x y : reflect (separates x y set0) (~~ connect edge_rel x y).
Proof.
  apply:(iffP idP) => [nconn_xy|]. 
  - rewrite /separates !inE. split => // p. by rewrite Path_connect in nconn_xy.
  - case => _ _ H. apply/negP. case/uPathP => p _. case: (H p) => z. by rewrite inE.
Qed.

End Separators.

Corollary theta (G : diGraph) (x y : G) s :
  ~~ x -- y -> x != y ->
  (forall S, separates x y S -> s <= #|S|) -> 
  exists p : 'I_s -> IPath x y, forall i j : 'I_s, i != j -> independent (p i) (p j).
Proof.
  move => xNy xDy min_s. 
  pose G' := path.induced (~: [set x;y]).
  pose A := [set z : G' | x -- val z].
  pose B := [set z : G' | val z -- y].
  (** Every AB-separator also separates x and y *)
  have sepAB S : separator G' A B S -> separates x y [set val x | x in S].
  { move => sepS. apply: separatesI; split.
    - apply/negP. case/imsetP => x' _ E. move: (valP x'). by rewrite !inE -E eqxx.
    - apply/negP. case/imsetP => y' _ E. move: (valP y'). by rewrite !inE -E eqxx orbT.
    - move => p Ip. case: (splitL p xDy) => a [xA] [p'] [Ep _].
      have aDy : (a != y) by apply: contraNneq xNy => <-. 
      case: (splitR p' aDy) => b [q] [By] Ep'. 
      have Hq : {subset q <= ~: [set x;y]}.
      { subst. rewrite irred_edgeL irred_edgeR mem_pcat_edgeR (negbTE xDy) /= in Ip.
        case/and3P : Ip => I1 I2 _ u. rewrite inE. 
        apply: contraTN. case/setU1P => [->//|]. by move/set1P->. }
      have [Ha Hb] : a \in ~: [set x;y] /\ b \in ~: [set x;y] by split; apply: Hq.
      case: (@path.Path_to_induced G (~: [set x;y]) (Sub a Ha) (Sub b Hb) q Hq) => q' Eq. 
      case: (sepS _ _ q'); rewrite ?inE // => s0 in_S in_q'.
      exists (val s0); last exact: mem_imset. subst. 
      by rewrite !inE [_ \in q]mem_path -Eq map_f. }
  have min_s' S : separator G' A B S -> s <= #|S|.
  { move => HS. 
    rewrite -[#|S|](_ : #|[set val x | x in S]| = _) ?min_s ?card_imset //. 
    + exact: sepAB.
    + exact: val_inj. }
  have [p conn_p] := Menger min_s'.
  have xA (i : 'I_s) : x -- val (fst (p i)).
  { move: (connector_fst conn_p i). by rewrite inE. } 
  have By (i : 'I_s) : val (lst (p i)) -- y.
  { move: (connector_lst conn_p i). by rewrite inE. } 
  have X (i : 'I_s) : { pi : @IPath G x y | [set x in pi] :\: [set x;y] = [set val x | x in p i] }.
  { case def_pi : (p i) => [[a b] /= pi]. rewrite -/(PathS pi) in def_pi *.
    case: (path.Path_from_induced pi) => pi' P1 P2. 
    have [? ?] : a = fst (p i) /\ b = lst (p i) by rewrite def_pi.
    subst. 
    set q := (pcat (edgep (xA i)) (pcat pi' (edgep (By i)))).
    have Iq : irred q. 
    { rewrite /q irred_edgeL irred_edgeR mem_pcat_edgeR negb_or xDy /=. apply/and3P;split.
      - apply/negP => /P1. by rewrite !inE eqxx.
      - apply/negP => /P1. by rewrite !inE eqxx orbT.
      - rewrite irredE P2 map_inj_uniq; last exact: val_inj. 
        move: (conn_irred conn_p i). by rewrite -(@irredE G') [in irred _]def_pi. }
    exists (Sub q Iq).
    apply/setP => u. apply/setDP/imsetP => [[U1 U2]|].
    - move: (U2) U1. rewrite 4!inE negb_or mem_pcat_edgeL mem_pcat_edgeR => /andP [/negbTE-> /negbTE->] /=.
      by rewrite mem_path P2 => /mapP. 
    - case => u' => U1' U2'. rewrite -in_setC U2' (valP u') !inE [_ \in pi'](_ : _ = true) //.
      rewrite mem_path P2 mem_map //. exact: val_inj. }
  exists (fun i => sval (X i)). 
  + move => i j iDj. apply/disjointP => u. rewrite /interior (svalP (X i)) (svalP (X j)).
    case/imsetP => u1 UP1 UE1. case/imsetP => u2 UP2 UE2. 
    have ? : u1 = u2 by apply: val_inj; congruence.
    subst u2. by rewrite [i](connector_eq conn_p UP1 UP2) eqxx in iDj.
Qed.

(** In addition to the independent paths, we also get a function proving a
default vertex on each path *)
Fact theta_vertices (G : diGraph) (x y : G) s (p : 'I_s -> IPath x y) :
  x != y -> ~~ x -- y ->
  exists (f : 'I_s -> G), forall i, f i \in interior (p i).
Proof.
  move => xDy xNy.
  suff S i : { s | s \in interior (p i) }. 
  { exists (fun i => val (S i)) => i. exact: (svalP (S i)). }
  case: (set_0Vmem (interior (p i))) => [I0|//].
  exfalso. case: (interior0E xDy (valP (p i)) I0) => xy.
  by rewrite xy in xNy.
Qed.


(** ** Arc Variant of Menger's Theorem *)

Corollary independent_walks (G : mGraph) (a b : G) n : 
  a != b -> (forall E, eseparates a b E -> n <= #|E|) -> 
  exists2 W : 'I_n -> seq (edge G), 
    forall i, walk a b (W i) & forall i j, i != j -> [disjoint W i & W j].
Proof.
  move => aDb min_sep.
  pose A := [set e : line_graph G | source e == a].
  pose B := [set e : line_graph G | target e == b].
  have sep E : separator _ A B E -> n <= #|E|.
  { move => sep_E. apply: min_sep => w walk_w. 
    have Nw : ~~ nilp w. { case: w walk_w => //=. by rewrite (negbTE aDb). }
    case: (line_of_walk walk_w Nw) => e1 [e2] [p] [P1 P2 P3].
    case: (sep_E _ _ p) => [||e in_E in_p]; rewrite ?inE ?P1 ?P2 //.
    exists e => //. by rewrite mem_path P3 in in_p. }
  case: (Menger sep) => X con_X. pose W i := nodes (tagged (X i)). exists W.
  - move => i. rewrite /W. 
    case: (X i) (connector_fst con_X i) (connector_lst con_X i) => [[e1 e2] /= p].
    rewrite /fst/lst/= !inE => /eqP<- /eqP <-. exact: walk_of_line.
  - move => i j iDj. apply/disjointP => e. rewrite /W -!(@mem_path (line_graph G)).
    move => in_i in_j. move/(_ i j e in_i in_j) : (connector_eq con_X) => E.
    by rewrite E eqxx in iDj.
Qed.

(** ** Hall's Marriage Theorem *)

(** Neighboorhoods and bipartitions are the same for digraphs and simple graphs *)

Definition N (G : diGraph) (A : {set G}) := 
  [set y in ~: A | [exists x in A, x -- y]].

Definition bipartition (G : diGraph) (A : {set G}) :=
  forall x y : G, x -- y -> (x \in A) = (y \notin A).

(** The (natural) notion of a matching on digraphs - a set of ordered
pairs - is not a resonable notion of matching on simple graphs, where
we should use unordered pairs. Hence, we have two separate definitions *)

Definition dimatching (G : diGraph) (M : {set G * G}) :=
    (forall e, e \in M -> e.1 -- e.2) 
  /\ {in M &, forall e1 e2 x, x \in [set e1.1;e1.2] -> x \in [set e2.1 ; e2.2] -> e1 = e2}.

Definition edges (G : sgraph) := [set [set x;y] | x in G, y in G & x -- y].

Lemma edgesP (G : sgraph) (e : {set G}) : 
  reflect (exists x y, e = [set x;y] /\ x -- y) (e \in edges G).
Proof.
  apply: (iffP imset2P) => [[x y]|[x] [y] [E xy]].
  - rewrite !inE /= => _ xy ->. by exists x; exists y.
  - exists x y => //. by rewrite inE.
Qed.

Definition matching (G : sgraph) (M : {set {set G}}) := 
  {subset M <= edges G} /\ 
  {in M&, forall (e1 e2 : {set G}) (x:G), x \in e1 -> x \in e2 -> e1 = e2}.

Lemma connectorC_edge (G : diGraph) (A : {set G}) n (p : 'I_n -> pathS G) i : 
  connector A (~: A) p -> 
  exists fl : fst (p i) -- lst (p i), p i = PathS (edgep fl).
Proof.
  move => conn_p. 
  case def_q : (p i) => [[a b] /= q]. rewrite -/(PathS q) in def_q *.
  case: (irred_is_edge q). 
  - move: (conn_irred conn_p i). by rewrite def_q.
  - case: (altP (a =P b)) => // ?; subst. 
    move: (connector_fst conn_p i) (connector_lst conn_p i). 
    by rewrite def_q !inE => ->.
  - move => z zq. rewrite !inE. case: (boolP (z \in A)) => [zA|zNA].
    + by rewrite [z](connector_left conn_p (i := i)) ?def_q // eqxx.
    + by rewrite {2}[z](connector_right conn_p (i := i)) ?def_q ?inE // eqxx.
  - move => ab ->. by exists ab.
Qed.

Definition dimatching_of (G : diGraph) n (p : 'I_n -> pathS G) := 
  [set (fst (p i),lst (p i)) | i : 'I_n].

Lemma connector_dimatching (G : diGraph) (A : {set G} ) n (p : 'I_n -> pathS G) :
  connector A (~:A) p -> dimatching (dimatching_of p).
Proof. 
  move => con_p. split.
  + move => e. case/imsetP => i _ -> /=. 
    by case: (connectorC_edge i con_p).
  + move => [a b] [a' b'] /imsetP [i _ [-> ->]] /imsetP [j _ [-> ->]] /= x /set2P [->|->]. 
    * case/set2P; by [move/(fst_inj con_p) -> | move/(fst_lst_eq con_p) ->]. 
    * case/set2P; by [move/(lst_inj con_p) -> | move/esym/(fst_lst_eq con_p) ->].
Qed.

Lemma card_dimatching_of (G : diGraph) A B n (p : 'I_n -> pathS G) :
  connector A B p -> #|dimatching_of p| = n.
Proof.
  move => con_p. rewrite /dimatching_of card_imset ?card_ord // => i j.
  case. by move/(fst_inj con_p).
Qed.

Definition matching_of (G : diGraph) (M' : {set G * G}) := 
  [set [set e.1;e.2] | e in M'].

Lemma matching_of_bimatching (G : sgraph) (A : {set G}) M : 
  dimatching M -> @matching G (matching_of M).
Proof.
  move => [M1 M2]. split.  
  - move => e. case/imsetP => x /M1 ? ?. apply/edgesP. by exists x.1; exists x.2. 
  - move => e1 e2 /imsetP [x X1 X2] /imsetP [y Y1 Y2] z. subst e1 e2.  
    move => Z1 Z2. by rewrite (M2 x y X1 Y1 z Z1 Z2).
Qed.

Lemma card_matching_of (G : diGraph) (M : {set G * G}) : 
  dimatching M -> #|matching_of M| = #|M|.
Proof.
  move => [? dim_M]. rewrite /matching_of card_in_imset //.
  move => e1 e2 /= inM1 inM2 E. apply dim_M with e1.1 => //.
  all: by rewrite -?E !inE eqxx.
Qed. 
    
Theorem diHall (G : diGraph) A : 
  bipartition A -> (forall S : {set G}, S \subset A -> #|S| <= #|N S|) -> 
  exists M, dimatching M /\ A = [set x.1 | x in M].
Proof.
  move => bip_A N_A. 
  have sep_A S : separator G A (~:A) S -> #|A| <= #|S|.
  { move => sep_S. rewrite -[#|A|](cardsID S). 
    apply: (@leq_trans (#|A :&: S| + #|N (A :\: S)|)).
    - by rewrite leq_add2l N_A // subsetDl.
    - rewrite -cardsUI [X in _ + X]eq_card0 ?addn0.
      + apply: subset_leq_card. rewrite subUset subsetIr.
        apply/subsetP => z. rewrite !inE negb_and negbK. case: (boolP (z \in S)) => //=.
        move => zS /andP [zA /exists_inP [x /setDP [xA xS] xz]]. 
        move: (sep_S _ _ (edgep xz)). rewrite xA inE zA. case => // s sS. 
        rewrite mem_edgep => /orP[]/eqP ?; subst; by contrab. 
      + move => z. rewrite !inE. case: (boolP (z \in A)) => //=. 
        apply: contraTF => /and3P[_ _ /exists_inP [x /setDP [xA xS] xz]]. 
        by rewrite -(bip_A _ _ xz). }
  case: (Menger sep_A) => p con_p. clear sep_A bip_A.
  exists (dimatching_of p). split; first exact: connector_dimatching con_p.
  apply/setP => a. apply/idP/imsetP => [inA|[x]].
  + move: (inj_card_onto_pred (f := fun i => fst (p i)) (P := (mem A))) => /=.
    case/(_ _ _ _ _ inA)/Wrap => //. 
    * apply: fst_inj con_p. 
    * apply: connector_fst con_p.
    * by rewrite card_ord.
    * case/mapP => i _ ->. exists (fst (p i),lst (p i)) => //. by rewrite mem_imset.
  + case/imsetP => i _ -> /= ->. apply: connector_fst. exact: con_p.
Qed.

Theorem Hall (G : sgraph) A : 
  bipartition A -> (forall S : {set G}, S \subset A -> #|S| <= #|N S|) -> 
  exists M, matching M /\ A \subset cover M.
Proof.
  move => bip_A N_A. case: (@diHall G A) => [//|//|M' [M1 M2]].
  - case: M1 => M1 M1'. exists (matching_of M'). 
    split; first exact: matching_of_bimatching.
    rewrite M2. apply/subsetP => a. case/imsetP => e E1 E2. apply/bigcupP. 
    exists [set e.1; e.2]; last by rewrite E2 !inE eqxx. exact: mem_imset.
Qed.

(** ** König's Theorem *)

Section vcover.
Variables (G : sgraph) (V :{set G}).

Definition vcover := [forall x, forall (y | x -- y), (x \in V) || (y \in V)].

Lemma vcoverP : reflect (forall x y, x -- y -> (x \in V) \/ (y \in V)) vcover.
Proof. 
  apply: (equivP idP).
  rewrite /vcover -(rwP forallP).
  setoid_rewrite <- (rwP forall_inP).
  by setoid_rewrite <- (rwP orP).
Qed.

(** The [x0] is needed to ensure that [G] is inhabited. 
    Otherwise, [{set G} -> G] is empty as well. *)
Lemma matching_cover_map (x0 : G) M :
  matching M -> vcover -> 
  exists2 f : {set G} -> G, (forall e : {set G}, e \in M -> f e \in V :&: e) & {in M&, injective f}.
Proof.
  move => [M1 M2] cover_V.
  pose f (A : {set G}) := if [pick x | x \in V :&: A] is Some x then x else x0.
  have fP e : e \in M -> f e \in V :&: e.
  { move/M1. case/edgesP => x [y] [E xy]. 
    rewrite /f. case: pickP => [//|]. 
    case/(vcoverP cover_V) : xy => xV; 
    [move/(_ x)|move/(_ y)]; by rewrite E !inE xV eqxx ?orbT. }
  exists f => // e1 e2 eM1 eM2. 
  move: (eM1) (eM2) => /fP [/setIP [V1 E1]] /fP [/setIP [V2 E2]] E.
  apply M2 with (f e1) => //. by rewrite E.
Qed.

Lemma cover_matching (M :{set {set G}}) : 
  matching M -> vcover -> #|M| <= #|V|.
Proof.
  move => [M1 M2] cover_V.
  wlog [x0] : / inhabited G.
  { move => W. case: (set_0Vmem M) => [->|[e /M1]]; first by rewrite cards0.
    case/edgesP => x _. exact: W. }
  case: (matching_cover_map x0 (conj M1 M2) cover_V) => f F1 F2.
  have f_V e : e \in M -> f e \in V by move/F1 => /setIP[].
  rewrite -(card_in_image F2). apply: subset_leq_card.
  apply/subsetP => y /mapP [x Hx ->]. apply: f_V. by rewrite mem_enum in Hx.
Qed.

Proposition min_max_cover (M : {set {set G}}) :  
  vcover -> matching M -> #|M| = #|V| -> V \subset cover M.
Proof.
  move => cov_V match_V MV. 
  wlog [x0] : / inhabited G.
  { move => W. case: (set_0Vmem V) => [-> //|[x _]]; first by rewrite sub0set.
    exact: W. }
  case: (matching_cover_map x0 match_V cov_V) => f F1 F2.
  pose f' (e : { e | e \in M}) := f (val e).
  have inj_f' : injective f'. 
  { case => e1 M1. case => e2 M2. rewrite /f' /= => E. 
    apply/eqP. change (e1 == e2). by rewrite (F2 _ _ M1 M2 E). }
  move: (inj_card_onto_pred (P := (mem V)) inj_f') => /=. case/(_ _ _)/Wrap.
  - case => e inM. by case/setIP : (F1 _ inM).
  - by rewrite card_sig. 
  - move => X. apply/subsetP => v vV. case/mapP : (X _ vV) => /= [[e inM] _ E].
    apply/bigcupP. exists e => //. rewrite E /f' /=. by case/setIP : (F1 _ inM).
Qed. 

End vcover.
Prenex Implicits vcover.

Lemma bip_separation_vcover (G : sgraph) (A S : {set G}) : 
  bipartition A -> separator G A (~: A) S -> vcover S.
Proof.
  move => bip_A sep_S. apply/vcoverP => x y xy.
  wlog/andP [xA yNA] : x y xy / (x \in A) && (y \notin A). 
  { move: (bip_A x y xy). case: (boolP (y \in A)) => /= yA xA; last by apply.
    rewrite or_comm. apply; by rewrite 1?sgP ?xA ?yA. }
  move: (sep_S _ _ (edgep xy)). rewrite xA inE yNA. case => // s sS. 
  rewrite mem_edgep => /orP [/eqP<-|/eqP<-]; by tauto.
Qed.

(* TODO: use [smallest] / [largest] *)
Lemma min_vcover_matching (G : sgraph) (A V : {set G}) : 
  bipartition A -> vcover V -> (forall V' : {set G}, vcover V' -> #|V| <= #|V'|) ->
  exists2 M, @matching G M & #|V| = #|M|.
Proof.
  move => bip_A cover_V min_V. 
  have sep_A S : separator G A (~:A) S -> #|V| <= #|S|.
  { move/bip_separation_vcover => /(_ bip_A). exact: min_V. }
  case: (Menger sep_A) => p conn_p. 
  move/connector_dimatching : (conn_p) => dim_M.
  exists (matching_of (dimatching_of p)). exact: matching_of_bimatching.
  by rewrite card_matching_of // (card_dimatching_of conn_p).
Qed.

Theorem Konig (G : sgraph) (A V : {set G}) (M : {set {set G}}) : 
  bipartition A -> 
  vcover V -> (forall V' : {set G}, vcover V' -> #|V| <= #|V'|) ->
  matching M -> (forall M' : {set {set G}}, matching M -> #|M'| <= #|M|) ->
  #|V| = #|M|.
Proof.
  move => bip_A cov_V min_V match_M max_M. apply/eqP.
  rewrite eqn_leq cover_matching // andbT.
  case: (min_vcover_matching bip_A cov_V min_V) => M' H ->. exact: max_M.
Qed.

