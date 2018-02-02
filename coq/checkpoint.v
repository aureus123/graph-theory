From mathcomp Require Import all_ssreflect.
Require Import edone finite_quotient preliminaries sgraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope quotient_scope.
Set Bullet Behavior "Strict Subproofs". 

(** * Checkpoints *)

Section CheckPoints.
  Variables (G : sgraph).
  Implicit Types (x y z : G) (U : {set G}).

  Let avoids z x y (p : seq G) := upath x y p && (z \notin x::p).
  Definition avoidable z x y := [exists n : 'I_#|G|, exists p : n.-tuple G, avoids z x y p].

  Definition cp x y := locked [set z | ~~ avoidable z x y].

  Lemma cpPn {z x y} : reflect (exists2 p, upath x y p & z \notin x::p) (z \notin cp x y).
  Proof.
    rewrite /cp -lock inE negbK. apply: (iffP existsP) => [[n] /exists_inP|[p]].
    - case => p ? ?. by exists p.
    - case/andP => U S I.
      have size_p : size p < #|G|.
      { by rewrite -[(size p).+1]/(size (x::p)) -(card_uniqP U) max_card. }
      exists (Ordinal size_p). by apply/exists_inP; exists (in_tuple p).
  Qed.

  Lemma cpNI z x y p : spath x y p -> z \notin x::p -> z \notin cp x y.
  Proof.
    case/andP. case/shortenP => p' ? ? sub_p ? E. apply/cpPn. exists p' => //.
    apply: contraNN E. rewrite !inE. case: (_ == _) => //=. exact: sub_p.
  Qed.
  
  Definition checkpoint x y z := forall p, spath x y p -> z \in x :: p.

  Lemma cpP {x y z} : reflect (checkpoint x y z) (z \in cp x y).
  Proof.
    apply: introP.
    - move => H p pth_p. apply: contraTT H. exact: cpNI.
    - case/cpPn => p /upathW pth_p mem_p /(_ p pth_p). by rewrite (negbTE mem_p).
  Qed.

  (** wrapped versions of the checkpoint/path lemmas *)
  
  Lemma cpP' x y z : reflect (forall p : Path x y, z \in p) (z \in cp x y).
  Proof. 
    apply: (iffP cpP) => [H p|H p Hp]. 
    + rewrite in_collective nodesE. apply: H. exact: valP. 
    + move: (H (Sub p Hp)). by rewrite in_collective nodesE. 
  Qed.
  Arguments cpP' [x y z].

  Lemma cpPn' x y z : reflect (exists2 p : Path x y, irred p & z \notin p) (z \notin cp x y).
  Proof. 
    apply: (iffP cpPn) => [[p /andP [I Hp] N]|[p U N]]. 
    + exists (Sub p Hp); by rewrite /irred ?in_collective nodesE. 
    + rewrite /irred ?in_collective nodesE in U N.
      exists (val p) => //. apply/andP. split => //. exact: valP. 
  Qed.

  Lemma cpNI' x y (p : Path x y) z : z \notin p -> z \notin cp x y.
  Proof. by apply: contraNN => /cpP'. Qed.

  Hypothesis G_conn' : connected [set: G].
  Let G_conn : forall x y:G, connect sedge x y.
  Proof. exact: connectedTE. Qed.

  Lemma cp_sym x y : cp x y = cp y x.
  Proof.
    wlog suff S : x y / cp x y \subset cp y x. 
    { apply/eqP. by rewrite eqEsubset !S. }
    apply/subsetP => z /cpP H. apply/cpP => p p_pth. 
    rewrite (srev_nodes p_pth). apply: H. exact: spath_rev.
  Qed.

  Lemma mem_cpl x y : x \in cp x y.
  Proof. apply/cpP => p. by rewrite mem_head. Qed.

  Lemma subcp x y : [set x;y] \subset cp x y.
  Proof. by rewrite subUset !sub1set {2}cp_sym !mem_cpl. Qed.

  Lemma cpxx x : cp x x = [set x].
  Proof. 
    apply/setP => z; rewrite !inE. 
    apply/idP/idP; last by move/eqP ->; rewrite mem_cpl.
    move/cpP/(_ [::] (spathxx _)). by rewrite inE.
  Qed.

  Lemma cp_triangle z {x y} : cp x y \subset cp x z :|: cp z y.
  Proof.
    apply/subsetP => u /cpP' => A. apply: contraT. 
    rewrite !inE negb_or => /andP[/cpPn' [p1 _ up1]] /cpPn' [p2 _ up2]. 
    move: (A (pcat p1 p2)). by rewrite mem_pcat (negbTE up1) (negbTE up2).
  Qed.
  
  Lemma cpN_trans a x z y : a \notin cp x z -> a \notin cp z y -> a \notin cp x y.
  Proof. 
    move => /negbTE A /negbTE B. apply/negP. move/(subsetP (cp_triangle z)). 
    by rewrite !inE A B.
  Qed.

  Lemma cp_mid (z x y t : G) : t != z -> z \in cp x y ->
   exists (p1 : Path z x) (p2 : Path z y), t \notin p1 \/ t \notin p2.
  Proof. 
    move => tNz cp_z.
    case/uPathP : (G_conn x y) => p irr_p.
    move/cpP'/(_ p) : cp_z. case/(isplitP irr_p) => p1 p2 A B C.
    exists (prev p1). exists p2. rewrite mem_prev. apply/orP. 
    case E : (t \in p1) => //=. 
    by rewrite mem_path !inE (negbTE tNz) (disjointFr C E).
  Qed.

  Lemma cp_widenR (x y u v : G) :
    u \in cp x y -> v \in cp x u -> v \in cp x y.
  Abort.

  Lemma cp_widen (i o x y z : G) :
    x \in cp i o -> y \in cp i o -> z \in cp x y -> z \in cp i o.
  Proof.
    move=> x_cpio y_cpio z_cpxy.
    apply/cpPn'=> -[p] Ip; apply/negP; rewrite negbK.
    move: x_cpio y_cpio => /cpP'/(_ p) x_p /cpP'/(_ p) y_p.
    wlog : x y z_cpxy p Ip x_p y_p / x <[p] y.
    { move=> Hyp. case: (ltngtP (idx p x) (idx p y)); first exact: Hyp.
      - by apply: Hyp; first rewrite cp_sym.
      - move=>/(idx_inj x_p) x_y.
        by move: z_cpxy; rewrite -{1}x_y cpxx inE =>/eqP->. }
    case/(three_way_split Ip x_p y_p) => [p1][p2][p3][-> _ _].
    rewrite !mem_pcat. by move: z_cpxy => /cpP'/(_ p2)->.
  Qed.

  Lemma cp_tightenR (x y z u : G) : z \in cp x y -> x \in cp u y -> x \in cp u z.
  Proof.
    move=> z_cpxy x_cpuy. apply/cpP' => pi.
    case/uPathP: (G_conn z y) => pi_o irred_o.
    move/cpP'/(_ (pcat pi pi_o)): x_cpuy.
    rewrite mem_pcatT => /orP[//|x_tail]; exfalso.
    case: (altP (z =P y)). (* TODO: worth a lemma *)
    { move=> eq_z; move: pi_o irred_o x_tail.
      by rewrite -eq_z => pi_o /irredxx->. }
    case/(splitL pi_o) => [v] [zv] [pi'] [eq_pio eq_tail].
    rewrite -{}eq_tail in x_tail.
    move: irred_o; rewrite eq_pio irredE (lock uniq) /= -(nodesE pi') -lock /=.
    move=> /andP[zNpi']; rewrite nodesE -irredE => Ipi'.
    move: zNpi'; apply/idP.
    case: (isplitP Ipi' x_tail) z_cpxy => [p1 p2 _ _ _] /cpP'/(_ p2).
    by rewrite mem_pcat =>->.
  Qed.

  (* The two-sided version of the previous lemma, not used. *)
  Lemma cp_tighten (i o p x y : G) :
    i \in cp x p -> o \in cp p y -> p \in cp x y -> p \in cp i o.
  (* Proof sketch:
   * Let [pi : Path i o]. By connectedness, there are irredundant paths
   * [pi_i : Path x i] and [pi_o : Path o y]. Then [p] must be in the
   * concatenation [pi_i ++ pi ++ pi_o]. It cannot be in the tail of [pi_o]
   * because [o \in cp p z] but [pi_o] is assumed to be irredundant. A
   * symmetrical reasoning for [pi_i] shows that [p \in pi].             Qed. *)
  Abort.
  
  Lemma cp_neighbours (x y : G) z : 
    x != y -> (forall x', x -- x' -> z \in cp x' y) -> z \in cp x y.
  Proof.
    move => A B. apply/cpP => p. case: p => [|x' p].
    - move/spath_nil/eqP => ?. by contrab.
    - rewrite spath_cons in_cons => /andP [C D]. apply/orP;right. 
      apply/(cpP (y := y)) => //. exact: B. 
  Qed.

  (** ** CP Closure Operator *)

  Definition CP (U : {set G}) := \bigcup_(xy in setX U U) cp xy.1 xy.2.
  
  Unset Printing Implicit Defensive.

  Lemma CP_set2 (x y : G) : CP [set x; y] = cp x y.
  Proof.
    apply/setP => z. apply/bigcupP/idP => /=.
    + case=> -[a b] /=/setXP[].
      rewrite !inE =>/orP[]/eqP->; last rewrite (cp_sym x y);
      move=>/orP[]/eqP->//; rewrite cpxx inE => /eqP->; by rewrite mem_cpl.
    + move=> Hz. exists (x, y) => //. by apply/setXP; rewrite !inE !eqxx.
  Qed.
  
  Lemma CP_extensive (U : {set G}) : {subset U <= CP U}.
  Proof.
    move => x inU. apply/bigcupP; exists (x,x); by rewrite ?inE /= ?inU // cpxx inE.
  Qed.

  Lemma CP_mono (U U' : {set G}) : U \subset U' -> CP U \subset CP U'.
  Proof. 
    move/subsetP => A. apply/bigcupsP => [[x y] /setXP [/A Hx /A Hy] /=].
    apply/subsetP => z Hz. apply/bigcupP; exists (x,y) => //. exact/setXP.
  Qed.
  
  Lemma CP_closed U x y : 
    x \in CP U -> y \in CP U -> cp x y \subset CP U.
  Proof.
    case/bigcupP => [[x1 x2] /= /setXP [x1U x2U] x_cp]. 
    case/bigcupP => [[y1 y2] /= /setXP [y1U y2U] y_cp]. 
    apply/subsetP => t t_cp. 
    case (boolP (t == y)) => [/eqP-> //|T2].
    { apply/bigcupP. exists (y1,y2); by [exact/setXP|]. }
    case (boolP (t == x)) => [/eqP-> //|T1].
    { apply/bigcupP. exists (x1,x2); by [exact/setXP|]. }
    move: (cp_mid T1 x_cp) => [p1] [p2] H.
    wlog P1 : x1 x2 p1 p2 x1U x2U x_cp H / t \notin p1 => [W|{H}].
    { case: H => H. 
      - by apply : (W _ _ p1 p2) => //; tauto.
      - rewrite cp_sym in x_cp. apply : (W _ _ p2 p1) => //; tauto. }
    move: (cp_mid T2 y_cp) => [q1] [q2] H.
    wlog P2 : y1 y2 q1 q2 y1U y2U y_cp H / t \notin q1 => [W|{H}].
    { case: H => H. 
      - by apply : (W _ _ q1 q2) => //; tauto.
      - rewrite cp_sym in y_cp. apply : (W _ _ q2 q1) => //; tauto. }
    apply/bigcupP; exists (x1,y1) => /= ; first exact/setXP. 
    apply: contraTT t_cp => /cpPn' [s _ Hs]. 
    suff: t \notin (pcat p1 (pcat s (prev q1))) by apply: cpNI'.
    by rewrite !mem_pcat !mem_prev (negbTE P1) (negbTE P2) (negbTE Hs).
  Qed.

  (* Lemma 16 *)
  Lemma CP_base U x y : x \in CP U -> y \in CP U ->
    exists x' y':G, [/\ x' \in U, y' \in U & [set x;y] \subset cp x' y'].
  Proof.
    move => U1 U2. case/bigcupP : U1 => [[x1 x2]]. case/bigcupP : U2 => [[y1 y2]] /=.
    rewrite !inE /= => /andP[Uy1 Uy2] cp_y /andP[Ux1 Ux2] cp_x.
    case: (boolP (x \in cp y1 y2)) => [C|Wx]; first by exists y1; exists y2; rewrite subUset !sub1set C.
    case: (boolP (y \in cp x1 x2)) => [C|Wy]; first by exists x1; exists x2; rewrite subUset !sub1set C.
    gen have H,A: x x1 x2 y1 y2 {Ux1 Ux2 Uy1 Uy2 Wy cp_y} Wx cp_x /
      (x \in cp x1 y1) || (x \in cp x2 y2).
    { (* TODO: use transitivity *)
      case/cpPn' : Wx => p irr_p av_x. 
      apply: contraTT cp_x. rewrite negb_or => /andP[/cpPn' [s s1 s2] /cpPn' [t t1 t2]].
      apply (cpNI' (p := pcat s (pcat p (prev t)))). 
      by rewrite !mem_pcat !mem_prev (negbTE av_x) (negbTE s2) (negbTE t2). }
    have {H} B : (y \in cp x1 y1) || (y \in cp x2 y2).
    { rewrite -(cp_sym y1 x1) -(cp_sym y2 x2). exact: H. }
    wlog {A} /andP [Hx Hy] : x1 x2 y1 y2 A B cp_x cp_y Ux1 Ux2 Uy1 Uy2 Wx Wy
        / (x \in cp x1 y1) && (y \notin cp x1 y1).
    { case: (boolP (y \in cp x1 y1)) A B => A; case: (boolP (x \in cp x1 y1)) => /= B C D W. 
      - by exists x1; exists y1; rewrite subUset !sub1set B. 
      - (* TOTHINK: why the second case anlysis in this case? *)
        case: (boolP (y \in cp x2 y2)) => E. 
        + exists x2; exists y2; by rewrite subUset !sub1set C.
        + move: (W x2 x1 y2 y1). rewrite (cp_sym x2 x1) (cp_sym y2 y1) A C /= orbT. exact.
      - apply: (W x1 x2 y1 y2) => //. by rewrite B. by rewrite D.
      - exists x2; exists y2; by rewrite subUset !sub1set C D. }
    rewrite (negbTE Hy) /= in B.
    case: (boolP (x \in cp x2 y2)) => [C|Wx']; first by exists x2; exists y2; rewrite subUset !sub1set C.
    exists x1. exists y2. rewrite subUset !sub1set. split => //. apply/andP; split.
    - apply: contraTT cp_x => C. apply: cpN_trans C _. by rewrite cp_sym.
    - apply: contraTT cp_y. apply: cpN_trans. by rewrite cp_sym.
  Qed.

  (** ** Link Graph *)

  Definition link_rel := [rel x y | (x != y) && (cp x y \subset [set x; y])].

  Lemma link_sym : symmetric link_rel.
  Proof. move => x y. by rewrite /= eq_sym cp_sym set2C. Qed.

  Lemma link_irrefl : irreflexive link_rel.
  Proof. move => x /=. by rewrite eqxx. Qed.

  Definition link_graph := SGraph link_sym link_irrefl.

  Local Notation "x ⋄ y" := (@sedge link_graph x y) (at level 30).

  Lemma link_cpN (x y z : G) : 
    (x : link_graph) -- y -> z != x -> z != y -> z \notin cp x y.
  Proof.
    move => /= /andP [_ /subsetP A] B C. apply/negP => /A. 
    by rewrite !inE (negbTE B) (negbTE C).
  Qed.

  Lemma link_avoid (x y z : G) : 
    z \notin [set x; y] -> link_rel x y -> exists2 p, spath x y p & z \notin (x::p).
  Abort. (* not acutally used *)

  Lemma link_seq_cp (y x : G) p :
    @spath link_graph x y p -> cp x y \subset x :: p.
  Proof.
    elim: p x => [|z p IH] x /=.
    - move/spath_nil->. rewrite cpxx. apply/subsetP => z. by rewrite !inE.
    - rewrite spath_cons => /andP [/= /andP [A B] /IH C]. 
      apply: subset_trans (cp_triangle z) _.
      rewrite subset_seqR. apply/subUsetP; split. 
      + apply: subset_trans B _. by rewrite !set_cons setUA subsetUl.
      + apply: subset_trans C _. by rewrite set_cons subset_seqL subsetUr.
  Qed.

  Lemma link_path_cp (x y : G) (p : @Path link_graph x y) : 
    {subset cp x y <= p}.
  Proof. 
    apply/subsetP. rewrite /in_nodes nodesE. apply: link_seq_cp.
    exact: (valP p). 
  Qed.

  (* Lemma 10 *)
  Lemma link_cycle (p : seq link_graph) : ucycle sedge p -> clique [set x in p].
  Proof. 
    move => cycle_p x y. rewrite !inE /= => xp yp xy. rewrite xy /=.
    case/andP : cycle_p => C1 C2. 
    case: (rot_to_arc C2 xp yp xy) => i p1 p2 _ _ I. 
    have {C1} C1 : cycle sedge (x :: p1 ++ y :: p2) by rewrite -I rot_cycle. 
    have {C2} C2 : uniq (x :: p1 ++ y :: p2) by rewrite -I rot_uniq.
    rewrite /cycle -cat_rcons rcons_cat cat_path last_rcons in C1. 
    case/andP : C1 => /rcons_spath P1 /rcons_spath /spath_rev P2. 
    rewrite srev_rcons in P2. 
    move/link_seq_cp in P1. move/link_seq_cp in P2.
    have D: [disjoint p1 & p2].
    { move: C2 => /= /andP [_]. rewrite cat_uniq -disjoint_has disjoint_cons disjoint_sym.
      by case/and3P => _ /andP [_ ?] _. }
    apply: contraTT D. case/subsetPn => z. rewrite !inE negb_or => A /andP [B C].
    move: (subsetP P1 _ A) (subsetP P2 _ A). 
    rewrite !(inE,mem_rcons,negbTE B,negbTE C,mem_rev) /=. 
    exact: disjointNI.
  Qed.

  Lemma CP_clique U : @clique link_graph U -> CP U = U.
  Proof.
    move => clique_U. apply/setP => x. apply/bigcupP/idP. 
    - case => [[x1 x2]]. rewrite !inE /= => /andP [U1 U2]. 
      move: (clique_U x1 x2 U1 U2). case: (boolP (x1 == x2)) => A B.
      + rewrite (eqP A) cpxx inE. by move/eqP->.
      + case/andP: (B erefl) => _ /subsetP => S /S. by case/setUP => /set1P->.
    - move => inU. by exists (x,x); rewrite ?inE /= ?inU // cpxx inE. 
  Qed.

  (** *** Checkpoint graph *)

  (* TOTHINK: Is it really worthwile to have this as a graph in addition to the set [CP U]? *)
  Definition CP_ U := @induced link_graph (CP U).
  Local Notation "x ⋄ y" := (@sedge (CP_ _) x y) (at level 30).
  Arguments Path : clear implicits.
  Arguments spath : clear implicits.

  Lemma CP_base_ U (x y : CP_ U) : 
    exists x' y':G, [/\ x' \in U, y' \in U & [set val x;val y] \subset cp x' y'].
  Proof. exact: CP_base  (svalP x) (svalP y). Qed.

  (* Lemma 14 *)
  Lemma CP_path (U : {set G}) (x y : CP_ U) (p : Path G (val x) (val y)) :
    irred p -> 
    exists2 q : Path (CP_ U) x y, irred q & [set val z | z in q] \subset p.
  Proof.
    (* The proof goes by strong induction on the size of p. *)
    move: {2}#|p|.+1 (ltnSn #|p|) => n.
    elim: n x y p => [//|n IHn] x y p.
    rewrite ltnS leq_eqVlt => /orP[/eqP size_p Ip|]; last exact: IHn.
    case: (x =P y) => [x_y | /eqP xNy].
      (* When x = y, the empty path works. (Actually, p is empty too.) *)
      move: x_y p size_p Ip => {y}<- [p p_pth] _ _.
      exists (idp x); first by rewrite irredE.
      rewrite sub_imset_pre. apply/subsetP => z.
      rewrite /preimset inE /in_nodes !in_collective !nodesE /= !inE.
      by move=> /eqP->; rewrite eqxx.
    (* When x != y, split the path and apply the induction hypothesis. To avoid
     * getting a useless decomposition, x is excluded from the predicate. *)
    pose C := CP U :\ val x.
    (* TOTHINK: Can all_C and all_CP be factored out ? Is it worth ? *)
    have all_CP (P : G -> Prop) :
        {in C, forall z, P z} -> forall z : CP_ U, z != x -> P (val z).
    { move=> H z zNx. apply: H.
      rewrite /C !inE (inj_eq val_inj) zNx /=.
      exact: svalP z. }
    have all_C (P : G -> Prop) :
        (forall z : CP_ U, z != x -> P (val z)) -> {in C, forall z, P z}.
    { move=> H z. rewrite /C in_setD1 => /andP[zNx z_cpu].
      apply: (H (Sub z z_cpu)). apply: contraNN zNx.
      by rewrite -(inj_eq val_inj). }
    (* Use y as a witness of the existence of a splitting point. *)
    have {xNy} : val y \in C.
      move: xNy. rewrite eq_sym. exact: (all_CP (fun z => z \in C)).
    move=> /(fun H => split_at_first H (nodes_end p)).
    (* Let z be the first element in CP(U) after x on p. Call p1 and p2 the
     * parts of p respectively before and after z. *)
    case=> [z [p1 [p2 [eq_p z_C]]]].
    move: z z_C p1 p2 eq_p. apply: (all_C).
    move=> z zNx p1 p2 eq_p /all_CP z_1st.
    move: (eq_p) (Ip) => ->.
    rewrite irred_cat => /andP[Ip1 /andP[Ip2 p1_p2]].
    (* Apply the induction hypothesis to get an irreducible path q using only
     * vertices in p2. *)
    have /IHn /(_ Ip2) [q Iq /subsetP qSp2] : #|p2| < n. {
      (* The size decreases because x cannot be a splitting point. *)
      rewrite -size_p. apply: proper_card. apply/properP. split; last exists (val x).
      - by apply/subsetP => a; rewrite eq_p mem_pcat => ->.
      - exact: nodes_start.
      - have {zNx p1_p2} /andP := conj zNx p1_p2. apply/contraTN.
        rewrite negb_and negbK in_collective nodesE inE.
        case/orP => [/eqP/val_inj x_z | x_p2].
        * by apply/orP; left; apply/eqP.
        * apply/orP; right. apply: disjointNI x_p2. exact: nodes_start.
    }
    (* All checkpoints for (x, z) are in p1 (by definition of a checkpoint) and
     * in CP(U) (by closure). Finally, z is by definition the only vertex on p1
     * and in CP(U) that isn't x. *)
    have xz : @sedge (CP_ U) x z. {
      rewrite /= (inj_eq val_inj) eq_sym zNx /=. apply/subsetP => a a_cp.
      rewrite !inE -implyNb. apply/implyP => aNx. apply/eqP.
      suff a_c : a \in C.
        move: {aNx} a a_c a_cp. apply: all_C => a aNx /cpP'/(_ p1).
        exact: z_1st a aNx.
      rewrite /C !inE {}aNx /=.
      have x_cpu : sval x \in CP U by exact: svalP x.
      have z_cpu : sval z \in CP U by exact: svalP z.
      by have /subsetP/(_ a a_cp) := CP_closed x_cpu z_cpu.
    }
    (* Thus there is an x -- z edge in CP(U) that can be prepended to q.
     * That's the path that was looked for. *)
    exists (pcat (edgep xz) q); last first.
    + apply/subsetP => /= ? /imsetP[a].
      rewrite in_collective !mem_pcat in_collective nodesE /= !inE.
      move=> /orP[/orP[]/eqP->-> | /(mem_imset val)/qSp2 a_q->].
      - by rewrite nodes_start.
      - by rewrite nodes_end.
      - by rewrite a_q.
    + rewrite irred_cat irred_edge Iq /=.
      have /eq_disjoint-> : edgep xz =i [:: x; z].
        by move=> a; rewrite in_collective nodesE /=.
      rewrite !disjoint_cons eq_disjoint0 // andbT.
      apply/andP; split; last first.
        by move: Iq; rewrite /tail irredE /= => /andP[].
      apply/negP => /tailW/(mem_imset val)/qSp2.
      rewrite in_collective nodesE inE (inj_eq val_inj) eq_sym (negbTE zNx) /=.
      have := nodes_start p1.
      exact: disjointE.
  Qed.

  Lemma CP_connected (U : {set G}) : connected [set: CP_ U].
  Proof.
    apply: connectedTI => x y.
    have /uPathP[? /CP_path[q Iq _]] := G_conn (val x) (val y).
    by apply/uPathP; exists q.
  Qed.

  Lemma CP_path_cp (U : {set G}) (x y z : CP_ U) (p : Path (CP_ U) x y) : 
    val z \in cp (val x) (val y) -> z \in p.
  Proof. 
    case: (Path_from_induced p) => q _ eq_q /link_path_cp-/(_ q).
    rewrite in_collective eq_q mem_map //. exact: val_inj.
  Qed.

  (**: If [CP_ U] is a tree, the uniqe irredundant path bewteen any
  two nodes contains exactly the checkpoints bewteen these nodes *)
  Lemma CP_tree_paths (U : {set G}) (x y z : CP_ U) (p : Path (CP_ U) x y) : 
    is_tree (CP_ U) -> irred p -> (z \in p <-> val z \in cp (val x) (val y)).
  Proof.
    move => /tree_unique_Path tree_U irr_p. split.
    - move => z_in_p. apply/negPn. apply/negP => /=. 
      case/cpPn' => q irr_q av_z. case: (CP_path irr_q) => r irr_r /subsetP sub_q. 
      have zr : z \notin r. 
      { apply: contraNN av_z => in_r. apply: sub_q. by rewrite mem_imset. }
      have := tree_U x y p r. case/(_ _ _)/Wrap => // ?. subst. by contrab.
    - simpl. exact: CP_path_cp.
  Qed.

  Arguments Path : default implicits.
  Arguments spath : default implicits.

  (** ** Intervals and bags *)

  (** *** Strict intervals *)

  Definition sinterval x y := 
    [set z in ~: [set x; y] | connect (restrict (predC1 y) (@sedge G)) z x && 
                              connect (restrict (predC1 x) (@sedge G)) z y ].

  Lemma sinterval_sym x y : sinterval x y = sinterval y x.
  Proof. apply/setP => p. by rewrite !inE orbC [_ _ _ _ && _ _ _ _]andbC. Qed.

  Lemma sinterval_bounds x y : (x \in sinterval x y = false) * 
                               (y \in sinterval x y = false).
  Proof. by rewrite !inE !eqxx. Qed.

  Lemma sintervalP x y u :
    u \in sinterval x y = (x \notin cp u y) && (y \notin cp u x).
  Proof.
    rewrite 5!inE negb_or. apply/andP/andP.
    + case=> /andP[uNx uNy] /andP[].
      move=> /(uPathRP uNx)[px] Ipx /subsetP/(_ y).
      rewrite inE eqxx =>/contraTN/(_ isT) yNpx.
      move=> /(uPathRP uNy)[py] Ipy /subsetP/(_ x).
      rewrite inE eqxx =>/contraTN/(_ isT) xNpy.
      by split; apply/cpPn'; eexists; eassumption.
    + case=> /cpPn'[py Ipy xNpy] /cpPn'[px Ipx yNpx].
      have uNx : u != x by apply: contraNneq xNpy =><-; exact: nodes_start.
      have uNy : u != y by apply: contraNneq yNpx =><-; exact: nodes_start.
      split; apply/andP; split=> //; apply/PathRP => //.
      - exists px; apply/subsetP => z ?; rewrite inE.
        by apply: contraNneq yNpx =><-.
      - exists py; apply/subsetP => z ?; rewrite inE.
        by apply: contraNneq xNpy =><-.
  Qed.

  Lemma sintervalP2 x y u :
    reflect ((exists2 p : Path u x, irred p & y \notin p) /\
             (exists2 q : Path u y, irred q & x \notin q))    (u \in sinterval x y).
  Proof.
    apply/(iffP idP).
    + rewrite !inE negb_or => /andP[/andP[uNx uNy]] /andP[].
      case/(uPathRP uNx) => [p] Ip /subsetP/memPn yNp.
      case/(uPathRP uNy) => [q] Iq /subsetP/memPn xNq.
      split; by [exists p | exists q].
    + case=>- [p] Ip yNp [q] Iq xNq.
      rewrite !inE negb_or.
      apply/andP; split.
      - by apply/andP; split; [move: xNq | move: yNp];
        apply: contraNN =>/eqP<-; exact: nodes_start.
      - apply/andP; split; move: connectRI => /(_ G _ u);
        [ move=>/(_ _ x p) | move=>/(_ _ y q) ]; apply=> v; rewrite inE;
        by apply: contraTN =>/eqP->.
  Qed.

  Lemma sinterval_sub x y z : z \in cp x y -> sinterval x z \subset sinterval x y.
  Proof.
    move=> z_cpxy. apply/subsetP=> u. rewrite !sintervalP. case/andP=> xNcpuz zNcpux.
    apply/andP; split.
    - apply: contraNN xNcpuz => x_cpuy. exact: cp_tightenR z_cpxy x_cpuy.
    - apply: contraNN zNcpux => y_cpux. apply: cp_widen y_cpux z_cpxy.
      by rewrite cp_sym mem_cpl.
  Qed.

  Lemma sinterval_exit x y u v : u \notin sinterval x y -> v \in sinterval x y ->
    x \in cp u v \/ y \in cp u v.
  Proof.
    rewrite [v \in _]inE ![in _ && _]inE negb_or => uNIxy /andP[]/andP[vNx vNy].
    case/andP => /(uPathRP vNx)[p1 Ip1 yNp1] /(uPathRP vNy)[p2 Ip2 xNp2].
    have {yNp1 xNp2} [yNp1 xNp2] : y \notin p1 /\ x \notin p2.
      by split; rewrite -disjoint1 disjoint_sym disjoint_subset.
    apply/orP; apply: contraNT uNIxy.
    rewrite negb_or =>/andP[] /cpPn'[q1 Iq1 xNq1] /cpPn'[q2 Iq2 yNq2].
    have uNx : u != x by apply: contraNN xNq1 => /eqP<-; exact: nodes_start.
    have uNy : u != y by apply: contraNN yNq2 => /eqP<-; exact: nodes_start.
    rewrite !inE negb_or. apply/andP; split; first by rewrite uNx uNy.
    apply/andP; split.
    + apply/PathRP => //. exists (pcat q2 p1).
      apply/subsetP => z. rewrite mem_pcat inE.
      apply: contraTN =>/eqP->. by rewrite negb_or yNp1 yNq2.
    + apply/PathRP => //. exists (pcat q1 p2).
      apply/subsetP => z. rewrite mem_pcat inE.
      apply: contraTN =>/eqP->. by rewrite negb_or xNp2 xNq1.
  Qed.

  Lemma sinterval_outside x y u : u \notin sinterval x y ->
    forall (p : Path u x), irred p -> y \notin p -> [disjoint p & sinterval x y].
  Proof.
    move=> uNIxy p Ip yNp.
    rewrite disjoint_subset; apply/subsetP => v.
    rewrite inE /= -[mem (in_nodes p)]/(mem p) => v_p.
    apply/negP => v_Ixy.
    case/(isplitP Ip) eq_p : {-}p / v_p => [p1 p2 _ _ D]. 
    case: (sinterval_exit uNIxy v_Ixy) => /cpP'/(_ p1); last first.
    + apply/negP; apply: contraNN yNp.
      by rewrite eq_p mem_pcat => ->.
    + suff S: x \in tail p2 by rewrite (disjointFl D S).
      have:= nodes_end p2. rewrite mem_path inE => /predU1P [E|//].
      subst v. by rewrite sinterval_bounds in v_Ixy.
  Qed.

  Lemma sinterval_disj_cp (x y z : G) :
    z \in cp x y -> [disjoint sinterval x z & sinterval z y].
  Proof.
    move=> z_cpxy. rewrite -setI_eq0 -subset0. apply/subsetP=> u. rewrite inE.
    case/andP=> /sintervalP2[][p _ /negbTE zNp] _ /sintervalP2[_][q _ /negbTE zNq].
    rewrite !inE. apply: contraTT z_cpxy => _. apply/cpP' => /(_ (pcat (prev p) q)).
    by rewrite mem_pcat mem_prev zNp zNq.
  Qed.

  Lemma sinterval_noedge_cp (x y z u v : G) :
    u -- v -> u \in sinterval x z -> v \in sinterval z y -> z \notin cp x y.
  Proof.
    move=> uv /sintervalP2[][p _ /negbTE zNp] _ /sintervalP2[_][q _ /negbTE zNq].
    apply/cpP' => /(_ (pcat (prev p) (pcat (edgep uv) q))).
    rewrite !mem_pcat mem_prev mem_edgep zNp zNq orbF /=.
    apply/negP. rewrite negb_or. apply/andP. split.
    - apply: contraFneq zNp =>->. exact: nodes_start.
    - apply: contraFneq zNq =>->. exact: nodes_start.
  Qed.

  Lemma sinterval_components (C : {set G}) x y :
    C \in components (sinterval x y) ->
    (exists2 u, u \in C & x -- u) /\ (exists2 v, v \in C & y -- v).
  Proof.
    case/and3P: (partition_components (sinterval x y)).
    move=> /eqP compU compI comp0 C_comp.
    have /card_gt0P[a a_C] : 0 < #|C|.
    { rewrite card_gt0. by apply: contraTneq C_comp =>->. }
    have a_sI : a \in sinterval x y. { rewrite -compU. by apply/bigcupP; exists C. }
    rewrite -{C C_comp a_C}(def_pblock compI C_comp a_C).

    case/sintervalP2: (a_sI) (a_sI) => -[p] Ip yNp [q] Iq xNq.
    rewrite !inE negb_or =>/andP[] /andP[aNx aNy] _.
    case: (splitR p aNx) Ip (yNp) => [u][p'][ux] ->.
    case: (splitR q aNy) Iq (xNq) => [v][q'][vy] ->.
    rewrite !irred_cat' !mem_pcat !mem_edgep !negb_or.
    case/and3P=> Iq' _ /eqP/setP/(_ y).
    rewrite !inE nodes_end andbT eq_sym sg_edgeNeq //.
    move=> /negbT yNq' /and3P[xNq' xNv xNy].
    case/and3P=> Ip' _ /eqP/setP/(_ x).
    rewrite !inE nodes_end andbT eq_sym sg_edgeNeq //.
    move=> /negbT xNp' /and3P[yNp' yNu yNx].

    split; [exists u | exists v]; rewrite 1?sg_sym //; apply/components_pblockP.
    - exists p'. apply/subsetP => z z_p. rewrite sintervalP.
      case: (Path_split z_p) xNp' yNp' => [p1][p2]->.
      rewrite !mem_pcat !negb_or => /andP[xNp1 xNp2] /andP[yNp1 yNp2].
      apply/andP; split; apply/cpP'.
      + move=> /(_ (pcat (prev p1) q)). apply/negP.
        by rewrite !mem_pcat mem_prev negb_or xNp1 xNq.
      + move=> /(_ (pcat p2 (edgep ux))). apply/negP.
        by rewrite !mem_pcat mem_edgep !negb_or yNp2 yNu yNx.
    - exists q'. apply/subsetP => z z_q. rewrite sintervalP.
      case: (Path_split z_q) xNq' yNq' => [q1][q2]->.
      rewrite !mem_pcat !negb_or => /andP[xNq1 xNq2] /andP[yNq1 yNq2].
      apply/andP; split; apply/cpP'.
      + move=> /(_ (pcat q2 (edgep vy))). apply/negP.
        by rewrite !mem_pcat mem_edgep !negb_or xNq2 xNv xNy.
      + move=> /(_ (pcat (prev q1) p)). apply/negP.
        by rewrite !mem_pcat mem_prev negb_or yNq1 yNp.
  Qed.

  (** *** Intervals *)

  Definition interval x y := [set x;y] :|: sinterval x y.

  Lemma interval_sym x y : interval x y = interval y x.
  Proof. by rewrite /interval [[set x; y]]setUC sinterval_sym. Qed.

  Lemma cp_sub_interval x y : cp x y \subset interval x y.
  Proof.
    apply/subsetP=> z z_cpxy. rewrite !in_setU !in_set1 sintervalP -implyNb negb_or.
    apply/implyP=> /andP[zNx zNy]. apply/andP; split.
    - apply: contraNN zNx => /(cp_tightenR z_cpxy). by rewrite cpxx !inE eq_sym.
    - rewrite cp_sym in z_cpxy. apply: contraNN zNy => /(cp_tightenR z_cpxy).
      by rewrite cpxx !inE eq_sym.
  Qed.

  Lemma intervalI_cp (x y z : G) :
    z \in cp x y -> interval x z :&: interval z y = [set z].
  Proof.
    move=> z_cpxy. apply/setP=> u.
    rewrite inE ![_ \in interval _ _]inE (lock sinterval) !inE -lock -!orbA.
    apply/idP/idP; last by move=>->.
    case/andP=> /or3P[/eqP->|->//|u_sIxz] /or3P[->//|/eqP u_y|u_sIzy].
    - move: z_cpxy. by rewrite -u_y cpxx inE eq_sym.
    - move: u_sIzy. by rewrite sintervalP z_cpxy.
    - move: u_sIxz. by rewrite u_y sintervalP (cp_sym y x) z_cpxy andbF.
    - by case: (disjointE (sinterval_disj_cp z_cpxy) u_sIxz u_sIzy).
  Qed.

  Lemma connected_interval (x y : G) : 
    connected (interval x y).
  Proof.
    suff conn_y z : 
      z \in interval x y -> connect (restrict (mem (interval x y)) sedge) z y.
    { move => u v /conn_y Hu /conn_y Hv. 
      apply: connect_trans Hu _. by rewrite connect_symI. }
    move=> z_intv. wlog z_sintv : z {z_intv} / z \in sinterval x y.
    { move=> Hyp. move: z_intv.
      rewrite 4!inE -orbA => /or3P[/eqP->|/eqP->|//];
      last exact: Hyp; last exact: connect0.
      case: (altP (x =P y)) => [->|xNy]; first exact: connect0.
      case/uPathP: (G_conn x y) => p.
      case: (splitL p xNy) => [u] [xu] [p'] [-> _].
      rewrite irred_cat' =>/and3P[_ Ip']/eqP/setP/(_ x).
      rewrite !inE nodes_start /= sg_edgeNeq // => xNp'.
      case: (altP (y =P u)) xu => [<- xy|yNu xu].
      { apply/(PathRP xNy). exists (edgep xy).
        apply/subsetP=> v. rewrite mem_edgep.
        by case/orP=> /eqP->; rewrite !inE eqxx. }
      have usi : u \in sinterval x y.
      { apply/sintervalP2; split; last by exists p'; rewrite // xNp'.
        exists (prev (edgep xu)); first by rewrite irred_rev irred_edge.
        by rewrite mem_prev mem_edgep negb_or eq_sym xNy yNu. }
      { apply: @connect_trans (Hyp u usi).
        apply/PathRP; first by rewrite sg_edgeNeq.
        exists (edgep xu); apply/subsetP=> v.
        rewrite mem_edgep => /orP[]/eqP->.
        - by rewrite !inE eqxx.
        - by rewrite inE usi. }
    }
    case/sintervalP2: (z_sintv) => _ [p Ip xNp].
    apply/PathRP; first by apply: contraTneq z_sintv =>->; rewrite sinterval_bounds.
    exists p. apply/subsetP=> u u_p.
    have uNx : u != x by apply: contraNneq xNp => <-.
    case: (Path_split u_p) Ip xNp => [p1][p2]->.
    rewrite irred_cat' => /and3P[_ _] /eqP/setP/(_ y).
    rewrite 2!inE nodes_end andbT eq_sym mem_pcat negb_or => y_up2 /andP[xNp1 xNp2].
    rewrite 4!inE (negbTE uNx) /= orbC -implyNb. apply/implyP=> uNsi.
    case: (sinterval_exit uNsi z_sintv); rewrite cp_sym => /cpP'/(_ p1).
    - by rewrite (negbTE xNp1).
    - by rewrite y_up2.
  Qed.

  (** *** Bags *)

  Definition bag (U : {set G}) x :=
    locked [set z | [forall y in CP U, x \in cp z y]].

  Lemma bag_id (U : {set G}) x : x \in bag U x.
  Proof. rewrite /bag -lock inE. apply/forall_inP => y _. exact: mem_cpl. Qed.

  Lemma bag_nontrivial (U : {set G}) x : 
    bag U x != [set x] -> exists2 y, y \in bag U x & y != x.
  Proof. apply: setN01E. apply/set0Pn. exists x. by rewrite bag_id. Qed.

  Lemma bagP (U : {set G}) x z : 
    reflect (forall y, y \in CP U -> x \in cp z y) (z \in bag U x).
  Proof. rewrite /bag -lock inE. exact: (iffP forall_inP). Qed.
  Arguments bagP [U x z].

  Lemma bagPn (U : {set G}) x z : 
    reflect (exists2 y, y \in CP U & x \notin cp z y) (z \notin bag U x).
  Proof.
    rewrite /bag -lock inE negb_forall. apply: (iffP existsP) => [[y]|[y] A B].
    - rewrite negb_imply => /andP[? ?]. by exists y.
    - exists y. by rewrite A.
  Qed.

  Lemma bag_sub_sinterval (U : {set G}) x y z :
    x \in CP U -> y \in CP U -> z \in cp x y :\: [set x; y] ->
    bag U z \subset sinterval x y.
  Proof.
    rewrite in_setD in_set2 negb_or => x_cp y_cp /andP[]/andP[zNx zNy] z_cpxy.
    apply/subsetP=> u /bagP u_bag.
    move: x_cp y_cp => /u_bag z_cpux /u_bag z_cpuy.
    rewrite sintervalP. apply/andP; split.
    - apply: contraNN zNx => x_cpuy.
      suff : x \in cp z z by rewrite cpxx in_set1 eq_sym.
      suff : x \in cp z u by apply: cp_tightenR; rewrite cp_sym.
      rewrite cp_sym; exact: cp_tightenR z_cpxy x_cpuy.
    - apply: contraNN zNy => y_cpux.
      suff : y \in cp z z by rewrite cpxx in_set1 eq_sym.
      suff : y \in cp z u by apply: cp_tightenR; rewrite cp_sym.
      rewrite cp_sym; apply: cp_tightenR y_cpux; by rewrite cp_sym.
  Qed.


  (** ** Neighouring Checkpoints *)

  Definition ncp (U : {set G}) (p : G) : {set G} := 
    locked [set x in CP U | connect (restrict [pred z | (z \in CP U) ==> (z == x)] sedge) p x].

  (* TOTHINK: Do we also want to require [irred q] *)
  Lemma ncpP (U : {set G}) (p : G) x : 
    reflect (x \in CP U /\ exists q : Path p x, forall y, y \in CP U -> y \in q -> y = x) 
            (x \in ncp U p).
  Proof.
    rewrite /ncp -lock inE. apply: (iffP andP) => [[cp_x A]|[cp_x [q Hq]]]; split => //.
    - case: (boolP (p == x)) => [/eqP ?|px]. 
      + subst p. exists (idp x) => y _ . by rewrite mem_idp => /eqP.
      + case/(uPathRP px) : A => q irr_q /subsetP sub_q. 
        exists q => y CPy /sub_q. by rewrite !inE CPy => /eqP.
    - apply: (connectRI (p := q)) => y y_in_q.
      rewrite inE. apply/implyP => A. by rewrite [y]Hq.
  Qed.
  
  Lemma ncp_CP (U : {set G}) (u : G) :
    u \in CP U -> ncp U u = [set u].
  Proof. 
    move => Hu.
    apply/setP => x. rewrite [_ \in [set _]]inE. apply/ncpP/eqP.
    - move => [Hx [q Hq]]. apply: esym. apply: Hq => //. exact: nodes_start.
    - move => ->. split => //. exists (idp u) => y _. by  rewrite mem_idp => /eqP.
  Qed.

  Lemma ncp_bag (U : {set G}) (p : G) x :
    x \in CP U -> (p \in bag U x) = (ncp U p == [set x]).
  Proof.
    move => Ux. apply/bagP/eq_set1P.
    - move => A. split.
      + apply/ncpP; split => //.
        case/uPathP : (G_conn p x) => q irr_q. 
        case: (boolP [exists y in CP U, y \in [predD1 q & x]]).
        * case/exists_inP => y /= B. rewrite inE eq_sym => /= /andP [C D]. 
          case:notF. apply: contraTT (A _ B) => _. apply/cpPn'.
          case/(isplitP irr_q) def_q : q / D => [q1 q2 irr_q1 irr_q2 D12].
          exists q1 => //. rewrite (disjointFl D12) //. 
          suff: x \in q2. by rewrite mem_path inE (negbTE C). 
          by rewrite nodes_end.
        * rewrite negb_exists_in => /forall_inP B.
          exists q => y /B => C D. apply/eqP. apply: contraNT C => C. 
          by rewrite inE C.
      + move => y /ncpP [Uy [q Hq]]. 
        have Hx : x \in q. { apply/cpP'. exact: A. }
        apply: esym. exact: Hq. 
    - case => A B y Hy. apply/cpP' => q.
      have qy : y \in q by rewrite nodes_end.
      move: (split_at_first Hy qy) => [x'] [q1] [q2] [def_q cp_x' Hq1]. 
      suff ?: x' = x. { subst x'. by rewrite def_q mem_pcat nodes_end. }
      apply: B. apply/ncpP. split => //. exists q1 => z' H1 H2. exact: Hq1.
  Qed.

  Lemma ncp0 (U : {set G}) x p : 
    x \in CP U -> ncp U p == set0 = false.
  Proof. 
    case/uPathP : (G_conn p x) => q irr_q Ux.  
    case: (split_at_first Ux (nodes_end q)) => y [q1] [q2] [def_q CPy Hy].
    suff: y \in ncp U p. { apply: contraTF => /eqP->. by rewrite inE. }
    apply/ncpP. split => //. by exists q1. 
  Qed.
  Arguments ncp0 [U] x p.
  
  Lemma ncp_interval U (x y p : G) : 
    x != y -> [set x; y] \subset ncp U p -> p \in sinterval x y.
  Proof.
    rewrite subUset !sub1set => xy /andP[Nx Ny]. 
    rewrite !inE negb_or. 
    gen have A,Ax : x y xy Nx Ny / p != x.
    { have Ux : x \in CP U. by case/ncpP : Nx.
      apply: contraNN xy => /eqP => ?; subst p. apply/eqP.
      case/ncpP : Ny => Uy [q] /(_ _ Ux). rewrite nodes_start. 
      by apply. }
    have Ay: p != y. apply: (A y x) => //. by rewrite eq_sym.
    rewrite Ax Ay /=. 
    gen have S,_: x y Nx Ny xy {A Ax Ay} / connect (restrict (predC1 y) sedge) p x.
    { case/ncpP : Nx => Ux [q Hq]. apply: (connectRI (p := q)).
      move => z in_q. apply: contraNT xy. rewrite negbK => /eqP ?; subst z.
      rewrite [y]Hq //. by case/ncpP : Ny. }
    apply/andP;split; apply: S => //. by rewrite eq_sym.
  Qed.

  (** *** Application to bags *)

  (** the root of a bag is a checkpoint separating the bag from
  the rest of the graph *)
  Lemma bag_exit (U : {set G}) x u v : 
    x \in CP U -> u \in bag U x -> v \notin bag U x -> x \in cp u v.
  Proof.
    move => cp_x. rewrite [v \in _]ncp_bag // => N1 N2.
    have [y [Y1 Y2 Y3]] : exists y, [/\ y \in CP U, x != y & y \in ncp U v].
    { case: (setN01E _ N2); first by rewrite (ncp0 x).
      move => y Y1 Y2. exists y; split => //; by [rewrite eq_sym|case/ncpP : Y1]. }
    move/bagP : N1 => /(_ _ Y1). 
    apply: contraTT => /cpPn' [p] irr_p av_x. 
    case/ncpP : Y3 => _ [q] /(_ _ cp_x) A. 
    have {A} Hq : x \notin q. { apply/negP => /A ?. subst. by rewrite eqxx in Y2. }
    apply: (cpNI' (p := pcat p q)). by rewrite mem_pcat negb_or av_x.
  Qed.

  Lemma bag_exit' (U : {set G}) x u v : 
    x \in CP U -> u \in bag U x -> v \in x |: ~: bag U x -> x \in cp u v.
  Proof. 
    move => cp_x Hu. case/setU1P => [->|]; first by rewrite cp_sym mem_cpl.
    rewrite inE. exact: bag_exit Hu.
  Qed.

  Lemma bag_exit_edge (U : {set G}) x u v :
    x \in CP U -> u \in bag U x -> v \notin bag U x -> u -- v -> u = x.
  Proof.
    move=> x_cp u_bag vNbag uv.
    move/cpP'/(_ (edgep uv)): (bag_exit x_cp u_bag vNbag).
    rewrite mem_edgep. case/orP=> /eqP// Exv.
    move: vNbag. by rewrite -Exv bag_id.
  Qed.

  Lemma bag_in_out (U : {set G}) x u v (p : Path u v) :
    x \in CP U -> u \in x |: ~: bag U x -> v \in x |: ~: bag U x -> irred p -> 
                                           p \subset x |: ~: bag U x.
  Proof.
    move => Ux Pu Pv. apply: contraTT => /subsetPn [w]. 
    rewrite !inE negb_or negbK => in_p /andP [W1 W2]. 
    case/Path_split : in_p => w1 [w2] def_p. subst. 
    rewrite irred_cat !negb_and (disjointNI (x := x)) //.
    + apply/cpP'. rewrite cp_sym. exact: bag_exit' Pu.
    + suff: x \in prev w2 by rewrite mem_prev mem_path inE eq_sym (negbTE W1). 
      apply/cpP'. rewrite cp_sym. exact: bag_exit' Pv.
  Qed.

  (** This is a bit bespoke, as it only only mentions bags rooted at
elements of [U] rather than [CP U]. At the point where we use it, U is
a clique, so [CP U] is [U]. *)
  Lemma bags_in_out (U : {set G}) u v (p : Path u v) :
    let T' := U :|: (~: \bigcup_(z in U) bag U z) in 
    u \in T' -> v \in T' -> irred p -> {subset p <= T'}.
  Proof. 
    move => T' uT vT irr_p. apply/subsetP/negPn/negP.  
    case/subsetPn => z zp. rewrite !inE negb_or negbK => /andP [zU].
    case/bigcupP => x xU zPx. 
    suff HT': {subset T' <= x |: ~: bag U x}. 
    { move/HT' in uT. move/HT' in vT. 
      move/subsetP : (bag_in_out (CP_extensive xU) uT vT irr_p) => sub.
      move/sub : zp. rewrite !inE zPx /= orbF => /eqP ?. by subst z;contrab. }
    move => w. case/setUP => [wU|H].
    + case: (altP (x =P w)) => [->|E]; rewrite !inE ?eqxx // 1?eq_sym.
      rewrite (negbTE E) /=. apply/bagPn; exists w; first exact: CP_extensive.
        by rewrite cpxx inE. 
    + apply/setUP;right. rewrite !inE in H *. apply: contraNN H => wP. 
      apply/bigcupP. by exists x.
  Qed.

  Lemma connected_bag x (U : {set G}) : x \in CP U -> connected (bag U x).
  Proof.
    move => cp_x.
    suff S z : z \in bag U x -> connect (restrict (mem (bag U x)) sedge) x z.
    { move => u v Hu Hv. apply: connect_trans (S _ Hv). 
      rewrite srestrict_sym. exact: S. }
    move => Hz. case/uPathP : (G_conn z x) => p irr_p. 
    suff/subsetP sP : p \subset bag U x.
    { rewrite srestrict_sym. exact: (connectRI (p := p)). }
    apply/negPn/negP. move/subsetPn => [z' in_p N]. 
    case/(isplitP irr_p): _ / in_p => [p1 p2 _ _ D]. 
    suff : x \in tail p2. 
    { rewrite (disjointFr D) //. apply/cpP'. exact: bag_exit N. }
    apply: in_tail => [|]; last exact: nodes_end.
    apply: contraNN N => /eqP<-. by rewrite bag_id.
  Qed.

  Lemma bag_extension (U : {set G}) x y : 
    x \in CP U -> y \notin bag U x -> bag U x = bag (y |: U) x.
  Proof.
    move => CPx Hy. apply/setP => u. apply/idP/bagP.
    - move => A z. 
      have cp_x : x \in cp u y by apply: bag_exit Hy.
      case: (boolP (x == z)) => [/eqP ? _|zx]; first by subst z; apply: (bagP A).
      case/bigcupP => [[v0 v1]] /setXP /= []. 
      have E v : v \in U -> z \in cp y v -> x \in cp u z.
      { move => Hv Hz. case: (cp_mid zx Hz) => p1 [p2] [/cpNI'|/cpNI'] C.
        * apply: contraTT cp_x => ?. exact: cpN_trans C.
        * apply: contraTT A => ?. apply/bagPn. 
          exists v; [exact: CP_extensive|exact: cpN_trans C]. }
      do 2 (case/setU1P => [->|?]). 
      + by rewrite cpxx inE => /eqP->. 
      + exact: E. 
      + rewrite cp_sym. exact: E.
      + move => Hz. apply: (bagP A). apply/bigcupP; exists (v0,v1) => //. exact/setXP.
    - move => A. apply/bagP => z Hz. apply: A. move: z Hz. apply/subsetP. 
      apply: CP_mono. exact: subsetUr.
  Qed.


  (** ** Partitioning with intervals, bags and checkpoints *)

  (** *** Disjointness statements *)

  (** A small part of Proposition 20. *)
  Lemma CP_tree_sinterval (U : {set G}) (x y : CP_ U) :
    is_tree (CP_ U) -> x -- y -> [disjoint CP U & sinterval (val x) (val y)].
  Proof.
    move=> CP_tree xy.
    rewrite -setI_eq0 -subset0; apply/subsetP => u.
    rewrite inE [u \in set0]inE =>/andP[u_CP].
    set u_ := Sub u u_CP : CP_ U; rewrite -[u]/(val u_).
    move: {u u_CP} u_ => u /sintervalP2[] -[p] Ip yNp [q] Iq xNq.
    case: (CP_path Ip) => p_ Ip_ /subsetP/(_ (val y)) p_p.
    case: (CP_path Iq) => q_ Iq_ /subsetP/(_ (val x)) q_q.
    have {p Ip yNp p_p} yNp_ : y \notin p_.
      by apply: contraNN yNp => ?; apply: p_p; exact: mem_imset.
    have {q Iq xNq q_q} xNq_ : x \notin q_.
      by apply: contraNN xNq => ?; apply: q_q; exact: mem_imset.
    have Ip_xy : irred (pcat p_ (edgep xy)).
      by [rewrite irred_cat Ip_ irred_edge /tail/=;
          rewrite disjoint_sym disjoint_cons eq_disjoint0].
    have eq_ : q_ = pcat p_ (edgep xy) := tree_unique_Path CP_tree Iq_ Ip_xy.
    apply: contraNT xNq_ => _.
    by rewrite eq_ mem_pcat !in_collective !nodesE/= !inE eqxx.
  Qed.
  
  Lemma bag_disj (U : {set G}) x y :
    x \in CP U -> y \in CP U -> x != y -> [disjoint bag U x & bag U y].
  Proof.
    move => Ux Uy xy. apply/pred0P => p /=. apply:contraNF xy => /andP[].
    rewrite !ncp_bag //. by move => /eqP-> /eqP/set1_inj->.
  Qed.

  Lemma bag_cp (U : {set G}) x y : 
    x \in CP U -> y \in CP U -> x \in bag U y = (x == y).
  Proof. 
    move => cp_x cp_y. 
    apply/idP/idP => [|/eqP <-]; last exact: bag_id.
    apply: contraTT => xy. 
    have D: [disjoint bag U x & bag U y] by apply : bag_disj.
      by rewrite (disjointFr D) // bag_id.
  Qed.
  
  (** NOTE: This looks fairly specific, but it also has a fairly
  straightforward proof *)
  Lemma interval_bag_disj U (x y : G) :
    y \in CP U -> [disjoint bag U x & sinterval x y].
  Proof.
    move => Uy. rewrite disjoint_sym disjoints_subset. apply/subsetP => z.
    rewrite 3!inE negb_or !in_set1 => /and3P [/andP [A1 A2] B C]. 
    rewrite inE. apply:contraTN C => /bagP/(_ _ Uy). 
    apply: contraTN. case/uPathRP => // p _ /subsetP sub_p. 
    apply: (cpNI' (p := p)). apply/negP => /sub_p. by rewrite inE eqxx.
  Qed.

  (** *** Covering statements *)

  Lemma sinterval_bag_cover x y : x != y ->
    [set: G] = bag [set x; y] x :|: sinterval x y :|: bag [set x; y] y.
  Proof.
    move=> xNy. apply/eqP. rewrite eqEsubset subsetT andbT. apply/subsetP => p _.
    rewrite setUAC setUC !in_setU sintervalP -negb_or -implybE. apply/implyP.
    wlog suff Hyp : x y {xNy} / x \in cp p y -> p \in bag [set x; y] x.
    { by case/orP => /Hyp; last rewrite setUC; move=>->. }
    move=> x_cppy; apply/bagP => z. rewrite CP_set2 => z_cpxy.
    exact: cp_tightenR z_cpxy x_cppy.
  Qed.

  Lemma sinterval_cp_cover x y z : z \in cp x y :\: [set x; y] ->
    sinterval x y = sinterval x z :|: bag [set x; y] z :|: sinterval z y.
  Proof.
    rewrite 4!inE negb_or => /andP[]/andP[zNx zNy] z_cpxy. apply/eqP.
    have [x_CP y_CP] : x \in CP [set x; y] /\ y \in CP [set x; y].
    { by split; apply: CP_extensive; rewrite !inE eqxx. }
    rewrite eqEsubset !subUset sinterval_sub //=.
    rewrite {3}(sinterval_sym x y) {2}(sinterval_sym z y) sinterval_sub 1?cp_sym //.
    rewrite bag_sub_sinterval /= ?andbT //;
      last by rewrite in_setD in_set2 negb_or zNx zNy.
    apply/subsetP=> u u_sIxy. rewrite !in_setU.
    have [uNx uNy] : u != x /\ u != y.
    { by split; apply: contraTneq u_sIxy => ->; rewrite sinterval_bounds. }
    move: u_sIxy; rewrite sintervalP. case/andP=> xNcpuy yNcpux.
    case: (boolP (z \in cp u x)) => Hx; case: (boolP (z \in cp u y)) => Hy.
    + suff -> : u \in bag [set x; y] z by []. apply/bagP=> c.
      rewrite CP_set2 => /(subsetP (cp_triangle z)). rewrite in_setU cp_sym.
      case/orP=> c_cp; exact: cp_tightenR c_cp _.
    + suff -> : u \in sinterval z y by []. rewrite sintervalP Hy /=.
      apply: cpN_trans yNcpux _. apply: contraNN zNy => y_cpxz.
      suff : z \in cp y y by rewrite cpxx in_set1 eq_sym.
      move: y_cpxz z_cpxy. rewrite [cp x z]cp_sym [cp x y]cp_sym.
      exact: cp_tightenR.
    + suff -> : u \in sinterval x z by []. rewrite sintervalP Hx andbT.
      apply: cpN_trans xNcpuy _. apply: contraNN zNx => x_cpyz.
      suff : z \in cp x x by rewrite cpxx in_set1 eq_sym.
      move: x_cpyz z_cpxy. rewrite [cp y z]cp_sym.
      exact: cp_tightenR.
    + rewrite cp_sym in Hx. have : z \notin cp x y := cpN_trans Hx Hy.
      by rewrite z_cpxy.
  Qed.

  Lemma interval_cp_cover x y z : z \in cp x y :\: [set x; y] ->
    interval x y = (x |: sinterval x z) :|: bag [set x; y] z :|: (y |: sinterval z y).
  Proof.
    rewrite /interval => /sinterval_cp_cover->.
    by rewrite setUAC -setUA [_ :|: set1 y]setUAC !setUA.
  Qed.

  Lemma interval_edge_cp (x y z u v : G) : z \in cp x y -> u -- v ->
    u \in interval x z -> v \in interval z y -> (u == z) || (v == z).
  Proof.
    move=> z_cpxy uv u_xz v_zy.
    wlog [Hu Evy] : x y u v z_cpxy uv {u_xz v_zy} / u \in sinterval x z /\ v = y.
    { move=> Hyp. move: u_xz v_zy. rewrite !in_setU !in_set1 -!orbA.
      case/or3P=> [/eqP Eux|->//|Hu]; case/or3P=> [->//|/eqP Evy|Hv].
      - move: uv; rewrite Eux Evy => xy. move/cpP'/(_ (edgep xy)): z_cpxy.
        by rewrite mem_edgep ![z == _]eq_sym.
      - rewrite orbC. move: (conj Hv Eux). rewrite sinterval_sym.
        apply: Hyp; by rewrite 1?cp_sym 1?sg_sym.
      - by apply: Hyp (conj Hu Evy).
      - move: (sinterval_noedge_cp uv Hu Hv). by rewrite z_cpxy. }
    move: uv Hu; rewrite {}Evy sintervalP => uy /andP[_]/cpPn'[p _ zNp].
    move/cpP'/(_ (pcat (prev p) (edgep uy))): z_cpxy.
    by rewrite mem_pcat mem_prev mem_edgep (negbTE zNp) /= ![z == _]eq_sym.
  Qed.


  Lemma CP_bags U x y : link_rel x y -> x \in CP U -> y \in CP U -> 
    exists x' y', [/\ x' \in U, y' \in U, x' \in bag [set x; y] x & y' \in bag [set x;y] y].
  Proof.
    move => xy xU yU. case: (CP_base xU yU) => x' [y'] [Hx' Hy' CPxy].
    case/uPathP : (G_conn x' y') => p irr_p. 
    have [Hx Hy] : x \in p /\ y \in p. 
    { by split; apply: cpP'; apply: (subsetP CPxy); rewrite !inE eqxx. }
    rewrite subUset !sub1set in CPxy. case/andP: CPxy => CPx CPy.
    wlog x_before_y : x y Hx Hy xy xU yU CPx CPy / x <[p] y.
    { move => W. 
      case: (ltngtP (idx p x) (idx p y)) => A; first exact: W.
      - case: (W y x) => //; first by rewrite link_sym.
        move => x0 [y0]. rewrite setUC. move => [? ? ? ?]. by exists y0; exists x0.
      - move/idx_inj : A. move/(_ Hx) => ?. subst y. by rewrite /link_rel /= eqxx in xy. }
    case: (three_way_split irr_p Hx Hy x_before_y) => p1 [p2] [p3] [? P1 P3].
    have H2 : CP [set x;y] = [set x;y]. { apply: CP_clique. exact: clique2. }
    exists x';exists y'; split => //. 
    - apply/bagP => ?. rewrite H2. case/set2P=>->; first by rewrite cp_sym mem_cpl.
      apply: contraTT CPx => C. 
      apply: cpN_trans C _. exact: (cpNI' (p := p3)).
    - apply/bagP => ?. rewrite H2. case/set2P=>->; last by rewrite cp_sym mem_cpl.
      apply: contraTT CPy => C. rewrite cp_sym in C. 
      apply: cpN_trans C. exact: (cpNI' (p := p1)).
  Qed.

  Lemma CP_triangle_bags U (x y z : CP_ U) : 
    x -- y -> y -- z -> z -- x -> 
    let U3 : {set G} := [set val x; val y; val z] in
    exists x' y' z' : G, 
      [/\ x' \in U, y' \in U & z' \in U] /\ 
      [/\ x' \in bag U3 (val x), y' \in bag U3 (val y) & z' \in bag U3 (val z)].
  Proof with try (apply: CP_extensive; rewrite ?inE ?eqxx //).
    move => xy yz zx.
    gen have T,_ : x y z xy yz zx / val z \notin cp (val x) (val y).
    { case/andP : xy => _ /subsetP S. apply/negP => /S. 
      case/set2P => /val_inj ?;subst; by rewrite sg_irrefl in zx yz. }
    move => U3.
    case: (CP_bags xy (valP x) (valP y)) => x' [y'] [xU yU Px Py].
    case: (CP_bags yz (valP y) (valP z)) => _ [z'] [_ zU _ Pz].
    have zPx : (val z) \notin bag [set val x;val y] (val x).
    { apply/bagPn. exists (val y)...  apply T => //; by rewrite sg_sym. }
    have zPy : (val z) \notin bag [set val x;val y] (val y).
    { apply/bagPn. exists (val x)... apply T => //; by rewrite sg_sym. }
    have xPz : (val x) \notin bag [set val y;val z] (val z).
    { apply/bagPn. exists (val y)... exact: T. }
    exists x';exists y';exists z'. split => //. split.
    - rewrite /U3 setUC -bag_extension //... 
    - rewrite /U3 setUC -bag_extension //... 
    - rewrite /U3 -setUA -bag_extension //...
  Qed.
 
End CheckPoints.

Notation "x ⋄ y" := (@sedge (link_graph _) x y) (at level 30).
Notation "x ⋄ y" := (@sedge (CP_ _) x y) (at level 30).

(** ** Checkpoint Order *)

Section CheckpointOrder.

  Variables (G : sgraph) (i o : G).
  Hypothesis conn_io : connect sedge i o.
  Implicit Types x y : G.

  Lemma the_uPath_proof : exists p : Path i o, irred p.
  Proof. case/uPathP: conn_io => p Ip. by exists p. Qed.
                                                                
  Definition the_uPath := xchoose (the_uPath_proof).

  Lemma the_uPathP : irred (the_uPath).
  Proof. exact: xchooseP. Qed.

  Definition cpo x y := let p := the_uPath in idx p x <= idx p y.

  Lemma cpo_refl : reflexive cpo.
  Proof. move => ?. exact: leqnn. Qed.

  Lemma cpo_trans : transitive cpo.
  Proof. move => ? ? ?. exact: leq_trans. Qed.

  Lemma cpo_total : total cpo.
  Proof. move => ? ?. exact: leq_total. Qed.

  Lemma cpo_antisym : {in cp i o&,antisymmetric cpo}.
  Proof. 
    move => x y /cpP'/(_ the_uPath) Hx _.
    rewrite /cpo -eqn_leq =>/eqP. exact: idx_inj.
  Qed.

  (** All paths visist all checkpoints in the same order as the canonical upath *)
  (* TOTHINK: Is this really the formulation that is needed in the proofs? *)
  Lemma cpo_order (x y : G) (p : Path i o) :
    x \in cp i o -> y \in cp i o -> irred p -> cpo x y = (idx p x <= idx p y).
  Proof.
    move => /cpP' cp_x /cpP' cp_y Ip. rewrite /cpo.
    wlog suff Hyp : p Ip / x <[p] y -> forall q : Path i o, irred q -> ~ y <[q] x.
    { apply/idP/idP; rewrite leq_eqVlt; case/orP=> [/eqP|x_lt_y].
      + by move=> /(idx_inj (cp_x the_uPath))->.
      + by rewrite leqNgt; apply/negP; apply: Hyp the_uPathP _ _ _.
      + by move=> /(idx_inj (cp_x p))->.
      + by rewrite leqNgt; apply/negP; apply: Hyp x_lt_y _ the_uPathP.
    }
    case/(three_way_split Ip (cp_x p) (cp_y p)) => [p1][_][p3][_ xNp3 yNp1].
    move=> q Iq.
    case/(three_way_split Iq (cp_y q) (cp_x q)) => [q1][_][q3][_ yNq3 xNq1].
    have := cp_x (pcat q1 p3); apply/negP.
    by rewrite mem_pcat negb_or; apply/andP.
  Qed.

  Lemma cpo_min x : cpo i x.
  Proof. by rewrite /cpo idx_start. Qed.

  Lemma cpo_max x : x \in cp i o -> cpo x o.
  Proof.
    move=> /cpP'/(_ the_uPath) x_path.
    rewrite /cpo idx_end; [ exact: idx_mem | exact: the_uPathP ].
  Qed.

  Lemma cpo_cp x y : x \in cp i o -> y \in cp i o -> cpo x y ->
    forall z, z \in cp x y = [&& (z \in cp i o), cpo x z & cpo z y].
  Proof.
    move=> x_cpio y_cpio.
    have [x_path y_path] : x \in the_uPath /\ y \in the_uPath.
    { by split; move: the_uPath; apply/cpP'. }
    rewrite {1}/cpo leq_eqVlt =>/orP[/eqP/(idx_inj x_path)<- z | x_lt_y].
    { rewrite cpxx inE eq_sym.
      apply/eqP/andP; last by case; exact: cpo_antisym.
      by move=><-; split; last rewrite /cpo. }
    case: (three_way_split the_uPathP x_path y_path x_lt_y)
      => [p1] [p2] [p3] [eq_path xNp3 yNp1].
    move: the_uPathP; rewrite eq_path !irred_cat =>/and3P[Ip1]/and3P[Ip2 Ip3].
    move=> disj23 disj123.
    move=> z; apply/idP/andP.
    + move=> z_cpxy. have z_cpio := cp_widen x_cpio y_cpio z_cpxy.
      split=>//. move: z_cpio => /cpP'/(_ the_uPath) z_path.
      move: z_cpxy => /cpP'/(_ p2) z_p2. rewrite /cpo.
      case: (altP (z =P x)) => [->|zNx]; first by rewrite leqnn (ltnW x_lt_y).
      apply/andP; split; last first.
      - rewrite eq_path idx_catR ?idx_catL ?nodes_end ?idx_end ?idx_mem //.
        have : z \in pcat p2 p3 by rewrite mem_pcat z_p2.
        by rewrite mem_path inE (negbTE zNx) => /(disjointFl disj123)->.
      - rewrite eq_path leq_eqVlt. apply/orP; right.
        rewrite -idxR -?eq_path ?the_uPathP //. apply: in_tail zNx _.
        by rewrite mem_pcat z_p2.
    + case=> z_cpio /andP[x_le_z z_le_y]. apply/cpP' => p.
      have /cpP'/(_ (pcat p1 (pcat p p3))) := z_cpio.
      case (altP (z =P x)) => [-> _ | zNx]; first exact: nodes_start.
      case (altP (z =P y)) => [-> _ | zNy]; first exact: nodes_end.
      have zNp1 : z \notin p1.
      { apply: contraNN zNx => z_p1. apply/eqP; apply: cpo_antisym => //.
        rewrite x_le_z andbT /cpo eq_path idx_catL ?nodes_end // idx_end //.
        exact: idx_mem. }
      rewrite mem_pcat -implyNb => /implyP/(_ zNp1).
      rewrite mem_pcat => /orP[// | /(in_tail zNy) z_p3].
      exfalso; have := zNy; apply/negP; rewrite negbK.
      apply/eqP; apply: cpo_antisym => //.
      rewrite z_le_y /=/cpo eq_path idx_catR // leq_eqVlt.
      by rewrite -idxR ?irred_cat ?nodesE/= ?inE ?mem_cat ?z_p3.
  Qed.

End CheckpointOrder.

Arguments ncp0 [G] G_conn [U] x p : rename.

Lemma CP_treeI (G : sgraph) (U : {set G}) :
  connected [set: G] ->
  (~ exists x y z : CP_ U, [/\ x -- y, y -- z & z -- x]) -> is_tree (CP_ U).
Proof.
  (* CP_ U is connected because G is. *)
  move/CP_connected => /(_ U)/connectedTE CP_conn.
  (* Since is_tree is decidable, prove the contraposition:
   *    if CP_U is not a tree then it has a triangle. *)
  case: (boolP (is_tree _)) => // CP_not_tree H; exfalso; apply: H.
  (* There are two distinct parallel paths in CP_ U ... *)
  move: connected_not_tree => /(_ _ CP_conn CP_not_tree) [x [y [p' [q' []]]]].
  (* ... and their first edge is different. *)
  wlog [z1 [z2 [p [q [-> -> z1Nz2]]]]] : x y p' q'
    / exists z1 z2 p q, [/\ p' = z1 :: p, q' = z2 :: q & z1 != z2].
    move=> base_case.
    elim: p' x y q' => [|z1 p IHp'] x y q'.
    (* If one is empty then x = y and so is the other. Contradiction ! *)
      by move=> /upathW/spath_nil<- /upath_nil->.
    case: q' => [|z2 q] Uzp.
      by move=> /upathW/spath_nil pq; move: Uzp; rewrite pq => /upath_nil.
    move=> Uzq.
    (* If z1 != z2, the goal is done. *)
    case: (altP (z1 =P z2)) => [eq_z | z1Nz2]; last first.
      by apply: base_case Uzp Uzq; do 4 eexists.
    (* Otherwise, use the induction hypothesis. *)
    move: eq_z Uzp Uzq => <- /upath_consE[_ _ Up] /upath_consE[_ _ Uq].
    rewrite eqseq_cons eqxx [~~ _]/=.
    exact: IHp' z1 y q Up Uq.
  (* The vertices of the triangle are z1, z2 and x. Two of the edges are obvious. *)
  move=> {p' q'} /upath_consE[x_z1 xNzp /upathW ps] /upath_consE[z2_x xNzq /upathW qs] _.
  rewrite sg_sym in z2_x; do 3 eexists; split; try eassumption.
  (* Both p and q avoid x. Package them... *)
  move: xNzp xNzq.
  rewrite -(mem_path (Sub p ps)) -(mem_path (Sub q qs)).
  move: (Sub p ps) (Sub q qs); rewrite ![sub_sort _]/= => {p q ps qs} p q xNp xNq.
  (* ...and concatenate them into a path avoiding x. *)
  have {p q xNp xNq} [p /negP xNp] : exists p : Path z1 z2, x \notin p.
    by exists (pcat p (prev q)); rewrite mem_pcat negb_or mem_prev.
  (* Remove the cycles in that path, to get an irredundant path from z1 to z2
   * avoiding x. *)
  have {p xNp} [p Ip xNp] : exists2 p : Path z1 z2, irred p & x \notin p.
    have [q qSp Iq] := uncycle p; exists q => //.
    by apply/negP => /qSp.
  (* Unpack it. *)
  case: p Ip xNp => p pz12.
  rewrite /irred in_collective nodesE [negb _]/= [_ :: _]/=.
  move: pz12 => /andP[pth /eqP pz2] Uzp xNzp.
  (* To get an irredundant cycle, prepend x and z1. *)
  have {Uzp xNzp} Uxzp : uniq (x :: z1 :: p).
    by move: xNzp Uzp => /= -> /=.
  have {pth Uxzp} /induced_ucycle /link_cycle : ucycle sedge [:: x, z1 & p].
    rewrite /ucycle {}Uxzp andbT (cycle_path z2).
    set sedge := sedge (* prevent /= from expanding (@sedge (CP_ U)) *).
    by rewrite /= {}/sedge x_z1 pth pz2 z2_x.
  (* In the link graph, that cycle gives a clique which contains z1 and z2. *)
  move=> /(_ _ _ _ _ z1Nz2). apply; rewrite inE; apply: map_f.
    by rewrite !inE eqxx.
  by rewrite inE -pz2 mem_last.
Qed.
