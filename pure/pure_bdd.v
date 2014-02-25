(** This file defines a library of states implemented in Coq, by making
a deep-embedding of the memory as finite maps, and using integers as
surrogates of pointers. *)

Require Import common ZArith.

Ltac sep :=
  repeat match goal with
             |- (_ * _)%type => constructor
           | |- (_ /\ _) => constructor
         end.

Inductive expr := | F | T | N : positive -> expr.

Notation var := positive.

Definition node := (expr * var * expr)%type.

(** Equality test on BDD.  *)
Definition eqb a b :=
  match a,b with
    | T,T => true
    | F,F => true
    | N x, N y => (x =? y)%positive
    | _, _ => false
  end.

Lemma eqb_iff e f : eqb e f = true <-> e = f.
Proof.
  destruct e; destruct f; simpl; try (split; (now trivial || discriminate)).
  rewrite Pos.eqb_eq. split; congruence.
Qed.

Definition expr_compare x y :=
  match x,y with
    | F , F => Eq
    | T , T => Eq
    | N x, N y => Pos.compare x y
    | F, _ =>  Lt
    | _, F => Gt
    | T, _ =>  Lt
    | _, T => Gt
  end.

Definition node_eqb (a b: node) :=
  match a with
    | (xa,ya,za) =>
        match b with
          | (xb,yb,zb) => (eqb xa xb && (Pos.eqb ya yb) && eqb za zb)%bool
        end
  end.



(** Rather painful proof of the fact that nodes form an ordered type *)
Module N <: OrderedTypeAlt.
  Definition t := node.
  Import Compare.
  Definition compare (x y : t) :=
    lex  (expr_compare (snd x) (snd y))
         (
           (fun (x: expr * var) (y : expr * var) =>
              let (r1,v1) := x in
              let (r2,v2) := y in
              lex (expr_compare r1 r2) (Pos.compare v1 v2)) (fst x) (fst y)).


  Lemma expr_compare_sym x y : expr_compare x y = CompOpp (expr_compare y x).
  Proof.
    unfold expr_compare; destruct x; destruct y; simpl; trivial.  eauto with compare.
  Qed.

  Lemma expr_compare_trans c x y z: expr_compare x y = c -> expr_compare y z = c -> expr_compare x z = c.
  Proof.
    unfold expr_compare; destruct x; destruct y; destruct z; simpl; trivial || (try (intros; subst; discriminate)); eauto with compare.
  Qed.


  Hint Resolve expr_compare_trans expr_compare_sym.

  Lemma compare_sym x y :compare y x = CompOpp (compare x y).
  Proof.
    intros.
    destruct x as [[l1 v1] r1]; destruct y as [ [l2 v2] r2]; simpl.
    apply lex_sym; eauto.
    intros [? ?] [? ?]. apply lex_sym; eauto with compare.
  Qed.

  Lemma compare_trans c x y z : (compare x y) = c -> (compare y z) = c -> (compare x z) = c.
  Proof.
    apply lex_trans; eauto.
    clear. intros c [? ?] [? ?] [? ?].  apply lex_trans; eauto with compare.
  Qed.

  Lemma expr_compare_refl e : expr_compare e e = Eq.
  Proof.
    destruct e; trivial.
    simpl.
    apply Pos.compare_refl.
  Qed.

  Lemma compare_refl n : compare n n = Eq.
  Proof.
    clear.
    destruct n as [[e1 v] e2]. unfold N.compare.
    rewrite expr_compare_refl; simpl.
    rewrite expr_compare_refl; simpl.
    rewrite Pos.compare_eq_iff. reflexivity.
  Qed.

  Lemma compare_eq_iff n1 n2 : N.compare n1 n2 = Eq <-> n1 = n2.
  Proof.
    split; intros.
    unfold compare in H.
    destruct (expr_compare (snd n1) (snd n2)) eqn:H3; try discriminate.
    destruct n1 as [[a b] c]; destruct n2 as [[a' b'] c']. simpl in H.
    destruct (expr_compare a a') eqn: H1; try discriminate.
    rewrite Pos.compare_eq_iff in H. subst.
    simpl in H3.
    Lemma expr_compare_eq a b: expr_compare a b = Eq -> a = b.
    Proof.
      destruct a ; destruct b; simpl; intros; subst;  try discriminate; try reflexivity.
      rewrite Pos.compare_eq_iff in H. subst. auto.
    Qed.
    apply expr_compare_eq in H1. apply expr_compare_eq in H3. subst; reflexivity.
    subst. apply compare_refl.
  Qed.
End N.
Module NO := OrderedType_from_Alt(N).

Module NMap := FMapAVL.Make (NO).
Module NMapFacts := FMapFacts.Facts (NMap).

Notation pmap := PMap.t.
Notation nmap := NMap.t.

Notation memo1 := (PMap.t expr).
Notation memo2 := (PPMap.t expr).

Module Memo2.
  Definition find (x y: positive) (t : memo2) : option expr :=
    let a := Pos.min x y in
    let b := Pos.max x y in
    PPMap.find (a,b) t.

  Definition add (x y: positive) n (t : memo2)  :=
    let a := Pos.min x y in
    let b := Pos.max x y in
    PPMap.add (a,b) n t.

End Memo2.


(** We are now ready to start speaking about hashconsing state and memoization state.

    States are built from two components: a part that deals with
    hash-consing, and a part that deals with the memoization of the
    various operations.

    Regarding the hashconsing part, we define it as follows:
    [graph] is a map from indexes to nodes;
    [hmap] is used to hash-cons nodes;
    [next] is the index of the next usable node.

    All the nodes below than [next] have a value: this means that the
    graph underlying [hmap] is acyclic, yet we do not express that
    fact (this maybe a good idea to express that fact in the
    invariant.)

    The memoization part is made of partial maps from pointers to
    expressions.

*)

Record hashcons := mk_hcons
  {
    graph : pmap node;
    hmap : nmap positive;
    next : positive
  }.

(* memoization part *)

Record memo :=
  mk_memo
    {
      mand : memo2;
      mor  : memo2;
      mxor : memo2;
      mneg : memo1
    }.

Record state :=
  mk_state
    {
      to_hashcons:> hashcons;
      to_memo:> memo
    }.

Definition empty :=
    mk_state
      {|
        graph := PMap.empty _;
        hmap := NMap.empty _;
        next := 1
      |}
      {|
        mand := PPMap.empty _;
        mor  := PPMap.empty _;
        mxor := PPMap.empty _;
        mneg := PMap.empty _
      |}.

Inductive wf_expr st : var -> expr -> Prop :=
| wfe_T : forall v, wf_expr st v T
| wfe_F : forall v, wf_expr st v F
| wfe_N : forall x l v h v', PMap.find x (graph st) = Some (l, v, h) ->
                             (v < v')%positive ->
                             wf_expr st v' (N x).

Hint Constructors wf_expr.

Lemma wf_expr_lt:
  forall b v v' e, wf_expr b v e -> (v < v')%positive -> wf_expr b v' e.
Proof.
  destruct 1; econstructor. eauto. zify; omega.
Qed.

Record wf_hashcons (b : hashcons) : Prop :=
  {
    wf_bijection : forall p n, NMap.find n (hmap b) = Some p <->
                               PMap.find p (graph b) = Some n;
    wf_expr_lt_next : forall p v, wf_expr b v (N p) -> (p < next b)%positive;
    wf_map_wf_expr_l : forall p x v y,
                       PMap.find p (graph b) = Some (x, v, y) -> wf_expr b v x;
    wf_map_wf_expr_h : forall p x v y,
                       PMap.find p (graph b) = Some (x, v, y) -> wf_expr b v y;
    wf_reduced : forall p l v h,
                 PMap.find p (graph b) = Some (l, v, h) ->
                 l <> h
  }.

Hint Resolve <- wf_bijection.
Hint Resolve -> wf_bijection.
Hint Resolve wf_map_wf_expr_h wf_map_wf_expr_l wf_expr_lt_next.

Notation find env v := (PositiveMap.find v env).

Inductive value env (st : hashcons) : expr -> bool -> Prop :=
| value_T : value env st T true
| value_F : value env st F false
| value_N : forall (p : positive) (l : expr) (v : var) (h : expr),
               PMap.find p (graph st) = Some (l, v, h) ->
               forall (vv: bool), find env v = Some vv ->
               forall vhl : bool, value env st (if vv then h else l) vhl ->
                                  value env st (N p) vhl.
Hint Constructors value.

Lemma wf_expr_value:
  forall env st e v, value env st e v ->
                      exists v, wf_expr st v e.
Proof.
  destruct 1; try (exists 1%positive; now eauto).
  exists (v+1)%positive.
  econstructor. eauto.
  zify; omega.
Qed.

Definition node_opb_rel opb st na nb res st' :=
  forall env va vb, value env st na va ->
               value env st nb vb ->
               value env st' res (opb va vb).

Record wf_memo2 (b: hashcons) (m: memo2) (opb : bool -> bool -> bool):=
  {
    wf_memo2_find_wf_res : forall x y v e,
                             Memo2.find x y m = Some e ->
                             wf_expr b v (N x) -> wf_expr b v (N y) -> wf_expr b v e;
    wf_memo2_find_wf : forall x y e, Memo2.find x y m = Some e ->
                                     exists v, wf_expr b v (N x) /\ wf_expr b v (N y);
    wf_memo2_find_sem : forall x y res, Memo2.find x y m = Some res ->
                                 node_opb_rel opb b (N x) (N y) res b
  }.

Hint Resolve
     wf_memo2_find_wf_res
     wf_memo2_find_wf
     wf_memo2_find_sem.

Record wf_memo_neg (b: hashcons) (m: memo1):=
  {
    wf_memo_neg_find_wf_res : forall x v e, PMap.find x m = Some e ->
                                            wf_expr b v (N x) -> wf_expr b v e;
    wf_memo_neg_find_wf : forall na e, PMap.find na m = Some e ->
                                       exists v, wf_expr b v (N na);
    wf_memo_neg_find_sem : forall na res, PMap.find na m = Some res ->
                               forall env va, value env b (N na) va ->
                                         value env b res (Datatypes.negb va)
  }.

Hint Resolve
     wf_memo_neg_find_wf_res
     wf_memo_neg_find_wf
     wf_memo_neg_find_sem.

Record wf_memo (b: state) :=
  {
    wf_memo_mand: wf_memo2 b (mand b) Datatypes.andb;
    wf_memo_mor : wf_memo2 b  (mor b) Datatypes.orb;
    wf_memo_mxor: wf_memo2 b  (mxor b) Datatypes.xorb;
    wf_memo_mneg: wf_memo_neg b  (mneg b)
  }.

Record wf_st (b:state) : Prop :=
  {
    wf_st_hashcons : wf_hashcons b;
    wf_st_memo : wf_memo b
  }.

Hint Resolve wf_st_hashcons wf_st_memo.

(** The evolution of sts is monotonic  *)
Record incr (b1 b2 : hashcons) : Prop := {
  incr_lt: (next b1 <= next b2)%positive;
  incr_find:
      forall p x, PMap.find p (graph b1) = Some x -> PMap.find p (graph b2) = Some x
}.

Hint Resolve incr_lt incr_find.
Hint Constructors incr.

Lemma incr_refl st : incr st st.
Proof.
  constructor. reflexivity. eauto.
Qed.

Hint Resolve incr_refl.

Lemma incr_trans  a b c : incr a b -> incr b c -> incr a c.
Proof.
  destruct 1, 1. constructor.
  zify; omega.
  eauto.
Qed.

Lemma wf_expr_incr:
  forall b1 b2 v e,
    wf_expr b1 v e ->
    incr b1 b2 ->
    wf_expr b2 v e.
Proof.
  destruct 1; eauto.
Qed.

Hint Resolve wf_expr_incr.

Definition wbo {alpha} (st:state) f P :=
  forall (st': state) (out:alpha),
    f st = Some (out, st') ->
    wf_st st' /\ incr st st' /\ P out st'.

Lemma wbo_wf alpha:
  forall st f P,
  forall (st': state) (out:alpha),
    f st = Some (out, st') ->
    wbo st f P ->
    wf_st st'.
Proof.
  intros. edestruct H0; eauto.
Qed.

Hint Resolve wbo_wf.

Lemma wbo_incr alpha:
  forall st f P,
  forall (st': state) (out:alpha),
    f st = Some (out, st') ->
    wbo st f P ->
    forall st'', incr st' st'' ->
                  incr st st''.
Proof.
  intros. edestruct H0 as [_ []]; eauto using incr_trans.
Qed.

Hint Resolve wbo_incr.

Lemma wbo_bind alpha beta:
  forall st f g P Q,
    wbo st f P ->
    (forall (a:alpha) (st':state),
       P a st' -> incr st st' -> wf_st st' -> f st = Some (a, st') -> wbo st' (g a) Q) ->
    wbo (alpha:=beta) st (fun st => do a, st' <- f st; g a st') Q.
Proof.
  unfold wbo.
  intros.
  destruct (f st) as [[]|].
  edestruct H as [? []]; eauto. edestruct H0 as [? []]; eauto.
  sep. auto. eapply incr_trans; eauto. auto.
  discriminate.
Qed.

Definition wb {alpha} (st:state) f := (wbo (alpha:=alpha) st (fun st => Some (f st))).

Lemma wb_ret alpha:
  forall (a:alpha) (st:state) P,
    wf_st st -> (P a st:Prop) ->
    wb st (fun st : state => (a, st)) P.
Proof.
  unfold wb, wbo.
  intros. inject H1; eauto.
Qed.

Hint Resolve wb_ret.

Lemma wb_wf alpha:
  forall st f P,
  forall (st': state) (out:alpha),
    f st = (out, st') ->
    wb st f P ->
    wf_st st'.
Proof.
  intros. eapply wbo_wf; eauto. simpl. f_equal. eauto.
Qed.

Hint Resolve wb_wf.

Lemma wb_incr alpha:
  forall st f P,
  forall (st': state) (out:alpha),
    f st = (out, st') ->
    wb st f P ->
    forall st'', incr st' st'' ->
                  incr st st''.
Proof.
  intros. eapply wbo_incr; eauto. simpl. f_equal. eauto.
Qed.

Hint Resolve wb_incr.

Lemma wb_bind alpha beta:
  forall st f g P Q,
    wb st f P ->
    (forall (a:alpha) (st':state),
       P a st' -> incr st st' -> wf_st st' -> f st = (a, st') -> wb st' (g a) Q) ->
    wb (alpha:=beta) st (fun st => let (a, st') := f st in g a st') Q.
Proof.
  unfold wb, wbo.
  intros.
  destruct (f st).
  edestruct H as [? []]; eauto. edestruct H0 as [? []]; eauto.
  sep. auto. eapply incr_trans; eauto. auto.
Qed.

Definition upd u (b: state) :=
  ((next b), mk_state
    {|
      graph := PMap.add (next b) u (graph b);
      hmap := NMap.add u (next b) (hmap b);
      next := (next b + 1)
    |}
    b).

Lemma value_incr:
  forall env st x vx, value env st x vx ->
  forall st', incr st st' ->
               value env st' x vx.
Proof.
  induction 1; auto.
  econstructor; eauto.
Qed.
Hint Resolve value_incr.

Lemma value_rcni: forall env e va st',
                      value env st' e va ->
                      forall st v,
                      wf_expr st v e ->
                      wf_hashcons st ->
                      wf_hashcons st' ->
                      incr st st' ->
                      value env st  e va.
Proof.
  induction 1; eauto.
  intros st v0 Hwfexpr Hst Hst' Hincr.
  inversion Hwfexpr. assert (H3':=H3). eapply incr_find in H3'; eauto.
  rewrite H in H3'. inject H3'.
  econstructor; eauto.
  eapply IHvalue; eauto.
  destruct vv; eauto.
Qed.

Hint Resolve value_rcni.

Lemma wf_expr_rcni: forall st st' e v v',
                      wf_expr st v e ->
                      wf_expr st' v' e ->
                      wf_hashcons st ->
                      wf_hashcons st' ->
                      incr st st' ->
                      wf_expr st v' e.
Proof.
  intros st st' e v v' Hv Hv' Hwf Hwf' Hincr.
  destruct Hv; inversion Hv'; econstructor. eauto.
  eapply incr_find in H; eauto.
  congruence.
Qed.

Lemma incr_wf_memo2 :
  forall opb hc1 hc2 memo,
    wf_hashcons hc1 ->
    wf_hashcons hc2 ->
    incr hc1 hc2 ->
    wf_memo2 hc1 memo opb ->
    wf_memo2 hc2 memo opb.
Proof.
  intros opb hc1 hc2 memo Hwf1 Hwf2 Hincr Hwfm.
  constructor.
  - intros.
    assert (Hwf_expr1:exists v, wf_expr hc1 v (N x) /\ wf_expr hc1 v (N y)) by eauto.
    destruct Hwf_expr1 as [v' [Hwfx Hwfy]].
    eauto using wf_expr_rcni.
  - destruct Hwfm. intros.  edestruct wf_memo2_find_wf0 as [v []]; eauto.
  - destruct Hwfm. intros.
    edestruct wf_memo2_find_wf0 as [v []]; eauto.
    unfold node_opb_rel in *; intros.
    eapply value_incr; eauto.
Qed.

Lemma incr_wf_memo_neg :
  forall hc1 hc2 memo,
    wf_hashcons hc1 ->
    wf_hashcons hc2 ->
    incr hc1 hc2 ->
    wf_memo_neg hc1 memo ->
    wf_memo_neg hc2 memo.
Proof.
  intros  hc1 hc2 memo Hwf1 Hwf2 Hincr Hwfm.
  constructor.
  - intros.
    assert (Hwf_expr1:exists v, wf_expr hc1 v (N x)) by eauto.
    destruct Hwf_expr1 as [v' Hwf_expr1].
    eauto using wf_expr_rcni.
  - destruct Hwfm. intros. edestruct wf_memo_neg_find_wf0; eauto.
  - destruct Hwfm.  intros.
    edestruct wf_memo_neg_find_wf0; eauto.
Qed.

Lemma incr_wf_memo :
  forall hc1 hc2 memo,
    wf_hashcons hc1 ->
    wf_hashcons hc2 ->
    incr hc1 hc2 ->
    wf_memo (mk_state hc1 memo) ->
    wf_memo (mk_state hc2 memo).
Proof.
  intros hc1 hc2 memo Hwf1 Hwf2 Hincr Hmemo.
  inversion Hmemo.
  constructor; eauto using incr_wf_memo2.
  constructor; eauto using incr_wf_memo_neg.
Qed.

Lemma wb_upd : forall (st:state) l v h,
                 wf_st st ->
                 wf_expr st v l ->
                 wf_expr st v h ->
                 NMap.find (l, v, h) (hmap st) = None ->
                 l <> h ->
                 wb st (upd (l, v, h)) (fun p st' =>
                   PMap.find p (graph st') = Some (l, v, h)).
Proof.
  unfold upd. intros st l v h Hst Hl Hh HNone Hreduced st' n Heq.
  inject Heq.
  match goal with |- _ /\ ?P /\ _ => assert (Hincr:P) end.
  { constructor. simpl. zify; omega.
    simpl. intros p x Hfind. rewrite PMap.gso. eauto.
    assert (p < next st)%positive.
    destruct x as [[l' v'] h']. apply wf_expr_lt_next with (v:=Psucc v'). auto.
    econstructor. eauto. zify; omega.
    zify; omega.
  }
  match goal with |- _ ?st' /\ _ /\ _ => assert (Hwf':wf_hashcons st') end.
  { constructor; simpl.
    - intros p n.
      rewrite NMapFacts.add_o. rewrite PMapFacts.add_o.
      destruct (NMap.E.eq_dec (l, v, h) n) as [Hn | Hn]; rewrite N.compare_eq_iff in Hn.
      + subst. destruct (PMap.E.eq_dec (next st) p). subst. tauto.
        rewrite <- wf_bijection, HNone by auto. split; congruence.
      + rewrite wf_bijection by auto.
        destruct (PMap.E.eq_dec (next st) p).
        * split. intro.
          assert (p < next st)%positive.
          destruct n as [[l' v'] h']. apply wf_expr_lt_next with (v:=Psucc v'). auto.
          econstructor. eauto. zify; omega.
          exfalso. zify; omega.
          congruence.
        * tauto.
    - intros p v' Hwf. destruct (Pos.eq_dec p (next st)).
      + zify; omega.
      + inversion Hwf. simpl in H0. rewrite PMap.gso in H0 by trivial.
        assert (p < next st)%positive by eauto.
        zify; omega.
    - intros p x v' y Hfind.
      destruct (Pos.eq_dec p (next st)).
      + subst. rewrite PMap.gss in Hfind. inject Hfind.
        eapply wf_expr_incr; eauto.
      + rewrite PMap.gso in Hfind by eauto.
        eapply wf_expr_incr; eauto.
    - intros p x v' y Hfind.
      destruct (Pos.eq_dec p (next st)).
      + subst. rewrite PMap.gss in Hfind. inject Hfind.
        eapply wf_expr_incr; eauto.
      + rewrite PMap.gso in Hfind by eauto.
        eapply wf_expr_incr; eauto.
    - intros. rewrite PMapFacts.add_o in H.
      destruct (PMap.E.eq_dec (next st) p).
      + inject H. auto.
      + eapply wf_reduced; eauto.
  }
  sep; trivial. constructor; trivial.
  destruct st; simpl; eauto using incr_wf_memo.
  simpl. apply PMap.gss.
Qed.

(** [mk_node l v h st] creates a node corresponding to the triple [l,v,h] if needed. *)

Definition mk_node (l : expr) (v: var) (h : expr) (st: state) :=
  if eqb l  h then (l,st)
  else
    match NMap.find (l,v,h) (hmap st) with
        | Some x => (N x, st)
        | None => let (x, st) := upd (l,v,h) st in (N x, st)
     end.

Definition mk_node_sem l v h st res st' :=
  (forall v', (v < v')%positive -> wf_expr st' v' res )
  /\ (forall env vhl r, find env v = Some r ->
                        value env st (if r then h else l) vhl ->
                        value env st' res vhl).

Lemma value_inj st env x vx:
  value env st x vx ->
  forall vx' , value env st x vx' ->
          vx = vx'.
Proof.
  induction 1.
  inversion 1. reflexivity.
  inversion 1; reflexivity.
  intros v2 Hv2.
  inversion Hv2.
  simpl in *. subst.
  rewrite H in H3. inject H3.
  rewrite H4 in H0. inject H0.
  eauto.
Qed.

Lemma wb_mk_node :
  forall l v h (st:state),
    wf_st st ->
    wf_expr st v l -> wf_expr st v h ->
    wb st (mk_node l v h) (mk_node_sem l v h st).
Proof.
  intros l v h st Hst Hwfl Hwfh.
  unfold mk_node.
  destruct (eqb l h)  eqn:Heq.
  - intros st' l' EQ.
    inject EQ. unfold mk_node_sem.  sep; eauto 8 using wf_expr_lt.
    rewrite eqb_iff in Heq. subst. intros.
    destruct r; eauto.
  - intros st' res EQ.
    destruct (NMap.find (elt:=positive) (l, v, h) (hmap st)) eqn:Hfind.
    + inject EQ.
      sep; eauto.
      unfold mk_node_sem.
      split; eauto.
    + destruct (upd (l, v, h) st) eqn:Hupd.
      inject EQ.
      edestruct (wb_upd st l v h) as [? []]; eauto.
      rewrite <- eqb_iff. congruence.
      f_equal; eauto.
      sep; eauto.
      unfold mk_node_sem.
      split; econstructor; eauto.
Qed.

Hint Resolve wb_mk_node.

Section t.
  Section operations.

    (** All the binary operations on the st follow the same
    structure. We define partial operations that use an explicit
    bound on the number of recursive calls, and fail if that number
    is not sufficent. We cannot easily use open-recursion and a
    common skeleton for these operations, as we would in OCaml
    (problem of termination), and this is the reason why the code is
    verbose.

    Note that we cannot esasily use Program or Function, because we use
    nested calls to the function we define (that is, the
    well-founded relation that terminates shall mention the fact
    that our sts are well-formed, and refinements of each other)*)

    Section combinator.
      Variable fx : expr -> state -> option (expr * state).
      Variable tx : expr -> state -> option (expr * state).
      Variable memo_get : positive -> positive -> state -> option expr.
      Variable memo_update : positive -> positive -> expr -> state -> (unit * state).
      Variable opb : bool -> bool -> bool.

      Definition combinator_sem v na nb st res st' :=
        wf_expr st' v res
        /\  node_opb_rel opb st na nb res st'.


      Hypothesis opb_sym : forall x y, opb x y = opb y x.

      Hypothesis Hfx1: forall v a (st:state), wf_expr st v a -> wf_st st -> wbo st (fx a) (combinator_sem v a F st).
      Hypothesis Htx1: forall v a (st:state), wf_expr st v a -> wf_st st -> wbo st (tx a) (combinator_sem v a T st).

      Hypothesis Hmemo_update1 : forall (st:state) v a b res,
                                   wf_expr st v (N a) ->
                                   wf_expr st v (N b) ->
                                   wf_st st ->
                                   (forall v',
                                      wf_expr st v' (N a) ->
                                      wf_expr st v' (N b) ->
                                      wf_expr st v' res) ->
                                   node_opb_rel opb st (N a) (N b) res st ->
                                   wb st (memo_update a b res) (fun _ _ => True).

      Hypothesis Hmemo_get :
        forall v a b st e, memo_get a b st = Some e ->
                            wf_expr st v (N a) -> wf_expr st v (N b) ->
                            wf_st st ->
                            (wf_expr st v e /\ node_opb_rel opb st (N a) (N b) e st).

      Definition memo_node a b l v h st :=
        let (res, st) := mk_node l v h st in
        let (_, st) := memo_update a b res st in
        (res,st).

      Lemma wb_memo_node :
        forall v' (a b:positive) l v h (st:state),
          wf_st st ->
          wf_expr st v h ->
          wf_expr st v l ->
          (forall v'', wf_expr st v'' (N a) -> wf_expr st v'' (N b) ->
                       (v < v'')%positive) ->
          wf_expr st v' (N a) ->
          wf_expr st v' (N b) ->
          (forall env ,
           forall va vb,
             value env st (N a) va ->
             value env st (N b) vb ->
             exists r,
               find env v = Some r /\
               value env st (if r then h else l) (opb va vb)) ->
          wb st (memo_node a b l v h) (combinator_sem v' (N a) (N b) st).
      Proof.
        intros v' a b l v h st Hwf Hh Hl Hlt Ha Hb Z.
        unfold memo_node.
        eapply wb_bind. eapply wb_mk_node; eauto.
        simpl.
        intros res st' [H1 H2] Hincr Hwf' Heq.

        assert (HH : forall (st0  st'': state),
                       incr st0 st' ->
                       incr st st0 ->
                       incr st' st'' ->
                       wf_st st0 ->
                       wf_st st'' ->
                       node_opb_rel opb st0 (N a) (N b) res st'').
        {
          intros; unfold node_opb_rel. intros  env va vb Hva Hvb.
          specialize (Z env va vb).
          eapply value_rcni in Hva; eauto.
          eapply value_rcni in Hvb; eauto.
          specialize (Z Hva Hvb).
          destruct Z  as [r [Hr Hval]].
          eauto.
        }
        eapply wb_bind. eapply Hmemo_update1; eauto.

        intros v'' Ha' Hb'.
        eapply wf_expr_rcni with (st:=st) in Ha'; eauto.
        eapply wf_expr_rcni with (st:=st) in Hb'; eauto.

        {
          simpl.
          intros [] st'' _ Hincr'' Hwf'' H'.
          eapply wb_ret; eauto.
          unfold combinator_sem. split; eauto.
        }
      Qed.

      Fixpoint combinator depth a b st :=
        match depth with
        | 0 => None
        | S depth =>
          match a,b with
            | F, _ => fx b st
            | _, F => fx a st
            | T, _ => tx b st
            | _, T => tx a st
            | N na, N nb =>
              match memo_get na nb st with
                | Some p => Some (p,st)
                | None =>
                  do nodea <- PMap.find na (graph st);
                  do nodeb <- PMap.find nb (graph st);
                  let '(l1,v1,h1) := nodea in
                  let '(l2,v2,h2) := nodeb in
                  match Pos.compare v1  v2 with
                    | Eq =>
                      do x, st <- combinator depth l1 l2 st;
                      do y, st <- combinator depth h1 h2 st;
                      Some (memo_node na nb x v1 y st)
                    | Gt =>
                      do x, st <- combinator depth l1 b st;
                      do y, st <- combinator depth h1 b st;
                      Some (memo_node na nb x v1 y st)
                    | Lt =>
                      do x, st <- combinator depth a l2 st;
                      do y, st <- combinator depth a h2 st;
                      Some (memo_node na nb x v2 y st)
                  end
              end
          end
        end.

      Lemma combinator_sem_comm: forall st m a b v,
                                   wbo st m (combinator_sem v a b st) ->
                                   wbo st m (combinator_sem v b a st).
      Proof.
        intros.
        unfold wbo, combinator_sem, node_opb_rel in *.
        intros.  specialize (H st' out H0).
        setoid_rewrite opb_sym.
        intuition.
      Qed.

      Lemma combinator_sem_incr : forall (st st': state) m v a b,
                                    wbo st' m (combinator_sem v a b st') ->
                                    incr st st' ->
                                    wbo st' m (combinator_sem v a b st).
      Proof.
        intros.
        unfold wbo, combinator_sem, node_opb_rel in *.
        intros.  specialize (H st'0 out H1).
        intuition.
        eauto 6 using value_incr.
      Qed.

      Lemma pmap_value_inversion : forall (st: state ) na va l v h env,
                    PMap.find na (graph st) = Some (l,v,h) ->
                    value env st (N na) va ->
                    exists r,
                      find env v = Some r /\
                      value env st (if r then h else l) va.
      Proof.
        intros.
        inversion H0. subst.
        rewrite H in H2. inject H2.
        eauto.
      Qed.

      Remark combinator_sem_eauto v na nb st res (st' st'' : state):
        combinator_sem v na nb st res st' ->
        incr st' st'' ->
        wf_st st' ->
        wf_st st'' ->
        wf_expr st'' v res.
      Proof.
        intros [ H _].  intuition eauto.
      Qed.
      Hint Resolve combinator_sem_eauto.

      Lemma wbo_combinator :
        forall depth v a b st,
          wf_st st ->
          wf_expr st v a -> wf_expr st v b ->
          wbo st (combinator depth a b) (combinator_sem v a b st).
      Proof.
        induction depth.
        - unfold wbo. split; easy.
        - intros v [| |na] [| |nb] st Hst Ha Hb; simpl; eauto using combinator_sem_comm.
          {
            intros st' out EQ.
            destruct (memo_get na nb st) eqn:Hmemo.
            - inject EQ. sep;eauto.
              eapply Hmemo_get in Hmemo; eauto.
            - destruct (PMap.find na (graph st)) as [[[l1 v1] h1]|] eqn:Hna;
                destruct (PMap.find nb  (graph st)) as [[[l2 v2] h2]|] eqn:Hnb;
                try easy; simpl in EQ.
              destruct (Pos.compare_spec v1 v2).
              * subst.
                eapply wbo_bind with (Q := combinator_sem v (N na) (N nb) st) in EQ; eauto 6.
                simpl.
                intros; eapply wbo_bind. eauto 8.
                simpl; intros. eapply combinator_sem_incr; [| now eauto 7].
                assert (incr st st'1) by eauto using incr_trans.
                apply wb_memo_node;  eauto.

                intros v'' Ha' Hb'.
                inversion Ha'. apply incr_find with (b2:=st'1) in Hna; auto.
                congruence.

                intros.
                eapply pmap_value_inversion in Hna; eauto.
                eapply pmap_value_inversion in Hnb; eauto.
                destruct Hna as [ra [Hra Hva]].
                destruct Hnb as [rb [Hrb Hvb]].
                rewrite Hra in Hrb. inject Hrb.
                unfold combinator_sem, node_opb_rel in *.
                destruct rb; intuition eauto 10.
              * eapply wbo_bind with (Q := combinator_sem v (N na) (N nb) st) in EQ; eauto.
                simpl.
                intros; eapply wbo_bind. eauto 7.
                simpl; intros; eapply combinator_sem_incr; [| now eauto 6].
                assert (incr st st'1) by eauto using incr_trans.
                apply wb_memo_node;  eauto.

                intros v'' Ha' Hb'.
                inversion Hb'. apply incr_find with (b2:=st'1) in Hnb; auto.
                congruence.

                intros.
                eapply pmap_value_inversion in Hnb; eauto.
                destruct Hnb as [rb [Hrb Hvb]].
                unfold combinator_sem, node_opb_rel in *.

                destruct rb, H4, H0; eauto 10.
              * eapply wbo_bind with (Q := combinator_sem v (N na) (N nb) st) in EQ; eauto.
                simpl.
                intros; eapply wbo_bind. eauto 7.
                simpl; intros. eapply combinator_sem_incr; [| now eauto 6].

                assert (incr st st'1) by eauto using incr_trans.
                apply wb_memo_node;  eauto.

                intros v'' Ha' Hb'.
                inversion Ha'. apply incr_find with (b2:=st'1) in Hna; auto.
                congruence.

                intros.
                eapply pmap_value_inversion in Hna; eauto.
                destruct Hna as [ra  [Hra Hva]].
                unfold combinator_sem, node_opb_rel in *.

                destruct ra, H4, H0; eauto 10.
          }
      Qed.

    End combinator.


    Section memo_add.
      Variable opb : bool -> bool -> bool.
      Hypothesis opb_sym : forall x y, opb x y = opb y x.
      Variable tmemo : state -> memo2.
      Variable st : state.
      Variable Hwf : wf_hashcons st.
      Variable Hwfm : wf_memo2 st (tmemo st) opb.

      Lemma minmax_eq_inv:
        forall p1 p2 p3 p4, Pos.min p1 p2 = Pos.min p3 p4 ->
                            Pos.max p1 p2 = Pos.max p3 p4 ->
                            p1 = p3 /\ p2 = p4 \/ p1 = p4 /\ p2 = p3.
      Proof.
        intros.
        destruct (p1 <=? p2)%positive eqn:?; destruct (p3 <=? p4)%positive eqn:?;
          rewrite ?Pos.leb_le , ?Pos.leb_gt in *;
          repeat
            (try (rewrite ! Pos.max_r in * by (auto || zify; omega));
             try (rewrite ! Pos.min_l in * by (auto || zify; omega));
             try (rewrite ! Pos.max_l in * by (auto || zify; omega));
             try (rewrite ! Pos.min_r in * by (auto || zify; omega))); eauto.
      Qed.

      Lemma memo_add : forall a b v res ,
                         wf_expr st v (N a) ->
                         wf_expr st v (N b) ->
                         node_opb_rel opb st (N a) (N b) res st ->
                         (forall v',
                            wf_expr st v' (N a) ->
                            wf_expr st v' (N b) ->
                            wf_expr st v' res) ->
                         wf_memo2 st (Memo2.add a b res (tmemo st)) opb.
      Proof.
        intros na nb v res Hna Hnb Hres Hres'.
        constructor.
        - intros.
          unfold Memo2.find, Memo2.add in H.
          rewrite PPMapFacts.add_o in H.

          destruct (PPMap.E.eq_dec (Pos.min na nb, Pos.max na nb)
                                   (Pos.min x y, Pos.max x y)).
          + inject H.
            apply PP.reflect in e0. inject e0.
            edestruct minmax_eq_inv as [[]|[]]; eauto.
            subst; eauto.
            subst; eauto.
          + destruct Hwfm; eauto.
        - intros.
          unfold Memo2.find, Memo2.add in H.
          rewrite PPMapFacts.add_o in H.

          destruct (PPMap.E.eq_dec (Pos.min na nb, Pos.max na nb)
                                   (Pos.min x y, Pos.max x y)) as [H' | H'].
          + inject H.

            apply PP.reflect in H'. inject H'.
            edestruct minmax_eq_inv as [[]|[]]; eauto.
            subst; eauto. subst; eauto.
          + destruct Hwfm; eauto.

        - unfold node_opb_rel. intros.
          unfold Memo2.find, Memo2.add in H.
          rewrite PPMapFacts.add_o in H.
          destruct (PPMap.E.eq_dec (Pos.min na nb, Pos.max na nb)
                                   (Pos.min x y, Pos.max x y)).
          inject H.
          {
            apply PP.reflect in e. inject e.
            edestruct minmax_eq_inv as [[]|[]]; eauto.
            + subst. eauto.
            + subst. rewrite opb_sym; eauto.
          }
          eapply wf_memo2_find_sem in H; eauto.
      Qed.

      Lemma memo_find a b v e: Memo2.find a b (tmemo st) = Some e ->
                        wf_expr st v (N a) -> wf_expr st v (N b) ->
                        wf_expr st v e /\ node_opb_rel opb st (N a) (N b) e st.
      Proof.
        destruct e; eauto.
      Qed.
    End memo_add.



    Section mk_and.
      Definition update_and na nb res (st: state) :=
        (tt,
         mk_state
           st
           {| mand := Memo2.add na nb res (mand st);
              mor  := mor st;
              mxor  := mxor st;
              mneg  := mneg st
           |}).

      Definition mk_and :=
        combinator
          (fun x st => Some (F,st) )             (* F x *)
          (fun x st => Some (x,st) )             (* T x *)
          (fun a b st => Memo2.find a b (mand st))
          update_and.

      Theorem mk_and_correct depth v0 (st: state) a b :
        wf_st st ->
        wf_expr st v0 a -> wf_expr st v0 b ->
        forall res st', mk_and depth a b st = Some (res, st') ->
          wf_st st' /\ incr st st' /\
          wf_expr st' v0 res /\
          forall env va vb,
            value env st a va ->
            value env st b vb ->
            value env st' res (va && vb).
      Proof.
        intros Hwf ; intros.
        unfold mk_and in H1. eapply wbo_combinator; eauto.
        - apply Bool.andb_comm.
        - clear.
          intros v res st' hwf h.
          eapply wb_ret. eauto.
          repeat constructor. unfold node_opb_rel. intros. inversion H0; subst.
          rewrite Bool.andb_false_r. constructor.
        - clear.
          intros v res  st' hwf h.
          eapply wb_ret; eauto.
          repeat constructor; eauto.  unfold node_opb_rel. intros. inversion H0; subst.
          rewrite Bool.andb_true_r. eauto.
        - clear. intros.
          repeat intro. inject H4. simpl. intuition.
          destruct H1 as [? []].
          constructor; simpl; auto.
          constructor; simpl; eauto.
          eapply (memo_add Datatypes.andb Bool.andb_comm mand); eauto.
        - clear.  intros. eapply (memo_find _ mand); eauto using wf_st_memo, wf_memo_mand.
      Qed.

    End mk_and.

    Section mk_or.
      Definition update_or na nb res (st: state) :=
        (tt,
         mk_state
           st
           {| mand := mand st;
              mor  := Memo2.add na nb res (mor st);
              mxor  := mxor st;
              mneg := mneg st|}).

      Definition mk_or :=
        combinator
          (fun x st => Some (x,st) )             (* F x *)
          (fun x st => Some (T,st) )             (* T x *)
          (fun a b st => Memo2.find a b (mor st))
          update_or.

      Theorem mk_or_correct depth v0 (st: state)  a b :
        wf_st st ->
        wf_expr st v0 a -> wf_expr st v0 b ->
        forall res st', mk_or depth a b st = Some (res, st') ->
          wf_st st' /\ incr st st' /\
          wf_expr st' v0 res /\
          forall env va vb,
            value env st a va ->
            value env st b vb ->
            value env st' res (va || vb).
      Proof.
        intros Hwf ; intros.
        unfold mk_or in H1. eapply wbo_combinator; eauto.
        - apply Bool.orb_comm.
        - clear.
          intros v res  st' hwf h.
          eapply wb_ret; eauto.
          repeat constructor. eauto.
          unfold node_opb_rel. intros. inversion H0; subst.
          rewrite Bool.orb_false_r. eauto.
        - clear.
          intros v res  st' hwf h.
          eapply wb_ret; eauto.
          repeat constructor; eauto.  unfold node_opb_rel. intros. inversion H0; subst.
          rewrite Bool.orb_true_r. eauto.
        - clear. intros.
          repeat intro. inject H4. simpl. intuition.
          destruct H1 as [? []].
          constructor; simpl; auto.
          constructor; simpl; eauto.
          eapply (memo_add Datatypes.orb Bool.orb_comm mor); eauto.
        - clear.  intros. eapply (memo_find _ mor); eauto using wf_st_memo, wf_memo_mor.
      Qed.
    End mk_or.


    Section mk_not.

      Definition negb_sem v a st := (fun res st' =>
                                      wf_expr st' v res /\
                                      forall env va, value env st a va ->
                                              value env st' res (Datatypes.negb va)).

      Section memo1_add.
        Variable st : state.
        Variable Hwf : wf_hashcons st.
        Variable Hwfm : wf_memo_neg st (mneg st).

        Lemma memo1_add : forall a v res,
                           wf_expr st v (N a) ->
                           negb_sem v (N a) st res st ->
                           (forall v', wf_expr st v' (N a) -> wf_expr st v' res) ->
                           wf_memo_neg st (PMap.add a res (mneg st)).
        Proof.
          intros na v res Hna  Hres Hres'.
          constructor.
          - intros.
            destruct (Pos.eq_dec x na).
            + subst. rewrite PMap.gss in H. inject H. apply Hres'. auto.
            + rewrite PMap.gso in H by eauto. eauto.
          - intros nb; intros.
            destruct (Pos.eq_dec nb na).
            + subst. eauto.
            + rewrite PMap.gso in H by eauto. eauto.
          - intros nb res' H.
            unfold negb_sem in Hres. destruct Hres.
            intros.
            destruct (Pos.eq_dec nb na);subst.
            + rewrite PMap.gss in H. inject H. eauto.
            + eapply wf_memo_neg_find_sem; eauto. rewrite PMap.gso in H ; eauto.
        Qed.
      End memo1_add.

      Definition mneg_update na res (st: state) :=
        (tt,
         mk_state
           st
           {| mand := mand st;
              mor  := mor st;
              mxor  := mxor st;
              mneg := PMap.add na res (mneg st) |}).

      Lemma mneg_update1 : forall (st:state) v a  res,
                             wf_expr st v (N a) ->
                             wf_st st ->
                             (forall v', wf_expr st v' (N a) -> wf_expr st v' res) ->
                             negb_sem v (N a) st res st ->
                                   wb st (mneg_update a  res) (fun _ _ => True).
      Proof.
        unfold mneg_update. repeat intro. inject H3; sep; intuition eauto.
        constructor. simpl. eauto.
        constructor; simpl; try now (destruct H0 as [ ? [? ? ? ]]; eauto).
        eapply  memo1_add; eauto.
        destruct H0 as [_ H']. destruct H'. eauto.
      Qed.

      Definition memo1_node a  l v h st :=
        let (res, st) := mk_node l v h st in
        let (_, st) := mneg_update a res st in
        (res,st).

      Fixpoint mk_not depth (a : expr) st : option (expr * state) :=
        match depth with
          | 0 => None
          | S depth =>
            match a with
              | F => Some (T, st)
              | T => Some (F, st)
              | N na =>
                match PMap.find na (mneg st) with
                  | Some p => Some (p,st)
                  | None =>
                    do nodea <- PMap.find na (graph st);
                      let '(l,v,h) := nodea in
                      do x, st <- mk_not depth l st;
                      do y, st <- mk_not depth h st;
                      Some (memo1_node na x v y st)
                  end
            end
        end.

      Opaque mneg_update.

      Lemma wb_memo1_node :
        forall v' a l v h (st:state),
          wf_st st ->
          wf_expr st v h ->
          wf_expr st v l ->
          (forall v'', wf_expr st v'' (N a) -> (v < v'')%positive) ->
          wf_expr st v' (N a) ->

          (forall env,
           forall va,
             value env st (N a) va ->
             exists r,
               find env v = Some r /\
               value env st (if r then h else l) (Datatypes.negb va)) ->
          wb st (memo1_node a l v h) (negb_sem v' (N a) st).
      Proof.
        intros v' a l v h st Hwf Hh Hl Hlt Ha Z.
        unfold memo1_node.
        eapply wb_bind. eapply wb_mk_node with (l:=l) (h:=h); eauto.
        simpl.
        intros res st' [H1 H2] Hincr Hwf' Heq.

        assert (HH : forall (st0  st'': state),
                       incr st0 st' ->
                       incr st st0 ->
                       incr st' st'' ->
                       wf_st st0 ->
                       wf_st st'' ->
                       negb_sem v' (N a) st0  res st'').
        {
          intros; unfold negb_sem. split. eauto.
          intros  env va Hva .
          specialize (Z env va ).
          eapply value_rcni in Hva; eauto.
          specialize (Z Hva).
          destruct Z  as [r [Hr Hv]].
          eauto.
        }

        eapply wb_bind. eapply mneg_update1; eauto.
        intros v'' Ha'.
        eapply wf_expr_rcni with (st:=st) in Ha'; eauto.
        eauto.
      Qed.

      Lemma memo1_get : forall v a res (st: state),
                          PMap.find a (mneg st) = Some res ->
                          wf_expr st v (N a) ->
                          wf_st st ->
                          negb_sem v (N a) st res st.
      Proof.
        intros. destruct H1 as [ ? [_ _ _ [?]]].
        unfold negb_sem. split; intuition eauto.
      Qed.
      Hint Resolve memo1_get.

      Remark negb_sem_incr : forall v (st st': state) m a ,
                               wbo st' m (negb_sem v a st') ->
                               incr st st' ->
                               wbo st' m (negb_sem v a st).
      Proof.
        intros.
        unfold wbo, negb_sem in *.
        intros.  specialize (H st'0 out H1).
        intuition.
        eauto using value_incr.
      Qed.

      Remark negb_sem_eauto v na st res (st' st'' : state):
        negb_sem v na st res st' ->
        incr st' st'' ->
        wf_st st' ->
        wf_st st'' ->
        wf_expr st'' v res.
      Proof.
        intros [ H _].  intuition eauto.
      Qed.

      Hint Resolve negb_sem_eauto.

      Lemma wbo_mk_not depth v0 st a :
          wf_st st ->
          wf_expr st v0 a ->
          wbo st (mk_not depth a) (negb_sem v0 a st).
      Proof.
        revert v0 st a. induction depth.
        - intros; easy.
        - simpl. intros v0 st [| |na] Hst Ha;
          try now
              (unfold negb_sem; simpl; repeat intro; inject H; simpl; intuition;
               match goal with
                 | H : value _ _ T _ |-  _ => inversion H; subst; eauto
                 | H : value _ _ F _ |- _ => inversion H; subst; eauto
               end).
          {
            simpl. intros st' res EQ.
            destruct (PMap.find na (mneg st)) eqn: Hmemo.
            - inject EQ. sep; eauto.
            - destruct (PMap.find na (graph st)) as [[[l1 v1] h1]|] eqn:Hna; simpl in EQ; try easy.
              eapply wbo_bind with (Q := negb_sem v0 (N na) st) in EQ; eauto.
              intros. simpl in H.
              eapply wbo_bind; eauto.
              intros. simpl in *.
              eapply negb_sem_incr; [| now eauto using incr_trans].
              assert (incr st st'1) by eauto 8.
              eapply wb_memo1_node; eauto.
              + intros v'' Ha'.
                inversion Ha'. apply incr_find with (b2:=st'1) in Hna; auto.
                congruence.
              + intros.
                eapply pmap_value_inversion in Hna; eauto.
                destruct Hna as [ra  [Hra Hva]].
                unfold negb_sem in *.
                destruct ra; intuition eauto 10.
          }
      Qed.

      Lemma mk_not_correct depth v0 st a :
          wf_st st ->
          wf_expr st v0 a ->
          forall res st', mk_not depth a st = Some (res, st') ->
            wf_st st' /\
            incr st st' /\
            wf_expr st' v0 res /\
            forall env va,
              value env st a va ->
              value env st' res (negb va).
      Proof. intros; edestruct wbo_mk_not; eauto. Qed.
    End mk_not.

    Section mk_xor.
      Definition update_xor na nb res (st: state) :=
        (tt,
         mk_state
           st
           {| mand := mand st;
              mxor  := Memo2.add na nb res (mxor st);
              mor  := mor st;
              mneg := mneg st |}).

      Definition mk_xor depth :=
        combinator
          (fun x st => Some (x,st) )                                     (* F x *)
          (fun x st => do res, st <- mk_not depth x st; Some (res, st) ) (* T x *)
          (fun a b st => Memo2.find a b (mxor st))
          update_xor
          depth.

      Theorem mk_xor_correct depth v0 (st: state)  a b :
        wf_st st ->
        wf_expr st v0 a -> wf_expr st v0 b ->
        forall res st', mk_xor depth a b st = Some (res, st') ->
          wf_st st' /\ incr st st' /\
          wf_expr st' v0 res /\
          forall env va vb,
            value env st a va ->
            value env st b vb ->
            value env st' res (xorb va vb).
      Proof.
        intros Hwf ; intros.
        unfold mk_xor in H1. eapply wbo_combinator; eauto.
        - apply Bool.xorb_comm.
        - clear.
          intros v res  st' hwf h.
          eapply wb_ret; eauto.
          repeat constructor. eauto.
          unfold node_opb_rel. intros. inversion H0; subst.
          rewrite Bool.xorb_false_r. eauto.
        - clear.
          intros v res  st' hwf h.
          eapply wbo_bind. eapply wbo_mk_not; eauto.
          intros. eapply wb_ret; eauto.
          destruct H.
          repeat constructor; eauto. unfold node_opb_rel. intros. inversion H5; subst.
          rewrite Bool.xorb_true_r. eauto.
        - clear. intros.
          repeat intro. inject H4. simpl. intuition.
          destruct H1 as [? []].
          constructor; simpl; auto.
          constructor; simpl; eauto.
          eapply (memo_add Datatypes.xorb Bool.xorb_comm mxor); eauto.
        - clear.  intros. eapply (memo_find _ mxor); eauto using wf_st_memo, wf_memo_mxor.
      Qed.
    End mk_xor.
  End operations.

  Definition mk_var x st :=
    mk_node F x T st.

  Lemma mk_var_sem_correct env (st: state) x:
        wf_st st ->
        forall res st',
        mk_var x st = (res, st') ->
        forall r, find env x = Some r ->
                  value env st' res r.
  Proof.
    unfold mk_var.
    intros.
    edestruct wb_mk_node; [ | | | f_equal; apply H0 | ];eauto.
    unfold mk_node_sem in H3. destruct H3. destruct H4.
    destruct r; eauto.
  Qed.

  Definition mk_true  (st: state) := (T,st).
  Definition mk_false (st: state) := (F,st).

End t.

Lemma value_independent_aux:
  forall v',
  forall v st a, (v <= v')%positive -> wf_expr st v a -> wf_hashcons st ->
  forall x env va,
    value env st a va <-> value (PMap.add v' x env) st a va.
Proof.
  induction v using positive_strong_ind.
  intros st a Hle Ha Hwf x env va; split; intro Hval.
  + destruct Ha; inversion Hval; econstructor; rewrite H0 in H3; inject H3; eauto.
    rewrite PMap.gso; eauto. zify; omega.
    apply -> H; auto. destruct vv; eauto. zify; omega. auto.
  + destruct Ha; inversion Hval; econstructor; rewrite H0 in H3; inject H3; eauto.
    rewrite PMap.gso in H4; eauto. zify; omega.
    apply <- H; auto. eauto. destruct vv; eauto. zify; omega. auto.
Qed.

Lemma value_independent:
  forall v st a, wf_expr st v a -> wf_hashcons st ->
  forall x env va,
    value env st a va <-> value (PMap.add v x env) st a va.
Proof.
  intros. eapply value_independent_aux; eauto. reflexivity.
Qed.

Hint Resolve -> value_independent.

Definition equiv st e1 e2 :=
    (forall env v1 v2, value env st e1 v1 ->  value env st e2 v2 -> v1 = v2).

Lemma canonicity:
  forall st v e1 e2,
    wf_st st ->
    wf_expr st v e1 ->
    wf_expr st v e2 ->
    equiv st e1 e2 ->
    e1 = e2.
Proof.
  unfold equiv.
  induction v using positive_strong_ind.
  intros.
  destruct H1, H2; try reflexivity.
  - specialize (H3 (PMap.empty bool) true false (value_T _ _) (value_F _ _)).
    discriminate.
  - edestruct wf_reduced; eauto.
    eapply H; eauto.
    etransitivity. symmetry.
    + apply H3 with (env:=PMap.add v false env); eauto 6 using PMap.gss.
    + apply H3 with (env:=PMap.add v true env); eauto 6 using PMap.gss.
  - specialize (H3 (PMap.empty bool) false true (value_F _ _) (value_T _ _)).
    discriminate.
  - edestruct wf_reduced; eauto.
    eapply H; eauto.
    etransitivity. symmetry.
    + apply H3 with (env:=PMap.add v false env); eauto 6 using PMap.gss.
    + apply H3 with (env:=PMap.add v true env); eauto 6 using PMap.gss.
  - edestruct wf_reduced; eauto.
    eapply H; eauto.
    etransitivity. 2:symmetry.
    + apply H3 with (env:=PMap.add v false env); eauto 6 using PMap.gss.
    + apply H3 with (env:=PMap.add v true env); eauto 6 using PMap.gss.
  - edestruct wf_reduced; eauto.
    eapply H; eauto.
    etransitivity. 2:symmetry.
    + apply H3 with (env:=PMap.add v false env); eauto 6 using PMap.gss.
    + apply H3 with (env:=PMap.add v true env); eauto 6 using PMap.gss.
  - destruct (Pos.compare_spec v v0).
    + subst.
      assert (l = l0).
      { eapply H; eauto.
        intros. apply H3 with (env:=PMap.add v0 false env); eauto 6 using PMap.gss.
      }
      assert (h = h0).
      { eapply H; eauto.
        intros. apply H3 with (env:=PMap.add v0 true env); eauto 6 using PMap.gss.
      }
      subst.
      rewrite <- wf_bijection in H2, H1; auto.
      congruence.
    + edestruct wf_reduced; eauto.
      transitivity (N x); [symmetry|]; eapply H; eauto; intros.
      * apply H3 with (env:=PMap.add v0 false env); eauto 6 using PMap.gss.
      * apply H3 with (env:=PMap.add v0 true env); eauto 6 using PMap.gss.
    + edestruct wf_reduced with (p:=x); eauto.
      transitivity (N x0); [|symmetry]; eapply H with (m:=v); eauto; intros.
      * apply H3 with (env:=PMap.add v false env); eauto 6 using PMap.gss.
      * apply H3 with (env:=PMap.add v true env); eauto 6 using PMap.gss.
Qed.

(** The equality test is a correct and complete caracterisation of semantic equivalence  *)

Lemma eqb_correct st (Hst:wf_st st) e1 e2 v  (He1: wf_expr st v e1) (He2: wf_expr st v e2) :
  eqb e1 e2 = true <-> equiv st e1 e2.
Proof.
  unfold equiv. rewrite eqb_iff; intros; split; intro.
  - subst;  intros. eapply value_inj; eauto.
  - eapply canonicity; eauto.
Qed.
