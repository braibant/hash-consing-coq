(** This file defines a library of BDDs implemented in Coq, by making
a deep-embedding of the memory as finite maps, and using integers as
surrogates of pointers. *)

Require Import common ZArith.

Ltac sep :=
  repeat match goal with
             |- (_ * _)%type => constructor
           | |- (_ /\ _) => constructor
         end.

Notation var := positive.

Inductive expr := | F | T | N : hc_expr -> var -> hc_expr -> expr
with hc_expr := HC : expr -> positive -> hc_expr.

Definition unhc (e:hc_expr) := let 'HC res _ := e in res.
Coercion unhc : hc_expr >-> expr.
Definition ident (e:hc_expr) := let 'HC _ res := e in res.

Definition eqb a b :=
  match a,b with
    | T,T => true
    | F,F => true
    | N (HC _ id1) x (HC _ id2), N (HC _ id1') x' (HC _ id2') =>
      ((id1 =? id1')%positive && (x =? x')%positive && (id2 =? id2')%positive)%bool
    | _, _ => false
  end.

Require Import FMapPositive FMapAVL OrderedTypeAlt.
Require FMapFacts.
Module PMap := PositiveMap.
Module PMapFacts := FMapFacts.Facts(PMap).

(** Rather painful proof of the fact that expr form an ordered type *)
Module N <: OrderedTypeAlt.
  Definition t := expr.
  Import Compare.

  Definition compare x y :=
    match x,y with
      | F , F => Eq
      | T , T => Eq
      | N l x h, N l' x' h' =>
        (lex (x ?= x') (lex (ident l ?= ident l') (ident h ?= ident h')))%positive
      | F, _ =>  Lt
      | _, F => Gt
      | T, _ =>  Lt
      | _, T => Gt
    end.

  Lemma compare_sym y x : compare x y = CompOpp (compare y x).
  Proof.
    destruct x as [| |[]?[]]; destruct y as [| |[]?[]]; simpl; trivial.
    set (g:=(fun a b => let '(a, a'):=a in let '(b, b'):=b in
                        lex (a ?= b) (a' ?= b'))%positive).
    fold (g (p,p1) (p2,p4)). apply lex_sym; eauto with compare.
    intros [? ?] [? ?]. apply lex_sym; eauto with compare.
  Qed.

  Lemma compare_trans c x y z: compare x y = c -> compare y z = c -> compare x z = c.
  Proof.
    destruct x as [| |[]?[]]; destruct y as [| |[]?[]]; destruct z as [| |[]?[]];
      simpl; trivial; try congruence.
    set (g:=(fun a b => let '(a, a'):=a in let '(b, b'):=b in
                        lex (a ?= b) (a' ?= b'))%positive).
    fold (g (p,p1) (p2,p4)). fold (g (p2,p4) (p5,p7)).
    apply lex_trans; eauto with compare.
    intros ? [? ?] [? ?] [? ?]. apply lex_trans; eauto with compare.
  Qed.

  Lemma compare_refl n : compare n n = Eq.
  Proof.
    destruct n as [| |[]?[]]; try reflexivity.
    simpl. rewrite !Pos.compare_refl. reflexivity.
  Qed.
End N.
Module NO := OrderedType_from_Alt(N).

Module NMap := FMapAVL.Make (NO).
Module NMapFacts := FMapFacts.Facts (NMap).

Notation pmap := PMap.t.
Notation nmap := NMap.t.

Notation memo1 := (PMap.t (hc_expr)).
Notation memo2 := (PPMap.t (hc_expr)).

Module Memo2.
  Definition find (x y: positive) (t : memo2) : option (hc_expr) :=
    let a := Pos.min x y in
    let b := Pos.max x y in
    PPMap.find (a,b) t.

  Definition add (x y: positive) n (t : memo2)  :=
    let a := Pos.min x y in
    let b := Pos.max x y in
    PPMap.add (a,b) n t.

End Memo2.

(** We are now ready to start speaking about BDDs.

    BDDs are built from two components: a part that deals with
    hash-consing, and a part that deals with the memoization of the
    various operations.

    Regarding the hashconsing part, we define it as follows:
    [hmap] is used to hash-cons nodes;
    [next] is the index of the next usable node.

    All the nodes below than [next] have a value.

    The memoization part is made of partial maps from pointers to
    expressions.
*)

Record hashcons := mk_hcons
  {
    hmap : nmap (hc_expr);
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
| wfe_N : forall l v h v',
            l <> h ->
            wf_hc_expr st v l -> wf_hc_expr st v h ->
            (v < v')%positive ->
            wf_expr st v' (N l v h)
with wf_hc_expr st : var -> hc_expr -> Prop :=
| wf_hc_cons:
  forall e v id, NMap.find e (hmap st) = Some (HC e id) ->
               wf_expr st v e ->
               wf_hc_expr st v (HC e id).

Hint Constructors wf_expr wf_hc_expr.

Lemma wf_hc_expr_le:
  forall b v v' e, wf_hc_expr b v e -> (v <= v')%positive ->
                   wf_hc_expr b v' e.
Proof.
  destruct 1. constructor. auto.
  destruct H0; constructor; auto.
  zify; omega.
Qed.

Record wf_hashcons (b:hashcons) : Prop :=
  {
    wf_injection : forall e1 v1 e2 v2 id,
                     wf_hc_expr b v1 (HC e1 id) ->
                     wf_hc_expr b v2 (HC e2 id) ->
                     N.compare e1 e2 = Eq;
    wf_expr_lt_next : forall e v,
                        wf_hc_expr b v e ->
                        (ident e < next b)%positive;
    wf_find_wf_hc_expr : forall e e',
                           NMap.find e (hmap b) = Some e' ->
                           N.compare e e' = Eq /\
                           exists v, wf_hc_expr b v e'
  }.

Hint Resolve wf_expr_lt_next wf_find_wf_hc_expr.

Notation find env v := (PositiveMap.find v env).

Inductive value env : expr -> bool -> Prop :=
| value_T : value env T true
| value_F : value env F false
| value_N : forall (l : hc_expr) (v : var) (h : hc_expr),
               forall (vv: bool), find env v = Some vv ->
               forall vhl : bool, value env (if vv then h else l) vhl ->
                                  value env (N l v h) vhl.
Hint Constructors value.

Definition node_opb_rel opb (na nb res:expr) :=
  forall env va vb, value env na va ->
                    value env nb vb ->
                    value env res (opb va vb).

Record wf_memo2 (b: hashcons) (m: memo2) (opb : bool -> bool -> bool) :=
  { wf_memo2_wf_res:
      forall (x y:hc_expr) v res,
        wf_hc_expr b v x ->
        wf_hc_expr b v y ->
        Memo2.find (ident x) (ident y) m = Some res ->
        wf_hc_expr b v res /\ node_opb_rel opb x y res;
    wf_memo2_wfx:
      forall (x y:positive) res,
        Memo2.find x y m = Some res ->
        exists ex v, wf_hc_expr b v (HC ex x);
    wf_memo2_wfy:
      forall (x y:positive) res,
        Memo2.find x y m = Some res ->
        exists ey v, wf_hc_expr b v (HC ey y)
  }.

Hint Resolve wf_memo2_wf_res wf_memo2_wfx wf_memo2_wfy.

Record wf_memo_neg  (b: hashcons) (m: memo1) :=
  { wf_memo_neg_wf_res:
      forall (x:hc_expr) v res,
        wf_hc_expr b v x ->
        PMap.find (ident x) m = Some res ->
        wf_hc_expr b v res /\
        forall env va, value env x va ->
                       value env res (Datatypes.negb va);
    wf_memo_neg_wfx:
      forall (x:positive) res,
        PMap.find x m = Some res ->
        exists ex v, wf_hc_expr b v (HC ex x)
  }.

Hint Resolve wf_memo_neg_wf_res wf_memo_neg_wfx.

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
  incr_find: forall e v, wf_hc_expr b1 v e -> wf_hc_expr b2 v e
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

Lemma wf_hc_expr_incr:
  forall b1 b2 v e,
    wf_hc_expr b1 v e ->
    incr b1 b2 ->
    wf_hc_expr b2 v e.
Proof.
  destruct 1; eauto.
Qed.

Hint Resolve wf_hc_expr_incr.

Lemma wf_expr_incr:
  forall b1 b2 v e,
    wf_expr b1 v e ->
    incr b1 b2 ->
    wf_expr b2 v e.
Proof.
  destruct 1; eauto.
Qed.

Hint Resolve wf_expr_incr.

Definition wb {alpha} (st:state) m P :=
  forall (st': state) (out:alpha),
    m = (out, st') ->
    wf_st st' /\ incr st st' /\ P out st'.

Lemma wb_wf alpha:
  forall st m P,
  forall (st': state) (out:alpha),
    m = (out, st') ->
    wb st m P ->
    wf_st st'.
Proof.
  intros. edestruct H0; eauto.
Qed.

Hint Resolve wb_wf.

Lemma wb_incr alpha:
  forall st m P,
  forall (st': state) (out:alpha),
    m = (out, st') ->
    wb st m P ->
    forall st'', incr st' st'' ->
                  incr st st''.
Proof.
  intros. edestruct H0 as [_ []]; eauto using incr_trans.
Qed.

Hint Resolve wb_incr.

Lemma wb_bind alpha beta:
  forall st m f P Q,
    wb st m P ->
    (forall (a:alpha) (st':state),
       P a st' -> incr st st' -> wf_st st' -> m = (a, st') -> wb st' (f a st') Q) ->
    wb (alpha:=beta) st (let (a, st') := m in f a st') Q.
Proof.
  unfold wb.
  intros.
  destruct m as [].
  edestruct H as [? []]; eauto. edestruct H0 as [? []]; eauto.
Qed.

Lemma wb_impl alpha:
  forall st m P Q,
    wb (alpha:=alpha) st m P ->
    (forall st' res, m = (res, st') -> (P res st':Prop) -> (Q res st':Prop)) ->
    wb (alpha:=alpha) st m Q.
Proof.
  repeat intro.
  specialize (H0 _ _ H1). apply H in H1.
  intuition.
Qed.

Lemma wb_ret alpha:
  forall (a:alpha) (st:state) P,
    wf_st st -> (P a st:Prop) ->
    wb st (a, st) P.
Proof.
  unfold wb.
  intros. inject H1; eauto.
Qed.

Hint Resolve wb_ret.

Definition upd u (b: state) :=
  let r := HC u (next b) in
  (r, mk_state
    {|
      hmap := NMap.add u r (hmap b);
      next := (next b + 1)
    |}
    b).

Lemma wf_expr_rcni: forall st st' e v v',
                      wf_expr st v e ->
                      wf_expr st' v' e ->
                      incr st st' ->
                      wf_expr st v' e.
Proof.
  intros st st' e v v' Hv Hv' Hincr.
  destruct Hv'; inversion Hv; constructor; auto.
Qed.

Lemma wf_hc_expr_rcni: forall st st' e v v',
                      wf_hc_expr st v e ->
                      wf_expr st' v' e ->
                      incr st st' ->
                      wf_hc_expr st v' e.
Proof.
  intros st st' e v v' Hv Hv' Hincr.
  destruct Hv. destruct H0; inversion Hv'; econstructor; eauto.
Qed.

Lemma wf_expr_compare_eq:
  forall b e1 v1 e2 v2,
    wf_hashcons b ->
    wf_expr b v1 e1 ->
    wf_expr b v2 e2 ->
    N.compare e1 e2 = Eq ->
    e1 = e2
with wf_hc_expr_ident_inj:
  forall b e1 v1 e2 v2,
    wf_hashcons b ->
    wf_hc_expr b v1 e1 ->
    wf_hc_expr b v2 e2 ->
    ident e1 = ident e2 ->
    e1 = e2.
Proof.
  - intros.
    destruct H0, H1; simpl in H2; try congruence.
    destruct (Pos.compare_spec v v0), (Pos.compare_spec (ident l) (ident l0)),
             (Pos.compare_spec (ident h) (ident h0));
      try discriminate H2. clear H2. subst.
    f_equal; eapply wf_hc_expr_ident_inj; eauto.
  - intros. destruct H0, H1. simpl in H2. subst.
    f_equal. eapply wf_expr_compare_eq, wf_injection; eauto.
Qed.

Lemma incr_wf_memo2 :
  forall opb hc1 hc2 memo,
    wf_hashcons hc2 ->
    incr hc1 hc2 ->
    wf_memo2 hc1 memo opb ->
    wf_memo2 hc2 memo opb.
Proof.
  intros opb hc1 hc2 memo Hwf2 Hincr Hwfm.
  constructor.
  - intros. edestruct wf_memo2_wf_res; eauto.
    + edestruct wf_memo2_wfx as [e' [v' Hwfhc]]; eauto.
      eapply wf_hc_expr_rcni; eauto.
      assert (wf_hc_expr hc2 v' (HC e' (ident x))) by eauto.
      erewrite wf_hc_expr_ident_inj; eauto.
      destruct H; eauto.
    + edestruct wf_memo2_wfy as [e' [v' Hwfhc]]; eauto.
      eapply wf_hc_expr_rcni; eauto.
      assert (wf_hc_expr hc2 v' (HC e' (ident y))) by eauto.
      erewrite wf_hc_expr_ident_inj; eauto.
      destruct H0; eauto.
  - intros.
    eapply wf_memo2_wfx in Hwfm; eauto.
    destruct Hwfm as [? [? ?]]. eauto.
  - intros.
    eapply wf_memo2_wfy in Hwfm; eauto.
    destruct Hwfm as [? [? ?]]. eauto.
Qed.

Lemma incr_wf_memo_neg :
  forall hc1 hc2 memo,
    wf_hashcons hc2 ->
    incr hc1 hc2 ->
    wf_memo_neg hc1 memo ->
    wf_memo_neg hc2 memo.
Proof.
  intros  hc1 hc2 memo Hwf2 Hincr Hwfm.
  constructor.
  - intros. edestruct wf_memo_neg_wf_res; eauto.
    edestruct wf_memo_neg_wfx as [e' [v' Hwfhc]]; eauto.
    eapply wf_hc_expr_rcni; eauto.
    assert (wf_hc_expr hc2 v' (HC e' (ident x))) by eauto.
    erewrite wf_hc_expr_ident_inj; eauto.
    destruct H; eauto.
  - intros.
    eapply wf_memo_neg_wfx in Hwfm; eauto.
    destruct Hwfm as [? [? ?]]. eauto.
Qed.

Lemma incr_wf_memo :
  forall hc1 hc2 memo,
    wf_hashcons hc2 ->
    incr hc1 hc2 ->
    wf_memo (mk_state hc1 memo) ->
    wf_memo (mk_state hc2 memo).
Proof.
  intros hc1 hc2 memo Hwf2 Hincr Hmemo.
  inversion Hmemo.
  constructor; eauto using incr_wf_memo2.
  constructor; eauto using incr_wf_memo_neg.
Qed.

Lemma wb_upd : forall (st:state) v e,
                 wf_st st ->
                 wf_expr st v e ->
                 NMap.find e (hmap st) = None ->
                 wb st (upd e st)
                    (fun e' st' => unhc e' = e /\ wf_hc_expr st' v e').
Proof.
  unfold upd. intros st v ? Hst He HNone st' [e ide] Heq.
  inject Heq.
  match goal with |- _ /\ ?P /\ _ => assert (Hincr:P) end.
  { constructor. simpl. zify; omega.
    assert (forall e0 e0',
        NMap.find e0 (hmap st) = Some e0' ->
        NMap.find e0 (NMap.add e (HC e (next st)) (hmap st)) = Some e0').
    { intros. rewrite NMapFacts.add_neq_o; eauto.
      intro. rewrite NMapFacts.find_o with (y:=e0) in HNone; congruence. }
    fix 3. intros e' v' Hwfe0. simpl.
    destruct Hwfe0. constructor. auto.
    destruct H1; eauto. }
  match goal with |- _ ?st' /\ _ /\ _ => assert (Hwf':wf_hashcons st') end.
  { constructor; simpl.
    - intros.
      destruct (Pos.eq_dec id (next st)).
      + inversion H; inversion H0. clear H H0. simpl in *. subst.
        rewrite NMapFacts.add_o in H4, H9.
        destruct NMap.E.eq_dec. destruct NMap.E.eq_dec.
        * eapply N.compare_trans; eauto.
          rewrite N.compare_sym, e0. auto.
        * apply wf_find_wf_hc_expr in H9; auto. destruct H9 as [? [v' ?]].
          apply wf_expr_lt_next in H0; auto. simpl in H0. zify; omega.
        * apply wf_find_wf_hc_expr in H4; auto. destruct H4 as [? [v' ?]].
          apply wf_expr_lt_next in H0; auto. simpl in H0. zify; omega.
      + inversion H; inversion H0. subst. clear H H0. simpl in H4, H9.
        assert (N.compare e e1 <> Eq).
        { contradict n.
          rewrite NMapFacts.add_eq_o in H4; auto. congruence. }
        assert (N.compare e e2 <> Eq).
        { contradict n.
          rewrite NMapFacts.add_eq_o in H9; auto. congruence. }
        rewrite NMapFacts.add_neq_o in H4, H9 by auto.
        apply wf_find_wf_hc_expr in H4; auto. destruct H4 as [_ [v1' He1]].
        apply wf_find_wf_hc_expr in H9; auto. destruct H9 as [_ [v2' He2']].
        eapply wf_injection; eauto.
    - intros. destruct H. simpl in H.
      rewrite NMapFacts.add_o in H. destruct (NMap.E.eq_dec e e0).
      inject H. simpl. zify; omega.
      eapply wf_find_wf_hc_expr in H; eauto.
      destruct H as [? []].
      eapply wf_expr_lt_next in H1; auto.
      simpl in *. zify; omega.
    - intros.
      rewrite NMapFacts.add_o in H. destruct (NMap.E.eq_dec e e0).
      + inversion H. subst. clear H.
        split.
        * simpl. rewrite N.compare_sym, e1. auto.
        * exists v. constructor; eauto.
          simpl. apply NMapFacts.add_eq_o, NMap.E.eq_refl.
      + edestruct wf_find_wf_hc_expr as [? []]; eauto.
  }
  sep; trivial. constructor; trivial.
  destruct st; simpl; eauto using incr_wf_memo.
  intros. constructor; simpl.
  apply NMapFacts.add_eq_o, NMap.E.eq_refl.
  eauto.
Qed.

Definition hc_node (e:expr) (st:state) :=
  match NMap.find e (hmap st) with
    | Some x => (x, st)
    | None => upd e st
  end.

Lemma wb_hc_node :
  forall e v (st:state),
    wf_st st ->
    wf_expr st v e ->
    wb st (hc_node e st) (fun e' st' =>
      unhc e' = e /\ wf_hc_expr st' v e').
Proof.
  intros e v st Hst He. unfold hc_node.
  destruct (NMap.find e (hmap st)) eqn:EQ.
  - apply wb_ret. auto.
    eapply wf_find_wf_hc_expr in EQ; auto. destruct EQ as [Hee' [v' He']].
    destruct He'. eapply wf_expr_compare_eq in Hee'; eauto. subst.
    sep; auto.
  - eapply wb_upd; eauto.
Qed.

Definition mk_node (l:hc_expr) (v:var) (h:hc_expr) (st:state) :=
  if (ident l =? ident h)%positive then (l,st)
  else hc_node (N l v h) st.

Definition mk_node_sem (l:hc_expr) v h res st :=
  (wf_hc_expr st (v+1) res)
  /\ (forall env vhl r, find env v = Some r ->
                        value env (if r then h else l) vhl ->
                        value env res vhl).

Lemma value_inj env x vx:
  value env x vx ->
  forall vx', value env x vx' ->
     vx = vx'.
Proof.
  induction 1.
  inversion 1. reflexivity.
  inversion 1; reflexivity.
  intros v2 Hv2.
  inversion Hv2. subst. clear Hv2.
  rewrite H in H5. inject H5.
  eauto.
Qed.

Lemma wb_mk_node :
  forall l v h (st:state),
    wf_st st ->
    wf_hc_expr st v l -> wf_hc_expr st v h ->
    wb st (mk_node l v h st) (mk_node_sem l v h).
Proof.
  intros l v h st Hst Hwfl Hwfh.
  unfold mk_node.
  destruct (Pos.eqb_spec (ident l) (ident h)).
  - apply wb_ret. auto.
    eapply wf_hc_expr_ident_inj in e; eauto. subst.
    split.
    destruct Hwfh. constructor; eauto.
    destruct H0; constructor; auto. zify; omega.
    destruct r; auto.
  - assert (l <> h) by congruence. clear n.
    eapply wb_impl. apply wb_hc_node. eauto.
    assert (v < v+1)%positive by (zify; omega). eauto.
    intros. destruct H1. constructor; eauto.
    rewrite H1. eauto.
Qed.

Hint Resolve wb_mk_node.

Section t.
  Section operations.

    (** All the binary operations on the bdd follow the same
    structure. We define partial operations that use an explicit
    bound on the number of recursive calls, and fail if that number
    is not sufficent. We cannot easily use open-recursion and a
    common skeleton for these operations, as we would in OCaml
    (problem of termination), and this is the reason why the code is
    verbose.

    Note that we cannot esasily use Program or Function, because we use
    nested calls to the function we define (that is, the
    well-founded relation that terminates shall mention the fact
    that our bdds are well-formed, and refinements of each other)*)

    Section combinator.
      Variable fx : hc_expr -> state -> hc_expr * state.
      Variable tx : hc_expr -> state -> hc_expr * state.
      Variable memo_get : positive -> positive -> state -> option (hc_expr).
      Variable memo_update : positive -> positive -> hc_expr -> state -> (unit * state).
      Variable opb : bool -> bool -> bool.

      Definition combinator_sem na nb res st :=
        (forall v',
           wf_expr st v' na ->
           wf_expr st v' nb ->
           wf_hc_expr st v' res) /\
        node_opb_rel opb na nb res.

      Hypothesis opb_sym : forall x y, opb x y = opb y x.

      Hypothesis Hfx: forall v a (st:state),
        wf_hc_expr st v a -> wf_st st -> wb st (fx a st) (combinator_sem a F). 
      Hypothesis Htx: forall v a (st:state),
        wf_hc_expr st v a -> wf_st st -> wb st (tx a st) (combinator_sem a T).

      Hypothesis Hmemo_update:
        forall (st:state) v a b res,
          wf_hc_expr st v a -> wf_hc_expr st v b ->
          wf_st st ->
          combinator_sem a b res st ->
          wb st (memo_update (ident a) (ident b) res st) (fun _ _ => True).

      Hypothesis Hmemo_get :
        forall v a b st e,
          memo_get (ident a) (ident b) st = Some e ->
          wf_hc_expr st v a -> wf_hc_expr st v b ->
          wf_st st ->
          combinator_sem a b e st.

      Fixpoint combinator (a:hc_expr) :=
        fix combinator_rec (b:hc_expr) st :=
        match memo_get (ident a) (ident b) st with
          | Some p => (p,st)
          | None =>
            let '(res, st) :=
              match unhc a, unhc b with
                | F, _ => fx b st
                | _, F => fx a st
                | T, _ => tx b st
                | _, T => tx a st
                | N l1 v1 h1, N l2 v2 h2 =>
                  match Pos.compare v1 v2 with
                    | Eq =>
                      let '(x, st) := combinator l1 l2 st in
                      let '(y, st) := combinator h1 h2 st in
                      mk_node x v1 y st
                    | Gt =>
                      let '(x, st) := combinator l1 b st in
                      let '(y, st) := combinator h1 b st in
                      mk_node x v1 y st
                    | Lt =>
                      let '(x, st) := combinator_rec l2 st in
                      let '(y, st) := combinator_rec h2 st in
                      mk_node x v2 y st
                  end
              end
            in
            let '(_, st) := memo_update (ident a) (ident b) res st in
            (res, st)
        end.

      Lemma combinator_sem_comm: forall st m a b,
                                   wb st m (combinator_sem a b) ->
                                   wb st m (combinator_sem b a).
      Proof.
        intros.
        unfold wb, combinator_sem, node_opb_rel in *.
        intros. specialize (H st' out H0).
        setoid_rewrite opb_sym.
        intuition.
      Qed.

      Lemma wb_combinator :
        forall v a b st,
          wf_st st ->
          wf_hc_expr st v a -> wf_hc_expr st v b ->
          wb st (combinator a b st) (combinator_sem a b).
      Proof.
        induction v using positive_strong_ind.
        destruct a as [a ida], b as [b idb]; simpl combinator.
        intros st Hst Ha Hb.
        destruct (memo_get ida idb st) eqn:EQmg.
        - intros st' h' EQ. inject EQ. sep; eauto.
        - inversion Ha; inversion Hb; subst; clear Ha Hb.
          eapply wb_bind.
          Focus 2.
            intros; eapply wb_bind.
            change ida with (ident (HC a ida)). change idb with (ident (HC b idb)). 
            eapply Hmemo_update; eauto. eapply H0.
            intros. apply wb_ret. auto.
            destruct H0. split; auto.
            eauto 7 using wf_expr_rcni.
          destruct H4 as [| |la va ha v Hlaha Hla Hha Hvva];
          destruct H9 as [| |lb vb hb v Hlbhb Hlb Hhb Hvvb]; simpl;
          try (eapply Htx; now eauto); try (eapply Hfx; now eauto);
          try (apply combinator_sem_comm; eapply Htx; now eauto);
          try (apply combinator_sem_comm; eapply Hfx; now eauto).
          destruct (Pos.compare_spec va vb).
          + subst. eapply wb_bind; [|intros x ? Hx ? ? ?; eapply wb_bind]; eauto.
            intros y ? Hy ? ? ?. destruct Hx as [Hxwf Hx], Hy as [Hywf Hy].
            eapply wb_impl. apply wb_mk_node. eauto.
            destruct Hla, Hlb. eauto.
            destruct Hha, Hhb. eauto 6 using incr_trans.
            intros. destruct H9. split; intros.
            eapply wf_hc_expr_le. eauto. inversion H12. zify; omega.
            repeat intro. inversion H11; inversion H12; subst; clear H11 H12.
            destruct vv, vv0; eauto; congruence.
          + specialize (H vb Hvvb (HC (N la va ha) ida)).
            eapply wb_bind; [|intros x ? Hx ? ? ?; eapply wb_bind]; eauto 7.
            intros y ? Hy ? ? ?. destruct Hx as [Hxwf Hx], Hy as [Hywf Hy].
            eapply wb_impl. apply wb_mk_node. eauto.
            simpl in *. destruct Hlb. eauto 6.
            simpl in *. destruct Hhb. eauto 7.
            intros. destruct H10. split; intros.
            eapply wf_hc_expr_le. eauto. inversion H13. zify; omega.
            repeat intro. inversion H13; subst; clear H13.
            destruct vv; eauto.
          + eapply wb_bind; [|intros x ? Hx ? ? ?; eapply wb_bind]; eauto 6.
            intros y ? Hy ? ? ?. destruct Hx as [Hxwf Hx], Hy as [Hywf Hy].
            eapply wb_impl. apply wb_mk_node. eauto.
            simpl in *. destruct Hla. eauto 6.
            simpl in *. destruct Hha. eauto 7.
            intros. destruct H10. split; intros.
            eapply wf_hc_expr_le. eauto. inversion H12. zify; omega.
            repeat intro. inversion H12; subst; clear H12.
            destruct vv; eauto.
        Grab Existential Variables. exact xH. exact xH. exact xH. exact xH.
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
                         wf_hc_expr st v a ->
                         wf_hc_expr st v b ->
                         combinator_sem opb a b res st ->
                         wf_memo2 st (Memo2.add (ident a) (ident b) res (tmemo st)) opb.
      Proof.
        intros a b v res Ha Hb Hres.
        constructor.
        - intros.
          unfold Memo2.find, Memo2.add in H1.
          rewrite PPMapFacts.add_o in H1.
          destruct (PPMap.E.eq_dec (Pos.min (ident a) (ident b), Pos.max (ident a) (ident b))
                                   (Pos.min (ident x) (ident y), Pos.max (ident x) (ident y))). 
          + inject H1.
            apply PP.reflect in e. inject e.
            edestruct minmax_eq_inv as [[]|[]]; eauto.
            eapply wf_hc_expr_ident_inj in H3; eauto.
            eapply wf_hc_expr_ident_inj in H4; eauto.
            subst. destruct Hres, H, H0. eauto.
            eapply wf_hc_expr_ident_inj in H3; eauto.
            eapply wf_hc_expr_ident_inj in H4; eauto.
            subst. destruct Hres, H, H0. unfold node_opb_rel in *. setoid_rewrite opb_sym. eauto.
          + destruct Hwfm; eauto.

        - intros.
          unfold Memo2.find, Memo2.add in H.
          rewrite PPMapFacts.add_o in H.
          destruct (PPMap.E.eq_dec (Pos.min (ident a) (ident b), Pos.max (ident a) (ident b))
                                   (Pos.min x y, Pos.max x y)) as [H' | H'].
          + inject H.
            apply PP.reflect in H'. inject H'.
            edestruct minmax_eq_inv as [[]|[]]; eauto.
            subst. destruct a; eauto.
            subst. destruct b; eauto.
          + destruct Hwfm; eauto.

        - intros.
          unfold Memo2.find, Memo2.add in H.
          rewrite PPMapFacts.add_o in H.
          destruct (PPMap.E.eq_dec (Pos.min (ident a) (ident b), Pos.max (ident a) (ident b))
                                   (Pos.min x y, Pos.max x y)) as [H' | H'].
          + inject H.
            apply PP.reflect in H'. inject H'.
            edestruct minmax_eq_inv as [[]|[]]; eauto.
            subst. destruct b; eauto.
            subst. destruct a; eauto.
          + destruct Hwfm; eauto.
      Qed.

      Lemma memo_find a b v e:
        Memo2.find (ident a) (ident b) (tmemo st) = Some e ->
        wf_hc_expr st v a -> wf_hc_expr st v b ->
        combinator_sem opb a b e st.
      Proof.
        split.
        - intros. eapply wf_memo2_wf_res in H. destruct H. eauto.
          eauto.
          destruct H0; eauto.
          destruct H1; eauto.
        - eapply wf_memo2_wf_res in H; eauto. intuition.
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
          (fun x st => hc_node F st )     (* F x *)
          (fun x st => (x,st) )           (* T x *)
          (fun a b st => Memo2.find a b (mand st))
          update_and.

      Theorem wb_mk_and:
         forall v a b st,
           wf_st st ->
           wf_hc_expr st v a -> wf_hc_expr st v b ->
           wb st (mk_and a b st) (combinator_sem andb a b).
      Proof.
        intros. eapply wb_combinator; eauto.
        - apply Bool.andb_comm.
        - clear. intros. eapply wb_impl. apply wb_hc_node with (v:=xH); eauto.
          intros. destruct H2. split.
          + intros. eapply wf_hc_expr_le. eauto. zify; omega.
          + unfold node_opb_rel. intros.
            inversion H5; subst; clear H5. rewrite Bool.andb_false_r, H2. constructor.
        - clear. intros. eapply wb_ret. auto.
          split.
          + eauto using wf_hc_expr_rcni.
          + unfold node_opb_rel. intros.
            inversion H2. subst. clear H2. rewrite Bool.andb_true_r. auto.
        - clear. intros.
          repeat intro. inject H3. simpl. intuition.
          destruct H1 as [? []].
          constructor; simpl. auto.
          constructor; simpl; auto.
          eapply (memo_add Datatypes.andb Bool.andb_comm mand); eauto.
        - clear. intros. eapply (memo_find _ mand); eauto using wf_st_memo, wf_memo_mand. 
      Qed.

      Theorem mk_and_sem_correct env (st: state) (a b:hc_expr) v va vb:
        wf_st st ->
        wf_hc_expr st v a -> value env a va ->
        wf_hc_expr st v b -> value env b vb ->
        forall res st', mk_and a b st = (res, st') ->
                    value env res (va && vb)%bool.
      Proof.
        intros.
        eapply wb_mk_and in H4; eauto. destruct H4 as [? [? []]].
        apply H7; auto.
      Qed.

    End mk_and.

    Section mk_or.
      Definition update_or na nb res (st: state) :=
        (tt,
         mk_state
           st
           {| mor := Memo2.add na nb res (mor st);
              mand  := mand st;
              mxor  := mxor st;
              mneg  := mneg st
           |}).

      Definition mk_or :=
        combinator
          (fun x st => (x,st) )             (* F x *)
          (fun x st => hc_node T st )       (* T x *)
          (fun a b st => Memo2.find a b (mor st))
          update_or.

      Theorem wb_mk_or:
         forall v a b st,
           wf_st st ->
           wf_hc_expr st v a -> wf_hc_expr st v b ->
           wb st (mk_or a b st) (combinator_sem orb a b).
      Proof.
        intros. eapply wb_combinator; eauto.
        - apply Bool.orb_comm.
        - clear. intros. eapply wb_ret. eauto.
          split.
          + eauto using wf_hc_expr_rcni.
          + auto. unfold node_opb_rel. intros.
            inversion H2. subst. clear H2. rewrite Bool.orb_false_r. auto.
        - clear. intros. eapply wb_impl. apply wb_hc_node with (v:=xH); eauto.
          intros. destruct H2. split.
          + intros. eapply wf_hc_expr_le. eauto. zify; omega.
          + unfold node_opb_rel. intros.
            inversion H5; subst; clear H5. rewrite Bool.orb_true_r, H2. constructor.
        - clear. intros.
          repeat intro. inject H3. simpl. intuition.
          destruct H1 as [? []].
          constructor; simpl. auto.
          constructor; simpl; auto.
          eapply (memo_add Datatypes.orb Bool.orb_comm mor); eauto.
        - clear. intros. eapply (memo_find _ mor); eauto using wf_st_memo, wf_memo_mor.
      Qed.

      Theorem mk_or_sem_correct env (st: state) (a b:hc_expr) v va vb:
        wf_st st ->
        wf_hc_expr st v a -> value env a va ->
        wf_hc_expr st v b -> value env b vb ->
        forall res st', mk_or a b st = (res, st') ->
                    value env res (va || vb)%bool.
      Proof.
        intros.
        eapply wb_mk_or in H4; eauto. destruct H4 as [? [? []]].
        apply H7; auto.
      Qed.

    End mk_or.

    Section mk_not.

      Definition negb_sem a :=
        (fun res st =>
           (forall v', wf_expr st v' a -> wf_hc_expr st v' res) /\
           forall env va, value env a va ->
                          value env res (Datatypes.negb va)).

      Section memo1_add.
        Variable st : state.
        Variable Hwf : wf_hashcons st.
        Variable Hwfm : wf_memo_neg st (mneg st).

        Lemma memo1_add : forall a v res,
                            wf_hc_expr st v a ->
                            negb_sem a res st ->
                            wf_memo_neg st (PMap.add (ident a) res (mneg st)).
        Proof.
          intros a v res Ha  Hres.
          constructor.
          - intros.
            destruct (Pos.eq_dec (ident x) (ident a)).
            + eapply wf_hc_expr_ident_inj in e; eauto. subst.
              rewrite PMap.gss in H0. inject H0.
              destruct Hres. split; auto.
              apply H0. destruct H; auto.
            + rewrite PMap.gso in H0 by eauto. eauto.
          - intro idb; intros.
            destruct (Pos.eq_dec idb (ident a)).
            + subst. rewrite PMap.gss in H. inject H.
              destruct a. eauto.
            + rewrite PMap.gso in H by eauto. eauto.
        Qed.

      End memo1_add.

      Definition mneg_update ida (res:hc_expr) (st: state) :=
        (tt,
         mk_state
           st
           {| mand := mand st;
              mor  := mor st;
              mxor  := mxor st;
              mneg := PMap.add ida res (mneg st) |}).

      Lemma mneg_update1 : forall (st:state) v a  res,
                             wf_hc_expr st v a ->
                             wf_st st ->
                             negb_sem a res st ->
                             wb st (mneg_update (ident a) res st) (fun _ _ => True).
      Proof.
        unfold mneg_update. repeat intro. inject H2; sep; intuition eauto.
        constructor. simpl. eauto.
        constructor; simpl; try now (destruct H0 as [? [? ? ? ]]; eauto).
        eapply memo1_add; eauto.
        destruct H0 as [_ H']. destruct H'. eauto.
      Qed.

      Fixpoint mk_not (a:hc_expr) (st:state): (hc_expr * state) :=
        match PMap.find (ident a) (mneg st) with
          | Some p => (p,st)
          | None =>
            let '(res, st) :=
              match unhc a with
                | F => hc_node T st
                | T => hc_node F st
                | N l v h =>
                  let '(x, st) := mk_not l st in
                  let '(y, st) := mk_not h st in
                  mk_node x v y st
              end
            in
            let '(_, st) := mneg_update (ident a) res st in (res, st)
        end.

      Opaque mneg_update.

      Lemma memo1_get : forall v a res (st: state),
                          PMap.find (ident a) (mneg st) = Some res ->
                          wf_hc_expr st v a ->
                          wf_st st ->
                          negb_sem a res st.
      Proof.
        intros. destruct H1 as [ ? [_ _ _ [?]]].
        split.
        - intros. edestruct wf_memo_neg_wf_res0. 2:eauto. 2:eauto.
          eauto using wf_hc_expr_rcni.
        - intros. edestruct wf_memo_neg_wf_res0; eauto.
      Qed.
      Hint Resolve memo1_get.

      Lemma wb_mk_not :
        forall v a st,
          wf_st st ->
          wf_hc_expr st v a ->
          wb st (mk_not a st) (negb_sem a).
      Proof.
        induction v using positive_strong_ind.
        destruct a as [a ida]. simpl mk_not. intros st Hst Ha.
        destruct (find (mneg st) ida) eqn:EQfind.
        - apply wb_ret; eauto.
        - inversion Ha; subst; clear Ha.
          eapply wb_bind.
          Focus 2.
            intros; eapply wb_bind.
            change ida with (ident (HC a ida)).
            eapply mneg_update1; eauto. eapply H0.
            intros. apply wb_ret. auto.
            destruct H0. split; auto.
            eauto using wf_expr_rcni.
          destruct H4 as [| |la va ha v Hlaha Hla Hha Hvva]; simpl.
          + eapply wb_impl. apply wb_hc_node with (v:=xH); auto.
            intros. destruct H1. split.
            intros. eapply wf_hc_expr_le. eauto. zify; omega.
            intros. inversion H4. subst. clear H4. rewrite H1. constructor.
          + eapply wb_impl. apply wb_hc_node with (v:=xH); auto.
            intros. destruct H1. split.
            intros. eapply wf_hc_expr_le. eauto. zify; omega.
            intros. inversion H4. subst. clear H4. rewrite H1. constructor.
          + eapply wb_bind; [|intros x ? Hx ? ? ?; eapply wb_bind]; eauto.
            intros y ? Hy ? ? ?. destruct Hx as [Hxwf Hx], Hy as [Hywf Hy].
            eapply wb_impl. apply wb_mk_node. eauto.
            destruct Hla. eauto.
            destruct Hha. eauto.
            intros. destruct H8. split.
            intros. eapply wf_hc_expr_le. eauto. inversion H10. zify; omega.
            intros. inversion H10; subst; clear H10.
            destruct vv; eauto.
      Qed.

      Lemma mk_not_sem_correct env (st: state) v a va:
        wf_st st ->
        wf_hc_expr st v a -> value env a va ->
        forall res st', mk_not a st = (res, st') ->
                    value env res (Datatypes.negb va).
      Proof.
        intros.
        eapply wb_mk_not in H2; eauto. destruct H2 as [? [? []]].
        apply H5; auto.
      Qed.
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

      Definition mk_xor :=
        combinator
          (fun x st => (x,st) )             (* F x *)
          (fun x st => let '(res, st) := mk_not x st in (res, st) )             (* T x *)
          (fun a b st => Memo2.find a b (mxor st))
          update_xor.

      Theorem wb_mk_xor:
         forall v a b st,
           wf_st st ->
           wf_hc_expr st v a -> wf_hc_expr st v b ->
           wb st (mk_xor a b st) (combinator_sem xorb a b).
      Proof.
        intros. eapply wb_combinator; eauto.
        - apply Bool.xorb_comm.
        - clear. intros. eapply wb_ret. eauto.
          split.
          + eauto using wf_hc_expr_rcni.
          + auto. unfold node_opb_rel. intros.
            inversion H2. subst. clear H2. rewrite Bool.xorb_false_r. auto.
        - clear. intros.
          eapply wb_bind. eapply wb_mk_not; eauto.
          intros. apply wb_ret; auto.
          destruct H1. split. eauto.
          repeat intro. inversion H7. rewrite Bool.xorb_true_r. eauto.
        - clear. intros.
          repeat intro. inject H3. simpl. intuition.
          destruct H1 as [? []].
          constructor; simpl. auto.
          constructor; simpl; auto.
          eapply (memo_add Datatypes.xorb Bool.xorb_comm mxor); eauto.
        - clear. intros. eapply (memo_find _ mxor); eauto using wf_st_memo, wf_memo_mxor. 
      Qed.

      Theorem mk_xor_sem_correct env (st: state) (a b:hc_expr) v va vb:
        wf_st st ->
        wf_hc_expr st v a -> value env a va ->
        wf_hc_expr st v b -> value env b vb ->
        forall res st', mk_xor a b st = (res, st') ->
                    value env res (xorb va vb).
      Proof.
        intros.
        eapply wb_mk_xor in H4; eauto. destruct H4 as [? [? []]].
        apply H7; auto.
      Qed.

    End mk_xor.
  End operations.

  Definition mk_var x st :=
    let '(t, st) := hc_node T st in
    let '(f, st) := hc_node F st in
    hc_node (N f x t) st.

  Lemma mk_var_wb:
    forall x st, wf_st st ->
      wb st (mk_var x st)
          (fun res st' =>
             (forall v', (x < v')%positive -> wf_hc_expr st' v' res) /\
             (forall env v, find env x = Some v -> value env res v)).
  Proof.
    intros. eapply wb_bind. apply wb_hc_node; eauto.
    intros. eapply wb_bind. apply wb_hc_node; eauto.
    intros. destruct H0, H4.
    eapply wb_impl. apply wb_hc_node with (v:=(x+1)%positive). eauto.
    constructor; eauto. congruence. zify; omega.
    intros. destruct H11. split.
    intros. eapply wf_hc_expr_le. eauto. zify; omega.
    intros. rewrite H11. econstructor. eauto.
    destruct v.
    rewrite H0. constructor.
    rewrite H4. constructor.
  Qed.

  Lemma mk_var_sem_correct env (st: state) x:
    wf_st st ->
    forall res st',
      mk_var x st = (res, st') ->
      forall r, find env x = Some r ->
                value env res r.
  Proof.
    intros.
    eapply mk_var_wb in H1; eauto.
  Qed.

  Definition mk_true := hc_node T.
  Definition mk_false := hc_node F.

End t.

Lemma value_independent_aux:
  forall v',
  forall v st a, (v <= v')%positive -> wf_expr st v a -> wf_hashcons st ->
  forall x env va,
    value env a va <-> value (PMap.add v' x env) a va.
Proof.
  induction v using positive_strong_ind.
  intros st a Hle Ha Hwf x env va.
  split; intro Hval.
  + destruct Hval; inversion Ha; subst; econstructor.
    rewrite PMap.gso; eauto. zify; omega.
    apply -> H. auto. eauto.
    destruct vv, H7, H6; eauto. zify; omega. auto.
  + destruct Hval; inversion Ha; subst; econstructor.
    rewrite PMap.gso in H0; eauto. zify; omega.
    apply <- H. eauto. eauto.
    destruct vv, H7, H6; eauto. zify; omega. auto.
Qed.

Lemma value_independent:
  forall v st a, wf_expr st v a -> wf_hashcons st ->
  forall x env va,
    value env a va <-> value (PMap.add v x env) a va.
Proof.
  intros. eapply value_independent_aux; eauto. reflexivity.
Qed.

Hint Resolve -> value_independent.

Definition equiv e1 e2 := (forall env v1 v2, value env e1 v1 -> value env e2 v2 -> v1 = v2).

Lemma canonicity:
  forall st v e1 e2,
    wf_st st ->
    wf_expr st v e1 ->
    wf_expr st v e2 ->
    equiv e1 e2 ->
    e1 = e2.
Proof.
  unfold equiv.
  induction v using positive_strong_ind.
  intros.
  destruct H1, H2; try reflexivity.
  - specialize (H3 (PMap.empty bool) true false (value_T _) (value_F _)).
    discriminate.
  - destruct H2, H4.
    cut (e = e0). congruence.
    eapply H; eauto. etransitivity. symmetry.
    apply H3 with (env:=PMap.add v false env); eauto 6 using PMap.gss.
    apply H3 with (env:=PMap.add v true env); eauto 6 using PMap.gss.
  - specialize (H3 (PMap.empty bool) false true (value_F _) (value_T _)).
    discriminate.
  - destruct H2, H4.
    cut (e = e0). congruence.
    eapply H; eauto. etransitivity. symmetry.
    + apply H3 with (env:=PMap.add v false env); eauto 6 using PMap.gss.
    + apply H3 with (env:=PMap.add v true env); eauto 6 using PMap.gss.
  - destruct H4, H5.
    cut (e = e0). congruence.
    eapply H; eauto. etransitivity. 2:symmetry.
    + apply H3 with (env:=PMap.add v false env); eauto 6 using PMap.gss.
    + apply H3 with (env:=PMap.add v true env); eauto 6 using PMap.gss.
  - destruct H4, H5.
    cut (e = e0). congruence.
    eapply H; eauto. etransitivity. 2:symmetry.
    + apply H3 with (env:=PMap.add v false env); eauto 6 using PMap.gss.
    + apply H3 with (env:=PMap.add v true env); eauto 6 using PMap.gss.
  - destruct (Pos.compare_spec v v0).
    + subst.
      destruct H4, H5, H7, H8.
      cut(e = e1). cut(e0 = e2). congruence.
      * eapply H; eauto.
        intros. apply H3 with (env:=PMap.add v true env); eauto 6 using PMap.gss.
      * eapply H; eauto.
        intros. apply H3 with (env:=PMap.add v false env); eauto 6 using PMap.gss.
    + destruct H7, H8.
      cut (e = e0). congruence.
      transitivity (N l v h); [symmetry|]; eapply H; eauto; intros.
      * apply H3 with (env:=PMap.add v0 false env); eauto 6 using PMap.gss.
      * apply H3 with (env:=PMap.add v0 true env); eauto 6 using PMap.gss.
    + destruct H4, H5.
      cut (e = e0). congruence.
      transitivity (N l0 v0 h0); [|symmetry]; eapply H with (m:=v); eauto; intros.
      * apply H3 with (env:=PMap.add v false env); eauto 6 using PMap.gss.
      * apply H3 with (env:=PMap.add v true env); eauto 6 using PMap.gss.
Qed.

Require  Bool.
Lemma Pos_compare_eqb p1 p2 : Pos.eqb p1 p2 = true <-> Pos.compare p1 p2 = Eq.
Proof. 
  rewrite Pos.eqb_compare. 
  destruct (p1 ?= p2)%positive; intuition congruence. 
Qed.

Lemma Ncompare_eqb : forall e1 e2, eqb e1 e2 = true <-> N.compare e1 e2 = Eq. 
Proof. 
  destruct e1; destruct e2; simpl; split; intros; try congruence;
  repeat match goal with 
           | H: context [match ?x with _ => _ end] |- _ => destruct x eqn:?
           | |- context [match ?x with _ => _ end] => destruct x eqn:?
           | H: context [_ && _ = true] |- _ => rewrite Bool.andb_true_iff in H; destruct H  
           | |- context [_ && _ = true] => rewrite Bool.andb_true_iff; split
         end; try congruence; subst; simpl in *;
  try (rewrite -> Pos_compare_eqb in *; congruence).  
Qed. 


Lemma eqb_iff st v : wf_st st -> forall e1, wf_expr st v e1 -> forall e2, wf_expr st v e2 ->  (eqb e1 e2 = true <-> e1 = e2).
Proof. 
  intros. 
  rewrite Ncompare_eqb; split; intro.
  - eapply wf_expr_compare_eq; eauto.  
  - subst. apply N.compare_refl. 
Qed. 
  
Lemma eqb_correct st (Hst:wf_st st) e1 e2 v  (He1: wf_expr st v e1) (He2: wf_expr st v e2) :
  eqb e1 e2 = true <-> equiv e1 e2. 
Proof. 
  rewrite eqb_iff;eauto. 
  split; intros.  
  -  subst. unfold equiv. intros; eapply value_inj; eauto. 
  - eapply canonicity; eauto. 
Qed.
  


