Require Import common monads.
Require Import NArith Omega.

(* -------------------------------------------------------------------------------- *)
Inductive term : Type :=
| Var : N -> positive -> term
| App : term -> term -> positive -> term
| Abs : term -> positive -> term.

Definition ident t := match t with
                        | Var _ id => id
                        | App _ _ id => id
                        | Abs _ id => id
                      end. 

Definition eqb t1 t2 := 
  Pos.eqb (ident t1) (ident t2).

Fixpoint size (t:term) := 
  match t with
    | Var _ _ => 0
    | App t u _ => 1 + size t + size u
    | Abs t _ => 1 + size t
  end. 
(* -------------------------------------------------------------------------------- *)

(* First we have to state that we can equip term with an ordered type.  *)

Module T <: OrderedTypeAlt.
  Definition t := term.    
  Import Compare. 
  Definition compare x y := 
    match x,y with
      | Var n1 _, Var n2 _=> (n1 ?= n2)%N
      | App u1 v1 _, App u2 v2 _ =>  lex (ident u1 ?= ident u2)%positive (ident v1  ?= ident v2)%positive
      | Abs u1 _, Abs u2 _ => (ident u1 ?= ident u2)%positive
      | _, Abs _ _ => Lt
      | Abs _ _, _ => Gt
      | _, App _ _ _ => Lt
      | App _ _ _, _ => Gt
    end.

  Lemma compare_sym x y :  compare y x = CompOpp (compare x y). 
  Proof. 

    destruct x; destruct y;  simpl; try easy; eauto with compare.
    eapply lex_sym; eauto with compare. 
  Qed.

  Lemma compare_trans c x y z: 
    compare x y = c -> compare y z = c -> compare x z = c. 
  Proof.
    intros; destruct x; destruct y; destruct z; simpl in *;
    eauto  using lex_trans with compare || (try congruence).
  Qed.
End T.

(* From this ordered type, we can build finite maps indexed with terms *)
Module TO := OrderedType_from_Alt(T).

Module TMap := FMapAVL.Make (TO).
Module TMapFacts := FMapFacts.Facts (TMap).

Require Import minimap. 

Notation tmap := TMap.t.


Instance term_minimap_ops A : minimap_ops term A :=
  {| 
    content := @TMap.t A;
    set := @TMap.add A;
    get := @TMap.find A;
    empty := @TMap.empty A
  |}. 

Instance term_minimap_gempty A : minimap_gempty  (term_minimap_ops A).
Proof. constructor. Qed. 

Definition equiv x y :=  T.compare x y = Eq. 
Instance equiv_sym : Symmetric equiv. intros x y.   apply TMap.E.eq_sym. Qed.
Instance equiv_trans : Transitive equiv. intros x y z.   apply TMap.E.eq_trans. Qed.

Instance term_equiv : EquivDec term equiv. 
Proof. 
  repeat intro. unfold equiv.  destruct (T.compare x y); auto;  right; discriminate. 
Qed. 

Infix "==" := (equiv) (at level 80). 

Instance term_minimap_props A : minimap_eq_props _ term_equiv (term_minimap_ops A).
Proof.
  constructor.
  - intros. apply TMapFacts.add_eq_o. apply TMap.E.eq_sym; auto.
  - intros. apply TMapFacts.add_neq_o. intro. apply H. apply TMap.E.eq_sym. auto. 
  - repeat intro. subst. apply TMapFacts.find_m_Proper.  eauto. reflexivity. 
Qed.  

(* -------------------------------------------------------------------------------- *)

(* We are now ready to implement the hash-consing state *)
Record hashcons := mk_hcons
  {
    hmap : tmap (term);
    next : positive
  }.



(* memoization part *)

Record memo :=
  mk_memo
    { 
      memo_lifti : (N * positive * N) ~> term;
      memo_substi : (positive * positive * N) ~> term;
      memo_hnf : positive ~> term;
      memo_nf : positive ~> term
    }.

Record state :=
  mk_state
    {
      to_hashcons:> hashcons;
      to_memo:> memo
    }.

Definition empty_state : state :=
  {|
    to_hashcons := {| hmap := TMap.empty _; next := 1|};
    to_memo := mk_memo empty empty empty empty
  |}.

Definition tag t n :=
  match t with
    | Var x _ => Var x n
    | App t u _ => App t u n
    | Abs t _ => Abs t n
  end.

Definition upd t (st: state) :=
  let r := tag t (next st) in
  (r, mk_state
    {|
      hmap := set t r (hmap st);
      next := (next st + 1)
    |}
    st).

(* The smart constructor that performs a lookup in the hash-consing state. *)
Definition mk_term (t:term) (st:state) :=
  match get t (hmap st) with
    | Some x => (x, st)
    | None => upd t st
  end.

Definition mk_Var i st :=
  mk_term (Var i xH) st.

Definition mk_App t u st :=
  mk_term (App t u xH) st.

Definition mk_Abs t st :=
  mk_term (Abs t xH) st.
  
(* -------------------------------------------------------------------------------- *)

(* We are now ready to define lifting and substitution, as memoizing fixpoint combinators.  *)
Definition upd_lifti k v (st: state) :=
  let memo_lifti := set k v (memo_lifti st) in 
  mk_state st (mk_memo memo_lifti (memo_substi st) (memo_hnf st) (memo_nf st)).

Section lifti. 
  Let A := (term * N * state)%type.
  Let B := (term * state)%type.
  Let measure  := fun (n : A) => size (fst (fst n)).  
     
  Definition lifti_rec (n:N) (arg: A) (rec: forall x:A, measure x < measure arg -> B ) : B.
    refine(
        match arg as arg' return arg = arg' -> _ with
          | (t,k,st) => fun Harg => 
                         match get (n,ident t,k) (memo_lifti st) with
                           | Some t => (t,st)
                           | None => 
                             let (r,st) :=
                                 match t  as t' return t = t' -> _ with
                                   | Var i _ => fun H => if N.ltb i k then mk_Var i st else mk_Var (N.add i n) st
                                   | Abs t _ => fun H => let (t,st) := rec (t,(N.succ k),st) _  in  mk_Abs t st
                                   | App t u _ => fun H => let (t,st) := rec (t,k,st) _ in
                                                         let (u,st) := rec (u,k,st) _ in
                                                         mk_App t u st
                                 end eq_refl
                             in 
                             (r,upd_lifti (n,ident t,k) r st)
                         end
        end eq_refl);
    abstract (unfold ltof; destruct arg as [[? ?] ?]; unfold measure; simpl; injection Harg; intros; subst;  simpl; auto with arith).  
  Defined.
  Definition lifti (n: N) : term -> N -> state -> term * state := 
    fun t k st => @Fixm _ (term * state) measure (lifti_rec n) (t,k,st).
End lifti.

Definition lift n t st  := lifti n t 0%N st.

Definition upd_substi k v (st: state) :=
  let memo_substi := set k v (memo_substi st) in 
  mk_state st (mk_memo (memo_lifti st) memo_substi (memo_hnf st) (memo_nf st)).

Section substi. 
  Let A := (term*N*state)%type.
  Let B := (term * state)%type. 
  Let measure := fun (n:A) => size (fst (fst n)).
  Definition substi_rec (w:term) (arg:A) (rec : forall x:A, measure x < measure arg -> B) : B. 

    refine (  match arg as arg' return arg = arg' -> _ with
                     | (t,n,st) => 
                       fun Harg => 
                         match get (ident w,ident t,n) (memo_substi st) with
                           | Some t => (t,st)
                           | None =>
                             let (r,st) := match t as t' return t = t' -> _ with
                                             | Var k _ => fun H => if N.eqb k n 
                                                               then lift n w st
                                                               else if N.ltb k n 
                                                                    then mk_Var k st else mk_Var (N.pred k) st
                                             | Abs t _ => fun H => let (t,st) := rec (t, N.succ n, st) _ in
                                                 mk_Abs t st
                                             | App t u _ => fun H => let (t,st) := rec (t,n,st) _ in
                                                                 let (u,st) := rec (u,n,st) _ in
                                                                 mk_App t u st
                                           end eq_refl
                             in
                             (r,upd_substi (ident w,ident t,n) r st)
                         end
              end eq_refl); abstract   (unfold ltof; destruct arg as [[? ?] ?]; unfold measure; simpl; injection Harg; intros; subst; simpl; auto with arith). 
    Defined. 
  Definition substi (w: term) : term -> N -> state -> term * state :=
    fun t k st =>
      @Fixm _ (term * state) measure (substi_rec w) (t,k,st).
End substi. 
                                       
Definition subst u t st := substi u t 0%N st.

(* Time Eval compute in fuel_fix (fun _ => nat) 10000 (fun rec x => match x with 0 => Some 0 | S n => rec n end) (fun _ => None) 500. *)

Definition upd_hnf k v (st: state) :=
  let memo_hnf := set k v (memo_hnf st) in 
  mk_state st (mk_memo (memo_lifti st) (memo_substi st) memo_hnf (memo_nf st)).

Section fuel.
  Context {A : Type} (P : A -> Type) (f: forall x:A, (forall y:A, option (P y)) -> option (P x)).

  Fixpoint fuel_fix n x :=
    match n with
        0 => None
      | S n => f x (fuel_fix n)
    end.

  Lemma fuel_fix_eq : forall n x, fuel_fix (S n) x = f x (fuel_fix n).
  Proof.
    intros; simpl; f_equal.
  Qed.
End fuel.

Definition hnf_rec (arg: term * state) hnf : option (term * state):=
  let (t,st) := arg in 
  match get (ident t) (memo_hnf st) with
    | Some r => retn (r,st)
    | None =>
      let! (r,st) =
         match t with
               | Var n _ => @retn option _ _ (mk_Var n st)
               | Abs t _ => (let! (t,st) = hnf (t,st);
                               retn (mk_Abs t st))
               | App t u _ =>
                 (let! (t,st) = hnf (t,st);
                     match t with
                       | Abs w _ => let! (t,st) = retn (subst u w st);
                                      hnf (t,st)
                       | h => retn (mk_App t u st)
                     end)
         end;
        retn (r,upd_hnf (ident t) r st)
         end.

Definition hnf (fuel : nat) (t:term) (st: state):option (term * state):=
  fuel_fix (fun _ => term * state)%type hnf_rec fuel  (t,st). 

Definition upd_nf k v (st: state) :=
  let memo_nf := set k v (memo_nf st) in 
  mk_state st (mk_memo (memo_lifti st) (memo_substi st) (memo_hnf st) memo_nf).

Definition nf_rec fuel (arg: term * state) nf : option (term * state):=
  let (t,st) := arg in 
       match get (ident t) (memo_nf st) with
         | Some r => retn (r,st)
         | None =>
            let! (r,st) = 
               match t with
                 | Var n _ => @retn option _ _ (mk_Var n st)
                 | Abs t _  => (let! (t,st) = nf (t,st);
                               retn (mk_Abs t st))
                 | App t u _ =>
                   (let! (t,st) = hnf fuel t st;
                       match t with
                         | Abs w _ => let (t,st) := (subst u w st) in nf (t,st)
                         | h => let! (h,st) = nf (t,st);
                                  let! (u,st) = nf (u,st);
                                     retn (mk_App h u st)
                                     end)
               end;
            retn (r, upd_nf (ident t) r st)
       end.
Definition nf (fuel_hnf: nat) (fuel : nat) (t:term) (st: state):option (term * state):=
  fuel_fix 
    (fun _ => term * state)%type
    (nf_rec fuel_hnf) fuel (t,st). 

(* -------------------------------------------------------------------------------- *)
(* We now are ready for some proofs ! *)

Inductive beta : term -> term -> Prop :=
| beta_0 : forall t u st id1 id2, 
            forall r st', subst u t st = (r,st') ->
             beta (App (Abs t id1) u id2) r
| beta_Abs : forall t1 t2 id1 id2, beta t1 t2 -> beta (Abs t1 id1) (Abs t2 id2)
| beta_App1 : forall t1 t2 u id1 id2, beta t1 t2 -> beta (App t1 u id1) (App t2 u id2)
| beta_App2 : forall u t1 t2 id1 id2, beta t1 t2 -> beta (App u t1 id1) (App u t2 id2).

Inductive beta_star : term -> term -> Prop :=
| beta_star_0 : forall t, beta_star t t
| beta_star_S : forall t1 t2 t3, beta t1 t2 -> beta_star t2 t3 -> beta_star t1 t3.

Definition wf_term st t := 
  get t (hmap st) = Some t.

(* Guarantee that sub-nodes are well-formed. *)
Inductive wf_term_rec st : term -> Prop :=
| wf_term_Var : forall n p, wf_term_rec st (Var n p)
| wf_term_App : forall t u p,
                  wf_term_rec st t ->
                  wf_term_rec st u ->
                  wf_term st t ->
                  wf_term st u ->
                  wf_term_rec st (App t u p)
| wf_term_Abs : forall t p,
                  wf_term_rec st t ->
                  wf_term st t  ->
                  wf_term_rec st (Abs t p).

Hint Constructors wf_term_rec.

Record wf_hashcons (h:hashcons) : Prop :=
  {
    wf_injection : forall e1  e2,
                     wf_term h e1 ->
                     wf_term h e2 ->
                     ident e1 = ident e2 ->
                     e1 == e2;
    wf_lt_next : forall e,
                        wf_term h e ->
                        (ident e < next h)%positive;
    wf_get_wf_eq : forall e e',
                           get e (hmap h) = Some e' ->
                           e == e' /\ wf_term h e';
    wf_term_hered:forall t, wf_term h t -> 
                       wf_term_rec h t
  }.
Hint Constructors wf_hashcons. 
(* ---------------------------------------- *)
(*  *)

Definition wf_mlifti (st:state) : Prop := 
  forall n id i t, get (n,id,i) (memo_lifti st) = Some t -> wf_term st t. 

Definition wf_msubsti (st:state) : Prop := 
  forall id1 id2 i t, get (id1,id2,i) (memo_substi st) = Some t -> wf_term st t. 

Definition wf_hnf (st:state) : Prop :=
  forall id t, get id (memo_hnf st) = Some t -> wf_term st t. 

Definition wf_nf (st:state) : Prop :=
  forall id t, get id (memo_nf st) = Some t -> wf_term st t. 

Record wf_memo (st:state): Prop := 
  {
    wf_memo_lifti : wf_mlifti st;
    wf_memo_substi : wf_msubsti st;
    wf_memo_hnf : wf_hnf st;
    wf_memo_nf : wf_nf st
  }.
Hint Resolve wf_memo_lifti wf_memo_substi wf_memo_hnf wf_memo_nf.

Record wf_state (st:state) : Prop :=
  {
    wf_st_hashcons : wf_hashcons st;
    wf_st_memo : wf_memo st
  }.
Hint Resolve wf_st_hashcons wf_st_memo.

Lemma wf_get_eq st e e' : wf_state st -> get e (hmap st) = Some e' -> e == e'.
Proof. intros. apply wf_get_wf_eq in H0; intuition auto. Qed.
Lemma wf_get_wf st e e' : wf_state st -> get e (hmap st) = Some e' -> wf_term st e'.
Proof. intros. apply wf_get_wf_eq in H0; intuition auto. Qed.
Hint Resolve wf_get_eq wf_get_wf. 

(* ---------------------------------------- *)
(* Boilerplate properties of incr *)
Record incr (h1 h2 : hashcons) : Prop := {
  incr_lt: (next h1 <= next h2)%positive;
  incr_wf_term: forall e, wf_term h1 e -> wf_term h2 e
}.

Hint Resolve incr_lt incr_wf_term.
Hint Constructors incr.

Lemma incr_refl st : incr st st.
Proof. constructor. reflexivity. eauto. Qed.
Hint Immediate incr_refl.


Lemma incr_trans  a b c : incr a b -> incr b c -> incr a c.
Proof. destruct 1, 1. constructor.  zify; omega.  eauto. Qed.

(* ---------------------------------------- *)
(* Properties of equiv *)
Lemma equiv_tag : forall e e' p, e == e' -> e == tag e' p. 
Proof. intros; destruct e'; simpl in *; eauto. Qed.
Hint Resolve equiv_tag : equiv.

Lemma get_equiv st t t': wf_state st -> get t (hmap st) = Some t' -> t == t'.
Proof. intros. apply wf_get_wf_eq in H0; intuition eauto. Qed. 
Hint Resolve get_equiv:equiv.

Ltac inject H :=
  generalize tt; injection H; clear H;
  repeat match goal with
           | |- unit -> _ => intros _; idtac
           | |- _ = _ -> _ => let H := fresh in intro H; subst 
         end. 

Arguments set _ _ _ _ _ _  : simpl never. 
Arguments get  _ _ _ _ _  : simpl never. 

Ltac zomega := zify; omega.

(* ---------------------------------------- *)
(* properties of wb *)
Definition wb {alpha} (st: state) m P := forall (st':state) (out:alpha), m = (out,st') ->
                                                            wf_state st' /\ incr st st' /\ P out st'. 


Lemma wb_bind alpha beta:
  forall st m f P Q,
    wb st m P ->
    (forall (a:alpha) (st':state),
       P a st' -> incr st st' -> wf_state st' -> m = (a, st') -> wb st' (f a st') Q) ->
    wb (alpha:=beta) st (let (a, st') := m in f a st') Q.
Proof.
  unfold wb.
  intros.
  destruct m as [].
  edestruct H as [? []]; eauto. edestruct H0 as [? []]; intuition eauto. zify; omega. 
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
    wf_state st -> (P a st:Prop) ->
    wb st (a, st) P.
Proof.
  unfold wb.
  intros. inject H1; eauto.
Qed.

Lemma wb_branch alpha:
  forall
   (st:state) (b:bool) P1 P2 m1 m2,
    wf_state st -> 
    wb (alpha := alpha) st m1 P1 ->
    wb (alpha := alpha) st m2 P2 ->
    wb st (if b then m1 else m2) (fun out st' => if b then P1 out st' else P2 out st').
Proof.
  destruct b; intros; eapply wb_impl; eauto. 
Qed.

(* ---------------------------------------- *)

Hint Extern 20 => zomega.
Hint Extern 19 =>
(match goal with
   | H: get ?x _ = Some ?x |- _ => apply wf_lt_next in H; simpl in *
 end) : equiv.
Ltac casesR :=
  repeat match goal with
           | H : ?x == ?y, H' : get ?x (set ?y _ _ ) = _ |- _ => rewrite gssR in H' by eauto; try inject H'
           | H : ~ (?x == ?y), H' : get ?x (set ?y _ _ ) = _ |- _ => rewrite gsoR in H' by eauto
           | H : ?x == ?y |- get ?x (set ?y _ _ ) = _ => rewrite gssR by eauto
           | H : ~ (?x == ?y) |-  get ?x (set ?y _ _ ) = _ => rewrite gsoR  by eauto
           | H: get ?x (set ?y _ _) = _ |- _ => destruct (equiv_dec x y)
           | |- get ?x (set ?y _ _) = _ => destruct (equiv_dec x y)
         end; simpl in *. 

  
(* use transitivity, hence slower than eauto.  *)
Ltac equiv := eauto using equiv_trans, equiv_sym with equiv. 

Lemma ident_tag : forall e p, ident (tag e p) = p. 
Proof.  destruct e; simpl; eauto. Qed.

Lemma tag_refl : forall e p, tag e p == e.
Proof.  
  unfold equiv; intros e p.  destruct e; simpl; rewrite ?N.compare_refl, ?Pos.compare_refl; eauto. 
Qed. 
Hint Resolve tag_refl: equiv. 

    
Hint Extern 10 => match goal with 
                   | H: context [ident (tag ?e ?p)] |- _ => rewrite (ident_tag e p) in H
                  | |- context [ident (tag ?e ?p)]  => rewrite (ident_tag e p) 
                 end : equiv.

Hint Extern 5 (_ <= _)%positive => simpl.
Lemma incr_wf_term_rec : forall (st st': hashcons) t, incr st st' ->
                                                 wf_hashcons st ->
                                                 wf_term_rec st t ->
                                                 wf_term_rec st' t. 
Proof.
  intros. 
  induction t;constructor;  inversion H1; subst;eauto. 
Qed.
Hint Resolve incr_wf_term_rec. 
        
Lemma upd_correct  e st : wf_state st ->
                          get e (hmap st) = None ->
                          wf_term_rec st e ->
                          wb st (upd e st) (fun out st' => out == e /\ wf_term st' out).
Proof. 
  intros Hwf Hg He.  intros st' out Hm. 
  

  unfold upd in Hm. inject Hm. simpl. 
  match goal with
      |- _ /\ ?P /\ _ => assert (Hincr: P) 
  end.
  { intuition. unfold wf_term in *. simpl.  casesR.  rewrite <- e1 in Hg. congruence. eauto. }
  split; [| split;[easy|split]].  

  - constructor. 
    + constructor; simpl. 
      * intros.
        unfold wf_term in *. 
        simpl in *. casesR. equiv. equiv. equiv. eauto using wf_injection. 
      * intros. unfold wf_term in *. simpl in *; casesR; equiv. 
      * intros; casesR; simpl; eauto. 
        unfold wf_term.    simpl. 
        split; equiv. 
        rewrite gssR by equiv. f_equal. 
        
      * intros. 
        unfold wf_term in *. simpl in H. casesR.
        inversion He;subst; simpl;constructor; eauto.
        eapply incr_wf_term_rec; eauto. eapply wf_term_hered; eauto. 
    + (* wf_memo *)
      constructor. 
      * unfold wf_mlifti.  intros. simpl in *. apply wf_memo_lifti in H. unfold wf_term. simpl. 
        casesR. f_equal. unfold wf_term in *. rewrite <- e0 in Hg. congruence. apply H. eauto. 
      * unfold wf_msubsti.  intros. simpl in *. apply wf_memo_substi in H. unfold wf_term. simpl. 
        casesR. f_equal. unfold wf_term in *. rewrite <- e0 in Hg. congruence. apply H. eauto.
      * unfold wf_hnf.  intros. simpl in *. apply wf_memo_hnf in H. unfold wf_term. simpl. 
        casesR. f_equal. unfold wf_term in *. rewrite <- e0 in Hg. congruence. apply H. eauto.
      * unfold wf_nf.  intros. simpl in *. apply wf_memo_nf in H. unfold wf_term. simpl. 
        casesR. f_equal. unfold wf_term in *. rewrite <- e0 in Hg. congruence. apply H. eauto.
  - simpl; equiv. 
  - unfold wf_term in *.  simpl.
    casesR. f_equal.
    exfalso. apply n. 
    equiv. 
Qed.

Lemma mk_term_correct t (st: state) :
  wf_state st ->
  wf_term_rec st t ->
  wb st (mk_term t st) (fun t' st' => t' == t /\ wf_term st' t').
Proof.
  unfold mk_term.                     
  destruct (get t (hmap st)) eqn:Hg. 
  - intros. apply wb_ret. eauto. split; equiv.  
  - intros.   eapply upd_correct; eauto. 
Qed.

Lemma mk_App_correct t u (st: state) :  wf_state st ->  wf_term st u ->  wf_term st t -> 
                                        wb st (mk_App u t st) (fun t' st' =>  wf_term st' t').
Proof.
  intros. 
  unfold mk_App. eapply wb_impl. 
  eapply mk_term_correct; eauto. 
  constructor; eauto using wf_term_hered. 
  simpl. intuition.
Qed.

Lemma mk_Abs_correct u (st: state) : 
                     wf_state st ->
                     wf_term st u ->
                     wb st (mk_Abs u st) (fun t' st' => wf_term st' t'). 
Proof.
  intros.  eapply wb_impl. apply mk_term_correct; eauto. 
  constructor; eauto using wf_term_hered. 
  simpl. intuition.
Qed.
      
Lemma mk_Var_correct n (st: state):
                     wf_state st ->
                     wb st (mk_Var n st) (fun t' st' =>  wf_term st' t'). 
Proof.
  intros. eapply wb_impl. eapply mk_term_correct; equiv. 
  simpl; tauto.
Qed.

Hint Resolve mk_App_correct mk_Abs_correct mk_Var_correct.

Ltac cases :=
  repeat match goal with
           | H : ?x = ?y, H' : get ?x (set ?y _ _ ) = _ |- _ => rewrite H in H' by eauto;
                                                              rewrite gss in H' by eauto; 
                                                              try inject H'
                                                                     
           | H : get ?x (set ?x _ _ ) = _ |- _ =>  rewrite gss in H by eauto; try inject H
           | H : ~ (?x = ?y), H' : get ?x (set ?y _ _ ) = _ |- _ => rewrite gso in H' by eauto; try inject H'
           | |- get ?x (set ?x _ _ ) = _ => rewrite gss by eauto
           | H : ~ (?x = ?y) |-  get ?x (set ?y _ _ ) = _ => rewrite gso  by eauto
           | H: get ?x (set ?y _ _) = _ |- _ => destruct (eq_dec x y)
           | |- get ?x (set ?y _ _) = _ => destruct (eq_dec x y)

         end; simpl in *. 

  
    
Lemma wf_term_Abs_inv (st:state) t p : wf_term st (Abs t p) ->
                               wf_state st ->
                               wf_term st t.
Proof. 
  intros. apply wf_term_hered in H;eauto.   inversion H; subst; eauto. 
Qed. 

Lemma wf_term_App_inv1 (st:state) t u p : wf_term st (App t u p) ->
                                        wf_state st ->
                                        wf_term st t.
Proof. 
  intros.   apply wf_term_hered in H;eauto.   inversion H; subst; eauto. 
Qed. 

Lemma wf_term_App_inv2 (st:state) t u p : wf_term st (App t u p) ->
                                        wf_state st ->
                                        wf_term st u.
Proof. 
  intros.   apply wf_term_hered in H;eauto.   inversion H; subst; eauto. 
Qed. 

Hint Resolve wf_term_Abs_inv wf_term_App_inv1 wf_term_App_inv2. 

(* ---------------------------------------- *)
(* memo lifti *)
Lemma wb_upd_lifti n p i st t:
  wf_state st ->
  wf_term st t ->
  wb st (t, upd_lifti (n,p,i) t st)(fun t' st' => wf_term st' t').
Proof. 
  intros Hst Ht st' out Hout. inject Hout. intuition (simpl; eauto). 
  constructor. 
  - simpl; eauto.
  - constructor. 
    * unfold wf_mlifti. intros. simpl in *. cases; eauto.  eapply wf_memo_lifti; eauto. 
    * unfold wf_msubsti. intros. simpl in *. eapply wf_memo_substi; eauto.
    * unfold wf_hnf. intros. simpl in *. eapply wf_memo_hnf; eauto.
    * unfold wf_nf. intros. simpl in *. eapply wf_memo_nf; eauto.
Qed.
    

Lemma lifti_rec_correct n :
  forall (x: term * N * state), 
    forall t i st, x = (t,i,st) ->
       wf_term st t ->
       wf_state st ->
       wb st
          (Fixm (fun n0 : term * N * state => size (fst (fst n0))) (lifti_rec n) x)
          (fun (t' : term) (st' : state) => wf_term st' t').
Proof.
  induction x using (well_founded_induction_type (well_founded_ltof _ (fun x => (size (fst (fst x)) )) )).  
  intros. 
  destruct x as [[t' i'] st']. inject H0. 
  rewrite Fixm_eq. 
  unfold lifti_rec; simpl. 
  destruct (get ( n,ident t, i) (memo_lifti st)) eqn:Hg.
  
  - clear H. eapply wb_ret.  eauto. apply wf_memo_lifti in Hg; intuition  eauto. 
  - destruct t. 
    destruct (n0 <? i)%N. 
    + eapply wb_bind. eauto. 
      intros. simpl in H0.
      eapply wb_upd_lifti; intuition eauto. 
      
    + eapply wb_bind. eauto. 
      intros. simpl in H0.
      eapply wb_upd_lifti; intuition eauto. 
      
    + eapply wb_bind. eapply wb_bind. eapply H.
      unfold ltof. simpl. eauto with arith. 
      reflexivity. 
      eauto. eauto. 

      intros. eapply wb_bind. eapply H. 
      unfold ltof. simpl. eauto with arith. 
      reflexivity. 
      eauto. eauto. 

      intros. eauto. 
      intros. eapply wb_upd_lifti; eauto. 
    + eapply wb_bind. eapply wb_bind. eapply H. unfold ltof. simpl. eauto with arith. 
      reflexivity. 
      eauto. 
      eauto. 
      intros. eauto. 
      intros. eapply wb_upd_lifti; eauto. 
Qed.   

Lemma lifti_correct n t i (st: state) : wf_term st t ->
                               wf_state st -> wb st (lifti n t i st) (fun t' st' => wf_term st' t').
Proof. 
  unfold lifti. eapply lifti_rec_correct. reflexivity. 
Qed. 
 
(* ---------------------------------------- *)
(* substi *)

Lemma wb_upd_substi n p i st t:
  wf_state st ->
  wf_term st t ->
  wb st (t, upd_substi (n,p,i) t st)(fun t' st' => wf_term st' t').
Proof. 
  intros Hst Ht st' out Hout. inject Hout. intuition (simpl; eauto). 
  constructor. 
  - simpl; eauto.
  - constructor. 
    * unfold wf_mlifti. intros. simpl in *.  eapply wf_memo_lifti; eauto. 
    * unfold wf_msubsti. intros. simpl in *. cases; eauto. eapply wf_memo_substi; eauto. 
    * unfold wf_hnf. intros. simpl in *. eapply wf_memo_hnf; eauto.
    * unfold wf_nf. intros. simpl in *. eapply wf_memo_nf; eauto.
Qed.
  
Lemma substi_rec_correct w :
  forall (x: term * N * state), 
    forall t i st, x = (t,i,st) ->
       wf_term st t ->
       wf_term st w ->
       wf_state st ->
       wb st
          (Fixm (fun n0 : term * N * state => size (fst (fst n0))) (substi_rec w) x)
          (fun (t' : term) (st' : state) => wf_term st' t').
Proof.  
  induction x using (well_founded_induction_type (well_founded_ltof _ (fun x => (size (fst (fst x)) )) )).  
  intros. 
  destruct x as [[t' i'] st']. inject H0. 
  rewrite Fixm_eq. 
  unfold substi_rec; simpl. 
  destruct (get (ident w,ident t, i) (memo_substi st)) eqn:Hg.
  
  - clear H. eapply wb_ret.  eauto. apply wf_memo_substi in Hg; intuition  eauto. 
  - destruct t. 
    destruct (n =? i)%N. 
    + eapply wb_bind. eapply lifti_correct; eauto. 
      intros. simpl in H0.
      eapply wb_upd_substi; intuition eauto. 
      
    + eapply wb_bind. 
      eapply wb_branch; eauto.
      intros. 
      simpl in H0. 
      destruct (n <? i)%N; eapply wb_upd_substi; intuition eauto.        
    + eapply wb_bind. eapply wb_bind. eapply H.
      unfold ltof. simpl. eauto with arith. 
      reflexivity. 
      eauto. eauto. eauto.  

      intros. eapply wb_bind. eapply H. 
      unfold ltof. simpl. eauto with arith. 
      reflexivity. 
      eauto. eauto. eauto. 

      intros. eauto. 
      intros. eapply wb_upd_substi. eauto. eauto.  
    + eapply wb_bind. eapply wb_bind. eapply H. unfold ltof. simpl. eauto with arith. 
      reflexivity. 
      eauto. 
      eauto.
      eauto. 
      intros. eauto.  
      intros. eapply wb_upd_substi; eauto. 
Qed. 

Lemma substi_correct w t i (st: state) : 
  wf_term st w -> 
  wf_term st t ->
  wf_state st -> wb st (substi w t i st) (fun t' st' => wf_term st' t').
Proof. 
  unfold substi; intros. eapply substi_rec_correct;eauto. 
Qed. 
Print Assumptions substi_correct. 


(* ---------------------------------------- *)
(* hnf *)

Lemma wb_upd_hnf  i st t:
  wf_state st ->
  wf_term st t ->
  wb st (t, upd_hnf i t st)(fun t' st' => wf_term st' t').
Proof. 
  intros Hst Ht st' out Hout. inject Hout. intuition (simpl; eauto). 
  constructor. 
  - simpl; eauto.
  - constructor. 
    * unfold wf_mlifti. intros. simpl in *.  eapply wf_memo_lifti; eauto. 
    * unfold wf_msubsti. intros. simpl in *. eapply wf_memo_substi; eauto. 
    * unfold wf_hnf. intros. simpl in *. cases. eauto.  eapply wf_memo_hnf; eauto.
    * unfold wf_nf. intros. simpl in *. eapply wf_memo_nf; eauto.
Qed.

(* ---------------------------------------- *)
(* properties of wob *)
Definition wbo {alpha} (st: state) m P := forall (st':state) (out:alpha), m = Some (out,st') ->
                                                             wf_state st' /\ incr st st' /\ P out st'. 

Lemma wbo_bind alpha beta st (m:option (alpha * state)):
  forall f P Q,
    wbo st m P ->
    (forall (a:alpha) (st':state),
       P a st' -> incr st st' -> wf_state st' -> m = Some (a, st') -> wbo st' (f a st') Q) ->
    wbo (alpha:=beta) st (do a, st' <- m; f a st') Q.
Proof.
  unfold wbo; intros.
  destruct (m) as [[]|]; try discriminate. 
  edestruct H as [? []]; eauto. edestruct H0 as [? []];intuition  eauto. 
Qed.

Lemma wbo_wb_bind alpha beta st (m: (alpha * state)):
  forall f P Q,
    wb st m P ->
    (forall (a:alpha) (st':state),
       P a st' -> incr st st' -> wf_state st' -> m =  (a, st') -> wbo st' (f a st') Q) ->
    wbo (alpha:=beta) st (let (a,st') := m in f a st') Q.
Proof.
  unfold wbo; intros.
  destruct (m) as []; try discriminate. 
  edestruct H as [? []]; eauto. edestruct H0 as [? []];intuition  eauto. 
Qed.

Lemma wbo_wb alpha:
  forall m (st:state) (P: alpha -> state -> Prop),
    wf_state st -> 
    wb st m P ->
    wbo st (Some m) P.
Proof.
  unfold wbo.
  intros. inject H1; eauto.
Qed.
Hint Resolve wbo_wb. 

Lemma wbo_ret alpha:
  forall (a:alpha) (st:state) (P: alpha -> state -> Prop),
    wf_state st -> 
    P a st ->
    wbo st (Some (a,st)) P.
Proof.
  unfold wbo.
  intros. inject H1; eauto.
Qed.
Hint Resolve wbo_ret. 

  
Lemma hnf_correct: forall fuel t (st:state),
  wf_term st t ->
  wf_state st -> wbo st (hnf fuel t st) (fun t' st' => wf_term st' t').
Proof.
  unfold hnf. induction fuel. discriminate. 
  intros. rewrite fuel_fix_eq.
  simpl. 
  destruct (get (ident t) (memo_hnf st)) eqn:He. 
  - apply wbo_ret. eauto. apply wf_memo_hnf in He; eauto.  
  - eapply wbo_bind. destruct t; eauto.  
    eapply wbo_bind. 
    now eapply IHfuel; eauto. 
   
    intros. destruct a; eauto.      
    eapply wbo_wb_bind. eapply substi_correct; eauto. 
    intros. eapply IHfuel; eauto. 
    eapply wbo_bind; eauto. 
    intros. 
    eapply wbo_wb. eauto. eapply wb_upd_hnf; eauto. 
Qed. 


(* ---------------------------------------- *)
(* nf *)

Lemma wb_upd_nf  i st t:
  wf_state st ->
  wf_term st t ->
  wb st (t, upd_nf i t st)(fun t' st' => wf_term st' t').
Proof. 
  intros Hst Ht st' out Hout. inject Hout. intuition (simpl; eauto). 
  constructor. 
  - simpl; eauto.
  - constructor. 
    * unfold wf_mlifti. intros. simpl in *.  eapply wf_memo_lifti; eauto. 
    * unfold wf_msubsti. intros. simpl in *. eapply wf_memo_substi; eauto. 
    * unfold wf_hnf. intros. simpl in *.  eauto.  eapply wf_memo_hnf; eauto.
    * unfold wf_nf. intros. simpl in *. cases. eauto.  eapply wf_memo_nf; eauto.
Qed.


Lemma nf_correct fuel' : forall fuel t (st:state),
  wf_term st t ->
  wf_state st -> wbo st (nf fuel' fuel t st) (fun t' st' => wf_term st' t').
Proof.
  unfold nf.  induction fuel. discriminate. 
  intros. rewrite fuel_fix_eq.
  simpl. 
  destruct (get (ident t) (memo_nf st)) eqn:He. 
  - apply wbo_ret. eauto. apply wf_memo_nf in He; eauto.  
  - eapply wbo_bind. 
    destruct t; eauto.  
    * eapply wbo_bind. eapply hnf_correct; eauto.  
      intros. destruct a; eauto.          
      eapply wbo_bind. eapply IHfuel; eauto. 
      intros. eapply wbo_bind. eapply IHfuel; eauto. 
      intros. eauto. 
      intros. eapply wbo_bind. eapply IHfuel; eauto. 
      intros.  eapply wbo_bind. eapply IHfuel; eauto.  
      intros. eauto. eapply wbo_wb_bind. apply substi_correct. eauto. eauto. eauto. 
      
      intros. intuition.  
    * eapply wbo_bind. apply IHfuel; eauto. 
      intros. eauto. 
    * intros. eapply wbo_wb; eauto using wb_upd_nf. 
Qed. 

  

(*
Lemma beta_star_trans:
  forall t1 t2 t3,
    beta_star t1 t2 -> beta_star t2 t3 ->
    beta_star t1 t3.
Proof.
  fix 4.
  destruct 1. auto.
  intros. eapply beta_star_S. apply H. eapply beta_star_trans; eauto.
Qed.

Lemma hnf_beta :
  forall fuel t t',
    hnf fuel t = Some t' ->
    beta_star t t'.
Proof.
  induction fuel. discriminate. destruct t.
  - inversion 1. apply beta_star_0.
  - simpl. intros.
    destruct (hnf fuel t1) eqn:EQ; inversion H; subst; clear H.
    apply IHfuel in EQ.
    assert (beta_star (App t1 t2) (App t t2)).
    { clear H1. induction EQ. apply beta_star_0. eapply beta_star_S; eauto.
      apply beta_App1. auto. }
    eapply beta_star_trans. eauto.
    destruct t; inversion H1; subst; clear H1; try apply beta_star_0.
    eapply beta_star_S. apply beta_0. auto.
  - simpl. intros. destruct (hnf fuel t) eqn:?; inversion H; subst; clear H.
    apply IHfuel in Heqo.
    induction Heqo. apply beta_star_0. eapply beta_star_S. apply beta_Abs; eauto. auto.
Qed.

Lemma nf_beta :
  forall fuel1 fuel2 t t',
    nf fuel1 fuel2 t = Some t' ->
    beta_star t t'.
Proof.
  induction fuel2. discriminate. destruct t.
  - inversion 1. apply beta_star_0.
  - simpl. intros.
    destruct (hnf fuel1 t1) eqn:EQ; inversion H; subst; clear H.
    eapply hnf_beta in EQ.
    eapply beta_star_trans.
    { clear H1. induction EQ. apply beta_star_0. eapply beta_star_S; eauto.
      apply beta_App1. auto. }
    clear EQ. destruct t.
    + destruct (nf fuel1 fuel2 (Var n)) eqn:?; try discriminate.
      apply IHfuel2 in Heqo.
      eapply beta_star_trans.
      { clear H1. induction Heqo. apply beta_star_0. eapply beta_star_S; eauto.
        apply beta_App1. auto. }
      clear Heqo.
      destruct (nf fuel1 fuel2 t2) eqn:?; inversion H1. subst. clear H1.
      apply IHfuel2 in Heqo.
      induction Heqo. apply beta_star_0. eapply beta_star_S; eauto.
      apply beta_App2. auto.
    + destruct (nf fuel1 fuel2 (App t3 t4)) eqn:?; try discriminate.
      apply IHfuel2 in Heqo.
      eapply beta_star_trans.
      { clear H1. induction Heqo. apply beta_star_0. eapply beta_star_S; eauto.
        apply beta_App1. auto. }
      clear Heqo.
      destruct (nf fuel1 fuel2 t2) eqn:?; inversion H1. subst. clear H1.
      apply IHfuel2 in Heqo.
      induction Heqo. apply beta_star_0. eapply beta_star_S; eauto.
      apply beta_App2. auto.
    + apply IHfuel2 in H1.
      eapply beta_star_S. apply beta_0. auto.
  - simpl. intros.
    destruct (nf fuel1 fuel2 t) eqn:?; inversion H; subst; clear H.
    apply IHfuel2 in Heqo.
    induction Heqo. apply beta_star_0. eapply beta_star_S; eauto.
    apply beta_Abs. auto.
Qed.
*)
Section big.

Definition big := 1000.

Definition Nf t := nf big big t.

Section nat.
  Context {A : Type}.
  Variable iter : A -> A.
  Variable init : A.
  Fixpoint eval_rec t := match t with
                           | Var 0 _ => retn init
                           | App (Var 1 _ ) u _ => let! x = eval_rec u;
                                              retn (iter x)
                           | _ => None
                         end.
  Definition eval_nat (t: term) :=
    match t with
        | Abs (Abs t _) _  => eval_rec t
        | _ => None
    end.
End nat.
Definition compute_nat := eval_nat S O.

Definition normal_nat n st : option nat := let! (t,st) = Nf n st; compute_nat t.

Fixpoint eval_lrec t :=
  match  t with
    | Var 0 _ => retn (List.nil)
    | App (App (Var 1 _) x _) l _ =>
      let! x = compute_nat x;
      let! q = eval_lrec l  ;
         retn (List.cons x q)
    | _ => None
  end.

Fixpoint eval_list_of_nats t :=
  match  t with
    | Abs (Abs t _) _ => eval_lrec t
    | _ => None
  end.

Definition normal_list_of_nats l st := let! (l,st) = Nf l st; eval_list_of_nats l.

End big.

(* A bit of monadic boilerplate *)

Definition tconstr := (state -> term * state).
Definition abs : tconstr -> tconstr := fun x st => let (x,st) := x st in mk_Abs x st. 
Definition app :  tconstr -> tconstr -> tconstr := fun x y st => 
                                                   let (x,st) := x st in
                                                   let (y,st) := y st in
                                                   mk_App x y st.
Definition var : N -> tconstr := mk_Var.
 
Notation "\ x" := (abs x) (at level 20).
Notation "x # y" := (app x y) (left associativity, at level 25).
Coercion var : N >-> tconstr.

Module C.

Open Scope N.
Definition K := \\1.

(* Eval vm_compute in let (t,st) := (K # 0) empty_state in *)
(*                    let (k',st ) := K st in fst (lift 4 k' st). *)
Definition false := \\ 0.
Definition true  := \\ 1.
Definition cond  := \\\ (2 # 1 #  0).

Definition pair  := \\\ (0 #  2 #  1).
Definition fst  := \ (0 #  true).
Definition snd  := \ (0 #  false).

Definition zero := \\ 0.
Definition succ := \\\ (1 #  (2 #  1 #  0)).
Definition one  := succ #  zero.

Fixpoint church n := match n with O => zero | S n => (succ #  (church n)) end.

Definition null := \ (0 #  ( K #  false) #  true).

Definition add := \\ \\ (3 #  1 #  (2 #  1 #  0)).
Definition pred :=
  let loop := \ (let pred := fst #  0 in
                 pair #  (succ #  pred) #  pred )
  in \ (snd #  (0 #  loop #  (pair #  zero #  zero))).

Definition geq := \\ (1 #  pred #  0 #  (K #  false) #  true).

Definition iter := \\( 0 #  1 #  (1 #  one)).
Definition ack  := \(0 #  iter #  succ #  0).

Definition Y := \(  (\ (1 #  (0 #  0) ))  #  (\ ( 1 #  ( 0 #  0)))).
Definition FIX := let F := (\\
                    let f := 0 in
                    let x := 1 in
                    (f #  ( x #  x #  f ) )) in F #  F.

Definition SUM :=
  FIX # (\\ ( (cond # (null # 0)) # zero # (add # 0 # (1 # (pred # 0))))).



Definition nil := \\0.
Definition cons := \\ (\\ (1 #  3 #  (2 #  1 #  0))).
Definition isnil := \(0 # (\\ false) # true).
Definition head  := \ (0 # (\\ (1)) # false).
Definition tail  :=
  \(fst # (0 # (\\(pair # (snd # 0)# (cons # 1#(snd#0))))#(pair#nil#nil))).

Definition append := \\ \\ (3 #  1 #  (2 #  1 #  0)).

Definition partition :=
  \\
    (let fork :=
         \\
           (
             let pred := 3 in let l := 2 in let x := 1 in let acc := 0 in
             let l1 := fst #  acc in
             let l2 := snd #  acc in
             pred #  x #  (pair #  (cons #  x #  l1) #  l2) #  (pair #  l1 #  (cons #  x #  l2))
           )
     in
     0 #  fork #  (pair #  nil #  nil)
    ).

Definition quicksort' :=
  FIX #  (\
           (let sort :=
               \\
                 (let rec := 3 in let a := 1 in let l := 0 in
                 let p := partition #  (geq #  a) #  l in
                 append #  (rec # (fst #  p)) #  (cons #  a #  (rec #(snd #  p))) )
           in
           \ (0 #  sort #  nil))
        ).

(* A more usual presentation of quicksort. *)
Definition quicksort :=
  FIX #  (\\
            (cond
                # (isnil # 0)
                # (nil)
                # (let hd := head # 0 in
                    let tl := tail # 0 in
                    let p := partition #  (geq #  hd) #  tl in
                    let rec := 1 in
                    append #  (rec # (fst #  p)) #  (cons # hd #  (rec #(snd #  p))) ))).

Fixpoint list l :=
  match l with
    | List.cons t q => cons # t # (list q)
    | List.nil => nil
  end.

End C.

(* Definition big := pow 2 14. *)


Definition run_Nf (c: tconstr)  := 
  let (t,st) := c empty_state in  Nf t st.

Definition run_normal_nat (c: tconstr)  := 
  let (t,st) := c empty_state in  normal_nat t st.

Time Eval vm_compute in  run_normal_nat (C.SUM # C.church 3).
Time Eval vm_compute in run_normal_nat (C.SUM # C.church 5).
(* Eval vm_compute in normal_nat big (T.snd # (T.pair # T.zero # T.one)). *)
(* Eval vm_compute in normal_nat big (T.pred # T.church 5). *)

Require Import List.
Open Scope list_scope.

Definition list l := C.list (List.map C.church l).

(* Eval vm_compute in normal_list_of_nats big (list  (1::nil))%nat. *)
(* Eval vm_compute in normal_list_of_nats big (T.append #  (list  (1::2:: nil)) # (list (nil)))%nat. *)
(* Eval vm_compute in nf big big (T.geq # T.church 2 # T.church 1). *)

(* Eval vm_compute in normal_list_of_nats big (T.snd # (T.partition # (T.geq # T.church 3) # (list (1::2 ::5::nil))))%nat. *)
(* Eval vm_compute in normal_list_of_nats big (T.append #  (list  (1::2:: nil)) # (list  (nil)))%nat. *)

Definition run_normal_list (c:tconstr) := let (t,st) := c empty_state in 
                                normal_list_of_nats t st. 
Definition quicksort  l := run_normal_list (C.quicksort # (list l)).
Definition quicksort' l := run_normal_list (C.quicksort' # (list l)).
Require Import List.

Definition bench := 0 :: 3 :: 5 :: 2 :: 4 :: 1 :: nil.
(* Timings without memoization.  
Time Eval vm_compute in (quicksort bench). (* 73s *)
Time Eval vm_compute in quicksort' bench.  (* TIME OUT >  3600s *)
 *)             

(* Timing with memoization of lifti and substi 
Time Eval vm_compute in (quicksort bench). (* 2s *)
Time Eval vm_compute in quicksort' bench.  (* 120s *)
*)
(* Timing with memoization of lifti and substi and hnf*)
Time Eval vm_compute in (quicksort bench). (* 1s *)
Time Eval vm_compute in quicksort' bench.  (* 4s *)
