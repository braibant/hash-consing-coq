Require Import smart_common monads.
Require Import NArith Omega.

Inductive term : Type :=
| Var : N -> term
| App : term -> term -> term
| Abs : term -> term.

Fixpoint size t :=
  match t with
    | Var _ => 1
    | App u v => 1 + size u + size v
    | Abs t => 1 + size t
  end.

Extract Inductive term =>
  "Helpers_lambda.term"
  ["Helpers_lambda.hVar" "Helpers_lambda.hApp" "Helpers_lambda.hAbs"]
  "Helpers_lambda.term_match".

Parameter memo_term : memoizer term.
Extract Inlined Constant memo_term => "Helpers_lambda.term_memo".

Definition lifti : N -> term -> N -> term.
refine (
  memo (fun n =>
    memo_rec (well_founded_ltof _ size) (fun t rec k =>
      memo (fun k =>
        match t with
          | Var i => fun rec => if N.ltb i k then Var i else Var (N.add i n)
          | Abs t => fun rec => Abs (rec t _ (N.succ k) )
          | App t u => fun rec => App (rec t _ k) (rec u _ k)
        end) k rec)));
unfold ltof; simpl; abstract omega.
Defined.

Definition lift n t := lifti n t 0%N.

Definition substi : term -> term -> N -> term.
refine(
  memo (fun w =>
    memo_rec (well_founded_ltof _ size) (fun t rec n =>
      memo (fun n =>
        match t with
          | Var k => fun rec => if N.eqb k n then lift n w else if N.ltb k n then Var k else Var (N.pred k)
          | Abs t => fun rec => Abs (rec t _ (N.succ n))
          | App t u => fun rec => App (rec t _ n) (rec u _ n)
        end) n rec)));
unfold ltof; simpl; abstract (omega).
Defined.

Definition subst u t := substi u t 0%N.

Definition hnf : Fuel -> term  -> option (term) :=
  memo_fuel _ (fun x => term) (fun (t:term) hnf =>
    match t with
      | Var n => Some (Var n)
      | Abs t => let! t = hnf (t);
                 retn (Abs t)
      | App t u =>
        let! t = hnf t;
        match t with
          | Abs w => hnf (subst u w)
          | h => retn (App h u)
        end
    end).

Definition nf big_fuel :=
  memo_fuel _ (fun x => term) (fun (t: term) nf =>
    match t with
      | Var n => Some (Var n)
      | Abs t => let! t = nf (t);
                 retn (Abs t)
      | App t u =>
        let! t = hnf big_fuel t;
        match t with
          | Abs w => nf (subst u w)
          | h => let! h = nf h;
                 let! u = nf u;
                 retn (App h u)
        end
    end).

Inductive beta : term -> term -> Prop :=
| beta_0 : forall t u, beta (App (Abs t) u) (subst u t)
| beta_Abs : forall t1 t2, beta t1 t2 -> beta (Abs t1) (Abs t2)
| beta_App1 : forall t1 t2 u, beta t1 t2 -> beta (App t1 u) (App t2 u)
| beta_App2 : forall u t1 t2, beta t1 t2 -> beta (App u t1) (App u t2).

Inductive beta_star : term -> term -> Prop :=
| beta_star_0 : forall t, beta_star t t
| beta_star_S : forall t1 t2 t3, beta t1 t2 -> beta_star t2 t3 -> beta_star t1 t3.

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

Section big.

Variable big:nat.

Definition Nf t := nf big big t.

Section nat.
  Context {A : Type}.
  Variable iter : A -> A.
  Variable init : A.
  Fixpoint eval_rec t := match t with
                           | Var 0 => retn init
                           | App (Var 1) u => let! x = eval_rec u;
                                              retn (iter x)
                           | _ => None
                         end.
  Definition eval_nat t :=
    match t with
        | Abs (Abs t) => eval_rec t
        | _ => None
    end.
End nat.
Definition compute_nat := eval_nat S O.

Definition normal_nat n := let! t = Nf n; compute_nat t.

Fixpoint eval_lrec t :=
  match t with
    | Var 0 => retn (List.nil)
    | App (App (Var 1) x) l =>
      let! x = compute_nat x;
      let! q = eval_lrec l  ;
         retn (List.cons x q)
    | _ => None
  end.

Fixpoint eval_list_of_nats t :=
  match t with
    | Abs (Abs t) => eval_lrec t
    | _ => None
  end.

Definition normal_list_of_nats l := let! l = Nf l; eval_list_of_nats l.

End big.

Notation "\ x" := (Abs x) (at level 20).
Notation "x # y" := (App x y) (left associativity, at level 25).

Coercion Var : N >-> term.

Module T.

Open Scope N.
Definition K := \\1.

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
  \(fst # (0 # (\\(pair # (snd # 0)# (cons#1#(snd#0))))#(pair#nil#nil))).

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

End T.

(* Definition big := pow 2 14. *)

(* Time Eval vm_compute in nf big big (T.SUM # T.church 1). *)
(* Time Eval vm_compute in normal_nat big (T.SUM # T.church 5). *)
(* Eval vm_compute in normal_nat big (T.snd # (T.pair # T.zero # T.one)). *)
(* Eval vm_compute in normal_nat big (T.pred # T.church 5). *)

Require Import List.
Open Scope list_scope.

Definition list l := T.list (List.map T.church l).

(* Eval vm_compute in normal_list_of_nats big (list  (1::nil))%nat. *)
(* Eval vm_compute in normal_list_of_nats big (T.append #  (list  (1::2:: nil)) # (list (nil)))%nat. *)
(* Eval vm_compute in nf big big (T.geq # T.church 2 # T.church 1). *)

(* Eval vm_compute in normal_list_of_nats big (T.snd # (T.partition # (T.geq # T.church 3) # (list (1::2 ::5::nil))))%nat. *)
(* Eval vm_compute in normal_list_of_nats big (T.append #  (list  (1::2:: nil)) # (list  (nil)))%nat. *)

Definition quicksort fuel l := normal_list_of_nats fuel (T.quicksort # (list l)).
Definition quicksort' fuel l := normal_list_of_nats fuel (T.quicksort' # (list l)).
