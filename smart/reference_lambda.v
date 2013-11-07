Require Import NArith.
Require Import List.
Require Import smart_common monads. 

Inductive term : Type :=
| Var : N -> term
| App : term -> term -> term
| Abs : term -> term.

Fixpoint lifti n t k :=
  match t with
    | Var i => if N.ltb i k then Var i else Var (i + n)
    | Abs t => Abs ( lifti n t (N.succ k))
    | App t u => App (lifti n t k) (lifti n u k)
  end.
Definition lift n t := lifti n t 0.

Fixpoint substi w t n :=
  match t with
      Var k => if N.eqb k n then lift n w else if N.ltb k n then Var k else Var (N.pred k)
    | Abs t => Abs (substi w t (N.succ n))
    | App t u => App (substi w t n) (substi w u n)
  end.
Definition subst u t := substi u t 0.

Definition hnf : nat -> term  -> option (term) :=
  fuel_fix (fun x => term)
           (fun (t:term) hnf =>
              match t with
                | Var n => Some (Var n)
                | Abs t => let! t = hnf (t);
                              retn (Abs t)
                | App t u =>
                  let! t =  hnf (t);
                     match t with
                       | Abs w => hnf (subst u w)
                       | h => retn (App h u)
                     end
              end).

Definition nf big_fuel :=
  fuel_fix (fun x => term)
           (fun (t: term) nf =>
              match t with
                | Var n => Some (Var n)
                | Abs t => let! t = nf (t);
                               retn (Abs t)
                | App t u =>
                  let! t = hnf big_fuel t;
                     match t with
                       | Abs w => let! t = nf (subst u w);
                                     retn t
                       | h => let! h = nf h;
                              let! u = nf u;
                                 retn (App h u)
                     end
              end).

Definition big := 10000.

Definition Nf t := nf big big t.

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
                 append #  (rec # (fst #  p)) #  (cons #  a #  (rec #(snd #  p))))
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
                    append #  (rec # (fst #  p)) #  (cons # hd #  (rec #(snd #  p)))))).

Fixpoint list l :=
  match l with
    | List.cons t q => cons # t # (list q)
    | List.nil => nil
  end.
End T.


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

Definition normal_nat n := let! t = Nf n; compute_nat (t).

(* Time Eval vm_compute in nf big big (T.SUM # T.church 1). *)
(* Time Eval vm_compute in normal_nat (T.SUM # T.church 5). *)
(* Eval compute in normal_nat (T.snd # (T.pair # T.zero # T.one)). *)
(* Eval compute in normal_nat (T.pred # T.church 5). *)

Section u.
  Fixpoint eval_lrec t := match t with
                           | Var 0 => retn (List.nil)
                           | App (App (Var 1) x) l =>
                             let! x = compute_nat x;
                             let! q = eval_lrec l  ;
                             retn (List.cons x q)
                           | _ => None
                         end.
  Fixpoint eval_list_of_nats t :=
    match t with
        Abs (Abs t) => eval_lrec t
      | _ => None
    end.
End u.
Definition normal_list_of_nats l := let! l = Nf l; eval_list_of_nats l.

Open Scope list_scope.

Definition list l := T.list (List.map T.church l).
(* Eval vm_compute in normal_list_of_nats (list  (1::nil))%nat. *)
(* Eval vm_compute in normal_list_of_nats (T.append #  (list  (1::2:: nil)) # (list  (nil)))%nat. *)
(* Eval vm_compute in nf big big (T.geq # T.church 2 # T.church 1). *)

(* Eval vm_compute in normal_list_of_nats (T.snd # (T.partition # (T.geq # T.church 3) # (list  (1::2 ::5::nil))))%nat. *)
(* Eval vm_compute in normal_list_of_nats (T.append #  (list  (1::2:: nil)) # (list  (nil)))%nat. *)

Definition quicksort l := normal_list_of_nats  (T.quicksort # (list l)).
Definition quicksort' l := normal_list_of_nats  (T.quicksort' # (list l)).

(* Time Eval vm_compute in quicksort' (0::3::5::2::4::1::nil). *)