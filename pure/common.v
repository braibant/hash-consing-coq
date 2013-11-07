Require Eqdep.

(** Pot-pourri of definitions that are useful in other parts of the development. *)

Definition bind {A B: Type} (f: option A) (g: A -> option B) : option B :=
  match f with
    | Some x => g x
    | None => None
  end.

Definition bind2 {A B C: Type} (f: option (A * B)) (g: A -> B -> option C) : option C :=
  match f with
  | Some (x, y) => g x y
  | None => None
  end.

Remark bind_inversion:
  forall (A B: Type) (f: option A) (g: A -> option B) (y: B),
  bind f g = Some y ->
  {x | f = Some x /\ g x = Some y}.
Proof. 
  intros; destruct f.  simpl in H.
  exists a; auto. 
  discriminate. 
Qed. 

Remark bind_inversion_None {A B} x (f: A -> option B) : bind x f = None -> 
  (x = None) + (exists y, x = Some y /\ f y = None).
Proof. 
  destruct x; simpl; intuition.
  right. exists a; intuition.  
Qed. 

Remark bind2_inversion:
  forall {A B C: Type} (f: option (A*B)) (g: A -> B -> option C) (y: C),
    bind2 f g = Some y ->
      {x1 : A & {x2 : B | f = Some (x1,x2) /\ g x1 x2 = Some y}}.
Proof. 
  intros ? ? ? [ [x y] | ] ? ? H; simpl in H; eauto.
  discriminate. 
Qed.

Notation "'do' X <- A ; B" := (bind A (fun X => B) )
  (at level 200, X ident, A at level 100, B at level 200). 

Notation "'do' X , Y  <- A ; B" := (bind2 A (fun X Y => B))
 (at level 200, X ident, Y ident, A at level 100, B at level 200).


Notation "'check' A ; B" := (if A then B else None)
  (at level 200, A at level 100, B at level 200). 

Ltac invert_do H :=
  match type of H with
    | (Some _ = Some _) =>
        inversion H; clear H; try subst
    | (None = Some _) =>
        discriminate
    | (bind ?F ?G = Some ?X) => 
        let x := fresh "x" in
          let EQ1 := fresh "EQ" in
            let EQ2 := fresh "EQ" in
              destruct (bind_inversion _ _ F G _ H) as [x [EQ1 EQ2]];
        clear H;
        try (invert_do EQ2)
    | (bind ?x ?f = None) => 
        let EQ := fresh "EQ" in 
        let EQ1 := fresh "EQ" in
        let EQ2 := fresh "EQ" in
        let x' := fresh "x" in 
        destruct (bind_inversion_None x f H) as [EQ | [x' [EQ1 EQ2]]];
        clear H;
        try (invert_do EQ1);
        try (invert_do EQ2);
        try (invert_do EQ)
  end. 
  
Ltac simpl_do := 
    repeat match goal with 
      | H : Some _ = Some _ |- _ => injection H; clear H; intros; subst 
      | H : (None = Some _) |- _ => discriminate
      | H : (Some _ = None) |- _ => discriminate
      | H : None = None |- _ => clear H
      | H : (bind ?F ?G = Some ?X) |- _ => 
        destruct (bind_inversion _ _ F G _ H) as [? [? ?]]; clear H
      | H : (bind2 ?F ?G = Some ?X) |- _ => 
        destruct (bind2_inversion F G _ H) as [? [? [? ?]]]; clear H
      | |- context [(bind (Some _) ?G)] => simpl
      | H : (bind ?x ?f = None) |- _ => 
        let EQ := fresh in 
        destruct (bind_inversion_None x f H) as [EQ | [? [EQ ?]]]; 
          rewrite EQ in H; simpl in H
                                                  
      | H : ?x = Some ?y |- context [?x] => rewrite H
    end. 

Ltac intro_do n H :=
  match goal with 
    | |- context [do _ <- ?x; _] =>
      destruct x as [n|] eqn:H; simpl 
  end.


(** The dependent type swiss-knife. *)
Ltac injectT :=  subst; repeat match goal with 
                                   H : existT _ _ _ = existT _ _ _ |- _ => 
                                   apply Eqdep.EqdepTheory.inj_pair2 in H
                                 |   H : context [eq_rect ?t _ ?x ?t ?eq_refl] |- _ => 
                                     rewrite <- Eqdep.EqdepTheory.eq_rect_eq in H
                                 |   H : context [eq_rect ?t _ ?x ?t ?H'] |- _ => 
                                     rewrite (Eqdep.EqdepTheory.UIP_refl _ _ H') in H;
                                       rewrite <- Eqdep.EqdepTheory.eq_rect_eq in H
                                 |   H : existT _ ?t1 ?x1 = existT _ ?t2 ?x2 |- _ => 
                                     let H' := fresh "H'" in 
                                     assert (H' := EqdepFacts.eq_sigT_fst H); subst
                               end; subst.

Ltac inject H :=
      injection H; clear H; intros; subst. 

Require Import BinPos Omega.

Lemma positive_strong_ind:
  forall (P:positive->Prop),
    (forall n, (forall m, (m < n)%positive -> P m) -> P n) ->
    forall n, P n.
Proof.
  intros P HP.
  assert (forall n m, (m < n)%positive -> P m).
  induction n using Pos.peano_ind; intros.
  zify; omega.
  apply HP. intros.
  apply IHn. zify; omega.
  intros. apply (H (Psucc n)).
  zify; omega.
Qed.

(** missing lemmas from the stdlib  *)
Lemma N_compare_sym: forall x y, N.compare y x = CompOpp (N.compare x y). 
Proof. intros. rewrite Ncompare_antisym. auto. Qed.

Lemma Pos_compare_sym: forall x y, Pos.compare y x = CompOpp (Pos.compare x y). 
Proof. exact Pos.compare_antisym. Qed. 

Lemma N_compare_trans x y z c :
  N.compare x y = c -> N.compare y z = c -> N.compare x z = c. 
Proof.
  destruct c.
  intros; rewrite N.compare_eq_iff in * |- *. congruence. 
  intros; rewrite N.compare_lt_iff in * |- *. zify.  omega.
  intros; rewrite N.compare_gt_iff in * |- *. zify.  omega.
Qed. 

Lemma Pos_compare_trans: forall c x y z, Pos.compare x y = c -> Pos.compare y z = c -> Pos.compare x z = c.
Proof. 
  destruct c.
  intros; rewrite Pos.compare_eq_iff in * |- *. congruence. 
  intros; rewrite Pos.compare_lt_iff in * |- *. zify.  omega.
  intros; rewrite Pos.compare_gt_iff in * |- *. zify.  omega.
Qed. 

Hint Resolve N_compare_sym N_compare_trans Pos_compare_sym Pos_compare_trans : compare. 

(** Boilerplate definitions for FMaps. *)
Require Export FMapPositive FMapAVL OrderedTypeAlt.
Require Export FMapFacts. 

Module PMap := PositiveMap.
Module PMapFacts := FMapFacts.Facts(PMap).

Module Type MyOrderedTypeAlt.
 Parameter t : Type.

 Parameter compare : t -> t -> comparison.
 Infix "?=" := compare (at level 70, no associativity).

 Parameter compare_sym : forall x y, (y?=x) = CompOpp (x?=y).
 Parameter compare_trans : forall c x y z, (x?=y) = c -> (y?=z) = c -> (x?=z) = c.
 Parameter reflect : forall x y, x ?= y = Eq -> x = y.
End MyOrderedTypeAlt. 

 
Module PairOrderedTypeAlt(O U: MyOrderedTypeAlt) <: MyOrderedTypeAlt.
  Definition t := (O.t * U.t)%type.
  Definition compare (m n: t) :=
    let '(mo,mu) := m in
      let '(no,nu) := n in
        match O.compare mo no with
          | Eq => U.compare mu nu
          | r => r
        end.
  Lemma compare_sym: forall x y, compare y x = CompOpp (compare x y). 
  Proof.
    intros [x x'] [y y']; simpl.
    rewrite O.compare_sym, U.compare_sym. destruct (O.compare x y); reflexivity.
  Qed.
  Lemma compare_trans: forall c x y z, compare x y = c -> compare y z = c -> compare x z = c.
    intros c [x x'] [y y'] [z z']; simpl.
    case_eq (O.compare x y); case_eq (O.compare y z); intros xy yz; simpl;
      try rewrite (O.compare_trans _ _ _ _ yz xy); intros; subst; try discriminate; auto.
      eauto using U.compare_trans.
      apply O.reflect in yz; subst. rewrite xy. trivial.
      apply O.reflect in yz; subst. rewrite xy. trivial.
      apply O.reflect in xy; subst. rewrite yz. trivial.
      apply O.reflect in xy; subst. rewrite yz. trivial.
  Qed.
  Lemma reflect: forall x y, compare x y = Eq -> x = y.
  Proof.
    intros [x x'] [y y']. simpl.
    case_eq (O.compare x y); intro xy; try apply O.reflect in xy;
    case_eq (U.compare x' y'); intro xy'; try apply U.reflect in xy';
      intro; try discriminate; subst; auto.
  Qed.
End PairOrderedTypeAlt.

Module Pos_as_OTA <: OrderedTypeAlt.
  Definition t := positive.
  Fixpoint compare x y := 
    match x,y with 
      | xH, xH => Eq
      | xH, _ => Lt
      | _, xH => Gt
      | xO a, xO b => compare a b
      | xI a, xI b => compare a b
      | xI a, xO b => Gt
      | xO a, xI b => Lt
    end.
  Lemma compare_sym: forall x y, compare y x = CompOpp (compare x y). 
  Proof. induction x; intros y; destruct y; simpl; auto. Qed.
  Lemma compare_trans: forall c x y z, compare x y = c -> compare y z = c -> compare x z = c. 
  Proof. 
    intros c x. revert c.
    induction x; intros c y z; destruct y; simpl; intro H; auto; subst; try discriminate H;
      destruct z; simpl; intro H'; eauto; try discriminate H'.
  Qed.
  Lemma reflect: forall x y, compare x y = Eq -> x = y.
  Proof. 
    induction x; intros y; destruct y; simpl; intro H; auto; try discriminate.
    apply IHx in H. subst. reflexivity.
    apply IHx in H. subst. reflexivity.
  Qed.
End Pos_as_OTA.

Module PP := PairOrderedTypeAlt Pos_as_OTA Pos_as_OTA. 
Module PPO := OrderedType_from_Alt(PP).
Module PPMap := FMapAVL.Make PPO. 
Module PPMapFacts := FMapFacts.Facts (PPMap). 


(** Results about lexicographic order *)

Module Compare.

Require Import Setoid. 

Notation lex x y := 
  (match x with 
    | Eq => y
    | c => c
  end). 
Section t. 
  Variable A B: Type. 
  Variable f : A -> A -> comparison.
  Variable g : B -> B -> comparison.
  Hypothesis Hf_sym: forall x y,  f x y = CompOpp (f y x). 
  Hypothesis Hf_trans:forall c x y z,  f x y = c -> f y z = c -> f x z = c. 
  Hypothesis Hg_sym: forall x y,  g x y = CompOpp (g y x). 
  Hypothesis Hg_trans:forall c x y z,  g x y = c -> g y z = c -> g x z = c. 

  Hint Resolve Hf_sym Hf_trans Hg_sym Hg_trans : lex. 
  Lemma lex_sym x1 x2 y1 y2: lex (f x1 x2) (g y1 y2) = CompOpp (lex (f x2 x1) (g y2 y1)).
  Proof. 
    repeat match goal with 
               |- context [f ?x ?y] => case_eq (f x y); intros ?
             | |- context [f ?x ?y] => case_eq (g x y); intros ?
             | H : f ?x ?y = _, H' : f ?y ?x = _ |- _ => 
               rewrite Hf_sym, H' in H; simpl in H; clear H'; try discriminate
           end; simpl; try eauto with lex. 
  Qed.

  Lemma CompOpp_move x y : CompOpp x = y <-> x = CompOpp y. 
    destruct x; destruct y; simpl; intuition discriminate.  
  Qed. 
  
  Lemma Hf_sym' c x y : f x y = CompOpp c -> f y x = c. 
  Proof.   
    intros. rewrite Hf_sym. rewrite CompOpp_move. assumption.
  Qed. 

  Hint Resolve Hf_sym' : lex. 

  Lemma lex_trans c x1 x2 x3 y1 y2 y3: 
    lex (f x1 x2) (g y1 y2) = c -> 
    lex (f x2 x3) (g y2 y3) = c -> 
    lex (f x1 x3) (g y1 y3) = c.
  Proof. 
    Ltac finish :=
      repeat match goal with 
               | H : ?x = ?y, H' : ?x = ?z |- _ => constr_eq y z; clear H'
               | H : ?x = ?y, H' : ?x = ?z |- _ => 
                 rewrite H in H'; discriminate
             end; simpl; try eauto with lex. 

    repeat match goal with 
               |- context [f ?x ?y] => case_eq (f x y); intros ?
             | |- context [f ?x ?y] => case_eq (g x y); intros ?
             | H : f ?x ?y = _, H' : f ?y ?x = _ |- _ => 
               rewrite Hf_sym, H' in H; simpl in H; clear H'; try discriminate
             | H : f ?x ?y = _, H' : f ?y ?z = _ |- _ => 
               pose proof (Hf_trans _ _ _ _ H H'); clear H H'
           end; finish. 

    assert (f x2 x3 = Eq) by eauto with lex; finish. 
    assert (f x1 x2 = Gt) by eauto with lex; finish. 
    assert (f x2 x3 = Eq) by eauto with lex; finish. 
    assert (f x1 x2 = Lt) by eauto with lex; finish. 
    assert (f x1 x2 = Eq) by eauto with lex; finish. 
    assert (f x2 x3 = Gt) by eauto with lex; finish. 
    congruence. 
    assert (f x1 x2 = Eq) by eauto with lex; finish. 
    assert (f x2 x3 = Lt) by eauto with lex; finish. 
    congruence. 
  Qed. 
End t. 

End Compare.

(* -------------------------------------------------------------------------------- *)

(* When using well-founded recursion, it is useful to prefix the proof
of well-foundedness with 2^n Acc constructors *)

 Fixpoint guard A (R: A -> A -> Prop) n (wfR: well_founded R): well_founded R :=
   match n with 
     | 0 => wfR 
     | S n => fun x => Acc_intro x (fun y _ => guard _ _ n (guard _ _ n wfR) y) 
   end.


Definition wf A f :=
  guard _ _ 512 (well_founded_ltof A f).

(* slight adaptation of Leroy's Wfsimpl.v in Compcert  *)
Require Import FunctionalExtensionality. 

Section FIX.

  Variables A B: Type.
  Variable R: A -> A -> Prop.
  Hypothesis Rwf: well_founded R.
  Set Implicit Arguments.
  Variable F: forall (x: A), (forall (y: A), R y x -> B) -> B.

  Definition Fix (x: A) : B := Wf.Fix (guard _ _ 512 Rwf) (fun (x: A) => B) F x.

  Theorem Fix_eq:
    forall x, Fix x = F (fun (y: A) (P: R y x) => Fix y).
  Proof.
    unfold Fix; intros. apply Wf.Fix_eq with (P := fun (x: A) => B). 
    intros. assert (f = g). apply functional_extensionality_dep; intros.
    apply functional_extensionality; intros. auto. 
    subst g; auto.
  Qed.

End FIX.

(** Same, with a nonnegative measure instead of a well-founded ordering *)

Section FIXM.

  Variables A B: Type.
  Variable measure: A -> nat.
  Variable F: forall (x: A), (forall (y: A), measure y < measure x -> B) -> B.
  
  Definition Fixm (x: A) : B := Wf.Fix (guard _ _ 512 (well_founded_ltof A measure)) (fun (x: A) => B) F x.
  
  Theorem Fixm_eq:
    forall x, Fixm x = F (fun (y: A) (P: measure y < measure x) => Fixm y).
  Proof.
    unfold Fixm; intros. apply Wf.Fix_eq with (P := fun (x: A) => B). 
    intros. assert (f = g). apply functional_extensionality_dep; intros.
    apply functional_extensionality; intros. auto. 
    subst g; auto.
  Qed.

  Lemma Fixm_ind P:
    (forall x, (forall y, measure y < measure x -> P (Fixm y)) -> P (Fixm x)) ->
    forall x, P (Fixm x).
  Proof. 
    intros. 
    induction x using (well_founded_induction_type (well_founded_ltof _ measure)).
    apply X. intros. apply X0. unfold ltof. eauto. 
  Qed.  

    

End FIXM.

