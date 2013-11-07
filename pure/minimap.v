Require Import BinPos BinNums.

Class minimap_ops (A B: Type) :=
  {
    content :> Type;
    set : A -> B -> content -> content;
    get : A -> content -> option B;
    empty : content
  }.

Notation "A ~> B" := (@content A B _) (at level 80).
Require Import EquivDec.

Class minimap_gempty {A B : Type} (M : minimap_ops A B) :=
    gempty: forall i, get i empty = None.

Class EqDec (A: Type)  := eq_dec: forall (x y: A), {x = y} + {x <> y}.

Instance prod_EqDec (A B:Type) {EA: EqDec A} {EB: EqDec B} : EqDec (A * B).
Proof.
  intros [a b] [c d].
  decide equality.
Qed.


Class minimap_props {A B : Type} (EqA: EqDec A)(M : minimap_ops A B) :=
  {
    gss: forall i x m, get i (set i x m) = Some x;
    gso: forall i j x m, i <> j -> get i (set j x m) = get i m
  }.

Section prod.
  Context {A B: Type}.
  Context (MA: forall C, minimap_ops A C).
  Context (MB: forall C, minimap_ops B C).
  Global Instance minimap_prod C : minimap_ops (A*B) C:=
    {|
      content := A ~> (B~> C);
      set := fun k v st =>
               let(ka,kb) := k in
               match get ka st with
                 | Some ma =>  set ka (set kb v ma) st
                 | None => set ka (set kb v empty) st
               end;
      get := fun k st =>
               let (ka,kb) := k in
               match get ka st with
                 | None => None
                 | Some ma => get kb ma
               end;
      empty := empty
    |}.


  Context (EqA : EqDec A).
  Context (EqB : EqDec B).
  Context (HMA_empty: forall C, minimap_gempty  (MA C)).
  Context (HMB_empty: forall C,minimap_gempty  (MB C)).

  Context (HMA: forall C,minimap_props EqA (MA C)).
  Context (HMB: forall C,minimap_props  EqB (MB C)).

  Global Instance minimap_prod_gempty C : minimap_gempty (minimap_prod C).
  Proof.
  - intros [a b]. simpl. rewrite gempty; auto.
  Qed.


  Global Instance minimap_prod_props C : minimap_props (prod_EqDec A B )(minimap_prod C).
  Proof.
  constructor.
  - unfold get,set. intros [a b] x m. simpl.
    destruct (get a m) eqn:H. rewrite gss. rewrite gss. auto.
    rewrite gss. rewrite gss. auto.
  - intros [a b] [c d]; intros; simpl.
    destruct (get a m) eqn:Ha; destruct (get c m) eqn:Hc;
    destruct (eq_dec a c) as [Hac | Hac]; compute in Hac; subst;
    destruct (eq_dec b d) as [Hbd | Hbd]; compute in  Hbd; subst; try tauto;
    rewrite ?gss, ?gso, ?Ha, ?Hc by auto; try congruence.
  Qed.
End prod.

Class EquivDec (A:Type) (R: A -> A -> Prop) := equiv_dec : forall x y, {R x y} + {~ R x y}. 


Require Import Morphisms.
Class minimap_eq_props {A B : Type} R (EquivA: EquivDec A R )(M : minimap_ops A B) :=
  {
    gssR: forall i j x m, R i j -> get i (set j x m) = Some x;
    gsoR: forall i j x m, ~ R i j -> get i (set j x m) = get i m;
    get_proper :> Proper (R ==> eq ==> @eq (option B)) get
  }.

Require Import FMaps FMapPositive.
Require Import ZArith.
Definition pos_of_N n := match n with N0 => xH | Npos p => (Pos.succ p) end.
Lemma pos_of_N_inj i : forall j, pos_of_N i = pos_of_N j -> i = j.
Proof.
  destruct i; destruct j; simpl; eauto; zify; omega.
Qed.

Instance minimap_N A : minimap_ops N A :=
  {|
    content := PositiveMap.t A;
    set := fun k v st =>
             PositiveMap.add (pos_of_N k) v st;
    get := fun k  st =>
             PositiveMap.find (pos_of_N k) st;
    empty := PositiveMap.empty A
  |}.

Instance minimap_N_gempty C : minimap_gempty (minimap_N C).
Proof.
  unfold minimap_gempty. intros [|i]; try easy. apply PositiveMap.gempty.
Qed.

Instance EqDec_N : EqDec N.
Proof.
  unfold EqDec. decide equality. apply Pos.eq_dec.
Qed.

Instance minimap_N_props C : minimap_props _ (minimap_N C).
Proof.
  constructor; unfold get, set; simpl; intros.
  apply PositiveMap.gss.
  apply PositiveMap.gso.
  intro H'; apply H.
  eapply pos_of_N_inj; eauto.
Qed.

Instance minimap_pos A : minimap_ops positive A :=
  {|
    content := PositiveMap.t A;
    set := fun k v st =>
             PositiveMap.add k v st;
    get := fun k  st =>
             PositiveMap.find k st;
    empty := PositiveMap.empty A
  |}.

Instance minimap_pos_gempty C : minimap_gempty (minimap_pos C).
Proof.  unfold minimap_gempty. apply PositiveMap.gempty. Qed.

Instance EqDec_pos : EqDec positive. exact Pos.eq_dec. Qed.

Instance minimap_pos_props C : minimap_props _ (minimap_pos C).
Proof.
  constructor. intros. apply PositiveMap.gss.
  intros. apply PositiveMap.gso; eauto.
Qed.
