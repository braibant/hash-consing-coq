Require Import smart_common.
Require Import Arith.
Require Import BinPos.
Require Import FMapPositive.
Require Import Recdef.
Require Import FunctionalExtensionality.

Definition var := positive.

Inductive bdd: Type :=
| T | F | N: var -> bdd -> bdd -> bdd.
Extract Inductive bdd =>
  "Helpers_bdd.bdd"
  ["Helpers_bdd.hT" "Helpers_bdd.hF" "Helpers_bdd.hN"]
  "Helpers_bdd.bdd_match".

Fixpoint bdd_size b :=
  match b with
    | T | F => O
    | N _ b1 b2 => S(bdd_size b1 + bdd_size b2)
  end.

Fixpoint bdd_interp (b:bdd) (env:PositiveMap.t bool): option bool:=
  match b with
    | T => Some true
    | F => Some false
    | N v bt bf =>
      match PositiveMap.find v env with
        | Some true => bdd_interp bt env
        | Some false => bdd_interp bf env
        | None => None
      end
  end.

Fixpoint bdd_eqb (b1 b2:bdd): bool :=
  match b1, b2 with
    | T, T | F, F => true
    | N v1 b1t b1f, N v2 b2t b2f =>
      (Pos.eqb v1 v2 && bdd_eqb b1t b2t && bdd_eqb b1f b2f)%bool
    | _, _ => false
  end.

Extract Inlined Constant bdd_eqb => "(==)".

Theorem bdd_eqb_iff:
  forall b1 b2, bdd_eqb b1 b2 = true <-> b1 = b2.
Proof.
  induction b1; destruct b2; simpl; try (split; congruence).
  rewrite !Bool.andb_true_iff, IHb1_1, IHb1_2, Pos.eqb_eq.
  intuition; congruence.
Qed.

Parameter memo_bdd : memoizer bdd.
Extract Inlined Constant memo_bdd => "Helpers_bdd.bdd_memo".

Definition N_check (v:var) (bt bf:bdd) : bdd :=
  if bdd_eqb bt bf then bt else N v bt bf.

Theorem N_check_correct:
  forall env v bt bf,
    PositiveMap.find v env <> None ->
    bdd_interp (N_check v bt bf) env = bdd_interp (N v bt bf) env.
Proof.
  unfold N_check. intros. pose proof (bdd_eqb_iff bt bf). destruct (bdd_eqb bt bf).
  simpl. destruct (PositiveMap.find v env) as [[]|]. reflexivity. rewrite (proj1 H0 eq_refl); reflexivity.
  destruct H; auto.
  reflexivity.
Qed.

Definition bdd_var v := N_check v T F.

Definition bdd_false := F.

Definition bdd_true  := T.

Program Definition bdd_not : bdd -> bdd :=
  (memo_rec (well_founded_ltof _ bdd_size) (fun b =>
     match b with
       | T => fun _ => F
       | F => fun _ => T
       | N v bt bf =>
         fun rec => N v (rec bt _) (rec bf _)
     end)).
Next Obligation.
unfold ltof; simpl; clear; abstract omega.
Defined.
Next Obligation.
unfold ltof; simpl; clear; abstract omega.
Defined.

Ltac crush :=
  repeat match goal with
           | |- bdd_interp (N_check _ _ _) _ = _ =>
             rewrite N_check_correct; simpl
           | |- match ?o with _ => _ end  = _=>
             destruct o as [[]|]; try discriminate
           | H: context [match ?o with _ => _ end] |- ?o <> _ =>
             intro EQ; rewrite EQ in H; discriminate
         end.

Theorem bdd_not_correct:
  forall b env, bdd_interp (bdd_not b) env = option_map negb (bdd_interp b env).
Proof.
  unfold bdd_not, memo_rec.
  induction b; intros; rewrite Fix_eq; try easy.
  intros [] f g H; rewrite ?H; easy.
  intros [] f g H; rewrite ?H; easy.
  simpl. crush; easy.
  intros [] f g H; rewrite ?H; easy.
Qed.

Definition bdd_and : bdd -> bdd -> bdd.
refine
  (memo_rec (well_founded_ltof _ bdd_size) (fun x =>
     match x with
       | T => fun _ y => y
       | F => fun _ _ => F
       | N xv xt xf => fun recx =>
         memo_rec (well_founded_ltof _ bdd_size) (fun y =>
           match y with
             | T => fun _ => x
             | F => fun _ => F
             | N yv yt yf => fun recy =>
               match Pos.compare xv yv with
                 | Eq => N_check xv (recx xt _ yt) (recx xf _ yf)
                 | Lt => N_check yv (recy yt _) (recy yf _)
                 | Gt => N_check xv (recx xt _ y) (recx xf _ y)
               end
           end)
     end));
  unfold ltof; simpl; clear; abstract omega.
Defined.

Theorem bdd_and_correct:
  forall b1 x1 b2 x2 env,
    bdd_interp b1 env = Some x1 ->
    bdd_interp b2 env = Some x2 ->
    bdd_interp (bdd_and b1 b2) env = Some (x1 && x2)%bool.
Proof.
  intros b1 x1 b2 x2 env.
  unfold bdd_and, memo_rec.
  revert b2.
  induction b1; rewrite Fix_eq; intros;
  try (replace g with f; [easy|extensionality x'; extensionality p; auto]).
  - inversion H. easy.
  - inversion H. easy.
  - induction b2; rewrite Fix_eq; intros;
    try (replace g with f; [easy|extensionality y'; extensionality p; auto]);
    simpl in *.
    + inversion H0. rewrite Bool.andb_true_r. easy.
    + inversion H0. rewrite Bool.andb_false_r. easy.
    + destruct (Pos.compare_spec v v0); subst; crush; auto.
Qed.

Definition bdd_or : bdd -> bdd -> bdd.
refine
  (memo_rec (well_founded_ltof _ bdd_size) (fun x =>
     match x with
       | F => fun _ y => y
       | T => fun _ _ => T
       | N xv xt xf => fun recx =>
         memo_rec (well_founded_ltof _ bdd_size) (fun y =>
           match y with
             | F => fun _ => x
             | T => fun _ => T
             | N yv yt yf => fun recy =>
               match Pos.compare xv yv with
                 | Eq => N_check xv (recx xt _ yt) (recx xf _ yf)
                 | Lt => N_check yv (recy yt _) (recy yf _)
                 | Gt => N_check xv (recx xt _ y) (recx xf _ y)
               end
           end)
     end));
  unfold ltof; simpl; clear; abstract omega.
Defined.

Theorem bdd_or_correct:
  forall b1 x1 b2 x2 env,
    bdd_interp b1 env = Some x1 ->
    bdd_interp b2 env = Some x2 ->
    bdd_interp (bdd_or b1 b2) env = Some (x1 || x2)%bool.
Proof.
  intros b1 x1 b2 x2 env.
  unfold bdd_or, memo_rec.
  revert b2.
  induction b1; rewrite Fix_eq; intros;
  try (replace g with f; [easy|extensionality x'; extensionality p; auto]).
  - inversion H. easy.
  - inversion H. easy.
  - induction b2; rewrite Fix_eq; intros;
    try (replace g with f; [easy|extensionality x'; extensionality p; auto]);
    simpl in *.
    + inversion H0. rewrite Bool.orb_true_r. easy.
    + inversion H0. rewrite Bool.orb_false_r. easy.
    + destruct (Pos.compare_spec v v0); subst; crush; auto.
Qed.

Definition bdd_xor : bdd -> bdd -> bdd.
refine
  (memo_rec (well_founded_ltof _ bdd_size) (fun x =>
     match x with
       | F => fun _ y => y
       | T => fun _ => bdd_not
       | N xv xt xf => fun recx =>
         memo_rec (well_founded_ltof _ bdd_size) (fun y =>
           match y with
             | F => fun _ => x
             | T => fun _ => bdd_not x
             | N yv yt yf => fun recy =>
               match Pos.compare xv yv with
                 | Eq => N_check xv (recx xt _ yt) (recx xf _ yf)
                 | Lt => N_check yv (recy yt _) (recy yf _)
                 | Gt => N_check xv (recx xt _ y) (recx xf _ y)
               end
           end)
     end));
  unfold ltof; simpl; clear; abstract omega.
Defined.

Theorem bdd_xor_correct:
  forall b1 x1 b2 x2 env,
    bdd_interp b1 env = Some x1 ->
    bdd_interp b2 env = Some x2 ->
    bdd_interp (bdd_xor b1 b2) env = Some (xorb x1 x2).
Proof.
  intros b1 x1 b2 x2 env.
  unfold bdd_xor, memo_rec.
  revert b2.
  induction b1; rewrite Fix_eq; intros;
  try (replace g with f; [easy|extensionality x'; extensionality p; auto]).
  - inversion H. rewrite bdd_not_correct, H0. easy.
  - inversion H. destruct x2; easy.
  - induction b2; rewrite Fix_eq; intros;
    try (replace g with f; [easy|extensionality x'; extensionality p; auto]).
    + inversion H0. rewrite Bool.xorb_true_r, bdd_not_correct, H. easy.
    + inversion H0. rewrite Bool.xorb_false_r. easy.
    + simpl in *. destruct (Pos.compare_spec v v0); subst; crush; auto.
Qed.

(* If then else *)

Definition bdd_ite : bdd -> bdd -> bdd -> bdd.
refine
  (memo_rec (well_founded_ltof _ bdd_size) (fun x =>
     match x with
       | F => fun _ y z => z
       | T => fun _ y z => y
       | N xv xt xf => fun recx =>
         memo_rec (well_founded_ltof _ bdd_size) (fun y recy =>
           let '(rect, recf, v) :=
               match y return (forall y', ltof _ bdd_size y' y -> _) -> _ with
                 | F | T => fun _ => (recx xt _ y, recx xf _ y, xv)
                 | N yv yt yf => fun recy =>
                   match Pos.compare xv yv with
                     | Eq => (recx xt _ yt, recx xf _ yf, xv)
                     | Lt => (recy yt _, recy yf _, yv)
                     | Gt => (recx xt _ y, recx xf _ y, xv)
                   end
               end recy
           in
           memo_rec (well_founded_ltof _ bdd_size) (fun z =>
             match z with
               | F | T => fun _ => N_check v (rect z) (recf z)
               | N zv zt zf => fun recz =>
                 match Pos.compare v zv with
                   | Eq => N_check v (rect zt) (recf zf)
                   | Lt => N_check zv (recz zt _) (recz zf _)
                   | Gt => N_check v (rect z) (recf z)
                 end
             end))
     end));
  unfold ltof; simpl; clear; abstract omega.
Defined.

Theorem bdd_ite_correct:
  forall b1 x1 b2 x2 b3 x3 env,
    bdd_interp b1 env = Some x1 ->
    bdd_interp b2 env = Some x2 ->
    bdd_interp b3 env = Some x3 ->
    bdd_interp (bdd_ite b1 b2 b3) env = Some (if x1 then x2 else x3).
Proof.
  intros b1 x1 b2 x2 b3 x3 env.
  unfold bdd_ite, memo_rec.
  revert b2 b3.
  induction b1; rewrite Fix_eq; intros;
    try (replace g with f; [easy|extensionality x'; extensionality p; auto]).
  - inversion H. auto.
  - inversion H. auto.
  - change (Fix (well_founded_ltof bdd bdd_size))
    with (memo_rec (well_founded_ltof bdd bdd_size)) in *.
    fold bdd_ite in *. unfold memo_rec.
    revert b3 H1.
    induction b2; rewrite Fix_eq; intros;
      try (replace g with f; [easy|extensionality x'; extensionality p; auto]).
    + induction b3; rewrite Fix_eq; intros;
        try (replace g with f; [easy|extensionality x'; extensionality p; auto]);
      simpl in *.
      * crush; auto.
      * crush; auto.
      * destruct (Pos.compare_spec v v0); subst; crush; auto.
    + induction b3; rewrite Fix_eq; intros;
        try (replace g with f; [easy|extensionality x'; extensionality p; auto]);
      simpl in *.
      * crush; auto.
      * crush; auto.
      * destruct (Pos.compare_spec v v0); subst; crush; auto.
    + simpl in *.
      match goal with |- context [match ?t with (_, _) => _ end] =>
        remember t
      end.
      destruct p as [[rect recf] v1].
      assert (forall b3,
                bdd_interp b3 env = Some x3 ->
                match PositiveMap.find v1 env with
                  | Some true => bdd_interp (rect b3) env
                  | Some false => bdd_interp (recf b3) env
                  | None => None
                end = Some (if x1 then x2 else x3)).
      { intros.
        destruct (Pos.compare_spec v v0); inversion Heqp; subst; clear Heqp;
        crush; auto. }
      induction b3; rewrite Fix_eq; intros;
        try (replace g with f; [easy|extensionality x'; extensionality p; auto]);
      simpl in *.
      * specialize (H2 T H1). crush; auto.
      * specialize (H2 F H1). crush; auto.
      * pose proof (H2 (N _ _ _) H1).
        destruct (Pos.compare_spec v1 v2); subst; crush; auto.
Qed.
