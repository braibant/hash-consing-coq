Require Import ZArith.
Require Import smart_common.
Require Import smart_bdd.
Require Import FMapPositive.
Require Import FunctionalExtensionality.

Inductive canonical: var -> bdd -> Prop :=
  | Tcanonical : forall v, canonical v T
  | Fcanonical : forall v, canonical v F
  | Ncanonical :
      forall v v', (v' < v)%positive ->
      forall bt, canonical v' bt ->
      forall bf, canonical v' bf ->
      bt <> bf ->
      canonical v (N v' bt bf).

Hint Constructors canonical.

Lemma bdd_interp_canonical_independent:
  forall v b, canonical v b ->
  forall x env,
    bdd_interp b (PositiveMap.add v x env) = bdd_interp b env.
Proof.
  intros v b Hcan.
  remember v in |- *. assert (v <= v0)%positive by (subst; reflexivity). clear Heqv0.
  generalize dependent v0.
  induction Hcan; auto.
  simpl; intros.
  rewrite PositiveMap.gso by (zify; omega).
  destruct (PositiveMap.find v' env) as [[]|].
  - apply IHHcan1. zify; omega.
  - apply IHHcan2. zify; omega.
  - auto.
Qed.

Lemma bdd_canonical_aux1:
  forall bt bf v,
  forall b, canonical v b -> canonical v bt ->
    (forall env, bdd_interp b env = bdd_interp (N v bt bf) env) ->
    forall env, bdd_interp b env = bdd_interp bt env.
Proof.
  intros.
  specialize (H1 (PositiveMap.add v true env)). simpl in H1.
  rewrite PositiveMap.gss, !bdd_interp_canonical_independent in H1; auto.
Qed.

Local Hint Resolve bdd_canonical_aux1.

Lemma bdd_canonical_aux2:
  forall bt bf v,
  forall b, canonical v b -> canonical v bf ->
    (forall env, bdd_interp b env = bdd_interp (N v bt bf) env) ->
    forall env, bdd_interp b env = bdd_interp bf env.
Proof.
  intros.
  specialize (H1 (PositiveMap.add v false env)). simpl in H1.
  rewrite PositiveMap.gss, !bdd_interp_canonical_independent in H1; auto.
Qed.

Local Hint Resolve bdd_canonical_aux2.

Theorem bdd_canonical:
  forall a va, canonical va a ->
  forall b vb, canonical vb b ->
    (forall env, bdd_interp a env = bdd_interp b env) ->
    a = b.
Proof.
  induction 1; induction 1; subst; intro.
  - reflexivity.
  - specialize (H (PositiveMap.empty _)). discriminate.
  - rewrite <- IHcanonical2, <- IHcanonical1 in H2 by eauto. tauto.
  - specialize (H (PositiveMap.empty _)). discriminate.
  - reflexivity.
  - rewrite <- IHcanonical2, <- IHcanonical1 in H2 by eauto. tauto.
  - erewrite IHcanonical2 with (b:=T), IHcanonical1 with (b:=T) in H2 by (eauto; symmetry; eauto). tauto.
  - erewrite IHcanonical2 with (b:=F), IHcanonical1 with (b:=F) in H2 by (eauto; symmetry; eauto). tauto.
  - destruct (Pos.compare_spec v' v'0).
    + subst. f_equal.
      * eapply IHcanonical1; eauto.
        intro. specialize (H5 (PositiveMap.add v'0 true env)). simpl in H5.
        erewrite PositiveMap.gss, !bdd_interp_canonical_independent in H5 by eauto. auto.
      * eapply IHcanonical2; eauto.
        intro. specialize (H5 (PositiveMap.add v'0 false env)). simpl in H5.
        erewrite PositiveMap.gss, !bdd_interp_canonical_independent in H5 by eauto. auto.
    + erewrite <- IHcanonical3, <- IHcanonical4 in H4 by (eauto; symmetry; eauto). tauto.
    + erewrite IHcanonical2 with (b:=N v'0 bt0 bf0), IHcanonical1 with (b:=N v'0 bt0 bf0) in H2 by (eauto; symmetry; eauto). tauto.
  Grab Existential Variables.
  exact xH. exact xH. exact xH. exact xH.
Qed.

Lemma bdd_not_inj:
  forall b1 b2, bdd_not b1 = bdd_not b2 -> b1 = b2.
Proof.
  induction b1; induction b2; try reflexivity; try discriminate.
  unfold bdd_not, memo_rec.
  intro.
  rewrite Fix_eq with (x:=N v0 b2_1 b2_2) in H. rewrite Fix_eq in H.
  injection H. clear H. intros. subst.
  f_equal; auto.
  intros. replace g with f. easy. extensionality x'. extensionality p. auto.
  intros. replace g with f. easy. extensionality x'. extensionality p. auto.
Qed.

Theorem canonical_bdd_not:
  forall v b, canonical v b -> canonical v (bdd_not b).
Proof.
  induction 1; auto.
  unfold bdd_not, memo_rec.
  rewrite Fix_eq.
  constructor; auto.
  intro. apply bdd_not_inj in H3. tauto.
  intros. replace g with f. easy. extensionality x'. extensionality p. auto.
Qed.

Lemma canonical_le:
  forall v v' b, (v <= v')%positive ->
    canonical v b ->
    canonical v' b.
Proof.
  destruct 2; constructor; auto.
  zify; omega.
Qed.

Lemma canonical_N_check:
  forall v bt bf,
    canonical v bt ->
    canonical v bf ->
  forall v', (v < v')%positive ->
    canonical v' (N_check v bt bf).
Proof.
  unfold N_check. intros.
  pose proof (bdd_eqb_iff bt bf).
  destruct (bdd_eqb bt bf).
  eapply canonical_le; eauto. zify; omega.
  constructor; auto.
  unfold not. rewrite <- H2. discriminate.
Qed.

Theorem canonical_bdd_and:
  forall b1 b2 v,
    canonical v b1 ->
    canonical v b2 ->
    canonical v (bdd_and b1 b2).
Proof.
  intros. revert b2 H0.
  pose proof H. induction H; auto.
  intros.
  unfold bdd_and. unfold memo_rec.
  rewrite Fix_eq;
    try (intros; replace g with f; [easy|extensionality x'; extensionality p; auto]).
  induction H4; auto.
  unfold memo_rec.
  rewrite Fix_eq;
  try (intros; replace g with f; [easy|extensionality x'; extensionality p; auto]).
  destruct (Pos.compare_spec v' v'0); eapply canonical_N_check; subst; auto.
Qed.

Theorem canonical_bdd_or:
  forall b1 b2 v,
    canonical v b1 ->
    canonical v b2 ->
    canonical v (bdd_or b1 b2).
Proof.
  intros. revert b2 H0.
  pose proof H. induction H; auto.
  intros.
  unfold bdd_or. unfold memo_rec.
  rewrite Fix_eq;
    try (intros; replace g with f; [easy|extensionality x'; extensionality p; auto]).
  induction H4; auto.
  unfold memo_rec.
  rewrite Fix_eq;
    try (intros; replace g with f; [easy|extensionality x'; extensionality p; auto]).
  destruct (Pos.compare_spec v' v'0); eapply canonical_N_check; subst; auto.
Qed.

Theorem canonical_bdd_xor:
  forall b1 b2 v,
    canonical v b1 ->
    canonical v b2 ->
    canonical v (bdd_xor b1 b2).
Proof.
  intros. revert b2 H0.
  pose proof H. induction H; auto using canonical_bdd_not.
  intros.
  unfold bdd_xor, memo_rec.
  rewrite Fix_eq;
    try (intros; replace g with f; [easy|extensionality x'; extensionality p; auto]).
  induction H4; auto.
  unfold memo_rec.
  rewrite Fix_eq;
    try (intros; replace g with f; [easy|extensionality x'; extensionality p; auto]).
  auto using canonical_bdd_not.
  rewrite Fix_eq;
    try (intros; replace g with f; [easy|extensionality x'; extensionality p; auto]).
  destruct (Pos.compare_spec v' v'0); eapply canonical_N_check; subst; auto.
Qed.

(* BDD ITE  *)

Theorem canonical_bdd_ite:
  forall b1 b2 b3,
  forall v,
    canonical v b1 ->
    canonical v b2 ->
    canonical v b3 ->
    canonical v (bdd_ite b1 b2 b3).
Proof.
  intros. revert b2 H0 b3 H1.
  induction H; auto.
  unfold bdd_ite, memo_rec.
  rewrite Fix_eq;
    try (intros; replace g with f; [easy|extensionality x'; extensionality p; auto]).
  change (Fix (well_founded_ltof bdd bdd_size))
  with (memo_rec (well_founded_ltof bdd bdd_size)) in *.
  fold bdd_ite in *. unfold memo_rec.
  intros b2 ?.
  induction H3; auto;
  rewrite Fix_eq;
  try (intros; replace g with f; [easy|extensionality x'; extensionality p; auto]).
  - intros.
    induction H3;
    rewrite Fix_eq;
      try (intros; replace g with f; [easy|extensionality x'; extensionality p; auto]).
    apply canonical_N_check; auto.
    apply canonical_N_check; auto.
    destruct (Pos.compare_spec v' v'0); subst; apply canonical_N_check; auto.
  - intros.
    induction H3;
    rewrite Fix_eq;
      try (intros; replace g with f; [easy|extensionality x'; extensionality p; auto]).
    apply canonical_N_check; auto.
    apply canonical_N_check; auto.
    destruct (Pos.compare_spec v' v'0); subst; apply canonical_N_check; auto.
  - intros.
    match goal with |- context [match ?t with (_, _) => _ end] =>
                    remember t
    end.
    destruct p as [[rect recf] v1].
    assert (forall b, canonical v1 b -> canonical v1 (rect b)).
    { destruct (Pos.compare_spec v' v'0); inversion Heqp; subst; clear Heqp; auto. }
    assert (forall b, canonical v1 b -> canonical v1 (recf b)).
    { destruct (Pos.compare_spec v' v'0); inversion Heqp; subst; clear Heqp; auto. }
    assert (v1 < v)%positive.
    { destruct (Pos.compare_spec v' v'0); inversion Heqp; subst; clear Heqp; auto. }
    clear H H3.
    induction H5;
    rewrite Fix_eq;
      try (intros; replace g with f; [easy|extensionality x'; extensionality p; auto]).
    apply canonical_N_check; auto.
    apply canonical_N_check; auto.
    destruct (Pos.compare_spec v1 v'1); subst; apply canonical_N_check; auto.
Qed.
