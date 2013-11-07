Require Import Wf NArith.

Parameter memoizer : forall A:Type, Type.
Existing Class memoizer.
Extract Constant memoizer "'key" => "'key Helpers_common.memoizer".

Parameter memoizer_N : memoizer N.
Extract Inlined Constant memoizer_N => "Helpers_common.memoizer_N".

Definition memo A {H: memoizer A} P := @id (forall x:A, P x).
Extract Inlined Constant memo => "Helpers_common.memo".
Arguments memo [A] {H} [P] _ _.

Definition memo_rec A {H: memoizer A} := @Fix A.
Extract Inlined Constant memo_rec => "Helpers_common.memo_rec".
Arguments memo_rec [A] {H} [R] Rwf [P] F x.

Definition Fuel := nat.
Open Scope nat_scope.

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

Definition memo_fuel {A} (H: memoizer A) P := @fuel_fix A P.
Extract Inlined Constant memo_fuel => "Helpers_common.memo_fuel".
