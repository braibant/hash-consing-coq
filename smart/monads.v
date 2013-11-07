
Class MonadOps T :=
{ retn {X} : X -> T X
; bind {X Y} : T X -> (X -> T Y) -> T Y }.

Notation "'let!' x = c ; d" :=
  (bind c (fun x => d))
  (at level 200, x ident, c at level 150, d at level 200, right associativity).
Notation "'let!' ( x , y ) = c ; d" :=
  (bind c (fun z => match z with ( x , y ) => d end))
  (at level 200, x ident, y ident, c at level 150, d at level 200).

Instance optionMonadOps : MonadOps option :=
{ retn := Some
; bind := fun X Y (c: option X) f => match c with Some y => f y | _ => None end}.
