Require pure_bdd.
Require shallow_bdd.
Require shallow_lambda.

Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive option => option [ Some None ].

Extraction Blacklist String List.
Set Extraction AccessOpaque.

Cd "../extracted".
Recursive Extraction Library pure_bdd.
Recursive Extraction Library shallow_bdd.

Separate Extraction shallow_lambda.quicksort'.
