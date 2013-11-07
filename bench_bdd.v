Add LoadPath "pure".
Add LoadPath "smart".
Require pure_bdd.
Require shallow_bdd.
Require smart_bdd.

Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive option => option [ Some None ].

Extraction Blacklist String List.
Set Extraction AccessOpaque.
Cd "extracted".

Separate Extraction 
         pure_bdd
         shallow_bdd
         smart_bdd.


