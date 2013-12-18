Require Import reference_lambda smart_lambda smart_bdd.

Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive prod => "(*)"  [ "(,)" ].
Extract Inductive option => option [ Some None ].
Extract Inductive List.list => "list" [ "[]" "(::)" ].

Set Extraction AccessOpaque.


Extraction Blacklist String List.
Cd "../extracted".
Separate Extraction
         reference_lambda.quicksort'
         smart_lambda.quicksort' 
         smart_bdd.bdd_ite smart_bdd.bdd_xor.
