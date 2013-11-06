Require Import Deque.

Set Extraction AccessOpaque.

Extract Inlined Constant fst => "fst".
Extract Inlined Constant snd => "snd".

Extract Inductive option => "option" ["Some" "None"].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive prod => "( * )"  [ "(, )" ].
Extract Inductive nat => "int" [ "0" "succ" ]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extraction Blacklist Buffer Stack.

Separate Extraction t dec_is_empty empty push pop inject eject.
