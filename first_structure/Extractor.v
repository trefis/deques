Require Misc.
Require Buffer.
Require Level.
Require Stack.
Require Deque.

Set Extraction AccessOpaque.

Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive prod => "( * )"  [ "(, )" ].
Extract Inductive nat => "int" [ "0" "succ" ]
  "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extraction Blacklist Buffer Stack.

Recursive Extraction Library Deque.
