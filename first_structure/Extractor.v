Require Misc.
Require Buffer.
Require Level.
Require Stack.
Require Deque.

Set Extraction AccessOpaque.

Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive prod => "( * )"  [ "(, )" ].

Recursive Extraction Library Deque.
