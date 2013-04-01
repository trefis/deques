Require Misc.
Require Level.
Require Deque.

Set Extraction AccessOpaque.

Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive prod => "( * )"  [ "(, )" ].

Extraction "deque" Deque.Make.
