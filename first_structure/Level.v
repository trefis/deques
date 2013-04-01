Require Import Program.
Require Import Coq.Arith.Bool_nat.
Require Import List.

Require Import Misc.

Module Type Intf.
  Parameter t : Set -> Set.

  Parameter color : forall {A}, t A -> color.

  Parameter is_empty : forall {A}, t A -> Prop.
  Parameter empty : forall A, { lvl : t A | is_empty lvl }.

  Parameter pop  : forall {A:Set}, forall lvl : t A, ~ is_empty lvl -> A * t A.
  Parameter push : forall {A:Set}, A -> forall lvl: t A,
    (color lvl <> Red \/ is_empty lvl) -> t A.

  Parameter eject  : forall {A:Set}, forall lvl : t A, ~ is_empty lvl -> A * t A.
  Parameter inject : forall {A:Set}, A -> forall lvl: t A,
    (color lvl <> Red \/ is_empty lvl) -> t A.

  Parameter equilibrate :
    forall {A:Set}, forall last_levels : Prop,
      { lvli : t A | color lvli = Red }
      -> option { lvlSi : t (A * A) | color lvlSi <> Red }
      -> { lvli : t A | color lvli = Green } *
         { lvlSi : t (A * A) | color lvlSi <> Red \/ (is_empty lvlSi /\ last_levels) }.

  Axiom empty_is_red : forall A, forall lvl:t A, is_empty lvl -> color lvl = Red.

  Axiom empty_is_red_contr : (* yes, I'm lazy *)
    forall A, forall lvl : t A, color lvl <> Red -> ~ is_empty lvl.

  Axiom dec_is_empty : forall A, forall t:t A, {is_empty t} + {~ is_empty t}.
End Intf.
