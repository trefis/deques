Require Import Program.

Require Import Misc.
Require Level.

Inductive t : Set -> Set -> Type :=
  | Nil  : forall A, t A A
  | Cons : forall A B, Level.t A -> t (A * A) B -> t A B.

Arguments Nil [A].
Arguments Cons [A] [B] _ _.

Fixpoint all_yellows {A B : Set} (s : t A B) (is_last : bool): Prop :=
  match s with
  | Nil _ => True
  | Cons _ _ lvl (Nil _) => Level.color lvl is_last = Yellow
  | Cons _ _ lvl rest =>
    Level.color lvl false = Yellow /\ all_yellows rest is_last
  end.

Definition well_formed {A B : Set} (stack : t A B) is_last :=
  match stack with
  | Nil _ => False
  | Cons _ _ _top_level rest => all_yellows rest is_last
  end.

Definition is_empty {A B : Set} (stack : t A B) : Prop :=
  match stack with
  | Nil _ => True
  | Cons _ _ lvl (Nil _) => Level.is_empty lvl
  | _ => False
  end.

Definition dec_is_empty {A B} (s : t A B) : { is_empty s } + { ~ is_empty s }.
Proof.
  destruct s.
  + left ; simpl ; trivial.
  + dependent destruction s ; simpl.
    - apply Level.dec_is_empty.
    - right ; auto.
Defined.

Program Definition empty (A : Set) :
  { s : t A (A * A) | well_formed s false /\ is_empty s } :=
  Cons (Level.empty A) Nil.

Next Obligation.
Proof. compute ; tauto. Qed.

Definition color {A B} (s : t A B) b :=
  match s with
  | Nil _ => Red
  | Cons _ _ lvl (Nil _) => Level.color lvl b
  | Cons _ _ lvl _ => Level.color lvl false
  end.
