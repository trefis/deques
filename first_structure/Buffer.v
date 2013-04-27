Require Import Program.
Require Import Misc.

Inductive t (A : Set) :=
  | Zero  : t A
  | One   : A -> t A
  | Two   : A -> A -> t A
  | Three : A -> A -> A -> t A
  | Four  : A -> A -> A -> A -> t A
  | Five  : A -> A -> A -> A -> A -> t A.

Definition is_empty {A : Set} (buff : t A) : Prop :=
  match buff with
  | Zero => True
  | _ => False
  end.

Theorem dec_is_empty :
  forall {A : Set}, forall buff : t A,
    { is_empty buff } + { ~ is_empty buff }.
Proof.
  destruct buff ; simpl ; auto.
Qed.

Definition length {A : Set} (buff : t A) : nat :=
  match buff with
  | Zero => 0
  | One _ => 1
  | Two _ _ => 2
  | Three _ _ _ => 3
  | Four _ _ _ _ => 4
  | Five _ _ _ _ _ => 5
  end.

Definition color {A : Set} (buff : t A) : color :=
  match buff with
  | Zero | Five _ _ _ _ _ => Red
  | One _ | Four _ _ _ _ => Yellow
  | _ => Red
  end.

Program Definition push {A : Set} (elt : A) 
  (buff : t A | color buff <> Red \/ is_empty buff) : t A :=
  match buff with
  | Zero => One A elt
  | One a => Two A elt a
  | Two a b => Three A elt a b
  | Three a b c => Four A elt a b c
  | Four a b c d => Five A elt a b c d
  | Five _ _ _ _ _ => !
  end.

Next Obligation.
Proof.  firstorder. Qed.

Program Definition inject {A : Set} (elt : A) 
  (buff : t A | color buff <> Red \/ is_empty buff) : t A :=
  match buff with
  | Zero => One A elt
  | One a => Two A a elt
  | Two a b => Three A a b elt
  | Three a b c => Four A a b c elt
  | Four a b c d => Five A a b c d elt
  | Five _ _ _ _ _ => !
  end.

Next Obligation.
Proof. firstorder. Qed.

Program Definition pop {A : Set} (buff : t A | ~ is_empty buff) : A * t A :=
  match buff with
  | Zero => !
  | One a => (a, Zero A)
  | Two a b => (a, One A b)
  | Three a b c => (a, Two A b c)
  | Four a b c d => (a, Three A b c d)
  | Five a b c d e => (a, Four A b c d e)
  end.

Next Obligation.
Proof. firstorder. Qed.

Program Definition eject {A : Set} (buff : t A | ~ is_empty buff) : A * t A :=
  match buff with
  | Zero => !
  | One a => (a, Zero A)
  | Two a b => (b, One A a)
  | Three a b c => (c, Two A a b)
  | Four a b c d => (d, Three A a b c)
  | Five a b c d e => (e, Four A a b c d)
  end.

Next Obligation.
Proof. firstorder. Qed.
