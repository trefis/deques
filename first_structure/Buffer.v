Require Import Program.
Require Import Misc.

Inductive t (A : Set) :=
  | Zero  : t A
  | One   : A -> t A
  | Two   : A -> A -> t A
  | Three : A -> A -> A -> t A
  | Four  : A -> A -> A -> A -> t A
  | Five  : A -> A -> A -> A -> A -> t A.

Implicit Arguments Zero [A].
Implicit Arguments One [A].
Implicit Arguments Two [A].
Implicit Arguments Three [A].
Implicit Arguments Four [A].
Implicit Arguments Five [A].

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

Lemma bounded_length : forall {A} (b: t A), length b <= 5.
Proof. 
  destruct b; simpl; auto with arith.
Qed.

Lemma empty_length : forall {A} (b : t A), 
  length b = 0 <-> is_empty b.
Proof. 
  intros A b; destruct b; simpl in * |- *; firstorder; try (congruence || auto).
Qed.

Lemma nonempty_length : forall {A} (b : t A), 
  length b > 0 <-> ~ (is_empty b).
Proof. 
  intros A b; destruct b; simpl in * |- *; firstorder; try (congruence || auto).
  inversion H.
Qed.
                       
Definition color {A : Set} (buff : t A) : color :=
  match buff with
  | Zero | Five _ _ _ _ _ => Red
  | One _ | Four _ _ _ _ => Yellow
  | _ => Green (* Y: Il y avait Red ici, c'est bien Green non? *)
  end.

Lemma length_color : 
  forall {A} (buff : t A),
    match color buff, length buff with
      | Red, (0 | 5) => True
      | Yellow, (1 | 4) => True
      | Green, (2 | 3) => True
      | _, _ => False
    end.
Proof. intros A b; destruct b; simpl; auto. Qed.

Program Definition push {A : Set} (elt : A) 
  (buff : t A | color buff <> Red \/ is_empty buff) : 
  { buff' : t A | length buff' = S (length buff) } :=
  match buff with
  | Zero => One elt
  | One a => Two elt a
  | Two a b => Three elt a b
  | Three a b c => Four elt a b c
  | Four a b c d => Five elt a b c d
  | Five _ _ _ _ _ => !
  end.
Next Obligation.
Proof.  firstorder. Qed.

Program Definition inject {A : Set} (elt : A) 
  (buff : t A | color buff <> Red \/ is_empty buff) : 
  { buff' : t A | length buff' = S (length buff) } :=
  match buff with
  | Zero => One elt
  | One a => Two a elt
  | Two a b => Three a b elt
  | Three a b c => Four a b c elt
  | Four a b c d => Five a b c d elt
  | Five _ _ _ _ _ => !
  end.
Next Obligation.
Proof. firstorder. Qed.

Program Definition pop {A : Set} (buff : t A | ~ is_empty buff) : 
  { r : A * t A | S (length (snd r)) = length buff } :=
  match buff with
  | Zero => !
  | One a => (a, Zero)
  | Two a b => (a, One b)
  | Three a b c => (a, Two b c)
  | Four a b c d => (a, Three b c d)
  | Five a b c d e => (a, Four b c d e)
  end.
Next Obligation.
Proof. firstorder. Qed.

Program Definition eject {A : Set} (buff : t A | ~ is_empty buff) : 
  { r : A * t A | S (length (snd r)) = length buff } :=
  match buff with
  | Zero => !
  | One a => (a, Zero)
  | Two a b => (b, One a)
  | Three a b c => (c, Two a b)
  | Four a b c d => (d, Three a b c)
  | Five a b c d e => (e, Four a b c d)
  end.
Next Obligation.
Proof. firstorder. Qed.




