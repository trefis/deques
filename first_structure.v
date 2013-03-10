Require Import Program.
Require Import List.
Set Implicit Arguments.

Inductive color := Green | Yellow | Red.

Definition min_color a b :=
  match a, b with
  | Red, _ | _, Red => Red
  | Yellow, _ | _, Yellow => Yellow
  | _, _ => Green
  end.

Module Type Finite_buffer.
  Parameter max_len : nat.
  Parameter t : Set -> nat -> Set.

  Parameter empty : forall A, t A 0.

  Parameter push : forall A:Set, forall n, n < max_len -> A -> t A n -> t A (S n).
  Parameter pop  : forall A:Set, forall n, t A (S n) -> A * t A n.

  Parameter inject : forall A:Set, forall n, n < max_len -> A -> t A n -> t A (S n).
  Parameter eject  : forall A:Set, forall n, t A (S n) -> A * t A n.

  Parameter color : forall A, forall n, t A n -> color.

  Axiom max_len_positive : 0 < max_len.

  Axiom push_pop :
    forall A, forall elt, forall n, forall p : n < max_len, forall buff : t A n,
      pop (push p elt buff) = (elt, buff).

  Axiom inject_eject :
    forall A, forall elt, forall n, forall p : n < max_len, forall buff : t A n,
      eject (inject p elt buff) = (elt, buff).

  Axiom pop_inject :
    forall A, forall elt, forall n, forall p : S n < max_len, forall buff : t A (S n),
      let (elt_opt, buff2) := pop buff in
      let p2 : n < max_len := Lt.lt_trans n (S n) max_len (Lt.lt_n_Sn n) p in
      pop (inject p elt buff) = (elt_opt, inject p2 elt buff2).

  Axiom eject_push :
    forall A, forall elt, forall n, forall p : S n < max_len, forall buff : t A (S n),
      let (elt_opt, buff2) := eject buff in
      let p2 : n < max_len := Lt.lt_trans n (S n) max_len (Lt.lt_n_Sn n) p in
      eject (push p elt buff) = (elt_opt, push p2 elt buff2).

  Axiom full_is_red_contr :
    forall A, forall n, forall buff : t A n,
      color buff <> Red -> n < max_len.

  Axiom empty_is_red_contr :
    forall A, forall n, forall buff : t A n,
      color buff <> Red -> n > 0.
End Finite_buffer.

Module Deque (B : Finite_buffer).
  Module Stack.
    Inductive t (A : Set) : Set :=
      | Top : forall m n, B.t A m -> B.t A n -> t (A * A) -> t A
      | One_level : forall m n, B.t A m -> B.t A n -> t A.

    Definition top_color (A : Set) (stack : t A) :=
      match stack with
      | One_level _ _ hd tl
      | Top _ _ hd tl _ => min_color (B.color hd) (B.color tl)
      end.

    Definition regular (A : Set) (s : t A) :=
      let all_yellows :=
        fix f (B : Set) (lvl : t B) : Prop :=
          top_color lvl = Yellow /\
          (match lvl with
          | Top _ _ _ _ rest => f (prod B B) rest
          | _ => True
          end)
      in
      match s with
      | Top _ _ _ _ yellows => all_yellows (prod A A) yellows
      | _ => True
      end.

    Definition is_empty (A : Set) (s : t A) :=
      match s with
      | One_level 0 0 _ _ => True
      | _ => False
      end.

    Program Definition push (A : Set) (elt : A) (s : t A)
      (p : top_color s <> Red \/ is_empty s) : t A :=
      match s with
      | One_level n m prefix suffix =>
        One_level (B.push _ elt prefix) suffix
      | Top n m prefix suffix rest =>
        Top (B.push _ elt prefix) suffix rest
      end.

    Next Obligation.
    Proof.
      intuition.
        simpl in H.
        apply B.full_is_red_contr with (A := A) (buff := prefix).
        destruct (B.color prefix) ; auto ; try discriminate.

        destruct n ; firstorder.
        apply B.max_len_positive.
    Qed.

    Next Obligation.
    Proof.
      intuition.
        simpl in H.
        apply B.full_is_red_contr with (A := A) (buff := prefix).
        destruct (B.color prefix) ; auto ; try discriminate.
    Qed.

  End Stack.

  Definition t (A : Set) := list (Stack.t A).

  Definition green_first (A : Set) (d : t A) : Prop :=
    match d with
    | nil => True
    | stack :: stacks =>
      match Stack.top_color stack with
      | Green => True
      | _ => False
      end
    end.

  Fixpoint semi_regular (A : Set) (d : t A) : Prop :=
    match d with
    | nil => True
    | stack :: stacks =>
      let green_before_red :=
        match Stack.top_color stack with
        | Green => True
        | Red => green_first stacks
        | Yellow => False
        end
      in
      Stack.regular stack /\ semi_regular stacks /\ green_before_red
    end.

  Definition regular (A : Set) (d : t A) : Prop :=
    match d with
    | nil => False
    | [ Stack.One_level 0 0 _ _ ] => True (* ad-hoc case: the deque is empty *)
    | stack :: stacks =>
      match Stack.top_color stack with
      | Red => False
      | Green => Stack.regular stack /\ semi_regular stacks
      | Yellow => Stack.regular stack /\ semi_regular stacks /\  green_first stacks
      end
    end.

  Program Definition empty (A : Set) : { d : t A | regular d } :=
    [ Stack.One_level (B.empty A) (B.empty A) ].

  Program Definition push (A : Set) (elt : A) (d : t A) (p : regular d) : t A :=
    match d with
    | nil => !
    | stack :: stacks => (Stack.push elt stack _) :: stacks
    end.

  Next Obligation.
  Proof.
    intuition.
    destruct stacks, stack; destruct m, n ; solve [ 
      auto |
      (left ; intros ; unfold regular in p ; rewrite H in p ; trivial)
    ].
  Qed.

End Deque.
