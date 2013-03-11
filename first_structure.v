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

    Fixpoint type_of_last_lvl (A : Set) (s : t A) : Set :=
      match s with
      | One_level _ _ _ _ => A
      | Top _ _ _ _ rest => type_of_last_lvl rest
      end.

    Theorem push_on_regular_does_not_deepen :
      forall A : Set, forall x : A, forall s : t A, forall p,
        type_of_last_lvl s = type_of_last_lvl (push x s p).
    Proof. destruct s ; auto. Qed.
  End Stack.

  Inductive t (A : Set) : Set :=
    | mynil : t A
    | mycons : forall s : Stack.t A, t (Stack.type_of_last_lvl s) -> t A.

  Definition green_first (A : Set) (d : t A) : Prop :=
    match d with
    | mynil => True
    | mycons stack _ =>
      match Stack.top_color stack with
      | Green => True
      | _ => False
      end
    end.

  Fixpoint semi_regular (A : Set) (d : t A) : Prop :=
    match d with
    | mynil => True
    | mycons stack stacks =>
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
    | mynil => False
    | mycons (Stack.One_level 0 0 _ _) mynil => True (* ad-hoc case: the deque is empty *)
    | mycons stack stacks =>
      let green_before_red :=
        match Stack.top_color stack with
        | Red => False
        | Green => True
        | Yellow => green_first stacks
        end
      in
      green_before_red /\ Stack.regular stack /\ semi_regular stacks
    end.

  Program Definition empty (A : Set) : { d : t A | regular d } :=
    let singleton := Stack.One_level (B.empty A) (B.empty A) in
    mycons singleton (mynil (Stack.type_of_last_lvl singleton)).

  Program Definition dirty_push (A : Set) (elt : A) (d : t A) (p : regular d) : t A :=
    match d with
    | mynil => !
    | mycons stack stacks => mycons (Stack.push elt stack _) ((fun _ => _) stacks)
    end.

  Next Obligation.
  Proof.
    intuition.
    destruct stacks, stack; destruct m, n ; solve [ 
      auto |
      (left ; intros ; unfold regular in p ; rewrite H in p ; firstorder)
    ].
  Qed.

  Next Obligation.
  Proof.
    rewrite <- Stack.push_on_regular_does_not_deepen with
      (x := elt)
      (p := dirty_push_obligation_2 elt p eq_refl).
    exact H.
  Qed.

End Deque.
