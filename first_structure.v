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

  Axiom empty_is_red : forall A, forall buff : t A 0, color buff = Red.

  Axiom empty_is_red_contr : (* yes, I'm lazy *)
    forall A, forall n, forall buff : t A n,
      color buff <> Red -> n > 0.
End Finite_buffer.

Module Deque (B : Finite_buffer).
  Module Stack.
    Inductive lvl (A : Set) :=
      | Lvl : forall m n, B.t A m -> B.t A n -> lvl A.

    Inductive t (A : Set) : Set :=
      | Empty : t A
      | Cons  : lvl A -> t (A * A) -> t A.

    Definition lvl_color (A : Set) (lvl : lvl A) :=
      match lvl with
      (* limit case *)
      | Lvl 0 _ buff _
      | Lvl _ 0 _ buff => B.color buff
      (* general case *)
      | Lvl _ _ prefix suffix => min_color (B.color prefix) (B.color suffix)
      end.

    Definition top_color (A : Set) (stack : t A) :=
      match stack with
      | Empty => Red
      | Cons toplvl _ => lvl_color toplvl
      end.

    Definition regular (A : Set) (s : t A) :=
      let all_yellows :=
        fix f (B : Set) (s : t B) : Prop :=
          match s with
          | Empty => True
          | Cons lvl rest => (lvl_color lvl = Yellow) /\ f (prod B B) rest
          end
      in
      match s with
      | Empty => True (* FIXME: why not False? *)
      | Cons _ yellows => all_yellows (prod A A) yellows
      end.

    Definition is_empty (A : Set) (s : t A) :=
      match s with
      | Cons (Lvl 0 0 _ _) Empty  => True
      | _ => False
      end.

    Program Definition empty (A : Set) : { s : t A | regular s } :=
      Cons (Lvl (B.empty A) (B.empty A)) (Empty (prod A A)).

    Program Definition push (A : Set) (elt : A) (s : t A)
      (p : top_color s <> Red \/ is_empty s) : t A :=
      match s with
      | Empty => !
      | Cons (Lvl n m prefix suffix) rest =>
        Cons (Lvl (B.push _ elt prefix) suffix) rest
      end.

    Next Obligation.
    Proof. intuition. Qed.

    Next Obligation.
    Proof.
      intuition.
        apply B.full_is_red_contr with (A := A) (buff := prefix).
        destruct m, n ; simpl in H ; firstorder.
          rewrite B.empty_is_red in H ; auto.
          destruct (B.color prefix) ; auto ; try discriminate.

        destruct n; firstorder.
        apply B.max_len_positive.
    Qed.

    Fixpoint type_of_last_lvl (A : Set) (s : t A) : Set :=
      match s with
      | Empty => A
      | Cons _ rest => type_of_last_lvl rest
      end.

    Theorem push_on_regular_does_not_deepen :
      forall A : Set, forall x : A, forall s : t A, forall p,
        type_of_last_lvl s = type_of_last_lvl (push x s p).
    Proof. 
      intros ; destruct s.
        destruct p ; intuition.
        destruct l ; auto.
    Qed.

    Hint Rewrite <- push_on_regular_does_not_deepen : stack.
  End Stack.

  Module S := Stack.

  Inductive t (A : Set) : Set :=
    | Nil : t A
    | Cons : forall s : Stack.t A, t (Stack.type_of_last_lvl s) -> t A.

  Notation "∅" := Nil.
  Notation "x ++ y" := (Cons x y).

  Fixpoint no_yellow_on_top (A : Set) (d : t A) : Prop :=
    match d with
    | ∅ => True
    | stack ++ stacks =>
      match Stack.top_color stack with
      | Yellow => False
      | _ => no_yellow_on_top stacks
      end
    end.

  Fixpoint green_first (A : Set) (d : t A) : Prop :=
    match d with
    | ∅ => True
    | stack ++ stacks =>
      match Stack.top_color stack with
      | Green => True
      | Yellow => green_first stacks
      | Red => False
      end
    end.

  Fixpoint semi_regular (A : Set) (d : t A) : Prop :=
    match d with
    | ∅ => True
    | stack ++ stacks =>
      let green_before_red :=
        match Stack.top_color stack with
        | Green => True
        | Red => green_first stacks
        | Yellow => False
        end
      in
      Stack.regular stack /\ semi_regular stacks /\ green_before_red
    end.

  Lemma semi_impl_noyellow :
    forall A, forall d : t A, semi_regular d -> no_yellow_on_top d.
  Proof.
    intros.
    induction d; auto.
    inversion H ; inversion H1 ; apply IHd in H2; simpl.
    destruct (Stack.top_color s) ; assumption.
  Qed.

  Definition strongly_regular (A : Set) (d : t A) : Prop :=
    match d with
    | ∅ => True (* we won't be able to implement [do_regularize] otherwise. *)
    (* Unless we add another trillion of ad-hoc cases, of course. But that
     * should be enough. Also, I'm hoping it doesn't break anything elsewhere. *)
    | _ ++ stacks =>
      green_first d /\ semi_regular d /\ no_yellow_on_top stacks
    end.

  Definition regular (A : Set) (d : t A) : Prop :=
    match d with
    | ∅ => True (* same reason as in [strongly_regular]. *)
    (* ad-hoc case: the deque is empty *)
    | (S.Cons (S.Lvl 0 0 _ _) S.Empty) ++ ∅ => True
    (* general case *)
    | top_stack ++ stacks =>
      match Stack.top_color top_stack with
      | Yellow => strongly_regular stacks
      | _ => strongly_regular d
      end
    end.

  Program Definition empty (A : Set) : { d : t A | regular d } :=
    let empty_stack := ` (S.empty A) in
    empty_stack ++ (∅ (S.type_of_last_lvl empty_stack)).

  Program Definition dirty_push (A : Set) (elt : A) (d : t A | regular d) : t A :=
    match d with
    | ∅ =>
      let empty_stack := ` (S.empty A) in
      let singleton := S.push elt empty_stack _ in
      singleton ++ ( ∅ (S.type_of_last_lvl singleton) )
    | stack ++ stacks => 
      (Stack.push elt stack _) ++ ((fun _ => _) stacks)
    end.

  Next Obligation.
  Proof.
    intuition.
    destruct stacks, stack ; firstorder;
      destruct l, stack; destruct m, n ; firstorder;
      unfold regular in H;
      left ; intros ; unfold strongly_regular in H; rewrite H0 in H; intuition;
      unfold green_first in H1; rewrite H0 in H1 ; apply H1.
  Qed.

  Next Obligation.
  Proof.
    autorewrite with stack.
    exact H.
  Qed.

  Program Definition do_regularize (A : Set) (d : t A) (p : semi_regular d) :
    { d : t A | strongly_regular d } := !.

  Admit Obligations.

  Program Definition regularize (A : Set) (top_stack : Stack.t A)
    (rest : t (Stack.type_of_last_lvl top_stack) | semi_regular rest)
    (H0 : Stack.top_color top_stack = Red -> green_first rest)
    (H1 : Stack.regular top_stack) :
    { d : t A | regular d } :=
      match Stack.top_color top_stack with
      | Green => top_stack ++ rest
      | Yellow => top_stack ++ (do_regularize rest _)
      | Red => do_regularize (top_stack ++ rest) _
      end.

  Next Obligation.
  Proof.
    rewrite <- Heq_anonymous.
    destruct top_stack.
      firstorder ; apply semi_impl_noyellow ; auto.

      destruct l ; destruct m, n ; firstorder ; solve [
        (apply semi_impl_noyellow ; auto) |
        (destruct rest ; [ firstorder | firstorder ;
        simpl; (* destruct (Stack.top_color s). doesn't work *) admit]) |
        (destruct top_stack; destruct rest ; firstorder; simpl; admit)
      ].
  Qed.

  Next Obligation.
  Proof.
    rewrite <- Heq_anonymous.
    destruct top_stack ; firstorder.
      exact (proj2_sig (do_regularize rest H)).

      destruct l ; destruct m, n ; try solve [ (exact (proj2_sig (do_regularize rest H))) ].
      destruct top_stack ; firstorder; [
        (destruct (` (do_regularize rest H)) eqn:Heq; auto; rewrite <- Heq) |
        idtac
      ] ; exact (proj2_sig (do_regularize rest H)).
  Qed.

  Next Obligation.
  Proof.
    intuition.
    rewrite <- Heq_anonymous.
    auto.
  Qed.

  Next Obligation.
  Proof.
    Lemma strongr_impl_r :
      forall A, forall d : t A, strongly_regular d -> regular d.
    Proof.
      intros.
      destruct d ; auto.
      destruct s ; firstorder ; unfold regular.
      destruct l ; firstorder.
      destruct (S.top_color (S.Cons (S.Lvl t0 t1) s)) eqn:Color.
        (* TODO: factorize *)
        destruct m, n; firstorder; [
          (destruct s ; destruct d) | idtac | idtac | idtac
        ]; firstorder ; rewrite Color ; auto.

        destruct m, n; firstorder.

        destruct m, n; firstorder; [
          (destruct s ; destruct d) | idtac | idtac | idtac
        ]; firstorder ; rewrite Color ; auto.
    Qed.
    apply strongr_impl_r.
    exact ( proj2_sig ( do_regularize (top_stack ++ rest) _) ).
  Qed.

End Deque.
