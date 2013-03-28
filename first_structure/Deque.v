Require Import Program.
Require Import Coq.Arith.Bool_nat.
Require Import List.

Require Import Misc.
Require Level.

Module Make (Lvl : Level.Intf).

  Module Stack.
    Inductive t (A : Set) : Set :=
      | Empty : t A
      | Cons  : Lvl.t A -> t (A * A) -> t A.

    Arguments Cons [A] _ _.

    Definition top_color {A : Set} (stack : t A) :=
      match stack with
      | Empty => Red
      | Cons toplvl _ => Lvl.color toplvl
      end.

    Definition regular {A : Set} (s : t A) :=
      let all_yellows :=
        fix f (B : Set) (s : t B) : Prop :=
          match s with
          | Empty => True
          | Cons lvl rest => (Lvl.color lvl = Yellow) /\ f (prod B B) rest
          end
      in
      match s with
      | Empty => True (* FIXME: why not False? *)
      | Cons _ yellows => all_yellows (prod A A) yellows
      end.

    Definition is_empty {A : Set} (s : t A) :=
      match s with
      | Cons lvl Empty => Lvl.is_empty lvl
      | _ => False
      end.

    Theorem dec_is_empty :
        forall {A}, forall s : t A, {is_empty s} + {~ is_empty s}.
    Proof.
      destruct s.
        right ; auto.
        destruct s ; simpl.
          apply Lvl.dec_is_empty.
          right; auto.
    Qed.

    Program Definition empty (A : Set) : { s : t A | regular s } :=
      Cons (` (Lvl.empty A)) (Empty _).

    Program Definition push {A : Set} (elt : A) (s : t A)
      (p : top_color s <> Red \/ is_empty s) : t A :=
      match s with
      | Empty => !
      | Cons lvl rest => Cons (Lvl.push elt lvl _) rest
      end.

    Next Obligation.
    Proof. intuition. Qed.

    Next Obligation.
    Proof. destruct rest ; firstorder. Qed.

    Fixpoint type_of_last_lvl {A : Set} (s : t A) : Set :=
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
        auto.
    Qed.

    Hint Rewrite <- push_on_regular_does_not_deepen : stack.
  End Stack.

  Module S := Stack.

  Inductive t (A : Set) : Set :=
    | Nil : t A
    | Cons : forall s : S.t A, t (S.type_of_last_lvl s) -> t A.

  Arguments Cons [A] _ _.

  Notation "∅" := Nil.
  Notation "x ++ y" := (Cons x y).

  Fixpoint no_yellow_on_top {A : Set} (d : t A) : Prop :=
    match d with
    | ∅ => True
    | stack ++ stacks =>
      match Stack.top_color stack with
      | Yellow => False
      | _ => no_yellow_on_top stacks
      end
    end.

  Fixpoint green_first {A : Set} (d : t A) : Prop :=
    match d with
    | ∅ => True
    | stack ++ stacks =>
      match Stack.top_color stack with
      | Green => True
      | Yellow => green_first stacks
      | Red => False
      end
    end.

  Fixpoint semi_regular {A : Set} (d : t A) : Prop :=
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

  Definition strongly_regular {A : Set} (d : t A) : Prop :=
    match d with
    | ∅ => True (* we won't be able to implement [do_regularize] otherwise. *)
    (* Unless we add another trillion of ad-hoc cases, of course. But that
     * should be enough. Also, I'm hoping it doesn't break anything elsewhere. *)
    | _ ++ stacks => green_first d /\ semi_regular d
    end.

  Definition regular {A : Set} (d : t A) : Prop :=
    match d with
    | ∅ => True (* same reason as in [strongly_regular]. *)
    | top_stack ++ stacks =>
      match Stack.top_color top_stack with
      | Yellow => strongly_regular stacks
      | Green => strongly_regular d
      | Red =>
        match stacks with
        | ∅ => S.is_empty top_stack (* ad-hoc case: the deque is empty *)
        | _ => strongly_regular d
        end
      end
    end.

  Lemma strongr_impl_r :
    forall A, forall d : t A, strongly_regular d -> regular d.
  Proof.
    intros.
    destruct d ; auto.
    destruct s ; firstorder ; unfold regular.
    destruct (S.top_color (S.Cons t0 s)) eqn:Color.
      firstorder (rewrite Color); trivial.
      contradict H2.
      unfold green_first in H ; rewrite Color in H ; contradict H.
  Qed.

  Program Definition empty (A : Set) : { d : t A | regular d } :=
    let empty_stack := ` (S.empty A) in
    empty_stack ++ (∅ (S.type_of_last_lvl empty_stack)).

  Next Obligation.
  Proof.
    destruct (Lvl.color (` (Lvl.empty A))) ; auto.
    exact (proj2_sig (Lvl.empty A)).
  Qed.

  Program Definition dirty_push {A : Set} (elt : A) (d : t A | regular d) : t A :=
    match d with
    | ∅ =>
      let empty_stack := ` (S.empty A) in
      let singleton := S.push elt empty_stack _ in
      singleton ++ ( ∅ (S.type_of_last_lvl singleton) )
    | stack ++ stacks => 
      (Stack.push elt stack _) ++ ((fun _ => _) stacks)
    end.

  Next Obligation.
  Proof. right. exact (proj2_sig (Lvl.empty A)). Qed.

  Next Obligation.
  Proof.
    intuition.
    destruct stacks, stack ; firstorder; unfold regular in H.
      destruct (Stack.top_color (S.Cons t0 stack)) eqn:Heq.
        left ; intros ; discriminate.
        left ; intros ; discriminate.
        right ; assumption.
  
      left ; intros; simpl in H ; simpl in H0 ; rewrite H0 in H ; intuition.
  Qed.

  Next Obligation.
  Proof.
    autorewrite with stack.
    exact H.
  Qed.

  Program Definition do_regularize {A : Set} (d : t A) (p : semi_regular d) :
    { d : t A | strongly_regular d } :=
    match d with
    | ∅ => (fun _ => _) ∅
    (* shitty case: last lvl *)
    (* N.B. if [color lvli = Red] either [d] is empty, or we are in the
     * "One-Buffer Case". *)
    | (S.Cons lvli S.Empty) ++ ∅ =>
      match Lvl.color lvli with
      | Yellow => !
      | Green => d (* nothing to do *)
      | Red =>
        let (lvli, lvlSi) := Lvl.equilibrate lvli None in
        match lvlSi with
        | None => (S.Cons lvli (S.Empty (prod A A))) ++ (∅ (prod A A))
        | Some lvlSi =>
          match Lvl.color lvlSi with
          | Red => !
          | Green =>
            let AA : Set := prod A A in
            (S.Cons lvli (S.Empty AA))
            ++ (S.Cons lvlSi (S.Empty (prod AA AA)))
            ++ (∅ (prod AA AA))
          | Yellow =>
            let AA : Set := prod A A in
            (S.Cons lvli (S.Cons lvlSi (S.Empty (prod AA AA))))
            ++ (∅ (prod AA AA))
          end
        end
      end
    (* general case *)
    | (S.Cons lvli (S.Cons lvlSi yellows)) ++ stacks
    | (S.Cons lvli S.Empty) ++ (S.Cons lvlSi yellows) ++ stacks =>
(*      match Lvl.color lvli with
      | Yellow => !
      | Green => d (* nothing to do *)
      | Red =>
        let (lvli, lvlSi) := Lvl.equilibrate lvli (Some lvlSi) in
        match lvlSi with
        | None =>
          match yellows, stacks with
          | S.Empty, ∅ => (S.Cons lvli (S.Empty (prod A A))) ++ (∅ (prod A A))
          (* Type Error in the next case.
           * Why doesn't Coq accept [!] as always? *)
          | _, _ => ! (* lvlSi is removed only if it is the last level. *)
          end
        | Some lvlSi =>
          match Lvl.color lvlSi with
          | Red => !
          | Yellow => (S.Cons lvli (S.Cons lvlSi yellows)) ++ stacks
          | Green =>
            (S.Cons lvli (S.Empty (prod A A))) ++ (S.Cons lvlSi yellows) ++ stacks
          end
        end
      end*) !
    (* absurd cases *)
    | _ => !
    end.

  Admit Obligations.

  Program Definition regularize (A : Set) (top_stack : Stack.t A)
    (rest : t (Stack.type_of_last_lvl top_stack) | semi_regular rest)
    (H0 : Stack.top_color top_stack = Red -> green_first rest)
    (H1 : Stack.regular top_stack) :
    { d : t A | regular d } :=
      match Stack.top_color top_stack with
      | Green => top_stack ++ rest
      | Yellow => top_stack ++ (do_regularize rest _)
      | Red =>
        if (S.dec_is_empty top_stack) then
          match rest with
          | ∅ => top_stack ++ rest
          | _ => do_regularize (top_stack ++ rest) _
          end
        else
          do_regularize (top_stack ++ rest) _
      end.

  Next Obligation.
  Proof.
    rewrite <- Heq_anonymous.
    destruct top_stack.
      firstorder ; apply semi_impl_noyellow ; auto.

      intuition.
  Qed.

  Next Obligation.
  Proof.
    rewrite <- Heq_anonymous.
    exact (proj2_sig (do_regularize rest H)).
  Qed.

  Next Obligation.
  Proof. rewrite <- Heq_anonymous; intuition. Qed.

  Next Obligation.
  Proof. rewrite <- Heq_anonymous; intuition. Qed.

  Next Obligation.
  Proof.
    apply strongr_impl_r.
    exact ( proj2_sig ( do_regularize (top_stack ++ rest) _) ).
  Qed.

  Next Obligation.
  Proof. rewrite <- Heq_anonymous; intuition. Qed.

  Next Obligation.
  Proof.
    apply strongr_impl_r.
    exact ( proj2_sig ( do_regularize (top_stack ++ rest) _) ).
  Qed.

End Make.
