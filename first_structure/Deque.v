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
      | Empty => False
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

    Theorem push_preserves_regularity : (* TODO: inject that in the sig of push *)
      forall A:Set, forall x : A, forall s : t A, forall p,
        regular s -> regular (push x s p).
    Proof. intros ; destruct s ; firstorder. Qed.

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
      | Yellow => Stack.regular top_stack /\ strongly_regular stacks
      | Green => semi_regular d
      | Red =>
        match stacks with
        | ∅ => S.is_empty top_stack (* ad-hoc case: the deque is empty *)
        | _ => False
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
    | ∅ => ∅ A
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
      match Lvl.color lvli with
      | Yellow => !
      | Green => d (* nothing to do *)
      | Red =>
        let (lvli, lvlSi) := Lvl.equilibrate lvli (Some lvlSi) in
        match lvlSi with
        | None =>
          (* FIXME: I don't want to nest matchings like that, but Coq fails to
           * typecheck if I don't. (see the commented code just below)
           *
           * With the [return ...] there are obligations you can't even try to
           * solve (or admit) because it will fail to type then (resulting in an
           * uncaught exception when using [Admit Obligations].
           *   (N.B. that happens with [t A] as return type, or the one present
           *    in the comment at the moment.)
           *
           * Withouth the [return] it just refuses to type the definition. *)
          match yellows with
          | S.Empty =>
            match stacks with
            | ∅ => S.Cons lvli (S.Empty (prod A A)) ++ (∅ (prod A A))
            | _ => !
            end
          | _ => !
          end
            (*
          match yellows, stacks return { d : t A | strongly_regular d } with
          | S.Empty, ∅ => (S.Cons lvli (S.Empty (prod A A))) ++ (∅ (prod A A))
          | _, _ => ! (* lvlSi is removed only if it is the last level. *)
          end
          *)
        | Some lvlSi =>
          match Lvl.color lvlSi with
          | Red => !
          | Yellow => (S.Cons lvli (S.Cons lvlSi yellows)) ++ stacks
          | Green =>
            (S.Cons lvli (S.Empty (prod A A))) ++ (S.Cons lvlSi yellows) ++ stacks
          end
        end
      end
    (* absurd cases *)
    | _ => !
    end.

  Next Obligation.
  Proof.
    unfold semi_regular in p; intuition.
    simpl in H2; rewrite <- Heq_anonymous in H2.
    trivial.
  Qed.

  Next Obligation.
  Proof. simpl; rewrite <- Heq_anonymous; auto. Qed.

  Next Obligation.
  Proof. rewrite H ; auto. Qed.

  Next Obligation.
  Proof. rewrite H0; rewrite <- Heq_anonymous0; firstorder. Qed.

  Next Obligation.
  Proof. rewrite H0 ; rewrite <- Heq_anonymous0; auto. Qed.

  Next Obligation.
  Proof. firstorder; simpl in H2; rewrite <- Heq_anonymous in H2; trivial. Qed.

  Next Obligation.
  Proof. firstorder; simpl; rewrite <- Heq_anonymous; trivial. Qed.

  Next Obligation.
  Proof. firstorder; rewrite H ; discriminate. Qed.

  Next Obligation.
  Proof. rewrite H; auto. Qed.

  Next Obligation.
  Proof.
    contradict H.
    (* Here we want to prove that if [Level.equilibrate] removes the second
     * level, that level was the last one of the deque.
     * Unfortunately, I don't think that can be proved with the hypothesis we
     * have at hand.
     * That fact isn't proved in the original paper either, it merely says
     * "level i+1 must be the bottom most level". And that obligation doesn't
     * come from the (semi-)regularity of the structure, it is indeed possible
     * exhibit a semi-regular deque such that the "regularisation" operation
     * described in the paper would, if called on that deque, remove a level
     * which isn't the bottomest one.
     * So we must admit here (and maybe prove later) that we will never
     * encounter such shaped deques. *)
     admit.
  Qed.

  Next Obligation.
    (* Same obligation as earlier. *)
  Admitted.

  Next Obligation.
  Proof. firstorder; rewrite H0; trivial. Qed.

  Next Obligation.
  Proof.
    firstorder; first [ rewrite H0 | rewrite <- Heq_anonymous0 ] ; trivial.
  Qed.

  Next Obligation.
  Proof.
    inversion p ; inversion H0.
    simpl in H2 ; rewrite <- Heq_anonymous in H2.
    trivial.
  Qed.

  Next Obligation.
  Proof.
    constructor.
      simpl ; rewrite <- Heq_anonymous ; trivial.
      trivial.
  Qed.

  Next Obligation.
  Proof.
    inversion p ; inversion H0.
    simpl in H2 ; rewrite <- Heq_anonymous in H2.
    destruct (Lvl.color lvlSi) ; try discriminate || contradict H2 ; trivial.
  Qed.

  Next Obligation.
  Proof. rewrite H ; auto. Qed.

  Next Obligation.
  Admitted. (* once again *)

  Next Obligation.
  Admitted. (* and again *)

  Next Obligation.
  Proof. firstorder; rewrite H0; trivial. Qed.

  Next Obligation.
  Proof.
    firstorder; first [ rewrite H0 | rewrite <- Heq_anonymous0 ] ; trivial.
  Qed.

  (* Absurd case (finally) *)
  Next Obligation.
  Proof.
    destruct d ; firstorder.
    destruct s ; firstorder.
    destruct d, s ; intuition.
      apply H with (lvli := t0) ; reflexivity.
      apply H0 with (lvli := t0) (lvlSi := t1) (yellows := s)
        (stacks := ∅ (S.type_of_last_lvl s)) ; reflexivity.

      destruct s0 ; firstorder.
      apply H1 with (lvli := t0) (lvlSi := t1) (yellows := s0)
        (stacks := d) ; reflexivity.

      apply H0 with (lvli := t0) (lvlSi := t1) (yellows := s)
        (stacks := s0 ++ d) ; reflexivity.
  Qed.

  Next Obligation.
  Proof. intuition; discriminate. Qed.

  Next Obligation.
  Proof. intuition ; discriminate. Qed.

  Program Definition regularize {A : Set} (top_stack : Stack.t A)
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
    rewrite <- Heq_anonymous; intuition.
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

  Program Definition push {A : Set} (elt : A) (d : t A | regular d) :
    { d : t A | regular d } :=
    match d with
    | ∅ =>
      let empty_stack := ` (S.empty A) in
      let singleton := S.push elt empty_stack _ in
      singleton ++ ( ∅ (S.type_of_last_lvl singleton) )
    | stack ++ stacks =>
      let top_stack := Stack.push elt stack _ in
      let stacks' : t (S.type_of_last_lvl top_stack) := (fun _ => _) stacks in
      let proof : semi_regular stacks' := _ in
      regularize top_stack (exist _ stacks' proof) _ _
    end.

  Next Obligation.
  Proof. right; exact (proj2_sig (Lvl.empty A)). Qed.

  Next Obligation.
  Proof.
    destruct (Lvl.color (Lvl.push elt (` (Lvl.empty A)) _)) eqn:Color ; auto.
    contradict Color.
    (* yet another case we can't prove :
     *   Lvl.color Lvl.(push elt empty) <> Red *)
    admit.
  Qed.

  Next Obligation.
  Proof.
    intuition.
    destruct stacks, stack ; firstorder; unfold regular in H.
      destruct (Stack.top_color (S.Cons t0 stack)) eqn:Heq; solve [
        (left ; intros ; discriminate) |
        (right ; assumption)
      ].

      left ; intros; simpl in H ; simpl in H0 ; rewrite H0 in H ; intuition.
  Qed.

  Next Obligation.
  Proof.
    autorewrite with stack.
    exact H.
  Qed.

  Next Obligation.
  Proof.
    unfold regular in H.
    (* [destruct (Stack.top_color stack) eqn:Color.]
        -> "Error: The correctness of the conclusion relies on the body of c" *)
    admit. (* FIXME *)
  Qed.

  Next Obligation.
  Proof.
    (* The result of [Stack.push] begins with a Red level, that implicates that
     * what was given to [push] was Yellow, therefore [green_first stacks] holds.
     * However Coq doesn't know that. *)
  Admitted.

  Next Obligation.
    Lemma regdeque_impl_regstack :
      forall A:Set, forall stack:S.t A, forall deque: t (S.type_of_last_lvl stack),
        regular (stack ++ deque) -> S.regular stack.
    Proof.
      intros.
      unfold regular in H ; destruct stack.
        simpl in * |- *; destruct deque ; auto.
        destruct (Stack.top_color (S.Cons t0 stack)) eqn:Color ; solve [
          (inversion H; assumption) |
          (destruct deque ; destruct stack ; firstorder)
        ].
    Qed.
  Proof.
    apply S.push_preserves_regularity.
    apply regdeque_impl_regstack with (deque := stacks).
    assumption.
  Qed.

End Make.
