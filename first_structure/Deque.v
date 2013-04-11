(* ab :coerce: ⨞ *)
(* ab neo. Next Obligation. *)

Require Import Program.
Require Import Coq.Arith.Bool_nat.
Require Import List.

Require Import Misc.
Require Level.

Module Type Intf.
  Parameter t : Set -> Type.

  Parameter regular : forall {A:Set}, t A -> Prop.

  Parameter empty : forall A, { d : t A | regular d }.

  Parameter push : forall A:Set, A -> { d : t A | regular d } -> { d : t A | regular d }.
End Intf.

Notation "⨞ x" := ((fun _ => _) ((fun i => i) x)) (at level 1).

Module Make (Lvl : Level.Intf) : Intf.

  Module Stack.
    Inductive t (A : Set) : Set -> Type :=
      | Empty : t A A
      | Cons  : forall B:Set, Lvl.t A -> t (A * A) B -> t A B.

    Arguments Cons [A] [B] _ _.

    Notation "a ::: b" := (@Cons _ _ a b) (at level 40).

    Definition top_color {A B : Set} (stack : t A B) :=
      match stack with
      | Empty => Red
      | toplvl ::: _ => Lvl.color toplvl
      end.

    Fixpoint all_yellows {A B : Set} (s : t A B) :=
      match s with
      | Empty => True
      | lvl ::: rest => (Lvl.color lvl = Yellow) /\ all_yellows rest
      end.

    Program Definition regular {A B : Set} (s : t A B) :=
      match s with
      | Empty => False
      | _ ::: yellows => all_yellows yellows
      end.

    Definition real_empty {A B : Set} (s : t A B) :=
      match s with
      | Empty => True
      | _ => False
      end.

    Definition is_empty {A B : Set} (s : t A B) :=
      match s with
      | lvl ::: Empty => Lvl.is_empty lvl
      | _ => False
      end.

    Theorem dec_is_empty :
        forall {A B}, forall s : t A B, {is_empty s} + {~ is_empty s}.
    Proof.
      destruct s.
        right ; auto.
        destruct s ; simpl.
          apply Lvl.dec_is_empty.
          right; auto.
    Qed.

    Program Definition empty (A : Set) : { s : t A (A * A) | regular s } :=
      Cons (` (Lvl.empty A)) (Empty _).

    Program Definition push {A B : Set} (elt : A) (s : t A B)
      (p : top_color s <> Red \/ is_empty s) : t A B :=
      match s with
      | Empty => !
      | lvl ::: rest => (Lvl.push elt lvl _) ::: rest
      end.

    Next Obligation.
    Proof. rewrite <- Heq_s in p; intuition. Qed.

    Next Obligation.
    Proof. rewrite <- Heq_s in p; destruct rest ; firstorder. Qed.

    Theorem push_preserves_regularity : (* TODO: inject that in the sig of push *)
      forall A B:Set, forall x : A, forall s : t A B, forall p,
        regular s -> regular (push x s p).
    Proof. intros ; destruct s ; firstorder. Qed.
  End Stack.

  Module S := Stack.

  Inductive deque (A : Set) : Type :=
    | Nil : deque A
    | Cons : forall B : Set, forall s : S.t A B, deque B -> deque A.

  Definition t := deque.

  Arguments Cons [A B] _ _.

  Notation "∅" := Nil.
  Notation "x ++ y" := (Cons x y).

  Notation "x ::: y" := (@S.Cons _ _ x y) (at level 40).

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
    empty_stack ++ (∅ (prod A A)).

  Next Obligation.
  Proof.
    destruct (Lvl.color (` (Lvl.empty A))) ; auto.
    exact (proj2_sig (Lvl.empty A)).
  Qed.

  Definition is_empty {A : Set} (d : t A) : Prop :=
    match d with
    | ∅ => True
    | _ ++ _ => False
    end.

  Inductive regularization_cases (A : Set) : t A -> Type :=
    | empty_case : regularization_cases A (∅ A)
    | one_buffer_case :
      forall lvli : Lvl.t A,
        regularization_cases A ((lvli ::: (S.Empty _)) ++ (∅ _)) 
    | general_case1 :
        forall B : Set,
        forall lvli : Lvl.t A, forall lvlSi : Lvl.t (A * A),
        forall yellows : S.t ((A * A) * (A * A)) B,
        forall stacks : t B,
        regularization_cases A
            ((lvli ::: (lvlSi ::: yellows)) ++ stacks)
    | general_case2 :
        forall B : Set,
        forall lvli : Lvl.t A, forall lvlSi : Lvl.t (A * A),
        forall yellows : S.t ((A * A) * (A * A)) B,
        forall stacks : t B,
        regularization_cases A
            ((lvli ::: (S.Empty _)) ++ (lvlSi ::: yellows) ++ stacks).

  Parameter discrim : forall A : Set, forall d : t A, regularization_cases A d.

  Program Definition do_regularize {A : Set} (d : t A) (p : semi_regular d) :
    { d : t A | strongly_regular d } :=
    match discrim A d with
    | empty_case => ∅ A
    (* shitty case: last lvl *)
    (* N.B. if [color lvli = Red] either [d] is empty, or we are in the
     * "One-Buffer Case". *)
    | one_buffer_case lvli =>
      match Lvl.color lvli with
      | Yellow => !
      | Green => d (* nothing to do *)
      | Red =>
        let (lvli, lvlSi) := Lvl.equilibrate True lvli None in
        match Lvl.color lvlSi with
        | Red => (S.Cons lvli (S.Empty (prod A A))) ++ (∅ (prod A A))
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
    (* general case *)
    | general_case1 B lvli lvlSi yellows stacks
    | general_case2 B lvli lvlSi yellows stacks =>
      match Lvl.color lvli with
      | Yellow => !
      | Green => d (* nothing to do *)
      | Red =>
        let last_levels := S.real_empty yellows /\ is_empty stacks in
        let (lvli, lvlSi) := Lvl.equilibrate last_levels lvli (Some lvlSi) in
        match Lvl.color lvlSi with
        | Red => _
        | Yellow => (S.Cons lvli (S.Cons lvlSi yellows)) ++ stacks
        | Green =>
          (S.Cons lvli (S.Empty (prod A A))) ++ (S.Cons lvlSi yellows) ++ stacks
        end
      end
    end.

  Next Obligation.
  Proof.
    unfold semi_regular in p; intuition.
    simpl in H2; rewrite <- Heq_anonymous0 in H2.
    trivial.
  Qed.

  Next Obligation.
  Proof. simpl; rewrite <- Heq_anonymous0; auto. Qed.

  Next Obligation.
  Proof. rewrite H0 ; auto. Qed.

  Next Obligation.
  Proof. rewrite H0; rewrite <- Heq_anonymous1; firstorder. Qed.

  Next Obligation.
  Proof. rewrite H0 ; rewrite <- Heq_anonymous1; auto. Qed.

  Next Obligation.
  Proof. firstorder; simpl in H2; rewrite <- Heq_anonymous0 in H2; trivial. Qed.

  Next Obligation.
  Proof. firstorder; simpl; rewrite <- Heq_anonymous0; trivial. Qed.

  Next Obligation.
  Proof. firstorder; rewrite H ; discriminate. Qed.

  Next Obligation.
  Proof.
    destruct yellows, stacks ; solve [
      (
        pose ( d := (lvli0 ::: S.Empty (prod A A)) ++ Nil (prod A A) ) ;
        assert (strongly_regular d); [
          (simpl; rewrite H0; tauto) |
          exact (exist strongly_regular d H1)
        ]
      ) |

      (contradict H; firstorder)
  ].
  Qed.
  
  Next Obligation.
  Proof.
    firstorder; first [ rewrite H0 | rewrite <- Heq_anonymous0 ] ; trivial.
  Qed.

  Next Obligation.
  Proof.
    rewrite H0 ; rewrite <- Heq_anonymous1.
    repeat split; inversion p.
      inversion H1; assumption.
      inversion H2; assumption.
  Qed.

  Next Obligation.
  Proof.
    inversion p ; inversion H0.
    simpl in H2 ; rewrite <- Heq_anonymous0 in H2.
    trivial.
  Qed.

  Next Obligation.
  Proof.
    constructor.
      simpl ; rewrite <- Heq_anonymous0 ; trivial.
      trivial.
  Qed.

  Next Obligation.
  Proof.
    inversion p ; inversion H0.
    simpl in H2 ; rewrite <- Heq_anonymous0 in H2.
    destruct (Lvl.color lvlSi) ; try discriminate || contradict H2 ; trivial.
  Qed.

  Next Obligation.
  Proof. 
    destruct yellows, stacks ; solve [
      (
        pose ( d := (lvli0 ::: S.Empty (prod A A)) ++ Nil (prod A A) ) ;
        assert (strongly_regular d); [
          (simpl; rewrite H0; tauto) |
          exact (exist strongly_regular d H1)
        ]
      ) |

      (contradict H; firstorder)
  ].
  Qed.
  
  Next Obligation.
  Proof.
    firstorder; first [ rewrite H0 | rewrite <- Heq_anonymous0 ] ; trivial.
  Qed.

  Next Obligation.
  Proof.
    rewrite H0 ; rewrite <- Heq_anonymous1.
    repeat split; inversion p; inversion H2; inversion H3.
      assumption.
      inversion H6. assumption.
  Qed.

  Program Definition regularize {A B : Set} (top_stack : Stack.t A B)
    (rest : t B | semi_regular rest)
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
      singleton ++ ( ∅ (prod A A) )
    | stack ++ stacks =>
      let top_stack := Stack.push elt stack _ in
      regularize top_stack stacks _ _
    end.

  Next Obligation.
  Proof. right; exact (proj2_sig (Lvl.empty A)). Qed.

  Next Obligation.
  Proof.
    rewrite Lvl.push_on_empty_yellowifies ; auto.
    exact (proj2_sig (Lvl.empty A)).
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
    simpl in H ; destruct (S.top_color stack) ; destruct stacks ; firstorder.
  Qed.

  Next Obligation.
  Proof. (* draft *)
    destruct stack.
      destruct stacks ; firstorder.
    simpl in H.
    apply Lvl.red_after_yellow in H.
    unfold regular in H0. unfold Stack.top_color in H0.  
    rewrite H in H0.
    intuition.
    unfold strongly_regular in H2.
    destruct stacks; simpl ; firstorder.
  Qed.

  Next Obligation.
    Lemma regdeque_impl_regstack :
      forall A B:Set, forall stack:S.t A B, forall deque: t B,
        regular (stack ++ deque) -> S.regular stack.
    Proof.
      intros.
      unfold regular in H ; destruct stack.
        simpl in * |- *; destruct deque0 ; auto.
        destruct (Stack.top_color (S.Cons t0 stack)) eqn:Color ; solve [
          (inversion H; assumption) |
          (destruct deque0 ; destruct stack ; firstorder)
        ].
    Qed.
  Proof.
    apply S.push_preserves_regularity.
    apply regdeque_impl_regstack with (deque := stacks).
    assumption.
  Qed.

End Make.
