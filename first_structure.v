Require Import Program.
Require Import Coq.Arith.Bool_nat.
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
  Module Lvl.
    Inductive t (A : Set) :=
      | Lvl : forall m n, B.t A m -> B.t A n -> t A.

    Definition prefix_length (A : Set) (x : t A) :=
      match x with
      | Lvl n _ _ _ => n
      end.

    Definition suffix_length (A : Set) (x : t A) :=
      match x with
      | Lvl _ n _ _ => n
      end.

    Definition color (A : Set) (lvl : t A) :=
      match lvl with
      (* limit case *)
      | Lvl 0 _ buff _
      | Lvl _ 0 _ buff => B.color buff
      (* general case *)
      | Lvl _ _ prefix suffix => min_color (B.color prefix) (B.color suffix)
      end.

    Definition is_empty (A : Set) (lvl : t A) :=
      match lvl with
      | Lvl 0 0 _ _ => True
      | _ => False
      end.

    Program Definition empty (A : Set) := Lvl (B.empty A) (B.empty A).

    Program Definition push (A : Set) (elt : A) (s : t A)
      (p : color s <> Red \/ is_empty s) : t A :=
      match s with
      | Lvl n m prefix suffix => Lvl (B.push _ elt prefix) suffix
      end.

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

    Program Definition inject (A : Set) (elt : A) (s : t A)
      (p : color s <> Red \/ is_empty s) : t A :=
      match s with
      | Lvl n m prefix suffix => Lvl prefix (B.inject _ elt suffix)
      end.

    (* TODO: clean-up *)
    Next Obligation.
    Proof.
      intuition.
        apply B.full_is_red_contr with (A := A) (buff := suffix).
        destruct m, n ; simpl in H ; firstorder.
          rewrite B.empty_is_red in H ; auto.
          rewrite B.empty_is_red in H ; auto.
          destruct (B.color suffix) ; auto ; try discriminate.
          destruct (B.color prefix) ; auto.
        
        destruct n, m; firstorder.
        apply B.max_len_positive.
    Qed.

    Program Definition pop (A : Set) (lvl : t A) (p : ~ is_empty lvl) : A * t A :=
      match lvl with
      (* prefix is not empty *)
      | Lvl (S k) _ prefix suffix =>
        let (elt, prefix) := B.pop prefix in
        (elt, Lvl prefix suffix)
      (* prefix is empty *)
      | Lvl 0 (S k) empty suffix =>
        let (elt, suffix) := B.pop suffix in
        (elt, Lvl empty suffix)
      (* lvl is empty : absurd *)
      | _ => !
      end.

    Next Obligation.
    Proof.
      contradict p; intuition.
      destruct lvl ; destruct m, n.
        firstorder.
        apply H with (k := n) (empty := t0) (suffix := t1) ; trivial.
        apply H0 with (k := m) (wildcard' := 0) (prefix := t0) (suffix := t1) ; trivial.
        apply H0 with (k := m) (wildcard' := (S n)) (prefix := t0) (suffix := t1) ; trivial.
    Qed.

    Next Obligation.
    Proof. intuition; contradict H; discriminate. Qed.

    Program Definition eject (A : Set) (lvl : t A) (p : ~ is_empty lvl) : A * t A :=
      match lvl with
      (* suffix is not empty *)
      | Lvl _ (S k) prefix suffix =>
        let (elt, suffix) := B.eject suffix in
        (elt, Lvl prefix suffix)
      (* suffix is empty *)
      | Lvl (S k) 0 prefix empty =>
        let (elt, prefix) := B.eject prefix in
        (elt, Lvl prefix empty)
      (* lvl is empty : absurd *)
      | _ => !
      end.

    Next Obligation.
    Proof.
      contradict p; intuition.
      destruct lvl ; destruct m, n.
        firstorder.
        apply H0 with (k := n) (wildcard' := 0) (prefix := t0) (suffix := t1) ; trivial.
        apply H with (k := m) (prefix := t0) (empty := t1) ; trivial.
        apply H0 with (k := n) (wildcard' := (S m)) (prefix := t0) (suffix := t1) ; trivial.
    Qed.

    Next Obligation.
    Proof. intuition; contradict H; discriminate. Qed.

  End Lvl.

  Module Stack.
    Inductive t (A : Set) : Set :=
      | Empty : t A
      | Cons  : Lvl.t A -> t (A * A) -> t A.

    Definition top_color (A : Set) (stack : t A) :=
      match stack with
      | Empty => Red
      | Cons toplvl _ => Lvl.color toplvl
      end.

    Definition regular (A : Set) (s : t A) :=
      let all_yellows :=
        fix f (B : Set) (s : t B) : Prop :=
          match s with
          | Empty => True
          | Cons lvl rest => (Lvl.color lvl = Yellow) /\ f (prod B B) rest
          end
      in
      match s with
      | Empty => False (* FIXME: why not False? *)
      | Cons _ yellows => all_yellows (prod A A) yellows
      end.

    Definition is_empty (A : Set) (s : t A) :=
      match s with
      | Cons lvl Empty => Lvl.is_empty lvl
      | _ => False
      end.

    Program Definition empty (A : Set) : { s : t A | regular s } :=
      Cons (Lvl.empty A) (Empty (prod A A)).

    (* TODO: probably unused, remove. *)
    Program Definition push (A : Set) (elt : A) (s : t A)
      (p : top_color s <> Red \/ is_empty s) : t A :=
      match s with
      | Empty => !
      | Cons lvl rest => Cons (Lvl.push elt lvl _) rest
      end.

    Next Obligation.
    Proof. intuition. Qed.

    Next Obligation.
    Proof. destruct rest ; firstorder. Qed.

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
        destruct t0 ; auto.
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
    | _ ++ stacks => green_first d /\ semi_regular d
    end.

  Definition regular (A : Set) (d : t A) : Prop :=
    match d with
    | ∅ => True (* same reason as in [strongly_regular]. *)
    (* ad-hoc case: the deque is empty *)
    | (S.Cons (Lvl.Lvl 0 0 _ _) S.Empty) ++ ∅ => True (* TODO: Use [is_empty] *)
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
      destruct t0, stack; destruct m, n ; firstorder;
      unfold regular in H;
      left ; intros ; unfold strongly_regular in H; rewrite H0 in H; intuition;
      unfold green_first in H1; rewrite H0 in H1 ; apply H1.
  Qed.

  Next Obligation.
  Proof.
    autorewrite with stack.
    exact H.
  Qed.

  Program Definition no_buff_case (A : Set) (x : Lvl.t A) (y : Lvl.t (A * A))
    (yellows : Stack.t ((A * A) * (A * A)))
    (rest : t (Stack.type_of_last_lvl yellows)) :
    { d : t A | strongly_regular d } :=
        !.

  Admit Obligations.

  Print Implicit Lvl.Lvl.
  Check Lvl.pop.
  Print Implicit Lvl.pop.
  Print Implicit Lvl.push.

  Program Definition do_regularize (A : Set) (d : t A) (p : semi_regular d) :
    { d : t A | strongly_regular d } :=
    match d with
    | ∅ => (fun _ => _) ∅
    (* shitty case: last lvl *)
    | (Stack.Cons lvli Stack.Empty) ++ ∅ => ! 
    (* general case *)
    | (Stack.Cons lvli (Stack.Cons lvlSi yellows)) ++ stacks
    | (Stack.Cons lvli Stack.Empty) ++ (Stack.Cons lvlSi yellows) ++ stacks =>
      match Lvl.color lvli with
      | Yellow => !
      | Green => d (* nothing to do *)
      | Red =>
        if le_gt_dec 2 (Lvl.prefix_length lvlSi + Lvl.suffix_length lvlSi) then
          (* Two-Buffer Case *)
          let lvlSi : Lvl.t (A * A) :=
            match lvlSi with
            | Lvl.Lvl 0 (S k) empty suffix =>
              let (elt, new_suffix) := B.pop suffix in
              Lvl.Lvl (B.inject _ elt empty) new_suffix
            | Lvl.Lvl (S k) 0 prefix empty =>
              let (elt, new_prefix) := B.eject prefix in
              Lvl.Lvl new_prefix (B.inject _ elt empty)
            | lvl => lvl
            end
          in
          (* greenify the prefix *)
          let pair : (Lvl.t A) * (Lvl.t (A * A)) :=
            match lvli, lvlSi with
            | Lvl.Lvl pi_len si_len pi si, Lvl.Lvl pSi_len _ pSi sSi =>
              match pi_len with
              | 4 | 5 =>
                let (last, pi) := B.pop pi in
                let (second_last, pi) := B.pop (n := pred (pred pi_len)) pi in
                let pSi := B.push _ (second_last, last) pSi in
                (Lvl.Lvl pi si, Lvl.Lvl pSi sSi)
              | 0 | 1 =>
                let (pair, pSi) := B.pop (n := pred pSi_len) pSi in
                let (elt1, elt2) := pair in (* Fuck you Coq, Fuck *you* *)
                let pi := B.inject _ elt2 (B.inject _ elt1 pi) in
                (Lvl.Lvl pi si, Lvl.Lvl pSi sSi)
              | _ => (lvli, lvlSi)
              end
            end
          in
          let (lvli, lvlSi) := pair in
          (* greenify the suffix *)
          let pair : (Lvl.t A) * (Lvl.t (A * A)) :=
            match lvli, lvlSi with
            | Lvl.Lvl pi_len si_len pi si, Lvl.Lvl _ sSi_len pSi sSi =>
              match si_len with
              | 4 | 5 =>
                let (first, si) := B.pop si in
                let (second, si) := B.pop (n := pred (pred si_len)) si in
                let lvlSi := B.inject _ (first, second) sSi in
                (Lvl.Lvl pi si, Lvl.Lvl pSi sSi)
              | 0 | 1 =>
                let (pair, lvlSi) := B.eject (n := pred sSi_len) sSi in
                let (elt1, elt2) := pair in (* Fuck you Coq, Fuck *you* *)
                let si := B.inject _ elt1 (B.inject _ elt2 si) in
                (Lvl.Lvl pi si, Lvl.Lvl pSi sSi)
              | _ => (lvli, lvlSi)
              end
            end
          in
          let (lvli, lvlSi) := pair in
          !
        else
          (* TODO *)
          !
      end
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
