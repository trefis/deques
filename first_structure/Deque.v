(* ab :o: ∅ *)
(* ab :coerce: ⨞ *)
(* ab neo. Next Obligation. *)

Require Import Program.
Require Import Coq.Arith.Bool_nat.
Require Import List.

Require Import Misc.
Require Buffer.

Notation "⨞ x" := ((fun _ => _) ((fun i => i) x)) (at level 1).

Module Lvl.
  Record t (A : Set) : Set := makeLvl {
    prefix : Buffer.t A ;
    suffix : Buffer.t A
  }.

  Arguments makeLvl [A] _ _.
  Arguments prefix [A] _. 
  Arguments suffix [A] _. 

  Definition color {A : Set} (lvl : t A) (is_last : bool) :=
    if Buffer.dec_is_empty lvl.(suffix) then 
      if is_last then
        Buffer.color lvl.(prefix)
      else
        Red
    else
      min_color (Buffer.color lvl.(prefix)) (Buffer.color lvl.(suffix)).

  Definition is_empty {A : Set} (lvl : t A) :=
    Buffer.is_empty (prefix lvl) /\ Buffer.is_empty (suffix lvl).

  Definition dec_is_empty {A : Set} (lvl : t A) :
    { is_empty lvl } + { ~ is_empty lvl }.
    destruct lvl ; destruct prefix0, suffix0 ; firstorder.
  Defined.

  Program Definition push {A : Set} (x : A)
    (t : t A | Buffer.color (prefix t) <> Red \/ Buffer.is_empty (prefix t)) :=
    makeLvl (Buffer.push x (prefix t)) (suffix t).

  Definition empty (A : Set) := makeLvl (Buffer.Zero A) (Buffer.Zero A).

  Notation "x ≥ y" := (nat_ge_lt_bool x y) (at level 70, right associativity).
  (* Notation "x ≤ y" := (le_gt_dec x y) (at level 70, right associativity). *)

  Program Definition two_buffer_case {A} (lvli : t A) (lvlSi : t (A * A))
    (H : (Buffer.length (prefix lvlSi)) + (Buffer.length (suffix lvlSi)) >= 2) :=
    let pairSi : Buffer.t (A * A) * Buffer.t (A * A) :=
      match Buffer.dec_is_empty (prefix lvlSi), Buffer.dec_is_empty (suffix lvlSi) with
      | left _, left _ => !
      | left _, right _ =>
        let (elt, buff) := Buffer.pop (suffix lvlSi) in
        pair (Buffer.One (A * A) elt) buff
      | right _, left _ =>
        let (elt, buff) := Buffer.eject (prefix lvlSi) in
        pair buff (Buffer.One (A * A) elt)
      | _, _ => (prefix lvlSi, suffix lvlSi)
      end
    in
    let (pSi, sSi) := pairSi in
    let pairP : Buffer.t A * Buffer.t (A * A) :=
      match Buffer.length (prefix lvli) ≥ 4 with
      | true =>
        let (elt1, buff1) := Buffer.eject (prefix lvli) in
        let Heq_buff1 : (elt1, buff1) = Buffer.eject (prefix lvli) := eq_refl in
        let (elt2, buff2) := Buffer.eject buff1 in
        let Heq_buffe2 : (elt2, buff2) = Buffer.eject buff1 := eq_refl in
        (buff2, Buffer.push (elt2, elt1) pSi)
      | false =>
        match 1 ≥ Buffer.length (prefix lvli) with
        | true =>
          let (pair, pSi) := Buffer.pop pSi in
          let (elt1, elt2) := pair in
          let buff := Buffer.inject elt1 (prefix lvli) in
          (Buffer.inject elt2 buff, pSi)
        | false =>
          (prefix lvli, pSi)
        end
      end
    in
    let pairS : Buffer.t A * Buffer.t (A * A) :=
      let (too_many, H_s4) := (Buffer.length (suffix lvli)) ≥ 4 in
      let (too_few, H_s1) := 1 ≥ (Buffer.length (suffix lvli)) in
      match (Buffer.length (suffix lvli)) ≥ 4 with
      | true =>
        let (elt1, buff) := Buffer.pop (suffix lvli) in
        let (elt2, buff) := Buffer.pop buff in
        (buff, Buffer.inject (elt1, elt2) sSi)
      | false =>
        match 1 ≥ (Buffer.length (suffix lvli)) with
        | true =>
          let (pair, pSi) := Buffer.eject sSi in
          let (elt1, elt2) := pair in
          let buff := Buffer.push elt2 (suffix lvli) in
          (Buffer.push elt1 buff, sSi)
        | false =>
          (suffix lvli, sSi)
        end
      end
    in
    let (pi, pSi) := pairP in
    let (si, sSi) := pairS in
    (makeLvl pi si, makeLvl pSi sSi).

  Require Import Omega.
  Next Obligation.
  Proof.
    destruct (prefix lvlSi), (suffix lvlSi); firstorder.
    simpl in H.
    omega. (* fuck it *)
  Qed.

  Next Obligation.
  Proof.
    destruct (prefix lvli) ; simpl in Heq_anonymous ; firstorder.
  Qed.

  Next Obligation.
  Proof.
    destruct (prefix lvli) ; simpl in Heq_anonymous ; firstorder.
  Qed.

  Next Obligation.
  Proof.
    (* Here Program wants me to prove [Heq_buff1], which I introduced to prove
     * the last obligation, since Program doesn't remember where buff1 comes
     * from.
     * I don't really know how to prove that. *)
     admit.
  Qed.

  Next Obligation.
  Proof.
    (* Despite [Heq_buff1], Coq/Program doesn't know where it comes from, … *)
  Admitted.

  Next Obligation.
  Admitted.

  Next Obligation.
  Proof.
    (* same thing with [buff2] *)
    admit.
  Qed.

  Admit Obligations.
  (* I give up *)

  Program Definition equilibrate {A : Set} (lvli : t A) (lvlSi : t (A * A)) :
    (t A * t (A * A)) :=
    let (bool, H) := 
      (Buffer.length (prefix lvlSi)) + (Buffer.length (suffix lvlSi)) ≥ 2
    in
    match bool with
    | true => two_buffer_case lvli lvlSi _
    | false => (lvli, lvlSi) (* TODO *)
    end.

End Lvl.

Module Stack.
  Inductive t : Set -> Set -> Type :=
    | Nil  : forall A, t A A
    | Cons : forall A B, Lvl.t A -> t (A * A) B -> t A B.

  Arguments Nil [A].
  Arguments Cons [A] [B] _ _.

  Definition is_nil {A B : Set} (stack : t A B) : Prop :=
    match stack with
    | Nil _ => True
    | _ => False
    end.

  Fixpoint all_yellows {A B : Set} (s : t A B) is_last : Prop :=
    match s with
    | Nil _ => True
    | Cons _ _ lvl (Nil _) => Lvl.color lvl is_last = Yellow
    | Cons _ _ lvl rest => (Lvl.color lvl false = Yellow) /\ all_yellows rest is_last
    end.

  Definition well_formed {A B : Set} (stack : t A B) is_last :=
    match stack with
    | Nil _ => False
    | Cons _ _ _top_level rest => all_yellows rest is_last
    end.

  Program Definition hd {A B : Set} (stack : t A B | ~ is_nil stack) :=
    match stack with
    | Nil _ => !
    | Cons _ _ hd _ => hd
    end.

  Next Obligation.
  Proof. contradict H. rewrite <- Heq_stack; simpl ; auto. Qed.

  Theorem wf_impl_nnil :
    forall A B, forall s : t A B, forall is_last,
      well_formed s is_last -> ~ is_nil s.
  Proof. induction s ; intros is_last H ; [ contradict H | auto ]. Qed.

  Definition is_empty {A B : Set} (stack : t A B) : Prop :=
    match stack with
    | Cons _ _ lvl (Nil _) => Lvl.is_empty lvl
    | _ => False
    end.

  Program Definition empty (A : Set) :
    { s : t A (A * A) | well_formed s true /\ is_empty s } :=
    Cons (Lvl.empty A) Nil.

  Next Obligation.
  Proof. compute ; tauto. Qed.

  Theorem wf_false_impl_true :
    forall A B, forall s : t A B, well_formed s false -> well_formed s true.
  Proof.
    Lemma all_yellows_false_impl_true :
      forall A B, forall s : t A B, all_yellows s false -> all_yellows s true.
    Proof.
      intros ; induction s ; auto; simpl in * |- *.
      dependent destruction s.
      - unfold Lvl.color in *.
        destruct (Buffer.dec_is_empty (Lvl.suffix t0)).
        + contradict H; discriminate.
        + assumption.
      - intuition.
    Qed.
    intros ; destruct s.
    - contradict H ; auto.
    - simpl in *. apply all_yellows_false_impl_true ; assumption.
  Qed.
End Stack.

Module S := Stack.

Inductive deque (A : Set) : Type :=
  | Nil : deque A
  | Cons :
    forall B : Set, forall s : S.t A B, S.well_formed s false -> deque B -> deque A.

Arguments Nil [A].
Arguments Cons [A B] _ _ _.

Definition t := deque.

Notation "∅" := Nil.
Notation "x ++ y" := (Cons x _ y).

Notation "[]" := (@S.Nil _) (at level 40).
Notation "a ::: b" := (@S.Cons _ _ a b) (at level 55, right associativity).

Program Definition color {A : Set} (d : t A) : color :=
  match d with
  | ∅ => Red
  | top_stack ++ rest =>
    match rest with
    | ∅ => Lvl.color (S.hd top_stack) true
    | _ => Lvl.color (S.hd top_stack) false
    end
  end.

Next Obligation.
Proof. destruct top_stack; auto. Qed.

Next Obligation.
Proof. destruct top_stack, rest ; firstorder. Qed.

Fixpoint semi_regular {A : Set} (d : t A) : Prop :=
  match d with
  | ∅ => True
  | _ ++ stacks =>
    let green_before_red :=
      match color d with
      | Red => color stacks = Green
      | Green => True
      | Yellow => False
      end
    in
    semi_regular stacks /\ green_before_red
  end.

Definition strongly_regular {A : Set} (d : t A) : Prop :=
  match d with
  | ∅ => True
  | _ =>
    match color d with
    | Red => False
    | _ => semi_regular d
    end
  end.

Definition regular {A : Set} (d : t A) : Prop :=
  match d with
  | ∅ => True
  | top_stack ++ stacks =>
    match color d with
    | Green => semi_regular d
    | Yellow => strongly_regular stacks
    | Red =>
      match stacks with
      | ∅ => S.is_empty top_stack
      | _ => False
      end
    end
  end.

(*
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
*)

Program Definition empty (A : Set) : { d : t A | regular d } :=
  let empty_stack := ` (S.empty A) in
  empty_stack ++ ∅ .

Next Obligation.
Proof with tauto.
  compute.
  destruct (Buffer.dec_is_empty (Buffer.Zero A))...
Qed.

Program Definition regularize {A : Set} (d : t A)
  (Hsr : semi_regular d) (Color : color d = Red) : t A :=
  match d with
  | ∅ => ∅
  | (top_lvl ::: []) ++ (second_lvl ::: yellows) ++ rest
  | (top_lvl ::: second_lvl ::: yellows) ++ rest =>
    !
  | _ => !
  end.
Admit Obligations.
(* Error: Anomaly: Uncaught exception Type_errors.TypeError(_, _).
 *        Please report. *)
