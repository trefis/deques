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
    prefix  : Buffer.t A ;
    suffix  : Buffer.t A ;
    is_last : bool
  }.

  Arguments makeLvl [A] _ _ _.
  Arguments prefix [A] _.
  Arguments suffix [A] _.
  Arguments is_last [A] _.

  Definition color {A : Set} (lvl : t A) :=
    if Buffer.dec_is_empty lvl.(suffix) then
      if is_last lvl then
        Buffer.color lvl.(prefix)
      else
        Red
    else if Buffer.dec_is_empty (prefix lvl) then
      if is_last lvl then
        Buffer.color (suffix lvl)
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

  (* Y: Le texte de l'article suggérerait plutôt quelque chose comme
     cela :

  Program Definition push {A : Set} (x : A) (is_last : bool)
    (t : t A | color t is_last <> Red) :=
    makeLvl (Buffer.push x (prefix t)) (suffix t).

     Pourquoi doit-on écrire une opération de plus bas-niveau
     (au sens où elle s'attache au "buffer" et non au "level")?

   Cela laisse à penser que l'abstraction de "couleur" n'est pas
   la bonne... Peut-être qu'il serait intéressant d'introduire
   un rouge+ et un rouge-.

    T: En effet, rétrospectivement l'intérêt de cette fonction de push est bien
       limité et je ne sais plus pourquoi je l'avais fait comme ça.
       Peut-être parce que je n'avais pas envie de devoir passer [is_last] qui
       est nécessaire au calcul de la couleur du niveau.
  *)
  Program Definition push {A : Set} (x : A)
    (t : t A | color t <> Red \/ is_empty t) :=
    if Buffer.dec_is_empty (prefix t) then
      makeLvl (Buffer.push x (suffix t)) Buffer.Zero
    else
      makeLvl (Buffer.push x (prefix t)) (suffix t).

  Next Obligation.
  Proof.
    destruct t0 ; compute in H0;
    destruct (Buffer.dec_is_empty prefix0), (Buffer.dec_is_empty suffix0);
    destruct prefix0, suffix0, is_last0 ; firstorder.
  Qed.

  Next Obligation.
  Proof.
    destruct t0 ; compute in H0 |- *;
    destruct (Buffer.dec_is_empty prefix0), (Buffer.dec_is_empty suffix0);
    destruct prefix0, suffix0, is_last0 ; firstorder;
    left ; intro Color_mismatch ; discriminate Color_mismatch.
  Qed.

  Definition empty (A : Set) := makeLvl (A := A) Buffer.Zero Buffer.Zero.

  Notation "x ≥ y" := (lt_ge_dec y x) (at level 70, right associativity).

  Require Import Omega.

  Obligation Tactic := (program_simpl;
     try (
        (simpl in * |- *; apply Buffer.nonempty_length; omega)
     || (left; congruence)
     )).

  Program Definition two_buffer_case {A}
    (lvli : t A)
    (lvlSi : t (A * A))
    (Colori : color lvli = Red)
    (ColorSi : color lvlSi <> Red)
    (H : (Buffer.length (prefix lvlSi)) + (Buffer.length (suffix lvlSi)) >= 2)
  :=
    (* Y:
       Hmm, si je comprends bien le code suivant, il s'agit ici de rééquilibrer
       les éléments entre le préfixe de lvlSi et le suffixe de lvlSi de façon à 
       ce qu'aucun des deux ne soit vide.

       J'imagine que l'on suppose que lvlSi est le dernier niveau de
       la structure si l'un des deux buffers est vide, sinon je ne
       vois pas comment cette opération pourrait avoir un sens : elle
       ne préserve pas la séquence d'éléments sous-jacente représentée
       par la structure. (Cette hypothèse est confirmée par la ligne
       13, p587 de l'article.)

       Du coup, n'est-il pas nécessaire d'expliciter cet invariant? J'écrirais
       bien quelque chose comme:

       Hbis: (Buffer.length (prefix lvlSi) = 0 \/ Buffer.length (suffix lvlSi) = 0)
             -> is_last lvlSi = true
       (Si on suppose avoir rajouté le champ is_last dans la structure.)      

       mais peut-être que ce n'est pas nécessaire à la preuve...

      T: C'est ça. Je vais essayer sans cette hypothèse et si nécessaire je
         rajouterai.
    *)
    let pairSi
    : { p : Buffer.t (A * A) | Buffer.color p <> Red }
      * 
      { p : Buffer.t (A * A) | Buffer.color p <> Red }
(*
    : { b : Buffer.t (A * A) * Buffer.t (A * A) 
      | Buffer.color (fst b) <> Red /\ Buffer.color (snd b) <> Red }
*)
    :=
      match Buffer.dec_is_empty (prefix lvlSi), Buffer.dec_is_empty (suffix lvlSi) with
      | left _, left _ => 
          (* By H. *)
          !
      | left _, right _ =>
          (* We have at least two elements in the suffix: 
             we push the first of theses elements in the prefix. *)
          let (p, Hp) := Buffer.pop (suffix lvlSi) in
          let '(elt, buff) := p in
          pair (Buffer.One elt) buff
      | right _, left _ =>
          (* Symmetric case. *)
          let (p, Hp) := Buffer.eject (prefix lvlSi) in
          let '(elt, buff) := p in
          pair buff (Buffer.One elt)
      | right _, right _ => 
          (* None of the two buffers is empty. *)
          (prefix lvlSi, suffix lvlSi)
      end
    in
    let (pSi, sSi) := pairSi in
    let pairP : Buffer.t A * Buffer.t (A * A) :=
      match Buffer.length (prefix lvli) ≥ 4 with 
      | left _ =>
        let (p, Hp) := Buffer.eject (prefix lvli) in
        let '(elt1, buff1) := p in
        let (p, Hp) := Buffer.eject buff1 in
        let '(elt2, buff2) := p in
        (buff2, Buffer.push (elt2, elt1) pSi)
      | right _ =>
        match 1 ≥ Buffer.length (prefix lvli) with
        | left _ =>
          let '(p, pSi) := Buffer.pop pSi in
          let '(elt1, elt2) := p in
          let (buff, Hbuff) := Buffer.inject elt1 (prefix lvli) in
          (Buffer.inject elt2 buff, pSi)
        | right _ =>
          (prefix lvli, pSi)
        end
      end
    in
    let pairS : Buffer.t A * Buffer.t (A * A) :=
(*      let '(too_many, H_s4) := (Buffer.length (suffix lvli)) ≥ 4 in
      let '(too_few, H_s1) := 1 ≥ (Buffer.length (suffix lvli)) in *)
      match (Buffer.length (suffix lvli)) ≥ 4 with
      | left H =>
          let (p, Hp) := Buffer.pop (suffix lvli) in
          let '(elt1, buff) :=  p in
          let (p, H) := Buffer.pop buff in
          let '(elt2, buff) := p in
         (buff, Buffer.inject (elt1, elt2) sSi)
      | right _ =>
        match 1 ≥ (Buffer.length (suffix lvli)) with
        | left _ =>
          let '(p, sSi) := Buffer.eject sSi in
          let '(elt1, elt2) := p in
          let (buff, Hbuff) := Buffer.push elt2 (suffix lvli) in
          (Buffer.push elt1 buff, sSi)
        | right _ =>
          (suffix lvli, sSi)
        end
      end
    in
    let (pi, pSi) := pairP in
    let (si, sSi) := pairS in
    (makeLvl pi si (is_last lvli), makeLvl pSi sSi (is_last lvlSi)).

  Next Obligation.
  Proof.
    assert (Buffer.length (prefix lvlSi) = 0) by (apply Buffer.empty_length; auto).
    assert (Buffer.length (suffix lvlSi) = 0) by (apply Buffer.empty_length; auto).
    omega.
  Qed.

  Next Obligation. 
  Proof. 
    simpl in * |- * .
    assert (Hs: Buffer.length (prefix lvlSi) = 0) by (apply Buffer.empty_length; auto).
    rewrite Hs in H; simpl in H.
    assert (Buffer.length (suffix lvlSi) <= 5) by (apply Buffer.bounded_length).    
    destruct t0 ; simpl in * |- *; firstorder; discriminate.
  Qed.    

  Next Obligation.
  Proof.
    simpl in * |- *. 
    assert (Hs: Buffer.length (suffix lvlSi) = 0) by (apply Buffer.empty_length; auto).
    rewrite Hs in H; simpl in H.
    assert (Buffer.length (prefix lvlSi) <= 5) by (apply Buffer.bounded_length).    
    destruct t0 ; simpl in * |- *; firstorder; discriminate.
  Qed.    

  Next Obligation.
  Proof. (* A bit crude, I'll admit. *)
    destruct lvlSi; compute in ColorSi; compute ;
    destruct (Buffer.dec_is_empty prefix0), (Buffer.dec_is_empty suffix0);
    destruct prefix0, suffix0, is_last0; firstorder;
    discriminate H0.
  Qed.

  Next Obligation.
  Proof.
    destruct lvlSi; compute in ColorSi; compute ;
    destruct (Buffer.dec_is_empty prefix0), (Buffer.dec_is_empty suffix0);
    destruct prefix0, suffix0, is_last0; firstorder;
    discriminate H0.
  Qed.

  Next Obligation.
  Proof. destruct pSi ; firstorder. Qed.

  Next Obligation.
  Proof.
    destruct lvli; destruct prefix0; compute; firstorder;
    left ; intro Color_mismatch ; contradict Color_mismatch ; discriminate.
  Qed.

  Next Obligation.
  Proof.
    left.
    assert (Hp: Buffer.length (prefix lvli) = 0) by omega.
    rewrite Hp in Hbuff.
    destruct buff ; simpl in * ; firstorder; discriminate.
  Qed.

  Next Obligation.
  Proof. destruct sSi ; firstorder. Qed.

  Next Obligation.
  Proof.
    destruct lvli; destruct suffix0; compute; firstorder;
    left ; intro Color_mismatch ; contradict Color_mismatch ; discriminate.
  Qed.

  Next Obligation.
  Proof.
    left ; assert (Hs: Buffer.length (suffix lvli) = 0) by omega.
    rewrite Hs in Hbuff.
    destruct buff ; simpl in * ; firstorder; discriminate.
  Qed.

  (* A note on the hypotheses :
   *   [ColorSi] assert that [lvlSi] might be empty. If that is the case, it
   *   means that we just created it, implying that [lvli] was the bottom-most
   *   level, and the conjunction of [Colori] and [Hi] tells us that one of its
   *   buffers is full. *)
  Program Definition one_buffer_case {A}
    (lvli : t A)
    (lvlSi : t (A * A))
    (Colori : color lvli = Red)
    (ColorSi : color lvlSi <> Red \/ is_empty lvlSi)
    (HSi : (Buffer.length (prefix lvlSi)) + (Buffer.length (suffix lvlSi)) <= 1)
    (Hi : Buffer.length (prefix lvli) >= 2 \/ Buffer.length (suffix lvli) >= 2)
    (LastLvl : is_empty lvlSi -> is_last lvli = true)
  :=
    let pSi_sig :
      { b : Buffer.t (A * A) |
        Buffer.length b <= 1 /\ (Buffer.length b = 0 -> is_last lvli = true) }:=
      match Buffer.length (suffix lvlSi) as len_suff with
      | 0 => prefix lvlSi
      | 1 => suffix lvlSi
      | _ => ! (* by HSi *)
      end
    in
    let (pSi, HpSi) := pSi_sig in
    let pairP :
      { b : Buffer.t A | Buffer.color b <> Red \/ Buffer.is_empty b } *
      { b : Buffer.t (A * A) |
        if Buffer.length (prefix lvli) ≥ 4
          then 0 < Buffer.length b <= 2
          else Buffer.length b <= 1 /\ (Buffer.length b = 0 -> is_last lvli = true)
      } :=
      match Buffer.length (prefix lvli) ≥ 4 with 
      | left _ =>
        let (p, Hp) := Buffer.eject (prefix lvli) in
        let '(elt1, buff1) := p in
        let (p, Hp) := Buffer.eject buff1 in
        let '(elt2, buff2) := p in
        let (pSi_internal, HpSi_internal) := Buffer.push (elt2, elt1) pSi in
        (buff2, pSi_internal)
      | right _ =>
        (* [prefix lvli] might contain less than two element, we want to pop
         * from [pSi], but at that point it might still be empty. We need to
         * push elements from [suffix lvli] (which by hypothesis contains more
         * than 2 element) into it before we can replenish the prefix. *)
        (prefix lvli, pSi)
      end
    in
    let (pi, pSi) := pairP in
    let pairSP : Buffer.t A *
      { b : Buffer.t (A * A) |
        if Buffer.length (suffix lvli) ≥ 4
          then 0 < Buffer.length b <= 3
          else Buffer.length b <= 2
               /\ (Buffer.length b = 0 ->
                    Buffer.length (suffix lvli) <= 1 \/ is_last lvli = true)
      } :=
      match (Buffer.length (suffix lvli)) ≥ 4 with
      | left H =>
          let (p, Hp) := Buffer.pop (suffix lvli) in
          let '(elt1, buff) :=  p in
          let (p, H) := Buffer.pop buff in
          let '(elt2, buff) := p in
         (buff, Buffer.inject (elt1, elt2) pSi)
      | right _ =>
        match 1 ≥ (Buffer.length (suffix lvli)) with
        | left _ =>
          let (p, Hp) := Buffer.eject pSi in
          let '((elt1, elt2), pSi) := p in
          let (buff, Hbuff) := Buffer.push elt2 (suffix lvli) in
          (Buffer.push elt1 buff, pSi)
        | right _ =>
          (suffix lvli, pSi)
        end
      end
    in
    let (si, pSi) := pairSP in
    let pairP2 : Buffer.t A * Buffer.t (A * A) :=
      match 1 ≥ (Buffer.length (prefix lvli)) with
      | left _ =>
        let (p, Hp) := Buffer.pop pSi in
        let '((elt1, elt2), pSi) := p in
        let (buff, Hbuff) := Buffer.inject elt1 pi in
        (Buffer.inject elt2 buff, pSi)
      | right _ =>
        (pi, pSi)
      end
    in
    let (pi, pSi) := pairP2 in
    (makeLvl pi si false, makeLvl pSi Buffer.Zero true).

  Next Obligation.
  Proof.
    split.
    - omega.
    - intro H ; apply LastLvl.
      destruct lvlSi ; destruct prefix0, suffix0 ; simpl in *; firstorder.
  Qed.

  Next Obligation.
  Proof. split ; omega. Qed.

  Next Obligation.
  Proof. omega. Qed.

  Next Obligation.
  Proof.
    simpl in *.
    destruct pSi ; simpl in * ; firstorder ; left ; discriminate.
  Qed.

  Next Obligation.
  Proof.
    left ; simpl in *.
    destruct (prefix lvli) ; compute in wildcard' ; try (exfalso ; omega).
    destruct t1, t0 ; compute in Hp ; compute in Hp0 ; compute ; intro C ;
    try discriminate Hp0 ; try discriminate Hp ; try discriminate C.
  Qed.

  Next Obligation.
  Proof. omega. Qed.

  Next Obligation.
  Proof.
    destruct (prefix lvli) ; simpl in wildcard' ; compute ; solve [
      (right ; trivial) |
      (left ; intro F ; discriminate F) |
      (exfalso ; omega)
    ].
  Qed.

  Next Obligation.
  Proof.
    destruct pSi0 ; simpl in * ; firstorder ; solve [
      (left ; discriminate) |
      (destruct (Buffer.length (prefix lvli) ≥ 4) ; omega)
    ].
  Qed.

  Next Obligation.
  Proof.
    simpl in *.
    destruct pSi0 ; compute ; try omega ; exfalso;
    destruct (Buffer.length (prefix lvli) ≥ 4) ; compute in H1 ; omega.
  Qed.

  Next Obligation.
  Proof.
    apply Buffer.nonempty_length.
    destruct (Buffer.length (prefix lvli) ≥ 4).
    - omega.
    - destruct H1; inversion H1.
      + omega.
      + inversion H5.
        apply H3 in H7.
        assert (EmptySuff : Buffer.length (suffix lvli) = 0) by omega.
        apply Buffer.empty_length in EmptySuff.
        contradict Colori.
        destruct lvli.
        compute.
        destruct (Buffer.dec_is_empty suffix0).
        * simpl in *.
          rewrite H7 ; simpl.
          destruct prefix0, suffix0 ; intro ; simpl in * ; firstorder ;
          discriminate H6.
        * simpl in *.
          contradiction.
  Qed. (* TODO: clean up *)

  Next Obligation.
  Proof.
    inversion wildcard'0.
    + right ; apply Buffer.empty_length ; assumption.
    + omega.
  Qed.

  Next Obligation.
  Proof.
    assert (HL : Buffer.length (suffix lvli) = 0) by omega.
    rewrite HL in Hbuff ; left.
    destruct buff ; simpl in Hbuff ; firstorder ; discriminate.
  Qed.

  Next Obligation.
  Proof. 
    simpl in * ; split; destruct (Buffer.length (prefix lvli) ≥ 4) ;
    try left ; omega.
  Qed.

  Next Obligation.
  Proof.
    simpl in * ; split; destruct (Buffer.length (prefix lvli) ≥ 4) ; try omega.
    intro HLpSi0 ; right.
    destruct H1.
    apply H3 ; apply HLpSi0.
  Qed.

  Next Obligation.
  Proof.
    apply Buffer.nonempty_length.
    destruct (Buffer.length (suffix lvli) ≥ 4) ; try omega.
    destruct H1.
    destruct (Buffer.length pSi1).
    - assert (trivial : 0 = 0) by omega.
      apply H4 in trivial.
      destruct trivial.
      + exfalso ; omega.
      + assert (EmptyPre : Buffer.length (prefix lvli) = 0) by omega.
        apply Buffer.empty_length in EmptyPre.
        contradict Colori.
        destruct lvli ; compute; destruct (Buffer.dec_is_empty suffix0);
        destruct (Buffer.dec_is_empty prefix0); simpl in *; try rewrite H5;
        destruct prefix0, suffix0 ; intro ; simpl in * ; firstorder ; discriminate H6.
    - auto with arith.
  Qed.

  Next Obligation.
  Proof.
    (* TODO:
     *   Change H3 from
     *       [Buffer.color pi <> Red \/ Buffer.is_empty pi]
     *   to:
     *       [Buffer.length pi < 4]
     *)
  Admitted.

  Program Definition equilibrate {A : Set} (lvli : t A) (lvlSi : t (A * A))
    (Colori : color lvli = Red) (ColorSi : color lvlSi <> Red) :
    (t A * t (A * A)) :=
    match Buffer.length (prefix lvlSi) + Buffer.length (suffix lvlSi) ≥ 2 with
    | left H => two_buffer_case lvli lvlSi Colori ColorSi _
    | right _ => (lvli, lvlSi) (* TODO *)
    end.

  Next Obligation.
  Proof.  omega. Qed.

End Lvl.

Module Stack.
  Inductive t : Set -> Set -> Type :=
    | Nil  : forall A, t A A
    | Cons : forall A B, Lvl.t A -> t (A * A) B -> t A B.

  Arguments Nil [A].
  Arguments Cons [A] [B] _ _.

  Definition is_nil {A B : Set} (stack : t A B) : Prop :=
    match stack with
    | Nil => True
    | _ => False
    end.

  Fixpoint all_yellows {A B : Set} (s : t A B) is_last : Prop :=
    match s with
    | Nil => True
    | Cons lvl Nil => Lvl.color lvl is_last = Yellow
    | Cons lvl rest => (Lvl.color lvl false = Yellow) /\ all_yellows rest is_last
    end.

  Definition well_formed {A B : Set} (stack : t A B) is_last :=
    match stack with
    | Nil => False
    | Cons _top_level rest => all_yellows rest is_last
    end.

  Program Definition hd {A B : Set} (stack : t A B | ~ is_nil stack) :=
    match stack with
    | Nil => !
    | Cons hd _ => hd
    end.

  Next Obligation.
  Proof. contradict H. rewrite <- Heq_stack; simpl ; auto. Qed.

  Theorem wf_impl_nnil :
    forall A B, forall s : t A B, forall is_last,
      well_formed s is_last -> ~ is_nil s.
  Proof. induction s ; intros is_last H ; [ contradict H | auto ]. Qed.

  Definition is_empty {A B : Set} (stack : t A B) : Prop :=
    match stack with
    | Cons lvl Nil => Lvl.is_empty lvl
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
  destruct (Buffer.dec_is_empty (Buffer.Zero (A:=A)))...
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
