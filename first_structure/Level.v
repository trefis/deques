Require Import Program.
Require Import Coq.Arith.Bool_nat.

Require Import Misc.
Require Buffer.

Record t (A : Set) : Set := makeLvl {
  prefix  : Buffer.t A ;
  suffix  : Buffer.t A
}.

Arguments makeLvl [A] _ _ .
Arguments prefix [A] _.
Arguments suffix [A] _.

Definition color {A : Set} (lvl : t A) (is_last : bool) :=
  if Buffer.dec_is_empty lvl.(suffix) then
    if is_last then
      Buffer.color lvl.(prefix)
    else
      Red
  else if Buffer.dec_is_empty (prefix lvl) then
    if is_last then
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

Program Definition push {A : Set} (x : A) (t : t A) (is_last : bool)
  (proof : color t is_last <> Red \/ is_empty t) :=
  if Buffer.dec_is_empty (prefix t) then
    makeLvl (Buffer.push x (suffix t)) Buffer.Zero
  else
    makeLvl (Buffer.push x (prefix t)) (suffix t).

Next Obligation.
Proof.
  destruct t0 ; compute in proof;
  destruct (Buffer.dec_is_empty prefix0), (Buffer.dec_is_empty suffix0);
  destruct prefix0, suffix0, is_last ; firstorder.
Qed.

Next Obligation.
Proof.
  destruct t0 ; compute in proof |- *;
  destruct (Buffer.dec_is_empty prefix0), (Buffer.dec_is_empty suffix0);
  destruct prefix0, suffix0, is_last ; firstorder;
  left ; intro Color_mismatch ; discriminate Color_mismatch.
Qed.

Theorem red_push_iff_yellow :
  forall A x is_last, forall t : t A,
  forall p : color t is_last <> Red \/ is_empty t,
    color (push x t is_last p) is_last = Red -> color t is_last <> Green.
Proof.
  intros.
  destruct t0, is_last ; destruct prefix0, suffix0 ; compute in * ;
  firstorder ; solve [
    discriminate H | discriminate H0 |
    (clear H ; destruct p as [ H1 | H1 ]  ; exfalso ; [ 
      (apply H1 ; reflexivity) | (destruct H1 ; assumption)
    ])
  ].
Qed.

Definition empty (A : Set) := makeLvl (A := A) Buffer.Zero Buffer.Zero.

Notation "x ≥ y" := (ge_dec x y) (at level 70, right associativity).

Require Import Omega.

Obligation Tactic := (program_simpl;
    try (
      (simpl in * |- *; apply Buffer.nonempty_length; omega)
    || (left; congruence)
    || (try split ; omega)
    )).

Program Definition two_buffer_case {A}
  (lvli : t A)
  (lvlSi : t (A * A))
  (Colori : color lvli false = Red)
  (last_Si : bool)
  (ColorSi : color lvlSi last_Si<> Red)
  (H : (Buffer.length (prefix lvlSi)) + (Buffer.length (suffix lvlSi)) >= 2)
  : { li  : t A | color li false = Green } *
    { lSi : t (A * A)
        | (color lSi last_Si= Red -> color lvlSi last_Si<> Green \/ last_Si = true)
    }
:=
  
  let pairSi
  : { p : Buffer.t (A * A) |
      Buffer.color p <> Red /\
      (Buffer.color p <> Green -> color lvlSi last_Si <> Green \/ last_Si = true)
    } * 
    { s : Buffer.t (A * A) |
      Buffer.color s <> Red /\
      (Buffer.color s <> Green -> color lvlSi last_Si <> Green \/ last_Si = true)
    }
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
  let pairP :
    { b : Buffer.t A | Buffer.color b = Green } *
    { b : Buffer.t (A * A)
        | Buffer.color b = Red -> color lvlSi last_Si <> Green \/ last_Si = true }
  :=
    match Buffer.length (prefix lvli) ≥ 4 with 
    | left _ =>
      let (p, Hp) := Buffer.eject (prefix lvli) in
      let '(elt1, buff1) := p in
      let (p, Hp) := Buffer.eject buff1 in
      let '(elt2, buff2) := p in
      let (buff3, Hlol) := Buffer.push (elt2, elt1) pSi in
      (buff2, buff3)
    | right _ =>
      match 1 ≥ Buffer.length (prefix lvli) with
      | left _ =>
        let (pair, HpSi) := Buffer.pop pSi in
        let '(p, pSi) := pair in
        let '(elt1, elt2) := p in
        let (buff, Hbuff) := Buffer.inject elt1 (prefix lvli) in
        let (buff2, Hbuff2) := Buffer.inject elt2 buff in
        (buff2, pSi)
      | right _ =>
        (prefix lvli, pSi)
      end
    end
  in
  let pairS :
    { b : Buffer.t A | Buffer.color b = Green } *
    { b : Buffer.t (A * A)
        | Buffer.color b = Red -> color lvlSi last_Si <> Green \/ last_Si = true }
  :=
    match (Buffer.length (suffix lvli)) ≥ 4 with
    | left H =>
      let (p, Hp) := Buffer.pop (suffix lvli) in
      let '(elt1, buff) :=  p in
      let (p, H) := Buffer.pop buff in
      let '(elt2, buff) := p in
      let (buff2, Hlol) := Buffer.inject (elt1, elt2) sSi in
      (buff, buff2)
    | right _ =>
      match 1 ≥ (Buffer.length (suffix lvli)) with
      | left _ =>
        let (pair, HsSi) := Buffer.eject sSi in
        let '(p, sSi) := pair in
        let '(elt1, elt2) := p in
        let (buff, Hbuff) := Buffer.push elt2 (suffix lvli) in
        let (buff2, Hbuff2) := Buffer.push elt1 buff in
        (buff2, sSi)
      | right _ =>
        (suffix lvli, sSi)
      end
    end
  in
  let (pi, pSi) := pairP in
  let (si, sSi) := pairS in
  (makeLvl pi si, makeLvl pSi sSi).

Next Obligation.
Proof.
  assert (Buffer.length (prefix lvlSi) = 0) by (apply Buffer.empty_length; auto).
  assert (Buffer.length (suffix lvlSi) = 0) by (apply Buffer.empty_length; auto).
  omega.
Qed.

Next Obligation. 
Proof. 
  split ; [ discriminate | intro ].
  assert (Hs: Buffer.length (prefix lvlSi) = 0) by (apply Buffer.empty_length; auto).
  rewrite Hs in H; simpl in H.
  assert (Buffer.length (suffix lvlSi) <= 5) by (apply Buffer.bounded_length).    
  destruct lvlSi; destruct prefix0, suffix0, last_Si; simpl in * ; try solve [
    omega |
    contradiction |
    (right ;reflexivity) |
    (left ; compute ; discriminate) |
    (compute in ColorSi ; discriminate ColorSi)
  ].
Qed.

Next Obligation.
Proof.
  simpl in *.
  assert (Hs: Buffer.length (prefix lvlSi) = 0) by (apply Buffer.empty_length; auto).
  rewrite Hs in H; simpl in H.
  assert (Buffer.length (suffix lvlSi) <= 5) by (apply Buffer.bounded_length).    
  split.
  - destruct t0 ; simpl in * ; discriminate || omega.
  - intro.
    destruct lvlSi ; destruct prefix0, suffix0, last_Si ; simpl in * ;
    solve [
      omega | (right ; reflexivity) | (left ; compute ; discriminate)
    ].
Qed.

Next Obligation.
Proof.
  simpl in *.
  assert (Hs: Buffer.length (suffix lvlSi) = 0) by (apply Buffer.empty_length; auto).
  rewrite Hs in H; simpl in H.
  assert (Buffer.length (prefix lvlSi) <= 5) by (apply Buffer.bounded_length).    
  split.
  - destruct t0 ; simpl in * ; discriminate || omega.
  - intro.
    destruct lvlSi ; destruct prefix0, suffix0, last_Si ; simpl in * ;
    solve [
      omega | (right ; reflexivity) | (left ; compute ; discriminate)
    ].
Qed.

Next Obligation.
Proof.
  simpl in *.
  split ; [ discriminate | intro ].
  assert (Hs: Buffer.length (suffix lvlSi) = 0) by (apply Buffer.empty_length; auto).
  rewrite Hs in H; simpl in H.
  assert (Buffer.length (prefix lvlSi) <= 5) by (apply Buffer.bounded_length).    
  destruct lvlSi ; destruct prefix0, suffix0, last_Si ; simpl in * ; solve [
    omega |
    (right ; reflexivity) |
    (left ; compute ; discriminate)
  ].
Qed.

Next Obligation.
Proof.
  destruct lvlSi; compute in ColorSi |- * .
  destruct prefix0, suffix0, last_Si ; simpl in * ; solve [
    auto with arith |
    (split ; [ idtac | intro ; left ] ; intro F ; discriminate F)
  ].
Qed.

Next Obligation.
Proof.
  destruct lvlSi; compute in ColorSi |- * ;
  destruct prefix0, suffix0, last_Si ; simpl in * ; solve [
    auto with arith |
    (split ; [ idtac | intro ; left ] ; intro F ; discriminate F)
  ].
Qed.

Next Obligation.
Proof.
  simpl in *.
  assert (Hmax : Buffer.length (prefix lvli) <= 5) by apply Buffer.bounded_length.
  destruct (Buffer.length (prefix lvli)) ; try omega.
  destruct t0 ; simpl in Hp0 ; try omega ; simpl ; reflexivity.
Qed.

Next Obligation.
Proof.
  simpl in * ; apply o.
  destruct buff3 ; simpl in * ; first [ omega | discriminate H0 | idtac ].
  destruct pSi ; simpl in * ; omega || discriminate.
Qed.

Next Obligation.
Proof.
  destruct pSi ; simpl in n ; solve [
    (contradict n ; reflexivity) |
    (compute ; trivial)
  ].
Qed.

Next Obligation.
Proof.
  destruct lvli; destruct prefix0; simpl ; solve [
    (right ; trivial) |
    (left ; discriminate)
  ].
Qed.

Next Obligation.
Proof.
  simpl in * ; left.
  destruct (Buffer.length (prefix lvli)).
  + destruct buff ; simpl in Hbuff ; discriminate || discriminate Hbuff.
  + assert (Hn : n0 = 0) by omega.
    destruct buff ; simpl in Hbuff ; discriminate || (exfalso ; omega).
Qed.

Next Obligation.
Proof.
  simpl in *.
  destruct (Buffer.length (prefix lvli)) ; try omega ;
  rewrite Hbuff in Hbuff2 ;
  destruct buff2 ; simpl in * ; try omega ; reflexivity.
Qed.

Next Obligation.
Proof.
  simpl in *; apply o.
  destruct pSi, t0 ; simpl in * ; omega || discriminate.
Qed.

Next Obligation.
Proof.
  destruct (prefix lvli) ; simpl in * ; solve [ omega | reflexivity ].
Qed.

Next Obligation.
Proof.
  simpl in *.
  assert (Hmax : Buffer.length (suffix lvli) <= 5) by apply Buffer.bounded_length.
  destruct (Buffer.length (suffix lvli)) ; try omega.
  destruct t0 ; simpl in H1 ; try omega ; simpl ; reflexivity.
Qed.

Next Obligation.
Proof.
  simpl in * ; apply o.
  destruct sSi, buff2 ; simpl in * ; omega || discriminate.
Qed.

Next Obligation.
Proof.
  destruct sSi ; simpl in * ; solve [ (contradict n ; reflexivity) | auto ].
Qed.

Next Obligation.
Proof.
  destruct (suffix lvli) ; simpl in * ; solve [
    omega |
    (left ; discriminate) |
    (right ; trivial)
  ].
Qed.

Next Obligation.
Proof.
  left ; simpl in *.
  destruct (Buffer.length (suffix lvli)), buff ; simpl in * ; omega || discriminate.
Qed.

Next Obligation.
Proof.
  simpl in *.
  destruct (Buffer.length (prefix lvli)) ; try omega ;
  rewrite Hbuff in Hbuff2 ;
  destruct buff2 ; simpl in * ; try omega ; reflexivity.
Qed.

Next Obligation.
Proof.
  simpl in * ; apply o.
  destruct t0, sSi ; simpl in * ; try (omega || discriminate H0).
  discriminate.
Qed.

Next Obligation.
Proof.
  destruct (suffix lvli) ; simpl in * ; solve [ omega | reflexivity ].
Qed.

Next Obligation.
Proof.
  destruct pi, si ; simpl in H1, H3 ; first [
    discriminate H3 | discriminate H1 | idtac
  ] ; simpl ; reflexivity.
Qed.

Next Obligation.
Proof.
  destruct pSi0, sSi0 ; simpl in * ; try solve [
    (compute in H0 ; discriminate H0) |
    (apply H1 ; reflexivity) |
    (apply H3 ; reflexivity)
  ].
Qed.

(* A note on the hypotheses :
  *   [ColorSi] assert that [lvlSi] might be empty. If that is the case, it
  *   means that we just created it, implying that [lvli] was the bottom-most
  *   level, and the conjunction of [Colori] and [Hi] tells us that one of its
  *   buffers is full. *)
Program Definition one_buffer_case {A}
  (lvli : t A)
  (lvlSi : t (A * A))
  (is_lasti is_lastSi : bool)
  (Colori : color lvli is_lasti = Red)
  (ColorSi : color lvlSi is_lastSi <> Red \/ is_empty lvlSi)
  (HSi : (Buffer.length (prefix lvlSi)) + (Buffer.length (suffix lvlSi)) <= 1)
  (Hi : Buffer.length (prefix lvli) >= 2 \/ Buffer.length (suffix lvli) >= 2)
  (LastLvl : is_empty lvlSi -> is_lasti = true)
  (Triviality : is_lasti = true -> is_lastSi = true)
: { l : t A | color l false = Green } * t (A * A)
:=
  let pSi_sig :
    { b : Buffer.t (A * A) |
      Buffer.length b <= 1 /\ (Buffer.length b = 0 -> is_lasti = true) }:=
    match Buffer.length (suffix lvlSi) as len_suff with
    | 0 => prefix lvlSi
    | 1 => suffix lvlSi
    | _ => ! (* by HSi *)
    end
  in
  let (pSi, HpSi) := pSi_sig in
  let pairP :
    { b : Buffer.t A |
      if Buffer.length (prefix lvli) ≥ 4
        then 1 < Buffer.length b <= 3
        else b = prefix lvli
    } *
    { b : Buffer.t (A * A) |
      if Buffer.length (prefix lvli) ≥ 4
        then 0 < Buffer.length b <= 2
        else Buffer.length b <= 1 /\ (Buffer.length b = 0 -> is_lasti = true)
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
  let pairSP : { b : Buffer.t A | Buffer.color b = Green } *
    { b : Buffer.t (A * A) |
      if Buffer.length (suffix lvli) ≥ 4
        then 0 < Buffer.length b <= 3
        else Buffer.length b <= 2
              /\ (Buffer.length b = 0 ->
                  Buffer.length (suffix lvli) <= 1 \/ is_lasti = true)
    } :=
    match (Buffer.length (suffix lvli)) ≥ 4 with
    | left H =>
      let (p, Hp) := Buffer.pop (suffix lvli) in
      let '(elt1, buff) :=  p in
      let (p, H) := Buffer.pop buff in
      let '(elt2, buff) := p in
      let (buff2, Hbuff2) := Buffer.inject (elt1, elt2) pSi in
      (buff, buff2)
    | right _ =>
      match 1 ≥ (Buffer.length (suffix lvli)) with
      | left _ =>
        let (p, Hp) := Buffer.eject pSi in
        let '((elt1, elt2), pSi) := p in
        let (buff, Hbuff) := Buffer.push elt2 (suffix lvli) in
        let (buff2, Hbuff2) := Buffer.push elt1 buff in
        (buff2, pSi)
      | right _ =>
        (suffix lvli, pSi)
      end
    end
  in
  let (si, pSi) := pairSP in
  let pairP2 : { b : Buffer.t A | Buffer.color b = Green }  * Buffer.t (A * A) :=
    match 1 ≥ Buffer.length (prefix lvli) with
    | left _ =>
      let (p, Hp) := Buffer.pop pSi in
      let '((elt1, elt2), pSi) := p in
      let (buff, Hbuff) := Buffer.inject elt1 (prefix lvli) in
      let (buff2, Hbuff2) := Buffer.inject elt2 buff in
      (buff2, pSi)
    | right _ =>
      (pi, pSi)
    end
  in
  let (pi, pSi) := pairP2 in
  (makeLvl pi si, makeLvl pSi Buffer.Zero).

Next Obligation.
Proof.
  split.
  - omega.
  - intro H ; apply LastLvl.
    destruct lvlSi ; destruct prefix0, suffix0 ; simpl in *; firstorder.
Qed.

Next Obligation.
Proof.
  simpl in * ;
  destruct pSi ; simpl in * ; try solve [
    (right ; trivial) |
    (left ; discriminate)
  ] ;
  omega.
Qed.

Next Obligation.
Proof.
  simpl in *.
  assert (HB: Buffer.length (prefix lvli) <= 5) by apply Buffer.bounded_length.
  destruct (Buffer.length (prefix lvli)) ; omega.
Qed.

Next Obligation.
Proof.
  destruct pSi0 ; simpl in * ; try solve [ (left ; discriminate) ] ; [
    (right ; trivial) |
    (destruct (Buffer.length (prefix lvli) ≥ 4) ; omega)
  ].
Qed.

Next Obligation.
Proof.
  simpl in *.
  assert (Hmax : Buffer.length (suffix lvli) <= 5) by apply Buffer.bounded_length.
  destruct (Buffer.length (suffix lvli)) ; try omega.
  injection Hp ; intro Hn ; rewrite Hn in H0 ; subst.
  destruct t0 ; simpl in * ; try omega ; reflexivity.
Qed.

Next Obligation.
Proof.
  simpl in *.
  destruct (Buffer.length (prefix lvli) ≥ 4) ; simpl in * ; omega.
Qed.

Next Obligation.
Proof.
  apply Buffer.nonempty_length.
  destruct (Buffer.length (prefix lvli) ≥ 4) ; try omega.
  destruct H1; inversion H1; try omega.
  exfalso ; inversion H5.
  apply H3 in H7.
  destruct (Buffer.length (suffix lvli)) eqn:HLsi; try omega;
  contradict Colori.
  - destruct lvli; compute; simpl in *.
    rewrite H7 ; simpl.
    destruct prefix0, suffix0 ; intro ; simpl in * ; solve [
      discriminate H6 | omega
    ].
  - assert (trivial : n0 = 0) by omega; subst.
    destruct lvli; compute; simpl in *.
    destruct prefix0, suffix0 ; intro ; simpl in * ; auto ;
    try discriminate H2 ; omega.
Qed. (* TODO: clean up *)

Next Obligation.
Proof.
  inversion wildcard'0.
  + left ; destruct (suffix lvli) ; simpl in H4 ; solve [
      discriminate H4 |
      (compute ; discriminate)
    ].
  + right ; apply Buffer.empty_length ; auto with arith.
Qed.

Next Obligation.
Proof.
  destruct (Buffer.length (suffix lvli));
    [ idtac | (assert (n = 0) by omega ; subst) ] ;
  left; destruct buff ; simpl in Hbuff ; discriminate || discriminate Hbuff.
Qed.

Next Obligation.
Proof. 
  simpl in *.
  destruct (Buffer.length (suffix lvli)) ; try omega ;
  destruct buff2 ; simpl in * ; try omega ; reflexivity.
Qed.

Next Obligation.
Proof. 
  simpl in * ; split; destruct (Buffer.length (prefix lvli) ≥ 4) ;
  try left ; omega.
Qed.

Next Obligation.
Proof.
  simpl in *.
  destruct (suffix lvli) ; simpl in * ; solve [ omega | reflexivity ].
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
    apply H5 in trivial.
    destruct trivial.
    + exfalso ; omega.
    + contradict Colori.
      destruct lvli ; compute; simpl in *; try rewrite H6;
      destruct prefix0, suffix0 ; intro ; simpl in * ; omega || discriminate H7.
  - auto with arith.
Qed.

Next Obligation.
Proof.
  destruct (prefix lvli) ; simpl in wildcard' ; solve [
    (left ; compute ; discriminate) |
    (right; simpl ; trivial) |
    omega
  ].
Qed.

Next Obligation.
Proof.
  left; destruct (Buffer.length pi); destruct buff ; solve [
    (simpl in Hbuff ; omega) |
    (compute ; intro C ; discriminate C)
  ].
Qed.

Next Obligation.
Proof.
  destruct (prefix lvli) ; simpl in * ; try omega ;
  rewrite Hbuff in Hbuff2 ; destruct buff2 ; simpl in * ; solve [
    omega | reflexivity
  ].
Qed.

Next Obligation.
Proof.
  destruct (Buffer.length (prefix lvli) ≥ 4).
  + destruct pi ; simpl in H4 |- *; solve [ omega | reflexivity ].
  + subst. destruct (prefix lvli) ; simpl in * ; solve [ omega | reflexivity ].
Qed.

Next Obligation.
Proof.
  destruct pi0, si; simpl in H1, H3 ; first [
    discriminate H1 | discriminate H3 | idtac
  ] ; simpl ; reflexivity.
Qed.

Program Definition no_buffer_case {A : Set}
  (lvli : t A)
  (lvlSi : t (A * A))
  (Colori : color lvli false = Red)
  (ColorSi : color lvlSi true <> Red)
  (Hi : Buffer.length (prefix lvli) <= 1 /\ Buffer.length (suffix lvli) <= 1)
  (HSi : (Buffer.length (prefix lvlSi)) + (Buffer.length (suffix lvlSi)) <= 1)
: { b : t A | color b true = Green }
:=
  let pi_sig : {
      b : Buffer.t A | Buffer.length b = 2 + Buffer.length (prefix lvli)
    }
  :=
    match Buffer.length (prefix lvlSi), Buffer.length (suffix lvlSi) with
    | 1, 0 =>
      let (pair, _) := Buffer.pop (prefix lvlSi) in
      let '((elt1, elt2), _) := pair in
      let (tmpi, _) := Buffer.inject elt1 (prefix lvli) in
      let (pi, _) := Buffer.inject elt2 tmpi in
      pi
    | 0, 1 =>
      let (pair, _) := Buffer.pop (suffix lvlSi) in
      let '((elt1, elt2), _) := pair in
      let (tmpi, _) := Buffer.inject elt1 (prefix lvli) in
      let (pi, _) := Buffer.inject elt2 tmpi in
      pi
    | _, _ => ! (* by HSi *)
    end
  in
  let (pi, Hpi) := pi_sig in
  let pi_sig2 : { b : Buffer.t A | Buffer.color b = Green } :=
    match Buffer.length (suffix lvli) with
    | 0 => pi
    | 1 =>
      let (pair, _) := Buffer.pop (suffix lvli) in
      let (elt, _) := pair in
      let (pi, _) := Buffer.inject elt pi in
      pi
    | _ => !
    end
  in
  let (pi, Hpi) := pi_sig2 in
  makeLvl pi Buffer.Zero.

Next Obligation.
Proof.
  destruct (prefix lvli) ; simpl in H0 ; try omega ; simpl ;
    [ (right ; trivial) | (left ; discriminate) ].
Qed.

Next Obligation.
Proof.
  left ; destruct (Buffer.length (prefix lvli)) ; try omega ;
  destruct tmpi ; simpl in H0 ; try omega ;
  simpl ; discriminate.
Qed.

Next Obligation.
Proof.
  destruct (prefix lvli) ; simpl in H0 ; try omega ; simpl ;
    [ (right ; trivial) | (left ; discriminate) ].
Qed.

Next Obligation.
Proof.
  left ; destruct (Buffer.length (prefix lvli)) ; try omega ;
  destruct tmpi ; simpl in H0 ; try omega ;
  simpl ; discriminate.
Qed.

Next Obligation.
Proof.
  destruct lvlSi; destruct prefix0, suffix0; simpl in *; try omega;
  contradict ColorSi ; simpl ; reflexivity.
Qed.

Next Obligation.
Proof.
  destruct pi ; simpl in * ; reflexivity || omega.
Qed.

Next Obligation.
Proof.
  left ; destruct pi ; simpl in * ; try omega ; discriminate.
Qed.

Next Obligation.
Proof.
  destruct pi0 ; simpl in * ; first [ reflexivity | omega | idtac ].
  destruct lvli ; destruct prefix0, suffix0 ; simpl in * ; try omega.
  simpl in Colori ; discriminate Colori.
Qed.

Program Definition equilibrate {A : Set} (lvli : t A) (lvlSi : t (A * A))
  (is_lasti is_lastSi : bool)
  (Colori : color lvli is_lasti = Red)
  (ColorSi : color lvlSi is_lastSi <> Red \/ is_empty lvlSi)
  (Last : is_empty lvlSi -> is_lasti = true)
  (Triviality : is_lasti = true -> is_lastSi = true)
  (Has_elements : ~ (is_empty lvli /\ is_empty lvlSi))
: (
    { lvl : t A | color lvl false = Green } *
    { lSi : t (A * A)
        | color lSi is_lastSi = Red ->
            color lvlSi is_lastSi <> Green \/ is_lastSi = true
    }
  ) +
  ( 
    { l : t A | color l true = Green /\ is_lastSi = true }
  )
:=
  match Buffer.length (prefix lvlSi) + Buffer.length (suffix lvlSi) ≥ 2 with
  | left H => inl (two_buffer_case lvli lvlSi Colori is_lastSi _ _)
  | right _ =>
    match Buffer.length (prefix lvli) ≥ 2, Buffer.length (suffix lvli) ≥ 2 with
    | left _, _
    | _, left _ =>
      let '(lvli_sig, lvlSi) :=
        one_buffer_case lvli lvlSi is_lasti is_lastSi Colori ColorSi _ _ _ _
      in
      let (lvli, Hlvli) := lvli_sig in
      inl (lvli, lvlSi)
    | right _, right _ =>
      let (lvli, Hlvli) := no_buffer_case lvli lvlSi Colori _ _ _ in
      inr lvli
    end
  end.

Next Obligation.
Proof.
  destruct lvli, is_lasti ; destruct prefix0, suffix0 ;
  compute in Colori |- *; solve [ discriminate Colori | reflexivity ].
Qed.

Next Obligation.
Proof.
  destruct ColorSi.
  + assumption.
  + unfold is_empty in H0 ; rewrite <- 2 Buffer.empty_length in H0.
    omega.
Qed.

Next Obligation.
Proof.
  clear Heq_anonymous2.
  left ; simpl in *.
  destruct lvlSi ; destruct prefix0, suffix0, is_lastSi ; simpl in * ; solve [
    omega |
    (compute ; discriminate)
  ].
Qed.

Next Obligation.
Proof.
  clear Heq_anonymous2.
  left ; simpl in *.
  destruct lvlSi ; destruct prefix0, suffix0, is_lastSi ; simpl in * ; solve [
    omega |
    (compute ; discriminate)
  ].
Qed.

Next Obligation.
Proof.
  destruct lvli, is_lasti ; destruct prefix0, suffix0 ;
  compute in Colori |- *; solve [ discriminate Colori | reflexivity ].
Qed.

Next Obligation.
Proof.
  destruct lvlSi eqn:Si ; destruct prefix0, suffix0 ; simpl in * ; try omega.
  - assert (H : is_empty lvlSi) by (subst ; compute ; tauto).
    subst ; apply Last in H.
    destruct lvli ; simpl in H ; subst ; destruct prefix0, suffix0 ;
    simpl in * ; try omega ; solve [
      (contradict Has_elements ; compute ; tauto) |
      (contradict Colori ; compute ; discriminate)
    ].
  - destruct is_lastSi.
    + compute ; discriminate.
    + destruct ColorSi as [ Hcolor_fail | Hempty_fail ].
      * contradict Hcolor_fail ; compute ; reflexivity.
      * contradict Hempty_fail ; compute ; firstorder.
  - destruct is_lastSi.
    + compute ; discriminate.
    + destruct ColorSi as [ Hcolor_fail | Hempty_fail ].
      * contradict Hcolor_fail ; compute ; reflexivity.
      * contradict Hempty_fail ; compute ; firstorder.
Qed.

Next Obligation.
Proof.
  split ; auto.
  destruct lvlSi, is_lastSi ; destruct prefix0, suffix0 ; simpl in * ;
  try solve [
    omega |
    reflexivity |
    (compute in ColorSi ; destruct ColorSi as [ Hfalse | Hfalse ] ; [
        (exfalso ; apply Hfalse ; reflexivity) |
        (apply Triviality ; apply Last ; compute ; tauto)
      ])
  ].
Qed.
