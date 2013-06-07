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
      makeLvl (Buffer.push x (suffix t)) Buffer.Zero (is_last t)
    else
      makeLvl (Buffer.push x (prefix t)) (suffix t) (is_last t).

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

  Definition empty (A : Set) := makeLvl (A := A) Buffer.Zero Buffer.Zero true.

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
    (Colori : color lvli = Red)
    (ColorSi : color lvlSi <> Red)
    (H : (Buffer.length (prefix lvlSi)) + (Buffer.length (suffix lvlSi)) >= 2)
    : { li  : t A | color li = Green /\ is_last li = false } *
      { lSi : t (A * A)
          | (color lSi = Red -> color lvlSi <> Green \/ is_last lvlSi = true)
            /\ is_last lSi = is_last lvlSi
      }
  :=
    
    let pairSi
    : { p : Buffer.t (A * A) |
        Buffer.color p <> Red /\
        (Buffer.color p <> Green -> color lvlSi <> Green \/ is_last lvlSi = true)
      } * 
      { s : Buffer.t (A * A) |
        Buffer.color s <> Red /\
        (Buffer.color s <> Green -> color lvlSi <> Green \/ is_last lvlSi = true)
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
          | Buffer.color b = Red -> color lvlSi <> Green \/ is_last lvlSi = true }
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
          | Buffer.color b = Red -> color lvlSi <> Green \/ is_last lvlSi = true }
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
    (makeLvl pi si false, makeLvl pSi sSi (is_last lvlSi)).

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
    destruct lvlSi; destruct prefix0, suffix0, is_last0; simpl in * ; try solve [
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
      destruct lvlSi ; destruct prefix0, suffix0, is_last0 ; simpl in * ;
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
      destruct lvlSi ; destruct prefix0, suffix0, is_last0 ; simpl in * ;
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
    destruct lvlSi ; destruct prefix0, suffix0, is_last0 ; simpl in * ; solve [
      omega |
      (right ; reflexivity) |
      (left ; compute ; discriminate)
    ].
  Qed.

  Next Obligation.
  Proof.
    destruct lvlSi; compute in ColorSi |- * .
    destruct prefix0, suffix0, is_last0 ; simpl in * ; solve [
      auto with arith |
      (split ; [ idtac | intro ; left ] ; intro F ; discriminate F)
    ].
  Qed.

  Next Obligation.
  Proof.
    destruct lvlSi; compute in ColorSi |- * ;
    destruct prefix0, suffix0, is_last0 ; simpl in * ; solve [
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
    split ; [ idtac | reflexivity ].
    destruct pi, si, (is_last lvli) ; simpl in H1, H3 ; first [
      discriminate H3 | discriminate H1 | idtac
    ] ; simpl ; reflexivity.
  Qed.

  Next Obligation.
  Proof.
    split ; [ idtac | reflexivity ].
    intro Hcol ; destruct pSi0, sSi0 ; destruct (is_last lvlSi) eqn:Last ;
    simpl in * ; solve [
      (compute in Hcol ; discriminate Hcol) |
      (apply H0 ; reflexivity) |
      (apply H2 ; reflexivity)
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
    (Colori : color lvli = Red)
    (ColorSi : color lvlSi <> Red \/ is_empty lvlSi)
    (HSi : (Buffer.length (prefix lvlSi)) + (Buffer.length (suffix lvlSi)) <= 1)
    (Hi : Buffer.length (prefix lvli) >= 2 \/ Buffer.length (suffix lvli) >= 2)
    (LastLvl : is_empty lvlSi -> is_last lvli = true)
    (Triviality : is_last lvli = true -> is_last lvlSi = true)
  : { l : t A | color l = Green /\ is_last l = false } *
    { l : t (A * A) | is_last l = is_last lvlSi }
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
      { b : Buffer.t A |
        if Buffer.length (prefix lvli) ≥ 4
          then 1 < Buffer.length b <= 3
          else b = prefix lvli
      } *
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
    let pairSP : { b : Buffer.t A | Buffer.color b = Green } *
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
    (makeLvl pi si false, makeLvl pSi Buffer.Zero true).

  Next Obligation.
  Proof.
    split.
    - omega.
    - intro H ; apply LastLvl.
      destruct lvlSi ; destruct prefix0, suffix0 ; simpl in *; firstorder.
  Qed.

  Next Obligation.
  Proof.
    simpl in *.
    destruct pSi ; simpl in * ; firstorder ; left ; discriminate.
  Qed.

  Next Obligation.
  Proof.
    simpl in *.
    assert (HB: Buffer.length (prefix lvli) <= 5) by apply Buffer.bounded_length.
    destruct (Buffer.length (prefix lvli)) ; omega.
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
      destruct prefix0, suffix0 ; intro ; simpl in * ; firstorder ;
      discriminate H6.
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
    split ; [ idtac | reflexivity ].
    destruct pi0, si; simpl in H1, H3 ; first [
      discriminate H1 | discriminate H3 | idtac
    ] ; simpl ; reflexivity.
  Qed.

  Next Obligation.
  Proof.
    destruct lvlSi ; destruct prefix0, suffix0, is_last0 ; simpl in * ;
    try solve [
      omega |
      reflexivity |
      (symmetry; apply Triviality; apply LastLvl; compute ; tauto) |
      (compute in ColorSi ; destruct ColorSi as [ Hfalse | Hfalse ] ;
          exfalso ; apply Hfalse ; reflexivity)
    ].
  Qed.

  Program Definition no_buffer_case {A : Set}
    (lvli : t A)
    (lvlSi : t (A * A))
    (Colori : color lvli = Red)
    (ColorSi : color lvlSi <> Red)
    (Hi : Buffer.length (prefix lvli) <= 1 /\ Buffer.length (suffix lvli) <= 1)
    (HSi : (Buffer.length (prefix lvlSi)) + (Buffer.length (suffix lvlSi)) <= 1)
  : { b : t A | color b = Green /\ is_last b = true }
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
    (makeLvl pi Buffer.Zero true).

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
    destruct lvlSi; destruct prefix0, suffix0, is_last0; simpl in *; try omega;
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
    destruct is_last0 ; simpl in Colori ; discriminate Colori.
  Qed.
  
  Program Definition equilibrate {A : Set} (lvli : t A) (lvlSi : t (A * A))
    (Colori : color lvli = Red)
    (ColorSi : color lvlSi <> Red \/ is_empty lvlSi)
    (Last : is_empty lvlSi -> is_last lvli = true)
    (Triviality : is_last lvli = true -> is_last lvlSi = true)
    (Has_elements : ~ (is_empty lvli /\ is_empty lvlSi))
  : (
      { lvl : t A | color lvl = Green /\ is_last lvl = false} *
      { lSi : t (A * A)
          | (color lSi = Red -> color lvlSi <> Green \/ is_last lvlSi = true)
            /\ is_last lSi = is_last lvlSi
      }
    ) +
    ( 
      { l : t A | color l = Green /\ is_last l = true /\ is_last lvlSi = true }
    )
  :=
    match Buffer.length (prefix lvlSi) + Buffer.length (suffix lvlSi) ≥ 2 with
    | left H => inl (two_buffer_case lvli lvlSi Colori _ _)
    | right _ =>
      match Buffer.length (prefix lvli) ≥ 2, Buffer.length (suffix lvli) ≥ 2 with
      | left _, _
      | _, left _ =>
        let '(lvli_sig, lvlSi_sig) :=
          one_buffer_case lvli lvlSi Colori ColorSi _ _ _ _
        in
        let (lvli, Hlvli) := lvli_sig in
        let (lvlSi, HlvlSi) := lvlSi_sig in
        inl (lvli, lvlSi)
      | right _, right _ =>
        let (lvli, Hlvli) := no_buffer_case lvli lvlSi Colori _ _ _ in
        inr lvli
      end
    end.

  Next Obligation.
  Proof.
    destruct ColorSi.
    + assumption.
    + unfold is_empty in H0 ; rewrite <- 2 Buffer.empty_length in H0.
      omega.
  Qed.

  Next Obligation.
  Proof.
    clear Heq_anonymous2 ; split.
    - intro HN ; clear HN ; left ; simpl in *.
      destruct lvlSi ; destruct prefix0, suffix0, is_last0 ; simpl in * ;
      try solve [
        omega |
        (compute ; discriminate)
      ].
    - reflexivity.
  Qed.

  Next Obligation.
  Proof.
    clear Heq_anonymous2 ; split ; [ idtac | reflexivity ].
    intro HN ; clear HN ; left ; simpl in *.
    destruct lvlSi ; destruct prefix0, suffix0, is_last0 ; simpl in * ;
    solve [
      omega |
      (compute ; discriminate)
    ].
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
    - destruct is_last0.
      + compute ; discriminate.
      + destruct ColorSi as [ Hcolor_fail | Hempty_fail ].
        * contradict Hcolor_fail ; compute ; reflexivity.
        * contradict Hempty_fail ; compute ; firstorder.
    - destruct is_last0.
      + compute ; discriminate.
      + destruct ColorSi as [ Hcolor_fail | Hempty_fail ].
        * contradict Hcolor_fail ; compute ; reflexivity.
        * contradict Hempty_fail ; compute ; firstorder.
  Qed.

  Next Obligation.
  Proof.
    split ; [ .. | split ] ; auto.
    destruct lvlSi ; destruct prefix0, suffix0, is_last0 ; simpl in * ;
    try solve [
      omega |
      reflexivity |
      (compute in ColorSi ; destruct ColorSi as [ Hfalse | Hfalse ] ; [
          (exfalso ; apply Hfalse ; reflexivity) |
          (apply Triviality ; apply Last ; compute ; tauto)
        ])
    ].
  Qed.

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

  Fixpoint is_last_coherence {A B : Set} (s : t A B) (is_last : bool) : Prop :=
    match s with
    | Nil _ => True
    | Cons _ _ lvl (Nil _) => Lvl.is_last lvl = is_last
    | Cons _ _ lvl rest    =>
      Lvl.is_last lvl = false /\ is_last_coherence rest is_last
    end.

  Fixpoint all_yellows {A B : Set} (s : t A B) : Prop :=
    match s with
    | Nil _ => True
    | Cons _ _ lvl (Nil _) => Lvl.color lvl = Yellow
    | Cons _ _ lvl rest    => Lvl.color lvl = Yellow /\ all_yellows rest
    end.

  Definition well_formed {A B : Set} (stack : t A B) :=
    match stack with
    | Nil _ => False
    | Cons _ _ _top_level rest => all_yellows rest
    end.

  Program Definition hd {A B : Set} (stack : t A B | ~ is_nil stack) :=
    match stack with
    | Nil _ => !
    | Cons _ _ hd _ => hd
    end.

  Next Obligation.
  Proof. contradict H. rewrite <- Heq_stack; simpl ; auto. Qed.

  Theorem wf_impl_nnil :
    forall A B, forall s : t A B, well_formed s -> ~ is_nil s.
  Proof. induction s ; intros H ; [ contradict H | auto ]. Qed.

  Definition is_empty {A B : Set} (stack : t A B) : Prop :=
    match stack with
    | Cons _ _ lvl (Nil _) => Lvl.is_empty lvl
    | _ => False
    end.

  Program Definition empty (A : Set) :
    { s : t A (A * A) | well_formed s /\ is_empty s } :=
    Cons (Lvl.empty A) Nil.

  Next Obligation.
  Proof. compute ; tauto. Qed.

End Stack.

Module S := Stack.

Inductive deque (A : Set) : Type :=
  | Nil : deque A
  | Cons :
    forall B : Set, forall s : S.t A B, S.well_formed s -> deque B -> deque A.

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
  | top_stack ++ _ =>
    match top_stack with
    | [] => !
    | toplvl ::: _ => Lvl.color toplvl
    end
  end.

Next Obligation.
Proof.
  apply JMeq_eq in Heq_top_stack.
  subst ; contradiction.
Qed.

Fixpoint semi_regular {A : Set} (d : t A) : Prop :=
  match d with
  | ∅ => True
  | top ++ ∅ => S.is_last_coherence top true
  | top ++ stacks =>
    let green_before_red :=
      match color d with
      | Red => color stacks = Green
      | Green => True
      | Yellow => False
      end
    in
    semi_regular stacks /\ green_before_red /\ S.is_last_coherence top false
  end.

Theorem semi_regular_ind :
  forall A B,
  forall top_stack : S.t A B, forall wf_p,
  forall deque : t B,
  semi_regular (Cons top_stack wf_p deque) -> semi_regular deque.
Proof.
  intros ; simpl in H.
  destruct deque0 ; [ (simpl ; auto) | .. ].
  destruct H as [ H _ ].
  exact H.
Qed.

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
Proof. compute ; tauto. Qed.

Definition is_empty {A} (d : t A) :=
  match d with
  | lvl ::: [] ++ ∅ => Lvl.is_empty lvl
  | _ => False
  end.

Definition dec_is_empty {A} (d : t A) : { is_empty d } + { ~ is_empty d }.
  destruct d.
  - right ; auto.
  - destruct s.
    + contradict w ; simpl.
    + dependent destruction s.
      * destruct (Lvl.dec_is_empty t0), d ; firstorder.
      * right ; auto.
Qed.

Inductive regularisation_cases (A : Set) : t A -> Type :=
  | empty_case : regularisation_cases A ∅
  | one_level_case :
    forall lvli : Lvl.t A,
    forall wf_p : S.well_formed (lvli ::: []),
    forall last : Lvl.is_last lvli = true,
    regularisation_cases A (Cons (lvli ::: []) wf_p ∅)
  | general_case1 :
    forall B : Set,
    forall lvli lvlSi yellows,
    forall rest : t B,
    forall wf_p : S.well_formed (lvli ::: lvlSi ::: yellows),
    forall not_last : Lvl.is_last lvli = false,
    regularisation_cases A (Cons (lvli ::: lvlSi ::: yellows) wf_p rest)
  | general_case2 :
    forall B : Set,
    forall lvli lvlSi yellows,
    forall rest : t B,
    forall wftop_p : S.well_formed (lvli ::: []),
    forall wfsnd_p : S.well_formed (lvlSi ::: yellows),
    forall not_last : Lvl.is_last lvli = false,
    regularisation_cases A
      (Cons (lvli ::: []) wftop_p
        (Cons (lvlSi ::: yellows) wfsnd_p rest)).

Parameter dispatch :
  forall A : Set,
  forall d : t A,
  regularisation_cases A d.

(* TODO: move in Lvl *)
Definition set_last {A} (l : Lvl.t A) bool :=
  Lvl.makeLvl (Lvl.prefix l) (Lvl.suffix l) bool.

Program Definition do_regularize {A : Set}
  (d : t A)
  (Hsr : semi_regular d)
  (Color : color d = Red)
  (NotEmpty : ~ is_empty d)
: { d : t A | strongly_regular d }
:=
  match dispatch A d with
  | empty_case => ∅
  | one_level_case lvli _ _ =>
    if Lvl.dec_is_empty lvli then ! (* by NotEmpty *) else
    let lvlSi := Lvl.empty (A * A) in
    let pair :
      {l : Lvl.t A | Lvl.color l = Green /\ Lvl.is_last l = false} *
      {l : Lvl.t (A * A) | Lvl.is_last l = Lvl.is_last lvlSi}
    :=
      Lvl.one_buffer_case lvli lvlSi _ _ _ _ _ _
    in
    let (lvli, lvlSi) := pair in
    match Lvl.color lvlSi with
    | Yellow => lvli ::: lvlSi ::: [] ++ ∅
    | _ =>
      if Lvl.dec_is_empty lvlSi
        then (set_last lvli true) ::: [] ++ ∅
        else lvli ::: [] ++ lvlSi ::: [] ++ ∅
    end
  | general_case1 _B lvli lvlSi yellows rest _ _
  | general_case2 _B lvli lvlSi yellows rest _ _ _ =>
    match Lvl.equilibrate lvli lvlSi _ _ _ _ _ with
    | inl p =>
        (*
    let pair :
      { l : Lvl.t A | Lvl.color l = Green } *
      { lSi : Lvl.t (A * A)
          | Lvl.color lSi = Red -> Lvl.color lvlSi <> Green \/ Lvl.is_last lvlSi = true
      }
    :=
      Lvl.equilibrate lvli lvlSi _ _ _ _
    in
    *)
      let (lvli', lvlSi'_sig) := p in
      let (lvlSi', HlvlSi') := lvlSi'_sig in
      match Lvl.color lvlSi' with
      | Yellow => lvli' ::: lvlSi' ::: yellows ++ rest
      | _ =>
        match Lvl.dec_is_empty lvlSi', Lvl.is_last lvlSi with
        | left HeSi, true =>
          (set_last lvli' true) ::: [] ++ ∅
        | _, _ => lvli' ::: [] ++ lvlSi' ::: yellows ++ rest
        end
      end
    | inr lvl_sig =>
      let (lvl, Hlvl) := lvl_sig in
      lvl ::: [] ++ ∅
    end
  end.

Next Obligation.
Proof. right ; compute ; tauto. Qed.

Next Obligation.
Proof.
  simpl in Color.
  destruct lvli ; destruct prefix, suffix, is_last ; solve [
    (simpl ; omega) |
    (compute in Color ; discriminate Color) |
    (compute in H ; exfalso ; apply H ; tauto) |
    (simpl in wildcard'0 ; discriminate wildcard'0)
  ].
Qed.

Next Obligation.
Proof. rewrite e ; split ; assumption. Qed.

Lemma color_preservation :
  forall {A}, forall lvl:Lvl.t A,
    Lvl.color lvl <> Red -> Lvl.color (set_last lvl true) = Lvl.color lvl.
Proof.
  intros.
  destruct lvl ; destruct prefix, suffix, is_last ; compute in H |- * ;
  reflexivity || (exfalso ; apply H ; reflexivity).
Qed.

Next Obligation.
Proof.
  rewrite color_preservation ; rewrite e ; [ trivial | discriminate ].
Qed.

Next Obligation.
Proof. rewrite e ; tauto. Qed.

Next Obligation.
Proof.
  left ; dependent destruction yellows ; [ idtac | destruct wildcard' ] ;
  congruence.
Qed.

Next Obligation.
Proof.
  dependent destruction yellows; [ idtac | destruct wildcard' as [ wildcard' ]];
  destruct lvlSi ; destruct prefix, suffix, is_last ; compute in H, wildcard' ;
  solve [
    discriminate wildcard' |
    (destruct H ; contradiction)
  ].
Qed.

Next Obligation.
Proof. congruence. Qed.

Next Obligation.
Proof.
  assert (ColSiY : Lvl.color lvlSi = Yellow) by
    (dependent destruction yellows ; try destruct wildcard' ; assumption).
  intuition.
  destruct lvlSi ; destruct prefix, suffix, is_last ;
  compute in ColSiY, H1 ; destruct H1 ; solve [
    assumption |
    discriminate ColSiY
  ].
Qed.

Next Obligation.
Proof.
  dependent destruction yellows ; intuition.
  destruct wildcard' ; assumption.
Qed.

Next Obligation.
Proof.
  clear Heq_anonymous0.
  rewrite e, H0.
  destruct rest ; intuition.
  - dependent destruction yellows ; destruct Hsr as [ _ Hlastco ] ;
    simpl in Hlastco ; assumption.
  - apply semi_regular_ind in Hsr ; assumption.
  - destruct Hsr as [ _ Htop ] ; destruct Htop as [ _ Hlastco ].
    simpl in Hlastco.
    destruct Hlastco ; assumption.
Qed.

Next Obligation.
Proof.
  clear Heq_anonymous0.
  rewrite color_preservation.
  - rewrite e ; trivial.
  - congruence.
Qed.

Next Obligation.
Proof.
  dependent destruction yellows.
  - simpl; trivial.
  - destruct wildcard' ; assumption.
Qed.

Next Obligation.
Proof.
  clear Heq_anonymous0.
  rewrite e, H2 ; intuition.
  destruct rest.
  - destruct Hsr as [ _ Hlastco ].
    simpl in Hlastco ; assumption.
  - split ; [ idtac | split ].
    + apply semi_regular_ind in Hsr.
      assumption.
    + destruct (Lvl.color lvlSi').
      * trivial.
      * apply H ; reflexivity.
      * unfold semi_regular in Hsr.
        destruct Hsr as [ _ Hsr ].
        destruct Hsr as [ Hsr _ ].
        rewrite Color in Hsr.
        assumption.
    + destruct Hsr as [ _ Hsr ].
      destruct Hsr as [ _ Hsr ].
      simpl in Hsr.
      destruct Hsr as [ _ Hsr ].
      assumption.
Qed.

Next Obligation.
Proof. rewrite H ; trivial. Qed.

Next Obligation.
Proof.
  left ; simpl in Color.
  simpl in Hsr ; destruct Hsr as [ _ H ].
  rewrite Color in H ; destruct H.
  congruence.
Qed.

Next Obligation.
Proof.
  simpl in Color.
  assert (ColorSi : Lvl.color lvlSi = Red) by
    (destruct lvlSi ; destruct prefix, suffix, is_last ; compute in H |- *;
      firstorder).
  simpl in Hsr ; destruct Hsr as [ _ ColorSi' ] ; rewrite Color in ColorSi'.
  destruct ColorSi' ; congruence.
Qed.

Next Obligation.
Proof. congruence. Qed.

Next Obligation.
Proof.
  simpl in Color.
  simpl in Hsr ; destruct Hsr as [ _ ColorSi ]; rewrite Color in ColorSi.
  intro Htmp ; destruct Htmp as [ _ Hempty ].
  destruct ColorSi as [ ColorSi _ ].
  destruct lvlSi ; destruct prefix, suffix, is_last ;
  compute in ColorSi, Hempty ; destruct Hempty ; solve [
    discriminate ColorSi |
    assumption
  ].
Qed.

Next Obligation.
Proof.
  dependent destruction yellows.
  - symmetry ; assumption.
  - split ; auto.
Qed.

Next Obligation.
Proof.
  clear Heq_anonymous0.
  rewrite e, H0.
  destruct rest ; intuition.
  - destruct Hsr as [ Hsr _ ].
    dependent destruction yellows.
    + simpl in Hsr ; assumption.
    + destruct Hsr ; split ; assumption.
  - do 2 apply semi_regular_ind in Hsr ; assumption.
  - destruct Hsr as [ Hsr _ ].
    destruct Hsr as [ _ Hsr ].
    destruct Hsr as [ _ Hlastco ].
    simpl in Hlastco ; assumption.
Qed.

Next Obligation.
Proof.
  clear Heq_anonymous0.
  rewrite color_preservation.
  - rewrite e; trivial.
  - congruence.
Qed.

Next Obligation.
Proof.
  clear Heq_anonymous0.
  rewrite e, H2 ; destruct rest ; intuition.
  - destruct Hsr as [ Hsr _ ].
    simpl in Hsr ; assumption.
  - do 2 apply semi_regular_ind in Hsr. assumption.
  - destruct (Lvl.color lvlSi') eqn:ColorSi'.
    + trivial.
    + apply H ; reflexivity.
    + unfold semi_regular in Hsr.
      destruct Hsr as [ Hsr' Hsr ].
      rewrite Color in Hsr.
      assert (trivial : Red = Red) by reflexivity.
      apply H1 in trivial.
      destruct trivial.
      * simpl in Hsr.
        exfalso ; apply H5.
        destruct Hsr as [ Hsr _ ] ; exact Hsr.
      * clear Hsr ; destruct Hsr' as [ _ Hsr ].
        destruct Hsr as [ _ Hlastco ].
        simpl in Hlastco.
        dependent destruction yellows ; [ .. | destruct Hlastco ] ; congruence.
  - destruct Hsr as [ Hsr _ ].
    destruct Hsr as [ _ Hlastco ].
    destruct Hlastco as [ _ Hlastco ].
    simpl in Hlastco ; assumption.
Qed.

Next Obligation.
Proof. rewrite H ; trivial. Qed.
