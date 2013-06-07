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
    : { bi : t A | color bi = Green } * t (A * A)
  :=
    
    let pairSi
    : { p : Buffer.t (A * A) | Buffer.color p <> Red } * 
      { p : Buffer.t (A * A) | Buffer.color p <> Red }
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
    let pairP : { b : Buffer.t A | Buffer.color b = Green } * Buffer.t (A * A) :=
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
          let '(p, pSi) := Buffer.pop pSi in
          let '(elt1, elt2) := p in
          let (buff, Hbuff) := Buffer.inject elt1 (prefix lvli) in
          let (buff2, Hbuff2) := Buffer.inject elt2 buff in
          (buff2, pSi)
        | right _ =>
          (prefix lvli, pSi)
        end
      end
    in
    let pairS : { b : Buffer.t A | Buffer.color b = Green } * Buffer.t (A * A) :=
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
          let '(p, sSi) := Buffer.eject sSi in
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
  Proof.
    destruct lvlSi; compute in ColorSi; compute ;
    destruct prefix0, suffix0, is_last0 ; simpl in * ;
    intro color_mismatch ; solve [
      discriminate color_mismatch |
      auto
    ].
  Qed.

  Next Obligation.
  Proof.
    destruct lvlSi; compute in ColorSi; compute ;
    destruct prefix0, suffix0, is_last0 ; simpl in * ;
    intro color_mismatch ; solve [
      discriminate color_mismatch |
      auto
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
  Proof. destruct pSi ; firstorder. Qed.

  Next Obligation.
  Proof.
    destruct lvli; destruct prefix0; compute; firstorder;
    left ; intro Color_mismatch ; contradict Color_mismatch ; discriminate.
  Qed.

  Next Obligation.
  Proof.
    left; clear Heq_anonymous1.
    destruct (Buffer.length (prefix lvli)).
    + destruct buff ; simpl in Hbuff ; discriminate || discriminate Hbuff.
    + assert (Hn : n = 0) by omega.
      destruct buff ; simpl in Hbuff ; discriminate || (exfalso ; omega).
  Qed.

  Next Obligation.
  Proof.
    clear Heq_anonymous1; simpl in *.
    destruct (Buffer.length (prefix lvli)) ; try omega ;
    rewrite Hbuff in Hbuff2 ;
    destruct buff2 ; simpl in * ; try omega ; reflexivity.
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
  Proof. destruct sSi ; firstorder. Qed.

  Next Obligation.
  Proof.
    destruct lvli; destruct suffix0; compute; firstorder;
    left ; intro Color_mismatch ; contradict Color_mismatch ; discriminate.
  Qed.

  Next Obligation.
  Proof.
    left; clear Heq_anonymous1.
    destruct (Buffer.length (suffix lvli)).
    + destruct buff ; simpl in Hbuff ; discriminate || discriminate Hbuff.
    + assert (Hn : n = 0) by omega.
      destruct buff ; simpl in Hbuff ; discriminate || (exfalso ; omega).
  Qed.

  Next Obligation.
  Proof.
    clear Heq_anonymous1; simpl in *.
    destruct (Buffer.length (prefix lvli)) ; try omega ;
    rewrite Hbuff in Hbuff2 ;
    destruct buff2 ; simpl in * ; try omega ; reflexivity.
  Qed.

  Next Obligation.
  Proof.
    destruct (suffix lvli) ; simpl in * ; solve [ omega | reflexivity ].
  Qed.

  Next Obligation.
  Proof.
    destruct pi, si, (is_last lvli) ; simpl in H1, H0 ; first [
      discriminate H0 | discriminate H1 | idtac
    ] ; simpl ; reflexivity.
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
  : { bi : t A | color bi = Green } * t (A * A)
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
    destruct (Buffer.length (prefix lvli) ≥ 4) ; compute in H1 ; omega.
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
        destruct prefix0, suffix0 ; intro ; simpl in * ; firstorder ; discriminate H7.
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
    (Colori : color lvli = Red)
    (ColorSi : color lvlSi <> Red)
    (Hi : Buffer.length (prefix lvli) <= 1 /\ Buffer.length (suffix lvli) <= 1)
    (HSi : (Buffer.length (prefix lvlSi)) + (Buffer.length (suffix lvlSi)) <= 1)
  : { b : t A | color b = Green }
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
    (Has_elements : ~ (is_empty lvli /\ is_empty lvlSi))
  : { lvl : t A | color lvl = Green } * t (A * A)
  :=
    match Buffer.length (prefix lvlSi) + Buffer.length (suffix lvlSi) ≥ 2 with
    | left H => two_buffer_case lvli lvlSi Colori _ _
    | right _ =>
      match Buffer.length (prefix lvli) ≥ 2, Buffer.length (suffix lvli) ≥ 2 with
      | left _, _
      | _, left _ => one_buffer_case lvli lvlSi Colori ColorSi _ _ _
      | right _, right _ =>
        (no_buffer_case lvli lvlSi Colori _ _ _, empty (A * A))
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
  | ∅ | _ ++ ∅ => True
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
Proof. compute ; tauto. Qed.

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
