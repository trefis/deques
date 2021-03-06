Require Import Program.
Require Import List.

Require Import Misc.
Require Level.
Require Stack.

Module S := Stack.

Inductive t (A : Set) : Type :=
  | SingleLevel :
    forall B, forall s : Stack.t A B, Stack.well_formed s true -> t A
  | SeveralLvls :
    forall B, forall s : Stack.t A B, Stack.well_formed s false -> t B -> t A.

Arguments SingleLevel [A B] _ _.
Arguments SeveralLvls [A B] _ _ _.

Notation "<< X >>" := (SingleLevel X _).
Notation "x ++ y" := (SeveralLvls x _ y).

Notation "[]" := (@Stack.Nil _) (at level 40).
Notation "a ::: b" := (@Stack.Cons _ _ a b) (at level 55, right associativity).

Definition color {A} (d : t A) :=
  match d with
  | << stack >> => Stack.color stack true
  | stack ++ _ => Stack.color stack false
  end.

Definition is_empty {A} (d : t A) :=
  match d with
  | << (lvl ::: []) >> => Level.is_empty lvl
  | _ => False
  end.

Definition dec_is_empty {A} (d : t A) : { is_empty d } + { ~ is_empty d }.
Proof.
  destruct d ; [ .. | (right ; simpl ; auto) ].
  destruct s ; [ (exfalso ; assumption) | .. ].
  dependent destruction s ; simpl ; [ .. | (right ; auto) ].
  apply Level.dec_is_empty.
Defined.

Fixpoint green_between_reds {A} (d : t A) : Prop :=
  match d with
  | << stack >> => Stack.color stack true <> Yellow
  | top ++ rest =>
    let g_before_r :=
      match Stack.color top false with
      | Red => color rest = Green
      | Green => True
      | Yellow => False
      end
    in
    g_before_r /\ green_between_reds rest
  end.

Definition semi_regular {A} (d : t A) : Prop :=
  match d with
  | << _ >> => True
  | top ++ rest =>
    match color d with
    | Yellow => green_between_reds rest
    | _ => green_between_reds d
    end
  end.

Definition regular {A} (d : t A) : Prop :=
  match d with
  | << s >> =>
    match Stack.color s true with
    | Red => Stack.is_empty s
    | _   => True
    end
  | top ++ rest =>
    match Stack.color top false with
    | Red    => False
    | Green  => green_between_reds rest
    | Yellow => color rest = Green /\ green_between_reds rest
    end
  end.

Program Definition empty A : { d : t A | regular d } := << Stack.empty A >>.
Next Obligation.
Proof. compute ; tauto. Qed.

Inductive regularisation_cases (A : Set) : t A -> Type :=
  | one_level :
    forall lvl : Level.t A,
    forall p_wf : Stack.well_formed (lvl ::: []) true,
    regularisation_cases A (SingleLevel (lvl ::: []) p_wf)
  | general_case1a :
    forall B lvli lvlSi,
    forall yellows : Stack.t ((A * A) * (A * A)) B,
    forall p_wf : Stack.well_formed (lvli ::: lvlSi ::: yellows) true,
    regularisation_cases A (SingleLevel (lvli ::: lvlSi ::: yellows) p_wf)
  | general_case1b :
    forall B lvli lvlSi,
    forall yellows : Stack.t ((A * A) * (A * A)) B,
    forall p_wf1 : Stack.well_formed (lvli ::: []) false,
    forall p_wf2 : Stack.well_formed (lvlSi ::: yellows) true,
    regularisation_cases A 
      (SeveralLvls (lvli ::: []) p_wf1
        (SingleLevel (lvlSi ::: yellows) p_wf2))
  | general_case2a :
    forall B lvli lvlSi,
    forall yellows : Stack.t ((A * A) * (A * A)) B,
    forall p_wf : Stack.well_formed (lvli ::: lvlSi ::: yellows) false,
    forall rest : t B,
    regularisation_cases A (SeveralLvls (lvli ::: lvlSi ::: yellows) p_wf rest)
  | general_case2b :
    forall B lvli lvlSi,
    forall yellows : Stack.t ((A * A) * (A * A)) B,
    forall p_wf1 : Stack.well_formed (lvli ::: []) false,
    forall p_wf2 : Stack.well_formed (lvlSi ::: yellows) false,
    forall rest : t B,
    regularisation_cases A 
      (SeveralLvls (lvli ::: []) p_wf1
        (SeveralLvls (lvlSi ::: yellows) p_wf2 rest)).

Definition dispatch (A : Set) (d : t A) (p : semi_regular d) :
  regularisation_cases A d.
Proof.
  destruct d ; (destruct s ; [ (exfalso ; apply w) | .. ]) ;
  dependent destruction s ; try constructor.
  destruct d ; dependent destruction s ; try (exfalso ; assumption) ;
  constructor.
Defined.

Lemma color_preservation :
  forall {A}, forall lvl:Level.t A,
    Level.color lvl false <> Red -> Level.color lvl true = Level.color lvl false.
Proof.
  intros.
  destruct lvl ; destruct prefix, suffix ; compute in H |- * ;
  reflexivity || (exfalso ; apply H ; reflexivity).
Qed.

Ltac is_color x :=
  match x with
  | Red => idtac
  | Green => idtac
  | Yellow => idtac
  | _ => fail
  end.

Ltac simpl_colors :=
  simpl in * ;
  repeat match goal with
  | [ H : ?Color = color ?deque |- _ ] =>
    is_color Color ; rewrite <- H in *
  | [ H : ?Color = Stack.color ?stack ?bool |- _ ] =>
    is_color Color ; rewrite <- H in *
  | [ H : ?Color = Level.color ?lvl ?is_last |- _ ] =>
    is_color Color ; rewrite <- H in *
  | [ H : Level.color ?lvl ?is_last = ?Color |- _ ] =>
    is_color Color ; rewrite H in *
  | [ Hcol : Level.color ?lvli false = Green
    |- context[Level.color ?lvli true = Green] ] =>
    rewrite color_preservation ; rewrite Hcol ; auto || discriminate
  end ; try split ; trivial || auto.

Local Obligation Tactic := (program_simpl ; try simpl_colors).

Program Definition do_regularize {A} (d : t A) (Hsr : semi_regular d)
  (Color : color d = Red) (Hempty : ~ is_empty d)
: { d : t A | regular d /\ color d = Green }
:=
  match dispatch A d Hsr with
  | one_level lvli _ =>
    if Level.dec_is_empty lvli then ! else
    let lvlSi := Level.empty (A * A) in
    let pair :
      {l : Level.t A | Level.color l false = Green } * Level.t (A * A)
    :=
      (* Why not [Level.equilibrate]? *)
      Level.one_buffer_case lvli lvlSi true true _ _ _ _ _ _
    in
    let (lvli, lvlSi) := pair in
    let (lvli, Hcol) := lvli in
    match Level.color lvlSi true with
    | Yellow => << lvli ::: lvlSi ::: [] >>
    | _ =>
      if Level.dec_is_empty lvlSi
        then << lvli ::: [] >>
        else lvli ::: [] ++ << lvlSi ::: [] >>
    end
  | general_case1a _ lvli lvlSi yellows _
  | general_case1b _ lvli lvlSi yellows _ _ =>
    let is_lastSi := 
      match yellows with
      | [] => true
      | _ ::: _  => false
      end
    in
    match Level.equilibrate lvli lvlSi false is_lastSi _ _ _ _ _ with
    | inl p =>
      let (lvli', lvlSi'_sig) := p in
      let (lvlSi', HlvlSi') := lvlSi'_sig in
      match Level.color lvlSi' is_lastSi with
      | Yellow => << lvli' ::: lvlSi' ::: yellows >>
      | _ =>
        match Level.dec_is_empty lvlSi', is_lastSi with
        | left HeSi, true =>
          << lvli' ::: [] >>
        | _, _ => lvli' ::: [] ++ << lvlSi' ::: yellows >>
        end
      end
    | inr lvl_sig =>
      let (lvl, Hlvl) := lvl_sig in
      << lvl ::: [] >>
    end
  | general_case2a _ lvli lvlSi yellows _ rest
  | general_case2b _ lvli lvlSi yellows _ _ rest =>
    match Level.equilibrate lvli lvlSi false false _ _ _ _ _ with
    | inl p =>
      let (lvli', lvlSi'_sig) := p in
      let (lvlSi', HlvlSi') := lvlSi'_sig in
      match Level.color lvlSi' false with
      | Yellow => lvli' ::: lvlSi' ::: yellows ++ rest
      | _ => lvli' ::: [] ++ lvlSi' ::: yellows ++ rest
      end
    | inr lvl_sig => !
    end
  end.

(* one_level case *)
Next Obligation.
Proof. right ; compute ; tauto. Qed.

Next Obligation.
Proof.
  destruct lvli ; destruct prefix, suffix ; solve [
    (simpl ; omega) |
    (compute in Color ; discriminate Color) |
    (compute in H ; exfalso ; apply H ; tauto) |
    (simpl in wildcard'0 ; discriminate wildcard'0)
  ].
Qed.

(* general_case1a *)
Next Obligation.
Proof.
  left; dependent destruction yellows; [ .. | destruct wildcard'0 ]; congruence.
Qed.

Next Obligation.
Proof.
  destruct lvlSi ; destruct prefix, suffix ; compute in H ;
  destruct H as [ Hp Hs ]; try (exfalso ; assumption) ;
  dependent destruction yellows.
  - discriminate wildcard'0.
  - dependent destruction wildcard'0.
    discriminate e.
Qed.

Next Obligation.
Proof.
  intuition.
  destruct lvlSi ; destruct prefix, suffix ; compute in H1 ;
  destruct H1 as [ Hp Hs ] ; try (exfalso ; assumption) ;
  dependent destruction yellows.
  - discriminate wildcard'0.
  - dependent destruction wildcard'0.
    discriminate e.
Qed.

Next Obligation.
Proof.
  dependent destruction yellows.
  - congruence.
  - split ; [ congruence | .. ].
    destruct wildcard'0.
    assumption.
Qed.

Next Obligation.
Proof.
  dependent destruction yellows ; [ .. | destruct wildcard'0 ] ; auto.
Qed.

Next Obligation.
Proof.
  dependent destruction yellows ; auto.
Qed.

(* general_case1b *)
Next Obligation.
Proof.
  clear Heq_anonymous.
  left; dependent destruction yellows; simpl_colors; destruct Hsr; congruence.
Qed.

Next Obligation.
Proof.
  clear Heq_anonymous.
  rewrite Color in Hsr.
  dependent destruction yellows ; destruct Hsr as [ Hcol _ ] ;
  destruct lvlSi ; destruct prefix, suffix ; compute in H, Hcol ;
  firstorder ; discriminate Hcol.
Qed.

Next Obligation.
Proof.
  clear Heq_anonymous.
  intuition ; simpl_colors.
  dependent destruction yellows ; destruct Hsr as [ Hcol _ ] ;
  destruct lvlSi ; destruct prefix, suffix ; compute in H1, Hcol ;
  firstorder ; discriminate Hcol.
Qed.

Next Obligation.
Proof.
  clear Heq_anonymous0 Heq_anonymous.
  dependent destruction yellows.
  - congruence.
  - split ; [ congruence | assumption ].
Qed.

Next Obligation.
Proof.
  clear Heq_anonymous0 Heq_anonymous H0 H1 H3 HlvlSi'.
  dependent destruction yellows ; auto.
Qed.

(* general_case2a *)
Next Obligation.
Proof.
  left; dependent destruction yellows; [ .. | destruct wildcard'0 ]; congruence.
Qed.

Next Obligation.
Proof.
  destruct lvlSi ; destruct prefix, suffix ; compute in H ; firstorder.
  compute in wildcard'0 ;
  dependent destruction yellows ; [ .. | destruct wildcard'0 ] ; congruence.
Qed.

Next Obligation.
Proof.
  intuition.
  destruct lvlSi ; destruct prefix, suffix ; compute in H1 ; firstorder.
  compute in wildcard'0 ;
  dependent destruction yellows ; [ .. | destruct wildcard'0 ] ; congruence.
Qed.

Next Obligation.
Proof.
  clear Heq_anonymous0 Heq_anonymous.
  dependent destruction yellows ; [ .. | split ] ; auto.
  destruct wildcard'0 ; assumption.
Qed.

Next Obligation.
Proof.
  clear Heq_anonymous0 Heq_anonymous.
  simpl_colors ; destruct Hsr ; assumption.
Qed.

Next Obligation.
Proof.
  clear Heq_anonymous0 Heq_anonymous.
  dependent destruction yellows.
  - simpl ; trivial.
  - destruct wildcard'0 ; assumption.
Qed.

Next Obligation.
Proof.
  clear Heq_anonymous0 Heq_anonymous.
  split.
  - dependent destruction yellows ;
    destruct (Level.color lvlSi' false) ; solve [
      trivial | (apply H ; reflexivity) | (simpl_colors ; firstorder)
    ].
  - simpl_colors ; destruct Hsr ; assumption.
Qed.

(* general_case2b *)
Next Obligation.
Proof.
  clear Heq_anonymous.
  left; dependent destruction yellows ;
    simpl_colors ; destruct Hsr ; congruence.
Qed.

Next Obligation.
Proof.
  clear Heq_anonymous.
  simpl_colors ; dependent destruction yellows ; destruct Hsr as [ Hcol _ ] ;
  destruct lvlSi ; destruct prefix, suffix ; compute in H, Hcol ;
  firstorder ; discriminate Hcol.
Qed.

Next Obligation.
Proof.
  clear Heq_anonymous ; intuition ; simpl_colors.
  dependent destruction yellows ; destruct Hsr as [ Hcol _ ] ;
  destruct lvlSi ; destruct prefix, suffix ; compute in H1, Hcol ;
  firstorder ; discriminate Hcol.
Qed.

Next Obligation.
Proof.
  clear Heq_anonymous0 Heq_anonymous.
  dependent destruction yellows ; auto.
Qed.

Next Obligation.
Proof.
  clear Heq_anonymous0 Heq_anonymous.
  simpl_colors ; do 2 destruct Hsr  as [ _ Hsr ]; assumption.
Qed.

Next Obligation.
Proof.
  clear Heq_anonymous0 Heq_anonymous.
  split.
  - dependent destruction yellows ;
    destruct (Level.color lvlSi' false) ; solve [
      trivial | (apply H ; reflexivity) | (simpl_colors ; firstorder)
    ].
  - simpl_colors ; do 2 destruct Hsr as [ _ Hsr ] ; assumption.
Qed.

Program Definition regularize {A : Set} (d : t A) (Hsr : semi_regular d) :
  { d : t A | regular d }
:=
  match color d with
  | Green => d
  | Yellow =>
    match d with
    | << _ >> => d
    | top ++ stacks =>
      match color stacks with
      | Green => d
      | Yellow => !
      | Red =>
        match dec_is_empty stacks with
        | left _ => << top >>
        | right NotEmpty =>
          let stacks' := do_regularize stacks _ _ NotEmpty in
          top ++ stacks'
        end
      end
    end
  | Red =>
    match dec_is_empty d with
    | left _ => d
    | right NotEmpty => do_regularize d _ _ NotEmpty
    end
  end.

Next Obligation.
Proof. destruct d ; simpl_colors ; tauto. Qed.

Next Obligation.
Proof.
  destruct stacks ; simpl in *.
  - congruence.
  - destruct Hsr as [ Hsr _ ].
    simpl_colors.
Qed.

Next Obligation.
Proof.
  clear Heq_anonymous Heq_anonymous0 Heq_anonymous1 Hsr wildcard'1 stacks.
  destruct top ; trivial.
  simpl in *.
  induction top ; trivial.
  simpl in *.
  destruct top.
  - rewrite color_preservation ; congruence.
  - destruct wildcard'0 as [ H1 H2 ] ; split.
    + assumption.
    + apply IHtop ; assumption.
Qed. (* well that was laborious *)

Next Obligation.
Proof.
  destruct top.
  - exfalso ; assumption.
  - simpl_colors.
    dependent destruction top ; [ rewrite color_preservation | .. ] ;
    simpl_colors ; discriminate.
Qed.

Next Obligation.
Proof.
  destruct stacks.
  - simpl ; trivial.
  - simpl in *.
    destruct (Stack.color s false) ; try assumption.
    destruct Hsr ; exfalso ; assumption.
Qed.

Next Obligation.
Proof.
  dependent rewrite <- Heq_anonymous.
  remember (do_regularize stacks _ _ _) as s ; clear Heqs.
  split.
  - exact (proj2 (proj2_sig s)).
  - destruct s ; simpl.
    destruct a, x.
    + simpl in H0 |- * ; congruence.
    + simpl in *.
      rewrite H0 in H |- *.
      auto.
Qed.

Next Obligation.
Proof.
  destruct d.
  - simpl in Heq_anonymous |- *.
    rewrite <- Heq_anonymous.
    destruct s ; simpl in *.
    + exfalso ; exact wildcard'.
    + assumption.
  - exfalso ; exact wildcard'.
Qed.

Next Obligation.
Proof.
  remember (do_regularize d _ _ _) as d' ; clear Heqd'.
  exact (proj1 (proj2_sig d')).
Qed.

Ltac trivial_cases :=
  match goal with
  | [ H : Stack.well_formed ?top ?bool, jmeq : [] ~= ?top |- False ] =>
    apply JMeq_eq in jmeq ; subst ; assumption
  | [ H : Stack.well_formed ?top ?bool, jmeq : ?lvl ::: ?yellows ~= ?top
      |- Stack.all_yellows ?yellows ?bool
    ] => apply JMeq_eq in jmeq ; subst ; assumption
  end.

Ltac clean_jmeq :=
  match goal with
  | [ H : ?Pattern ~= ?ident |- _ ] =>
      remember H as H' eqn:Heq ; clear Heq ;
      apply JMeq_eq in H ; subst
  end.

Ltac destruct_lvl_color :=
  match goal with
  | [ |- Level.color ?lvl ?bool <> Red \/ Level.is_empty ?lvl ] =>
    destruct (Level.color lvl bool) eqn:Hcol
  end.

Ltac destruct_yellows :=
  match goal with
  | [ H : Stack.well_formed (?lvl ::: ?Y) ?b
      |- Level.color ?lvl ?bool <> Red \/ Level.is_empty ?lvl
    ] =>
      let yellows := fresh in rename Y into yellows;
      dependent destruction yellows ; simpl in * ;
      destruct_lvl_color ; try solve [
        (left ; discriminate) | (right ; auto) | (exfalso ; assumption)
      ]
  end.

Ltac deduce_next_green :=
  match goal with
  | [ Hreg : regular (?lvl ::: ?yellows ++ ?stacks) ,
      Hcol : Level.color ?lvl ?is_last <> Green
      |- color ?stacks = Green
    ] =>
      simpl in Hreg ; destruct (Level.color lvl is_last) ; [
        (exfalso ; apply Hcol ; trivial) |
        (destruct Hreg ; assumption) |
        (exfalso ; assumption)
      ]
  end.

Local Obligation Tactic := (
  program_simpl ; try clean_jmeq ; try (assumption || destruct_yellows)
).

Inductive front_or_back : Set := Front | Back.

Definition push_helper {A : Set} (elt : A) (pos : front_or_back)
  (lvl : Level.t A) (is_last : bool) p
:=
  match pos with
  | Front => Level.push elt lvl is_last p
  | Back  => Level.inject elt lvl is_last p
  end.

Program Definition push {A : Set} (elt : A) (pos : front_or_back) (d : t A) (p : regular d) :
  { d : t A | regular d }
:=
  match d with
  | << top >> =>
    match top with
    | [] => !
    | Stack.Cons X Y lvl yellows =>
      let elt := eq_rect A (fun T => T) elt X eq_refl in
      let is_last :=
        match yellows with
        | [] => true
        | _ ::: _ => false
        end
      in
      let p := _ in
      let lvl := push_helper elt pos lvl is_last p in
      let d := << lvl ::: yellows >> in
      regularize d _
    end
  | @SeveralLvls B top _ stacks =>
    match top with
    | [] => !
    | Stack.Cons X Y lvl yellows =>
      let elt := eq_rect A (fun T => T) elt X eq_refl in
      let p := _ in
      let lvl := push_helper elt pos lvl false p in
      let stacks := eq_rect B t stacks Y eq_refl in
      let d := lvl ::: yellows ++ stacks in
      regularize d _
    end
  end.

Next Obligation.
Proof.
  remember (push_helper _ pos lvl false _) as lvl' ; simpl.
  assert (Hgbr : green_between_reds stacks) by
    (simpl in p ; clear Heqlvl' lvl';
    dependent destruction yellows ; destruct (Level.color lvl false) ;
    simpl in p ; firstorder).
  destruct pos ;
  dependent destruction yellows; destruct (Level.color lvl' false) eqn:Hcol ;
  try solve [ trivial | (split ; trivial) ] ; (split ; [ .. | trivial ]);
  subst lvl' ; (
    apply Level.red_push_iff_yellow in Hcol ||
    apply Level.red_inject_iff_not_green in Hcol
  ) ; deduce_next_green.
Qed.

Definition pop_helper {A : Set} (pos : front_or_back) (lvl : Level.t A) p :=
  match pos with
  | Front => Level.pop lvl p
  | Back  => Level.eject lvl p
  end.

Program Definition pop {A : Set} pos (d : t A) (p : regular d) :
  option (A * { d : t A | regular d })
:=
  match d with
  | << top >> =>
    match top with
    | [] => !
    | Stack.Cons X Y lvl yellows =>
      match Level.dec_is_empty lvl with
      | left _ => None
      | right NotEmpty  =>
        let (elt, lvl) := pop_helper pos lvl NotEmpty in
        let d := << lvl ::: yellows >> in
        Some (elt, regularize d _)
      end
    end
  | @SeveralLvls B top _ stacks =>
    match top with
    | [] => !
    | Stack.Cons X Y lvl yellows =>
      match Level.dec_is_empty lvl with
      | left _ => None
      | right NotEmpty  =>
        let pair := pop_helper pos lvl NotEmpty in
        let stacks := eq_rect B t stacks Y eq_refl in
        let d := (snd pair) ::: yellows ++ stacks in
        Some (fst pair, regularize d _)
      end
    end
  end.

Next Obligation.
Proof.
  remember (snd (pop_helper pos lvl NotEmpty)) as lvl0 ; simpl.
  assert (Hgbr : green_between_reds stacks) by
    (simpl in p ;
    dependent destruction yellows ; destruct (Level.color lvl false) ;
    simpl in p ; firstorder).
  destruct pos;
  dependent destruction yellows ; destruct (Level.color lvl0 false) eqn:Hcol;
  try solve [ trivial | (split ; trivial) ] ; (split ; [ .. | trivial ]) ;
  subst lvl0 ; (
    apply Level.red_pop_iff_not_green in Hcol ||
    apply Level.red_eject_iff_not_green in Hcol
  ) ; deduce_next_green.
Qed.
