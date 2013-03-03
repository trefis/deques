Require Import Program.
Require Import Recdef.
Require Import Arith.
Require Import Omega.

Ltac rewrite_eq foo := rewrite foo ; symmetry ; rewrite foo ; symmetry.

Require Import List.

Inductive digit :=
  | zero
  | one
  | two.

Definition stack := prod digit nat.

Definition RBR := list stack.

Fixpoint pow2 n :=
  match n with
  | O => 1
  | S i => 2 * pow2 i
  end.

Definition nat_of_digit d :=
  match d with
  | zero => 0
  | one  => 1
  | two  => 2
  end.

Fixpoint helper acc d ones i :=
  let acc := acc + nat_of_digit d * pow2 i in
  match ones with
  | O => (acc, S i)
  | S n => helper acc one n (S i)
  end.

Fixpoint aux i n :=
  match n with
  | nil => 0
  | (d, n) :: rest =>
    let foo := helper 0 d n i in
    (fst foo) + aux (snd foo) rest
  end.

Definition back_to_nat (n : RBR) := aux 0 n.

Fixpoint zero_first (n : RBR) :=
  match n with
  | (two, _) :: _ => False
  | (one, _) :: rest => zero_first rest
  | _ => True
  end.

Fixpoint semi_regular (n : RBR) :=
  match n with
  | nil => True
  | (two, _)  :: rest => zero_first rest /\ semi_regular rest
  | (zero, _) :: rest => semi_regular rest
  | _ => False
  end.

Definition regular (n : RBR) :=
  match n with
  | (one, _) :: rest
  | rest => zero_first rest /\ semi_regular rest
  end.

Lemma always_z_first : forall n, regular n -> zero_first n.
Proof.
  intros.
    destruct n ; firstorder.
    destruct s ; destruct d ; firstorder.
Qed.

Local Obligation Tactic := (program_simpl; intuition; firstorder ; try discriminate).

Program Definition do_regularize stacks (p : semi_regular stacks) : { n | regular n } :=
  match stacks with
  | (one, _) :: _ => !
  | (two, ones) :: stacks =>
    match ones, stacks with
    | 0, nil => [(zero, 1)]
    | 0, (zero, zones) :: rest => (zero, S zones) :: rest
    | S ones, rest => (zero, 0) :: (two, ones) :: rest
    | _, _ => !
    end
  | already_regular => already_regular
  end.

Next Obligation.
Proof.
  destruct ones ; destruct stacks0.
    auto.

    destruct s ; destruct d ; firstorder.
    apply H with (zones := n) (rest := stacks0) ; auto.

    apply H0 with (ones0 := ones) (rest := []) ; auto.

    apply H0 with (ones0 := ones) (rest := s :: stacks0) ; auto.
Qed.

Next Obligation.
  destruct stacks ; firstorder.
  destruct s ; destruct d ; firstorder.
  apply H with (ones := n) (stacks0 := stacks) ; auto.
Qed.

Lemma snd_helper :
  forall n, forall acc1 acc2, forall i, forall d1 d2,
    snd (helper acc1 d1 n i) = snd (helper acc2 d2 n i).
Proof.
  induction n ; intros ; auto.
  simpl. apply IHn.
Qed.

Lemma fst_helper_acc :
  forall n, forall acc, forall d, forall i,
    fst (helper acc d n i) = acc + (fst (helper 0 d n i)).
Proof.
  induction n ; intros.
    auto.
    simpl. rewrite_eq IHn. 
    auto with arith.
Qed.
    
Lemma fst_helper_01 :
  forall n, fst (helper 0 one n 1) = S (S (fst (helper 0 zero n 1))).
Proof.
  destruct n ; auto. 
  simpl; rewrite fst_helper_acc. auto.
Qed.

Theorem do_regularize_valid :
  forall n, forall p : semi_regular n,
    back_to_nat n = back_to_nat (` (do_regularize n p)).
Proof.
  destruct n ; intros ; auto.
  destruct s ; destruct d ; firstorder.
  destruct n0, n ; simpl ; auto.
    destruct s ; destruct d.
      unfold back_to_nat; simpl.
      rewrite snd_helper with (acc2 := 0) (d2 := one).
      rewrite fst_helper_01. auto.
      inversion p ; contradiction.
      inversion p ; contradiction.

    unfold back_to_nat; simpl. f_equal. induction n0 ; auto.

    unfold back_to_nat ; simpl.
    f_equal. induction n0 ; auto.
    rewrite snd_helper with (acc2 := 0) (d2 := two).
    reflexivity.
Qed.

Program Definition regularize top_stack stacks
  (H : fst top_stack = two -> zero_first stacks) (p : semi_regular stacks)
  : { n | regular n } :=
  match top_stack with
  | (zero, _) => top_stack :: stacks
  | (one, _) => top_stack :: do_regularize stacks p
  | _ => do_regularize (top_stack :: stacks) _
  end.

Next Obligation.
Proof.
  apply always_z_first.
  exact (proj2_sig (do_regularize stacks p)).

  destruct stacks ; auto.
  destruct s ; destruct d ; firstorder.
  destruct n0 ; auto.
  destruct stacks ; firstorder.
  destruct s ; destruct d; simpl in * |- *; inversion p; firstorder.
Qed.

Next Obligation.
Proof.
  destruct d0 ; firstorder.
  apply H0 with (wildcard' := n0) ; auto.
Qed.

Lemma pre_snd_test :
  forall ones, forall acc1 acc2, forall d, forall i,
    snd (helper acc1 d ones (S i)) = S (snd (helper acc2 d ones i)).
Proof.
  induction ones ; intros.
    destruct d ; auto.
    simpl. apply IHones.
Qed.

Lemma pre_fst_test :
  forall ones, forall d, forall i,
    fst (helper 0 d ones (S i)) = 2 * fst (helper 0 d ones i).
Proof.
  induction ones ; intros.
    destruct d ; auto. simpl. omega.
    unfold helper ; fold helper.
    rewrite_eq fst_helper_acc.
    rewrite mult_plus_distr_l.
    f_equal.
      induction i.
        simpl. omega.
        unfold pow2 ; fold pow2.
        rewrite mult_plus_distr_l. f_equal.
        repeat rewrite mult_assoc.
        firstorder.
    apply IHones.
Qed.

Lemma test : forall l, forall i, aux (S i) l = 2 * aux i l.
Proof.
  induction l ; intros.
    auto.
    destruct a. unfold aux. fold aux.
    rewrite pre_fst_test. rewrite pre_snd_test with (acc2 := 0).
    rewrite mult_plus_distr_l. f_equal. apply IHl.
Qed.

Lemma test3 : forall d1 d2, forall i, forall n, forall l1 l2,
  aux i ((d1, n) :: l1) = aux i ((d1, n) :: l2)
  -> aux i ((d2, S n) :: l1) = aux i ((d2, S n) :: l2).
Proof.
  intros.
  unfold aux in H; fold aux in H.
  apply plus_reg_l in H.
  simpl ; f_equal.
  rewrite snd_helper with (acc2 := 0) (d2 := d1).
  rewrite pre_snd_test with (acc2 := 0).
  rewrite_eq test.
  auto.
Qed.

Lemma aux_reg_prefix :
  forall n, forall d, forall i, forall l0 l1,
    aux i l0 = aux i l1 -> aux i ((d, n) :: l0) = aux i ((d, n) :: l1).
Proof.
  induction d, i ; intros ; 
      induction n;
        try solve [
          ( apply test3 with (d1 := zero) ; apply IHn ; apply H ) |
          ( apply test3 with (d1 := one) ; apply IHn ; apply H ) |
          ( apply test3 with (d1 := two) ; apply IHn ; apply H ) |
          ( simpl ; rewrite_eq test ; auto )
        ].
Qed.

Lemma back_to_nat_reg_prefix :
  forall d, forall n, forall l0 l1,
    back_to_nat l0 = back_to_nat l1
    -> back_to_nat ((d, n) :: l0) = back_to_nat ((d, n) :: l1).
Proof.
  intros.
  apply aux_reg_prefix.
  auto.
Qed.

Theorem regularize_valid :
  forall x, forall xs, forall h, forall p,
    back_to_nat (x :: xs) = back_to_nat (` (regularize x xs h p)).
Proof.
  intros.
  destruct x; destruct d.
    simpl ; reflexivity.

    unfold regularize, proj1_sig.
    apply back_to_nat_reg_prefix.
    apply do_regularize_valid.
      
    unfold regularize, proj1_sig.
    apply do_regularize_valid.
Qed.

Program Definition succ n (p : regular n) : { m | regular m } :=
  match n with
  | nil => [(one, 0)]
  | (zero, ones) :: rest => regularize (one, ones) rest _ _
  | (one,  ones) :: rest => regularize (two, ones) rest _ _
  | (two, _) :: _ => !
  end.

Theorem succ_valid :
  forall n : RBR, forall p : regular n,
    back_to_nat (` (succ n p)) = S (back_to_nat n).
Proof.
  intros.
  destruct n ; auto.
  destruct s ; destruct d.
    unfold succ. rewrite <- regularize_valid. unfold back_to_nat ; simpl.
    rewrite snd_helper with (acc2 := 0) (d2 := zero).
    rewrite <- plus_Sn_m; (destruct n0 ; auto) . simpl; rewrite fst_helper_acc;
    trivial.

    unfold succ ; rewrite <- regularize_valid ; unfold back_to_nat ; simpl.
    rewrite snd_helper with (acc2 := 0) (d2 := one).
    rewrite <- plus_Sn_m; (destruct n0 ; auto) ; simpl; rewrite_eq fst_helper_acc;
    trivial.

    inversion p ; contradiction.
Qed.
