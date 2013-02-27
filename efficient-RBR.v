Require Import Program.
Require Import Recdef.

Require Import List.

Inductive digit :=
  | zero
  | one
  | two.

Definition nat_of_digit d :=
  match d with
  | zero => 0
  | one  => 1
  | two  => 2
  end.

Definition RBR := list (list digit).

Fixpoint pow2 n :=
  match n with
  | O => 1
  | S i => 2 * pow2 i
  end.

Fixpoint digits (n : RBR) :=
  match n with
  | nil => 0
  | x :: xs => 1 + length x + digits xs
  end.

(* Est-ce [aux] ne peut pas s'exprimer de façon plus simple
   à l'aide de deux itérations imbriquées? *)
Function aux (n : RBR) (i : nat) {measure digits n } : nat :=
  match n with
  | nil => 0
  | nil :: rest => aux rest i
  | (d :: ds) :: rest => (nat_of_digit d) * pow2 i + aux (ds :: rest) (S i)
  end.

Proof. auto. auto. Qed.

Definition back_to_nat (n : RBR) := aux n 0.

Fixpoint zero_first (n : RBR) :=
  match n with
  | nil
  | (zero :: _) :: _ => True
  | _ => False
  end.

Fixpoint only_ones l :=
  match l with
  | nil => True
  | one :: rest => only_ones rest
  | _ => False
  end.

Fixpoint semi_regular (n : RBR) :=
  match n with
  | nil => True
  | (two :: ones)  :: rest => zero_first rest /\ semi_regular rest /\ only_ones ones
  | (zero :: ones) :: rest => semi_regular rest /\ only_ones ones
  | _ => False
  end.

Definition regular (n : RBR) :=
  match n with
  | (one :: ones) :: rest =>
    only_ones ones /\ zero_first rest /\ semi_regular rest
  | rest => zero_first rest /\ semi_regular rest
  end.

Local Obligation Tactic := (program_simpl; intuition; firstorder ; try discriminate).

(* 
   - introduire une notion de "toplevel (semi) regular stack"
   - externaliser la régularisation
 *)
Program Definition succ (n : RBR) (p : regular n) : { r : RBR | regular r } :=
  match n with
  | nil => [[one]]
  | (zero :: ones) :: stacks => 
    match stacks with
    | nil 
    | (zero :: _) :: _ => (one :: ones) :: stacks
    | (two :: tones) :: rest =>
      let rest' :=
        match tones, rest with
        | nil, nil => [[zero ; one]]
        | nil, (zero :: zones) :: rest => (zero :: one :: zones) :: rest
        | one :: ones, _ => [zero] :: (two :: ones) :: rest
        | _, _ => !
        end
      in (one :: ones) :: rest'
    | _ => !
    end
  | (one :: ones)  :: stacks =>
    match ones, stacks with
    | nil, nil => [[zero ; one ]]
    | nil, (zero :: zones) :: rest => (zero :: one :: zones) :: rest
    | one :: ones, rest => [zero] :: (two :: ones) :: rest
    | _, _ => !
    end
  | _ => !
  end.

Next Obligation.
Proof.
  destruct rest.
    destruct tones.
      apply H2 ; reflexivity.
      destruct d ; firstorder. apply H0 with (ones := tones) (wildcard' := []); auto.

    destruct tones ; destruct l ; firstorder.
    destruct d ; firstorder. apply H with (zones := l) (rest0 := rest); auto.
    destruct d ; firstorder. apply H0 with (ones := tones) (wildcard' := (d0 :: l) :: rest); auto.
Qed.

Next Obligation.
Proof.
  (* zero_first *)
  inversion p. inversion H0. inversion H1.
  destruct rest ; destruct ones ; destruct tones ; firstorder.
    destruct d ; firstorder.
    destruct d0 ; firstorder.
    destruct l ; firstorder. destruct d ; firstorder.
    destruct d ; firstorder.
    destruct l ; firstorder. destruct d0 ; firstorder.
    destruct d0 ; firstorder.
  (* semi_regular *)
  inversion p. inversion H0. inversion H1.
  destruct rest ; destruct ones ; destruct tones ; firstorder.
    destruct d; firstorder.
    destruct d0; firstorder.
    destruct l ; firstorder. destruct d ; firstorder.
    destruct d ; firstorder.
    destruct l ; firstorder. destruct d0 ; firstorder.
    destruct d0 ; firstorder.
Qed.

Next Obligation.
Proof.
  destruct stacks ; auto.
  destruct l ; firstorder.
  destruct d ; firstorder.
    apply H with (wildcard' := l) (wildcard'0 := stacks); auto.
    apply H0 with (tones := l) (rest := stacks); auto.
Qed.
    
Next Obligation.
Proof.
  destruct stacks ; destruct ones ; firstorder.
    destruct d ; firstorder. apply H0 with (ones0 := ones) (rest := []); auto.

    destruct l ; firstorder. destruct d ; firstorder.
    apply H with (zones := l) (rest := stacks); auto.

    destruct d; firstorder.
    apply H0 with (ones0 := ones) (rest := l :: stacks); auto.
Qed.

Next Obligation.
Proof.
  destruct n; firstorder.
  destruct l; firstorder.
  destruct d; firstorder.
    apply H with (ones := l) (stacks := n); auto.
    apply H0 with (ones := l) (stacks := n); auto.
Qed.

Ltac my_simpl := simpl ; unfold back_to_nat ; repeat rewrite aux_equation ; simpl.

Ltac unfold_once := rewrite aux_equation ; symmetry ; rewrite aux_equation ; symmetry.

Require Import Arith.

Lemma test : forall l, forall i, aux l (S i) = 2 * aux l i.
Proof.
  intros l i.
  functional induction (aux l i).
    my_simpl ; reflexivity.

    rewrite aux_equation. apply IHn.

    rewrite aux_equation. rewrite mult_plus_distr_l.
    unfold pow2 at 1. fold pow2. repeat rewrite mult_assoc.
    rewrite IHn.
    replace (nat_of_digit d * 2) with (2 * nat_of_digit d).
    reflexivity.
    rewrite mult_comm ; reflexivity.
Qed.

Lemma aux_reg_prefix :
  forall l, forall i, forall l0 l1, aux l0 i = aux l1 i -> aux (l :: l0) i = aux (l :: l1) i.
Proof.
  induction l ; intros.
    unfold_once ; assumption.

    unfold_once. f_equal. 

    apply IHl.
    repeat rewrite test. rewrite H. reflexivity.
Qed.

Theorem succ_valid :
  forall n : RBR, forall p : regular n,
    back_to_nat (proj1_sig (succ n p)) = S (back_to_nat n).
Proof.
  intros.
  destruct n. my_simpl ; reflexivity.
  destruct l.
    inversion p. inversion H0.

  destruct l; destruct d.
    destruct n.
      my_simpl ; reflexivity.

      inversion p ; destruct l ; firstorder.
      destruct d ; firstorder. my_simpl. reflexivity.
      destruct n ; destruct l.
        my_simpl ; reflexivity.
        destruct d ; firstorder ; my_simpl ; reflexivity.
        destruct l0 ; firstorder ; destruct d ; firstorder ; my_simpl ; reflexivity.
        destruct d ; firstorder ; my_simpl ; reflexivity.

    destruct n.
      my_simpl ; reflexivity.
      inversion p ; destruct l ; firstorder.
      destruct d ; firstorder. my_simpl ; reflexivity.
      
    inversion p. inversion H.

    destruct n.
      my_simpl ; reflexivity.

      inversion p ; destruct l0 ; firstorder.
      destruct d ; firstorder. my_simpl ; reflexivity.
      destruct d0 ; firstorder. destruct l0 ; firstorder.
      destruct n ; firstorder.
        simpl. unfold back_to_nat. unfold_once. simpl.
        apply eq_S. apply aux_reg_prefix. my_simpl. reflexivity.

        destruct l0 ; firstorder. destruct d ; firstorder.
        simpl. unfold back_to_nat. unfold_once. simpl.
        apply eq_S. apply aux_reg_prefix. my_simpl. reflexivity.

        destruct d ; firstorder. simpl. unfold back_to_nat.
        unfold_once. simpl. apply eq_S. apply aux_reg_prefix.
        my_simpl. reflexivity.

    inversion p. destruct d0 ; firstorder.
    my_simpl. reflexivity.

    inversion p ; firstorder.
Qed.
