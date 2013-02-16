Require Import Program.

Inductive RBR : Set :=
  | nil  : RBR
  | zero : RBR -> RBR
  | one  : RBR -> RBR
  | two  : RBR -> RBR.

Fixpoint pow2 (n:nat) : nat :=
  match n with
  | O => 1
  | S i => 2 * pow2 i
  end.

Fixpoint back_to_nat shift n :=
  match n with
  | nil => 0
  | zero rest => back_to_nat (S shift) rest
  | one  rest => pow2 shift + back_to_nat (S shift) rest
  | two  rest => pow2 (S shift) + back_to_nat (S shift) rest
  end.

Fixpoint z_before_t (n : RBR) : Prop :=
  match n with
  | one rest => z_before_t rest
  | two _ => False
  | _ => True
  end.

Fixpoint semi_regular (n : RBR) : Prop :=
  match n with
  | nil => True
  | two rest => z_before_t rest /\ semi_regular rest
  | one rest | zero rest => semi_regular rest
  end.

Definition regular (n : RBR) := z_before_t n /\ semi_regular n.

Lemma z_invert_t :
  forall n, regular n <-> regular (zero (two n)).
Proof.
  split ; intro.
    unfold regular. split.
      simpl. trivial.
      simpl. assumption.

    unfold regular in H. inversion H. clear H. clear H0.
    unfold semi_regular in H1. fold semi_regular in H1.
    assumption.
Qed.

Fixpoint regularize (n : RBR) :=
  match n with
  | two (zero rest) => zero (one rest)
  | two (one  rest) => zero (two rest)
  | two nil  => zero (one nil)
  | one rest => one (regularize rest)
  (* assumption : [2 :: 2 :: ...] can never be seen here *)
  | already_regular => already_regular
  end.

Theorem regular_after_regularize :
  forall n:RBR, semi_regular n -> regular (regularize n).
Proof.
  induction n ; intro.
    (* n = 0 *)
    simpl. constructor. constructor. assumption.
    simpl. constructor. constructor. assumption.
    (* n = 1 *)
    unfold semi_regular in H. fold semi_regular in H.
    apply IHn in H. inversion H.
    simpl. constructor ; simpl ; assumption.
    (* n = 2 *)
    unfold semi_regular in H. fold semi_regular in H. inversion H. clear H.
    destruct n.
      auto. auto.

      simpl. rewrite <- z_invert_t.
      unfold semi_regular in H1. fold semi_regular in H1.
      unfold z_before_t in H0. fold z_before_t in H0.
      constructor ; assumption.

      unfold z_before_t in H0. exfalso. assumption.
Qed.

Lemma plus_reg_l_inv : forall n m p:nat, n = m -> p + n = p + m.
Admitted. (* why isn't plus_reg_l an equivalence in the Coq stdlib ? *)

Theorem regularize_valid :
  forall n, forall i, back_to_nat i n = back_to_nat i (regularize n).
Proof.
  induction n ; intro ; simpl.
    reflexivity.
    reflexivity.
    auto.
    destruct n.
      auto.
      auto.
      simpl. admit. (* can't apply plus_n_O nor plus_reg_l_inv :/ *)
      simpl. trivial.
Qed.

Program Definition succ (n : RBR) (p : regular n) : RBR :=
  match n with
  | nil => one nil
  | zero rest => regularize (one rest)
  | one  rest => regularize (two rest)
  | two _ => !
  end.

Obligation 1.
Proof.
  inversion p.
  inversion H.
Qed.

Lemma ones_are_useless : forall n, regular n <-> regular (one n).
Proof.
  split ; intros.
    (* -> *)
    inversion H. constructor ; simpl ; assumption.
    (* <- *)
    inversion H. 
    unfold z_before_t in H0. fold z_before_t in H0.
    unfold semi_regular in H1. fold semi_regular in H1.
    assumption.
Qed.

Theorem succ_result_is_regular : forall n, forall proof, regular (succ n proof).
Proof.
  intros.
  destruct n.
    (* n = 0 *)
    auto.
    (* n = 2 * n' *)
    simpl. unfold regular in proof. inversion proof.
    unfold semi_regular in H0. fold semi_regular in H0.
    apply regular_after_regularize in H0. inversion H0.
    constructor ; simpl ; assumption.
    (* n = 2 * n' + 1 *)
    simpl. destruct n.
      auto. auto.
      rewrite <- z_invert_t. repeat apply ones_are_useless in proof. assumption.
      inversion proof. inversion H.
    (* n = 2 * n' + 2 *)
    inversion proof. inversion H.
Qed.

Theorem succ_valid :
  forall n, forall p, S (back_to_nat 0 n) = back_to_nat 0 (succ n p).
Proof.
  intros.
  destruct n.
    (* n = 0 *)
    simpl. reflexivity.
    (* n = 2 * n' *)
    simpl. rewrite regularize_valid. reflexivity.
    (* n = 2 * n' + 1 *)
    simpl. destruct n ; auto.
    (* n = 2 * n' + 2 *)
    inversion p. inversion H.
Qed.
