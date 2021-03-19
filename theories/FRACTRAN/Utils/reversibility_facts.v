Require Import List Arith Lia.
Import ListNotations.

From Undecidability.Shared.Libs.DLW Require Import gcd.
From Undecidability.FRACTRAN Require Import FRACTRAN.
From Undecidability.Synthetic Require Import Definitions.

Definition inj {X Y} (R : X -> Y -> Prop) :=
  forall x y z, R x z -> R y z -> x = y.

Definition redundant (l : list (nat*nat)) :=
  exists p1 q1 p2 q2 l1 l2 l3, l = l1 ++ [(p1, q1)] ++ l2 ++ [(p2, q2)] ++ l3 /\ divides q1 q2.

Definition non_redundant (l : list (nat*nat)) :=
  forall p1 q1 p2 q2 l1 l2 l3, l = l1 ++ [(p1, q1)] ++ l2 ++ [(p2, q2)] ++ l3 -> ~ divides q1 q2.

Fact foo l : non_redundant l -> ~ redundant l.
Proof.
  intros Hred [p1 [q1 [p2 [q2 [l1 [l2 [l3 [Hl Hdiv]]]]]]]].
  specialize (Hred p1 q1 p2 q2 l1 l2 l3). now apply Hred in Hl.
Qed.

Lemma redundant_simple_ex p1 q1 p2 : redundant ((p1, q1) :: (p2, 2*q1) :: nil).
Proof.
  exists p1, q1, p2, (2*q1), nil, nil, nil. constructor.
  - now constructor.
  - now exists 2.
Qed.

Lemma fractran_halt_dec_l0 l : length l = 0 -> decidable (fractran_terminates l).
Proof.
  intros H%length_zero_iff_nil.
  exists (fun _ => true). intros x. split.
  - now intros Hf.
  - intros _.
    exists x. split.
    + now exists 0.
    + intros z H2. now destruct H2.
Qed.

Lemma length_one_iff_singleton {X} (l : list X) : length l = 1 <-> exists x, l = [x].
Proof.
  destruct l.
  - simpl. split.
    + intros H. congruence.
    + intros [x H]. congruence.
  - simpl. split.
    + intros [=]. apply length_zero_iff_nil in H0. rewrite H0.
      now exists x.
    + intros [x0]. now inversion H.
Qed.

Search (length _).
Search (divides).

Lemma fractran_halt_dec_l1 l : length l = 1 -> decidable (fractran_terminates l).
Proof.
  intros H%length_one_iff_singleton. destruct H as [(p1,q1) H]. rewrite H.
  unfold decidable. unfold decider. unfold reflects.
  exists (fun x => match x with 0 => false | S _ => if divides_dec p1 q1 then false else true end).
  intros x. split.
  - destruct x.
    + admit.
    + destruct (divides_dec p1 q1).
      * destruct s as [k Hq1]. rewrite Hq1. intros [y [Hxy Hy]].
        exfalso. apply (Hy (y * k)).
        apply in_fractran_0. lia.
      * now intros.
  - destruct x.
    + admit.
    + destruct (divides_dec p1 q1).
      * congruence.
      * intros _. exists (S x).


    intros Hf. destruct q1.
    + simpl. reflexivity.
    + destruct q1.
      * reflexivity.
      *

Lemma baz l : (length l = 0 \/ length l = 1) -> decidable (fractran_terminates l).
Proof.
  intros [H|H]; revert H.
  - apply fractran_halt_dec_l0.
  - apply fractran_halt_dec_l1.
Qed.

Lemma fractran_step_inj_l l : length l <= 1 -> inj (fractran_step l).
Proof.
  split.
  - intros [Hred [|Hlen]] x y z H1 H2.
    + destruct H1 as [q|H1].

Section fractran_step_not_inj.

  Variables (l : list (nat * nat)) (Hl : ge (length l) 2).

  Lemma fractran_step_not_inj : ~ inj (fractran_step l).
  Proof.
    apply dn_1.

End fractran_step_not_inj.
