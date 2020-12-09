Require Import  List Lia.
Require Import PeanoNat.
Import ListNotations.

Require Import Undecidability.DiophantineConstraints.H10C.


Module Argument.

Lemma Forall_cons_iff {T : Type} {P} : forall (l : list T) (a : T), Forall P (a :: l) <-> P a /\ Forall P l.
Proof.
  split; intros.
  - now inversion H.
  - now constructor.
Qed.

(* Forall_app l1 l2 : Forall (l1 ++ l2) <-> Forall l1 /\ Forall l2*)

Lemma Forall_flat_map_iff {T U : Type} {P} {ds : list U} {f : U -> list T} :
  Forall P (flat_map f ds) <-> Forall (fun d => Forall P (f d)) ds.
Proof.
  split; intros.
  - induction ds; simpl.
    + firstorder.
    + simpl in H. apply Forall_app in H. apply Forall_cons_iff. firstorder.
  - induction ds; simpl.
    + firstorder.
    + apply Forall_cons_iff in H. apply Forall_app. firstorder.
Qed.

(* bijection from nat * nat to nat using the Cantor pairing function *)
Definition encode '(x, y) : nat :=
  y + (nat_rec _ 0 (fun i m => (S i) + m) (y + x)).

(* bijection from nat to nat * nat *)
Definition decode (n : nat) : nat * nat :=
  nat_rec _ (0, 0) (fun _ '(x, y) => match x with O => (S y, 0) | S x => (x, S y) end) n.

Lemma decode_encode {z : nat * nat} : decode (encode z) = z.
Proof.
  remember (encode z) eqn:H. revert z H. induction n as [|n IH].
  - destruct z as [[|?] [|?]]; now simpl.
  - destruct z as [x y]. destruct y; simpl.
    + destruct x; simpl; try congruence; intros [=].
      rewrite (IH (0, x)); simpl; try reflexivity.
      now rewrite H0, Nat.add_0_r.
    + intros [=]. rewrite (IH (S x, y)); simpl; try reflexivity.
      now rewrite Nat.add_succ_r, H0.
Qed.

Opaque encode decode.

Section Reduction.

Context (cs : list h10c).

(* Original variable renaming *)
Definition tau (x : nat) := encode (x, 0).

(* Mapped variable renaming *)
Definition theta (x y t : nat) := encode (x, 1 + encode (y, t)).

(* needs 6 fresh variables *)
(* x^2        -> theta x y 0
   y^2        -> theta x y 1
   2z         -> theta x y 2
   x + y      -> theta x y 3
   (x + y)^2  -> theta x y 4
   x^2 + y^2  -> theta x y 5 *)
(* x * y = z if
   2z + x^2 + y^2 = (x + y)^2 *)
Definition h10c_to_h10cs (c : h10c) : list h10sc :=
  match c with
  | h10c_one x => [h10sc_one (tau x)]
  | h10c_plus x y z => [h10sc_plus (tau x) (tau y) (tau z)]
  | h10c_mult x y z => [
      h10sc_sqr (tau x) (theta x y 0);
      h10sc_sqr (tau y) (theta x y 1);
      h10sc_plus (tau z) (tau z) (theta x y 2);
      h10sc_plus (tau x) (tau y) (theta x y 3);
      h10sc_sqr (theta x y 3) (theta x y 4);
      h10sc_plus (theta x y 0) (theta x y 1) (theta x y 5);
      h10sc_plus (theta x y 2) (theta x y 5) (theta x y 4)]
  end.

Definition scs := flat_map h10c_to_h10cs cs.

Section Transport.

(* Solution to a given set of H10C *)
Context (phi : nat -> nat) (H : forall c, In c cs -> h10c_sem c phi).

(* Construct a solution to a given set of H10SC given a solution of H10C *)
Definition psi (n : nat) :=
  match decode n with
  | (x, 0) => phi x
  | (x, S m) =>
    match decode m with
    | (y, 0) => (phi x) * (phi x)
    | (y, 1) => (phi y) * (phi y)
    | (y, 2) => ((phi x) * (phi y)) + ((phi x) * (phi y))
    | (y, 3) => (phi x) + (phi y)
    | (y, 4) => ((phi x) + (phi y)) * ((phi x) + (phi y))
    | (y, 5) => ((phi x) * (phi x)) + ((phi y) * (phi y))
    | (_, _) => 0
    end
  end.

Arguments psi /.
Arguments tau /.
Arguments theta /.

Lemma h10c_to_h10sc_spec {c} : h10c_sem c phi -> Forall (h10sc_sem psi) (h10c_to_h10cs c).
Proof.
  destruct c; simpl.
  - intros H1. constructor; simpl; try trivial.
    now rewrite decode_encode.
  - intros H1. constructor; try trivial.
    simpl. now repeat rewrite decode_encode.
  - intros H1. repeat constructor; repeat (simpl; rewrite decode_encode); nia.
Qed.

End Transport.

Lemma transport : H10C_SAT cs -> H10SC_SAT scs.
Proof.
  intros [phi H]. exists (psi phi).
  revert H. repeat rewrite <- Forall_forall.
  unfold scs.
  intros H. apply Forall_flat_map_iff.
  revert H. apply Forall_impl.
  apply h10c_to_h10sc_spec.
Qed.

Section Reflection.

Context (psi : nat -> nat) (H : forall c, In c scs -> h10sc_sem psi c).

Definition phi (n : nat) := psi (tau n).

Lemma h10sc_to_h10c_spec {c} : Forall (h10sc_sem psi) (h10c_to_h10cs c) -> h10c_sem c phi.
Proof.
  destruct c; simpl; try (intros H1; apply Forall_cons_iff in H1; now simpl in H1). intros H1.
  unfold phi.
  apply Forall_cons_iff in H1 as [H1 H2].
  apply Forall_cons_iff in H2 as [H2 H3].
  apply Forall_cons_iff in H3 as [H3 H4].
  apply Forall_cons_iff in H4 as [H4 H5].
  apply Forall_cons_iff in H5 as [H5 H6].
  apply Forall_cons_iff in H6 as [H6 H7].
  apply Forall_cons_iff in H7 as [H7 H8].
  unfold h10sc_sem in H1.
  unfold h10sc_sem in H2.
  unfold h10sc_sem in H3.
  unfold h10sc_sem in H4.
  unfold h10sc_sem in H5.
  unfold h10sc_sem in H6.
  unfold h10sc_sem in H7.
  nia.
Qed.

End Reflection.

Lemma reflection : H10SC_SAT scs -> H10C_SAT cs.
Proof.
  intros [psi H]. exists (phi psi).
  revert H. repeat rewrite <- Forall_forall.
  unfold scs.
  intros H. apply Forall_flat_map_iff in H.
  revert H. apply Forall_impl.
  apply h10sc_to_h10c_spec.
Qed.

End Reduction.

End Argument.

Require Import Undecidability.Synthetic.Definitions.

Theorem reduction : reduces H10C_SAT H10SC_SAT.
Proof.
  exists (fun cs => Argument.scs cs).
  intro l. constructor.
  - exact (Argument.transport l).
  - exact (Argument.reflection l).
Qed.
