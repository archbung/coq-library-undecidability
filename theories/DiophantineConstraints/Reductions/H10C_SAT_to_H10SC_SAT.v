Require Import  List Lia.
Require Import PeanoNat.
Import ListNotations.

Require Import Undecidability.DiophantineConstraints.H10C.

Module Argument.

Section ListFacts.

Lemma Forall_cons_iff {T : Type} {P} : forall (l : list T) (a : T), Forall P (a :: l) <-> P a /\ Forall P l.
Proof.
  split; intros.
  - now inversion H.
  - now constructor.
Qed.

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

End ListFacts.

Definition sat_sc psi l := Forall (h10sc_sem psi) l.

Lemma sat_sc_app {psi l1 l2} : sat_sc psi (l1 ++ l2) <-> sat_sc psi l1 /\ sat_sc psi l2.
Proof.
  unfold sat_sc. apply Forall_app.
Qed.

Lemma sat_sc_cons {psi c l} : sat_sc psi (c :: l) <-> h10sc_sem psi c /\ sat_sc psi l.
Proof.
  unfold sat_sc. apply Forall_cons_iff.
Qed.

Lemma sat_sc_singleton {psi c} : sat_sc psi [c] <-> h10sc_sem psi c.
Proof.
  unfold sat_sc. split; intros.
  - now apply Forall_cons_iff in H.
  - now apply Forall_cons_iff.
Qed.

Definition compatible (f psi : nat -> nat) l := forall i, nth i l (psi (f i)) = psi (f i).

Lemma compatible_cons {f psi n l} :
  compatible f psi (n :: l) <-> psi (f 0) = n /\ compatible (fun i => f (1 + i)) psi l.
Proof.
  split.
  - constructor.
    + specialize (H 0). simpl in H. now rewrite H.
    + intros i. specialize (H (1 + i)). now apply H.
  - intros [H1 H2]. unfold compatible. intros [ |i].
    + now simpl.
    + simpl. now apply H2.
Qed.

Lemma compatible_app {f psi l1 l2} :
  compatible f psi (l1 ++ l2) <-> compatible f psi l1 /\ compatible (fun i => f (length l1 + i)) psi l2.
Proof.
  split.
  - induction l1.
    + simpl. intros H. split.
      * intros [|i]; reflexivity.
      * apply H.
    + intros H. simpl app in H. apply compatible_cons in H. split.
      * intros i. induction i.
        -- now simpl.
        -- Admitted.

(* bijection from nat * nat to nat using the Cantor pairing function *)
Definition encode '(x, y) : nat :=
  (x + y) * (x + y + 1) / 2 + y.

(* bijection from nat to nat * nat *)
Definition decode (n : nat) : nat * nat :=
  let w := (Nat.sqrt (8 * n + 1) - 1) / 2 in
  let t := (w * w + w) / 2 in
  let y := n - t in
  (w - y, y).

Lemma decode_encode {z : nat * nat} : decode (encode z) = z.
Admitted.

Definition express_one (x : nat) (f : nat -> nat) :=
  [h10sc_one x].

Lemma express_one_elim x f psi : sat_sc psi (express_one x f) -> psi x = 1.
Proof.
  intros H. now apply sat_sc_singleton in H.
Qed.

Definition express_plus (x y z : nat) (f : nat -> nat) :=
  [h10sc_plus x y z].

Lemma express_plus_elim x y z f psi : sat_sc psi (express_plus x y z f) -> psi x + psi y = psi z.
Proof.
  intros H. now apply sat_sc_singleton in H.
Qed.

(* needs 7 fresh variables *)
(* x * y = z if
   z + z + y * y + x * x = (x + y) * (x + y)*)

Definition express_mult (x y z : nat) (f : nat -> nat) :=
  [h10sc_plus z z (f 2); h10sc_sqr y (f 1); h10sc_sqr x (f 0); h10sc_plus (f 2) (f 1) (f 3);
   h10sc_plus (f 3) (f 0) (f 4); h10sc_plus x y (f 5); h10sc_sqr (f 5) (f 4)].

Lemma express_mult_elim x y z f psi : sat_sc psi (express_mult x y z f) -> psi x * psi y = psi z.
Proof.
  intros H.
  apply Forall_cons_iff in H as [H1 H].
  apply Forall_cons_iff in H as [H2 H].
  apply Forall_cons_iff in H as [H3 H].
  apply Forall_cons_iff in H as [H4 H].
  apply Forall_cons_iff in H as [H5 H].
  apply Forall_cons_iff in H as [H6 H7].
  apply sat_sc_singleton in H7.
  unfold h10sc_sem in H1, H2, H3, H4, H5, H6, H7.
  nia.
Qed.

Definition embed '(x, y, z, i, j) : nat :=
  encode (encode (encode (encode (x, y), z), i), j).

Definition unembed (n : nat) :=
  let (xyzi, j) := decode n in
  let (xyz, i) := decode xyzi in
  let (xy, z) := decode xyz in
  let (x, y) := decode xy in
  (x, y, z, i, j).

Lemma unembed_embed {c : nat * nat * nat * nat * nat} : unembed (embed c) = c.
Proof.
  destruct c as [[[[? ?] ?] ?] ?].
  unfold embed. unfold unembed.
  now repeat rewrite decode_encode.
Qed.

Definition h10c_to_h10sc (c : h10c) : list h10sc :=
  let h x := embed (x, 0, 0, 0, 0) in
  match c with
    | h10c_one x => express_one (h x) (fun i => embed (x, 0, 0, 1, i))
    | h10c_plus x y z => express_plus (h x) (h y) (h z) (fun i => embed (x, y, z, 2, i))
    | h10c_mult x y z => express_mult (h x) (h y) (h z) (fun i => embed (x, y, z, 3, i))
  end.

Lemma transport (l : list h10c) : H10C_SAT l -> H10SC_SAT (flat_map h10c_to_h10sc l).
Admitted.

Lemma reflection (l : list h10c) : H10SC_SAT (flat_map h10c_to_h10sc l) -> H10C_SAT l.
Proof.
  intros [psi Hpsi]. apply Forall_forall in Hpsi.
  pose (h x := embed (x, 0, 0, 0, 0)).
  pose (phi x := psi (h x)).
  exists phi. induction l; revert Hpsi.
  - firstorder.
  - simpl flat_map. intros Hpsi. apply Forall_app in Hpsi. intros c [H1|H2].
    + destruct c.
      * rewrite H1 in Hpsi. apply (express_one_elim (h n) (fun i => embed (n, 0, 0, 1, i))).
        apply Hpsi.
      * rewrite H1 in Hpsi.
        apply (express_plus_elim (h n) (h n0) (h n1) (fun i => embed (n, n0, n1, 2, i))).
        apply Hpsi.
      * rewrite H1 in Hpsi.
        apply (express_mult_elim (h n) (h n0) (h n1) (fun i => embed (n, n0, n1, 3, i))).
        apply Hpsi.
    + now apply IHl.
Qed.

End Argument.

Require Import Undecidability.Synthetic.Definitions.

Theorem reduction : reduces H10C_SAT H10SC_SAT.
Proof.
  exists (flat_map Argument.h10c_to_h10sc).
  intro l. constructor.
  - exact (Argument.transport l).
  - exact (Argument.reflection l).
Qed.
