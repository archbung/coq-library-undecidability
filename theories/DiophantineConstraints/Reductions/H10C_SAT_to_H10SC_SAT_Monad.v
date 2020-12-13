Require Import Datatypes.
Require Import List Lia.
Require Import PeanoNat.
Import ListNotations.

Require Import Undecidability.DiophantineConstraints.H10C.
Require Import Undecidability.DiophantineConstraints.Util.State.

Module Argument.

Section ListFacts.

Lemma list_max_cons : forall a l, list_max (a :: l) = max a (list_max l).
Proof.
  now intros.
Qed.

End ListFacts.

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

Section Reduction.

Context (cs : list h10c).

Definition phi_update (phi : nat -> nat) (n : nat) (v : nat) :=
  fun x => if Nat.eqb x n then v else phi x.

Definition assignment_transformer := (nat -> nat) -> nat -> nat.

Definition transformer_update (n : nat) (v : nat) (F : assignment_transformer) :=
  fun f x => if Nat.eqb x n then v else (F f) x.

Definition ProofState : Set := nat * assignment_transformer.

(* needs 6 fresh variables *)
(* x^2        -> theta x y 0
   y^2        -> theta x y 1
   2z         -> theta x y 2
   x + y      -> theta x y 3
   (x + y)^2  -> theta x y 4
   x^2 + y^2  -> theta x y 5 *)
(* x * y = z if
   2z + x^2 + y^2 = (x + y)^2 *)
Definition h10c_to_h10sc (c : h10c) : State ProofState (list h10sc) :=
  fun s => match c with
           | h10c_one x => ([h10sc_one x], s)
           | h10c_plus x y z => ([h10sc_plus x y z], s)
           | h10c_mult x y z => let '(n, F) := s in
              ([
               h10sc_sqr x (n+1); h10sc_sqr y (n+2); h10sc_plus z z (n+3);
               h10sc_plus x y (n+4); h10sc_sqr (n+4) (n+5);
               h10sc_plus (n+1) (n+2) (n+6); h10sc_plus (n+3) (n+6) (n+5)],
               (n+6, fun phi' =>
                let F1 := transformer_update (n+1) ((F phi') x * (F phi') x) F in
                let F2 := transformer_update (n+2) ((F1 phi') y * (F1 phi') y) F1 in
                let F3 := transformer_update (n+3) ((F2 phi') z + (F2 phi') z) F2 in
                let F4 := transformer_update (n+4) ((F3 phi') x + (F3 phi') y) F3 in
                let F5 := transformer_update (n+5) ((F4 phi') (n+4) * (F4 phi') (n+4)) F4 in
                transformer_update (n+6) ((F5 phi') (n+1) + (F5 phi') (n+2)) F4 phi'))
           end.

Definition max_variable (c : h10c) :=
  match c with
  | h10c_one x => x
  | h10c_plus x y z => max (max x y) z
  | h10c_mult x y z => max (max x y) z
  end.

Definition h10scs_computation :=
  traverse h10c_to_h10sc cs (list_max (map max_variable cs), id).

Definition scs : list h10sc :=
  flat_map id (fst h10scs_computation).

Section Transport.

Context (phi : nat -> nat).

(* Variable assignments for h10sc constraints, given h10c constraints *)
Definition psi :=
  snd (snd h10scs_computation).

Lemma h10c_to_h10sc_spec : Forall (fun c => h10c_sem c phi) cs -> Forall (h10sc_sem (psi phi)) scs.
Proof.
  unfold scs. unfold id. unfold h10scs_computation. unfold psi.
  rewrite Forall_flat_map_iff. induction cs.
  - unfold h10scs_computation. simpl. trivial.
  - Admitted.

End Transport.

Lemma transport : H10C_SAT cs -> H10SC_SAT scs.
  intros [phi H]. exists (psi phi).
  revert H. repeat rewrite <- Forall_forall.
  apply h10c_to_h10sc_spec.
Qed.


Section Reflection.

Context (psi : nat -> nat).

Definition phi (n : nat) := psi n.

Lemma h10sc_to_h10c_spec : Forall (h10sc_sem psi) scs -> Forall (fun c => h10c_sem c phi) cs.
Proof.
  unfold scs. unfold id. unfold h10scs_computation. unfold phi.
  rewrite Forall_flat_map_iff. induction cs.
  - trivial.
  - revert cs. rewrite map_cons, list_max_cons. destruct a; simpl.
    + destruct (traverse h10c_to_h10sc l (max n (list_max (map max_variable l)), id)) eqn:H3. simpl.
      intros. apply Forall_cons_iff. constructor.
      * apply Forall_cons_iff in H as [H1 H2]. apply Forall_cons_iff in H1 as [H1 _].
        simpl. now simpl in H1.
      * apply IHl. apply Forall_cons_iff in H as [_ H1]. (* stuck *) Admitted.

End Reflection.

Lemma reflection : H10SC_SAT scs -> H10C_SAT cs.
Proof.
  intros [psi H]. exists (phi psi).
  revert H. repeat rewrite <- Forall_forall.
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
