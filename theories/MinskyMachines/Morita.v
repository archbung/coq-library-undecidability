From Undecidability.Shared.Libs.DLW
     Require Import Vec.pos Vec.vec Code.sss.

Require Import List Lia.

Set Implicit Arguments.

(** * Morita's k-Counter Machine

    5 type of instructions ("quadruples")

    1/ INC x i j : from i, increment register x by 1 and jump to j
    2/ DEC x i j : from i, decrement register x by 1 and jump to j
    3/ NOP x i j : from i, jump to j leaving x unchanged
    4/ ZER x i j : from i, jump to j if x = 0
    5/ POS x i j : from i, jump to j if x > 0
 *)

Inductive instr : Set := INC | DEC | NOP | ZER | POS.

(* We use a, b, c to range over quadruples and i, j to range over counters *)
Definition quad (I : Set) : Set := (nat * I * instr * nat).

Section Morita_CM.

  (* Number of counters *)
  Variable (k : nat).

  (* We use s, t, u to range over configurations *)
  Definition config := (nat*vec nat k)%type.

  Local Notation "v #> i" := (vec_pos v i).
  Local Notation "v [ w / i ]" := (vec_change v i w).

  (* Semantics of quadruples *)
  Inductive quad_sss : quad (pos k) -> config -> config -> Prop :=
  | in_quad_sss_inc p q i v   :               (p,i,INC,q) // (p,v) -1> (q,v[(S (v#>i)) / i])
  | in_quad_sss_dec p q i v w : v#>i = S w -> (p,i,DEC,q) // (p,v) -1> (q,v[w/i])
  | in_quad_sss_nop p q i v   :               (p,i,NOP,q) // (p,v) -1> (q,v)
  | in_quad_sss_zer p q i v   : v#>i = 0   -> (p,i,ZER,q) // (p,v) -1> (q,v)
  | in_quad_sss_pos p q i v w : v#>i = S w -> (p,i,POS,q) // (p,v) -1> (q,v)
  where "a // s -1> t" := (quad_sss a s t).

  (* Small step semantics of a Morita CM *)
  Inductive cm_sss : list (quad (pos k)) -> config -> config -> Prop :=
  | in_cm_sss a T s t : In a T -> a // s -1> t -> cm_sss T s t.

End Morita_CM.

Definition left_uniq {A B : Type} (R : A -> B -> Prop) :=
  forall x y z, R x z -> R y z -> x = y.

Definition right_uniq {A B : Type} (R : A -> B -> Prop) :=
  forall x y z, R x y -> R x z -> y = z.

Section Intensional_extensional.

  (* Number of counters *)
  Variable (k : nat).

  (* Overlap in domain *)
  Inductive dom_overlap : quad (pos k) -> quad (pos k) -> Prop :=
  | dom_overlap_ctr p i1 i2 x1 x2 q1 q2 :
      i1 <> i2 -> dom_overlap (p,i1,x1,q1) (p,i2,x2,q2)
  | dom_overlap_instr p i1 i2 x q1 q2   :
      dom_overlap (p,i1,x,q1) (p,i2,x,q2)
  | dom_overlap_inc_1 p i1 i2 x q1 q2   :
      dom_overlap (p,i1,INC,q1) (p,i2,x,q2)
  | dom_overlap_dec_1 p i1 i2 x q1 q2   :
      dom_overlap (p,i1,DEC,q1) (p,i2,x,q2)
  | dom_overlap_nop_1 p i1 i2 x q1 q2   :
      dom_overlap (p,i1,NOP,q1) (p,i2,x,q2)
  | dom_overlap_inc_2 p i1 i2 x q1 q2   :
      dom_overlap (p,i1,x,q1) (p,i2,INC,q2)
  | dom_overlap_dec_2 p i1 i2 x q1 q2   :
      dom_overlap (p,i1,x,q1) (p,i2,DEC,q2)
  | dom_overlap_nop_2 p i1 i2 x q1 q2   :
      dom_overlap (p,i1,x,q1) (p,i2,NOP,q2).

  (* Overlap in range *)
  Inductive ran_overlap : quad (pos k) -> quad (pos k) -> Prop :=
  | ran_overlap_ctr p1 p2 i1 i2 x1 x2 q :
      i1 <> i2 -> ran_overlap (p1,i1,x1,q) (p2,i2,x2,q)
  | ran_overlap_instr p1 p2 i1 i2 x q   :
      ran_overlap (p1,i1,x,q) (p2,i2,x,q)
  | ran_overlap_inc_1 p1 p2 i1 i2 x q   :
      ran_overlap (p1,i1,INC,q) (p2,i2,x,q)
  | ran_overlap_dec_1 p1 p2 i1 i2 x q   :
      ran_overlap (p1,i1,DEC,q) (p2,i2,x,q)
  | ran_overlap_nop_1 p1 p2 i1 i2 x q   :
      ran_overlap (p1,i1,NOP,q) (p2,i2,x,q)
  | ran_overlap_inc_2 p1 p2 i1 i2 x q   :
      ran_overlap (p1,i1,x,q) (p2,i2,INC,q)
  | ran_overlap_dec_2 p1 p2 i1 i2 x q   :
      ran_overlap (p1,i1,x,q) (p2,i2,DEC,q)
  | ran_overlap_nop_2 p1 p2 i1 i2 x q   :
      ran_overlap (p1,i1,x,q) (p2,i2,NOP,q).

  (* Morita's intensional notions of determinism and reversibility *)
  Definition ex_dom_overlap (T : list (quad (pos k))) :=
    exists a b, In a T /\ In b T /\ a <> b /\ dom_overlap a b.

  Definition intensional_determinism (T : list (quad (pos k))) :=
    forall a b, In a T -> In b T -> a <> b -> ~ dom_overlap a b.

  Definition ex_ran_overlap (T : list (quad (pos k))) :=
    exists a b, In a T /\ In b T /\ a <> b /\ ran_overlap a b.

  Definition intensional_reversibility (T : list (quad (pos k))) :=
    forall a b, In a T -> In b T -> a <> b -> ~ ran_overlap a b.

  (* Extensional notions of determinism and reversibility *)
  Definition extensional_determinism (T : list (quad (pos k))) := right_uniq (cm_sss T).

  Definition extensional_reversibility (T : list (quad (pos k))) := left_uniq (cm_sss T).

  Lemma intensional_determinism_implies_extensional_determinism (T : list (quad (pos k))) :
    intensional_determinism T -> extensional_determinism T.
  Admitted.

  Lemma vec_plus_inj n (v w x : vec nat n) : vec_plus x v = vec_plus x w -> v = w.
  Admitted.

  Lemma intensional_reversibility_implies_extensional_reversibility (T : list (quad (pos k))) :
    intensional_reversibility T -> extensional_reversibility T.
  Proof.
    (* unfold intensional_reversibility, extensional_reversibility. intros H. *)
    (* unfold left_uniq. intros s t u. *)
    (* assert (Hdec: { s = t } + { s <> t }). *)
    (* - decide equality. *)
    (*   + apply (Vector.eq_dec _ Nat.eqb), PeanoNat.Nat.eqb_eq. *)
    (*   + decide equality. *)
    (* - destruct Hdec. *)
    (*   + now intros. *)
    (*   + intros. exfalso. destruct H0, H1. eapply H. *)
    (*     * exact H0. *)
    (*     * exact H1. *)
    (*     * intros Hneq. subst. apply n. inversion H2; subst; inversion H3; subst. *)
    (*       -- do 2 rewrite vec_change_succ in H9. *)
    (*          apply vec_plus_inj in H9. now rewrite H9. *)
    (*       -- apply vec_change_pred in H4. apply vec_change_pred in H9. *)
    (*          rewrite H4 in H10. rewrite H9 in H10. *)
    (*          rewrite vec_change_succ in H10. *)
    (*          simpl in H10. *)
    (*          simpl. *)
    (*          rewrite vec_change_succ in H10. apply pair_equal_spec in H8 as [H8 H9]. subst. *)
    (*          apply pair_equal_spec in H8 as [_ H9]. *)
    (*          exfalso. discriminate H9. *)
    (*       -- apply pair_equal_spec in H7 as [H7 _]. *)
    (*          apply pair_equal_spec in H7 as [_ H10]. *)
    (*          exfalso. discriminate H10. *)
    (*       -- apply pair_equal_spec in H8 as [H8 H9]. subst. *)
    (*          apply pair_equal_spec in H8 as [_ H11]. *)
    (*          exfalso. discriminate H11. *)
    (*       -- apply pair_equal_spec in H8 as [H8 H9]. subst. *)
    (*          apply pair_equal_spec in H8 as [_ H11]. *)
    (*          exfalso. discriminate H11. *)
    Admitted.

  (* Computes a "normal" Morita CM that is equivalent to the given Morita CM
     but satisfies Morita's notions of determinism.

     IDEA:
     Perhaps some notions of "redundant" quadruples?
     That is, deterministic CMs with overlaps contain quadruples
     in the form of (p,i,ZER,q) for some p, i, q.
   *)
  Lemma normal_morita_determinism (T : list (quad (pos k))) :
    extensional_determinism T -> ex_dom_overlap T ->
      exists M, forall x y, cm_sss T x y <-> cm_sss M x y /\ intensional_determinism M.
  Admitted.

  (* Computes a "normal" Morita CM that is equivalent to the given Morita CM
     but satisfies Morita's notions of reversibility.
   *)
  Lemma normal_morita_reversibility (T : list (quad (pos k))) :
    extensional_reversibility T -> ex_ran_overlap T ->
      exists M, forall x y, cm_sss T x y <-> cm_sss M x y /\ intensional_reversibility M.
  Admitted.

End Intensional_extensional.

Section Morita_CM_problems.

  Notation "P // s ~~> t" := (sss_output (@quad_sss _) P s t).
  Notation "P // s ↓" := (sss_terminates (@quad_sss _) P s).

  (* The set of states is implicit from T *)
  Definition MORITA_CM :=
    { k : nat & { q0 : nat & { qf : nat & { T : list (quad (pos k)) & vec nat k } } } }.

  Definition MORITA_CM_HALTS_ON_ZERO (M : MORITA_CM) :=
    match M with existT _ k (existT _ q0 (existT _ qf (existT _ T v)))
                 => (q0,T) // (q0,v) ~~> (qf,vec_zero) end.

  Definition MORITA_CM_HALTING (M : MORITA_CM) :=
    match M with existT _ k (existT _ q0 (existT _ qf (existT _ T v)))
                 => (q0,T) // (q0, v) ↓ end.

End Morita_CM_problems.
