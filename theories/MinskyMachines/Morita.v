From Undecidability.Shared.Libs.DLW
     Require Import Vec.pos Vec.vec Code.sss.

Require Import List Lia.

Set Implicit Arguments.


Section Vector_Facts.

  Variable (n : nat).

  Local Notation "v #> i" := (vec_pos v i).
  Local Notation "v [ w / i ]" := (vec_change v i w).

  Lemma vec_eq_pos (v w : vec nat n) : v = w -> (forall p, v#>p = w#>p).
  Proof.
    intros H. now rewrite H.
  Qed.

  Lemma vec_plus_inj (v w x : vec nat n) : vec_plus v w = vec_plus v x -> x = w.
  Proof.
    intros H. apply vec_pos_ext. intros p.
    apply vec_eq_pos with (p:=p) in H. do 2 rewrite vec_pos_plus in H. lia.
  Qed.

  Lemma vec_pos_change i (v w : vec nat n) x y :
    v[x/i] = w[y/i] -> v#>i = S x -> w#>i = S y -> v = w.
  Proof.
    intros. apply vec_pos_ext. intros p.
    assert (pdec : { i = p } + { i <> p }).
    - apply pos_eq_dec.
    - destruct pdec as [ pdec | pdec ]; subst; apply vec_eq_pos with (p:=p) in H.
      + do 2 rewrite vec_change_eq in H; try reflexivity.
        subst. now rewrite H1, H0.
      + do 2 rewrite vec_change_neq in H; try exact pdec.
        exact H.
  Qed.

End Vector_Facts.


Section Morita_CM.

  (** * Morita's k-Counter Machine

      5 type of instructions ("quadruples")

      1/ INC x i j : from i, increment register x by 1 and jump to j
      2/ DEC x i j : from i, decrement register x by 1 and jump to j
      3/ NOP x i j : from i, jump to j leaving x unchanged
      4/ ZER x i j : from i, jump to j if x = 0
      5/ POS x i j : from i, jump to j if x > 0
  *)

  Inductive instr : Set := INC | DEC | NOP | ZER | POS.

  (* quadruples and reduced quadruples *)
  Definition quad (I : Set) : Set := (nat * I * instr * nat).

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


Section Morita_Facts.

  Import ListNotations.

  Variable (k : nat).

  Lemma cm_const p i (T : list (quad (pos (S k)))) :
    (forall a, In a T -> (a = (p,i,ZER,p) \/ a = (p,i,POS,p) \/ a = (p,i,NOP,p)))
              -> forall s t, cm_sss T s t -> s = t.
  Proof.
    intros H (p1,v1) (p2,v2) Hcm. inversion Hcm; subst.
    destruct (H a H0) as [H2|[H2|H2]]; rewrite H2 in H1; now inversion H1.
  Qed.

  Lemma config_eq_dec (s t : config k) : { s = t } + { s <> t }.
  Proof.
    decide equality.
    - apply (Vector.eq_dec _ Nat.eqb), PeanoNat.Nat.eqb_eq.
    - decide equality.
  Qed.

End Morita_Facts.


Section Determinism.

  Import ListNotations.

  Variables (k : nat).

  Local Notation "v #> i" := (vec_pos v i).
  Local Notation "v [ w / i ]" := (vec_change v i w).

  (* Morita's notion of domain overlap for quadruples *)
  Inductive dom_overlap : quad (pos (S k)) -> quad (pos (S k)) -> Prop :=
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

  (* Morita's notion of determinism *)
  Definition det_int (T : list (quad (pos (S k)))) :=
    forall a b, In a T -> In b T -> a <> b -> ~ dom_overlap a b.

  (* Extensional determinism *)
  Definition det_ext (T : list (quad (pos (S k)))) :=
    forall s t u, cm_sss T s t -> cm_sss T s u -> t = u.

  Lemma det_int_sound T : det_int T -> det_ext T.
  Proof.
    intros det_int s t u Hst Hsu.
    assert (Hdec : { t = u } + { t <> u }).
    - apply config_eq_dec.
    - destruct Hdec as [Hdec | Hdec].
      + exact Hdec.
      + exfalso. destruct Hst, Hsu.
        apply det_int with (a:=a) (b:=a0); auto.
        * intros H3. apply Hdec.
          destruct H0; subst; inversion H2; subst; try reflexivity.
          revert H8. rewrite H0. intros [=]. now rewrite H3.
        * destruct H0; subst; inversion H2; subst; try eauto using dom_overlap.
          -- apply dom_overlap_ctr. congruence.
          -- apply dom_overlap_ctr. congruence.
  Qed.

  Fact det_int_refl_not : exists T, det_ext T /\ ~ det_int T.
  Proof.
    exists [(0,pos0,ZER,0); (0,pos0,POS,0); (0,pos0,NOP,0)].
    split.
    - intros s t u Hst Hsu.
      apply cm_const with (p:=0) (i:=pos0) in Hst.
      apply cm_const with (p:=0) (i:=pos0) in Hsu.
      + now rewrite <- Hst, Hsu.
      + firstorder.
      + firstorder.
    - intros H. specialize (H (0,pos0,ZER,0) (0,pos0,NOP,0)).
      simpl in H. destruct H; auto.
      + congruence.
      + apply dom_overlap_nop_2.
  Qed.

End Determinism.


Section Reversibility.

  Import ListNotations.

  (* Number of counters *)
  Variable (k : nat).

  Local Notation "v #> i" := (vec_pos v i).
  Local Notation "v [ w / i ]" := (vec_change v i w).

  (* Overlap in range *)
  Inductive ran_overlap : quad (pos (S k)) -> quad (pos (S k)) -> Prop :=
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

  (* Morita's notion of intensional reversibility *)
  Definition rev_int (T : list (quad (pos (S k)))) :=
    forall a b, In a T -> In b T -> a <> b -> ~ ran_overlap a b.

  (* Extensional reversibility *)
  Definition rev_ext (T : list (quad (pos (S k)))) :=
    forall s t u, cm_sss T s u -> cm_sss T t u -> s = t.

  Lemma rev_int_soundness (T : list (quad (pos (S k)))) : rev_int T -> rev_ext T.
  Proof.
    intros rev_int s t u Hsu Htu.
    assert (Hdec : { s = t } + { s <> t }).
    - apply config_eq_dec.
    - destruct Hdec as [Hdec | Hdec].
      + exact Hdec.
      + exfalso. destruct Hsu, Htu. apply rev_int with (a:=a) (b:=a0); auto.
        * intros H3. apply Hdec.
          destruct H0; subst; inversion H2; subst; try reflexivity.
          -- revert H7. do 2 rewrite vec_change_succ.
             intros H7. apply vec_plus_inj in H7. now rewrite H7.
          -- f_equal. apply vec_pos_change with (i:=i) (x:=w) (y:=w0); auto.
        * destruct H0; subst; inversion H2; subst; try eauto using ran_overlap.
          -- apply ran_overlap_ctr. congruence.
          -- apply ran_overlap_ctr. congruence.
  Qed.

  Lemma rev_int_refl_not : exists T, rev_ext T /\ ~ rev_int T.
  Proof.
    exists [(0,pos0,ZER,0); (0,pos0,POS,0); (0,pos0,NOP,0)].
    split.
    - intros (p1,v1) (p2,v2) (p3,v3) Hsu Htu.
      apply cm_const with (p:=0) (i:=pos0) in Hsu.
      apply cm_const with (p:=0) (i:=pos0) in Htu.
      + now rewrite Hsu, Htu.
      + firstorder.
      + firstorder.
    - intros H. specialize (H (0,pos0,ZER,0) (0,pos0,NOP,0)).
      simpl in H. destruct H; auto.
      + congruence.
      + apply ran_overlap_nop_2.
  Qed.

End Reversibility.
