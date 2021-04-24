Require Import List Arith Lia Relation_Operators.

From Undecidability.Shared.Libs.DLW
     Require Import Vec.pos Vec.vec Code.sss.

From Undecidability.MinskyMachines
     Require Import Morita MMA.

Set Implicit Arguments.


Section Translation.

  Require Setoid.

  Local Notation "P // x ->> y" := (sss_compute (@mma_sss _) P x y).
  Local Notation "e #> x" := (vec_pos e x).
  Local Notation "e [ v / x ]" := (vec_change e x v).

  Variable (n : nat).

  Lemma mma_sss_to_quad_sss (p q : nat) (u v : vec nat n) :
    forall (x : mm_instr (pos n)), mma_sss x (p,u) (q,v) ->
    exists (a : quad (pos n)), quad_sss a (p,u) (q,v).
  Proof.
    intros. inversion H; subst.
    - exists (p, x0, Morita.INC, 1+p). constructor.
    - exists (p, x0, Morita.NOP, 1+p). now constructor.
    - exists (p, x0, Morita.DEC, q). now constructor.
  Qed.

  Lemma mma_simul_quad_INC (p q : nat) (i : pos n) (v : vec nat n) :
    exists (P : list (mm_instr (pos n))), (p,P) // (p,v) ->> (q,v[(S (v#>i))/i]).
  Proof.
    intros. exists (INC i :: INC i :: DEC i q :: nil). exists 3.
    apply sss_steps_trans with (n:=2) (st2:=(2+p,v[(S (v#>i))/i][(S (v[(S (v#>i))/i]#>i))/i])).
    - apply sss_steps_trans with (n:=1) (st2:=(1+p,v[(S (v#>i))/i])).
      + apply sss_steps_1.
        exists p. exists nil. exists (INC i). exists (INC i :: DEC i q :: nil). exists v.
        intuition; simpl.
        * f_equal. lia.
        * constructor.
      + apply sss_steps_1.
        exists p. exists (INC i :: nil). exists (INC i). exists (DEC i q :: nil).
        exists (v[(S (v#>i))/i]).
        intuition; simpl.
        * f_equal. lia.
        * constructor.
    - apply sss_steps_1.
      exists p. exists (INC i :: INC i :: nil). exists (DEC i q). exists nil.
      exists (v[(S (S (v#>i)))/i]).
      intuition; simpl.
      + f_equal.
        * lia.
        * rewrite vec_change_eq; try reflexivity.
          now rewrite vec_change_idem.
      + rewrite vec_change_idem. rewrite vec_change_eq; try reflexivity.
        assert (H: v[(S (S (v#>i)))/i][(S (v#>i))/i] = v[(S (v#>i))/i]) by apply vec_change_idem.
        rewrite <- H. constructor. rewrite vec_change_eq; reflexivity.
  Qed.

  Lemma mma_simul_quad_DEC (p q : nat) (i : pos n) (v : vec nat n) (w : nat) :
    v#>i = S w -> exists (P : list (mm_instr (pos n))), (p,P) // (p,v) ->> (q,v[w/i]).
  Proof.
    intros. exists (DEC i q :: nil). exists 1. apply sss_steps_1.
    exists p. exists nil. exists (DEC i q). exists nil. exists v. intuition; simpl.
    - f_equal. lia.
    - now constructor.
  Qed.

  Lemma mma_simul_quad_NOP (p q : nat) (i : pos n) (v : vec nat n) :
    exists (P : list (mm_instr (pos n))), (p,P) // (p,v) ->> (q,v).
  Proof.
    exists (INC i :: DEC i q :: nil). exists 2.
    apply sss_steps_trans with (n:=1) (st2:=(1+p,v[(S (v#>i))/i])).
    - apply sss_steps_1.
      exists p. exists nil. exists (INC i). exists (DEC i q :: nil). exists v.
      intuition; simpl.
      + f_equal. lia.
      + constructor.
    - apply sss_steps_1.
      exists p. exists (INC i :: nil). exists (DEC i q). exists nil. exists (v[(S (v#>i))/i]).
      intuition; simpl.
      + f_equal. lia.
      + assert (H : v[(S (v#>i))/i][(v#>i)/i] = v) by now rewrite vec_change_idem, vec_change_same.
        rewrite <- H at 3. constructor. rewrite vec_change_eq; reflexivity.
  Qed.

  Lemma quad_sss_to_mma_sss (p q : nat) (i : pos n) (u v : vec nat n) :
    forall (x : instr), quad_sss (p,i,x,q) (p,u) (q,v) ->
    exists (P : list (mm_instr (pos n))), (p,P) // (p,u) ->> (q,v).
  Proof.
    intros. inversion H; subst.
    - now apply mma_simul_quad_INC.
    - now apply mma_simul_quad_DEC.
    - now apply mma_simul_quad_NOP.
    - now apply mma_simul_quad_NOP.
    - now apply mma_simul_quad_NOP.
  Qed.

End Translation.
