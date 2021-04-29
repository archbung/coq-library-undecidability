Require Import List Arith Lia Permutation.
Import ListNotations.

From Undecidability.Shared.Libs.DLW
     Require Import gcd prime Utils.utils_tac.

From Undecidability.FRACTRAN
     Require Import FRACTRAN fractran_utils.

From Undecidability.Synthetic
     Require Import Definitions.

Section ListFacts.

  Lemma length_one_iff_singleton {X} (l : list X) : length l = 1 <-> exists x, l = [x].
  Proof.
    destruct l; simpl; split.
    - intros H. congruence.
    - intros [x H]. congruence.
    - intros [=]. apply length_zero_iff_nil in H0. exists x. now rewrite H0.
    - intros [y]. now inversion H.
  Qed.

  Lemma length_at_least_0 {X} (l : list X) : length l >= 0.
  Proof.
    induction l as [|a l IHl]; simpl; lia.
  Qed.

End ListFacts.

(* Some facts about prime factors due to Andrej *)
Section Prime_factors.

  Lemma count_occ_app H (n : nat) l1 l2:
    count_occ H (l1 ++ l2) n =
    count_occ H l1 n + count_occ H l2 n.
  Proof.
    revert l2. induction l1; [easy|].
    intro l2. cbn. rewrite IHl1.
    now destruct (H a n).
  Qed.

  Notation lprod := (fold_right mult 1).
  Infix "<d" := divides (at level 70, no associativity).

  Fact lprod_insert a ld l1c l2c :
    lprod (ld) <d lprod (l1c ++ l2c) -> lprod (a :: ld) <d lprod (l1c ++ a :: l2c).
  Proof.
    rewrite !lprod_app. cbn. unfold divides.
    intros [p Hp]. exists p. nia.
  Qed.

  Lemma prime_key_div {lc ld} :
    ~ (divides (lprod ld) (lprod lc)) ->
    Forall prime lc -> Forall prime ld ->
    exists (p : nat), prime p /\ count_occ Nat.eq_dec lc p < count_occ Nat.eq_dec ld p.
  Proof.
    revert lc. induction ld as [|a ld IHld].
    - intros lc H. exfalso. apply H.
      exists (lprod lc). cbn. lia.
    - intros lc H Hlc Hld'.
      pose proof (Ha := Forall_inv Hld').
      pose proof (Hld := Forall_inv_tail Hld').
      destruct (in_dec Nat.eq_dec a lc) as [Halc|Halc].
      + apply in_split in Halc as [l1c [l2c ?]]. subst lc.
        assert (H' : not (lprod (ld) <d lprod (l1c ++ l2c)))
          by now intros ?%(lprod_insert a).
        assert (H'lc : Forall prime (l1c ++ l2c)).
        { revert Hlc. rewrite !Forall_app.
          now intros [? ? %Forall_inv_tail]. }
        specialize (IHld _ H' H'lc Hld).
        destruct IHld as [p [? Hp]].
        exists p. split; [assumption|].
        revert Hp. rewrite !count_occ_app. cbn.
        destruct (Nat.eq_dec); lia.
      + exists a. split; [assumption|].
        apply (count_occ_not_In Nat.eq_dec) in Halc.
        rewrite count_occ_cons_eq, Halc; lia.
  Qed.

  Definition count_pow (p n : nat) : nat :=
    let (l, _) := (@prime_decomp (S n) (Nat.neq_succ_0 n))
     in count_occ Nat.eq_dec l p.

  Infix "~p" := (@Permutation _) (at level 70).

  Lemma Permutation_count_occ x l1 l2 : l1 ~p l2 ->
    count_occ Nat.eq_dec l1 x = count_occ Nat.eq_dec l2 x.
  Proof.
    revert l2. induction l1.
    - intros l2. cbn. intros ? %Permutation_nil. now subst.
    - intros l2. intros H %Permutation_sym.
      pose proof (H' := H).
      apply Permutation_vs_cons_inv in H' as [l2' [l2'' ?]]. subst.
      apply Permutation_sym, Permutation_cons_app_inv, IHl1 in H.
      rewrite count_occ_app in H.
      cbn. destruct Nat.eq_dec.
      + rewrite count_occ_app. cbn.
        destruct Nat.eq_dec; lia.
      + rewrite count_occ_app. cbn.
        destruct Nat.eq_dec; lia.
  Qed.

  Lemma prime_key_div' c d (Hc : c <> 0) (Hd : d <> 0) :
    ~ (divides d c) ->
    exists p,
      (forall x y (Hx : x <> 0) (Hy : y <> 0),
        x * c = y * d -> count_pow p (pred y) < count_pow p (pred x)).
  Proof.
    pose proof (@prime_decomp c Hc) as [lc [Hclc Hlc]].
    pose proof (@prime_decomp d Hd) as [ld [Hdld Hld]].
    subst. intros H. apply prime_key_div in H as [p [? Hp]]; [|assumption ..].
    exists p. intros x y Hx Hy. unfold count_pow.
    destruct (@prime_decomp (S (pred x)) _) as [lx [Hxlx Hlx]].
    destruct (@prime_decomp (S (pred y)) _) as [ly [Hyly Hly]].
    assert (S (pred x) = x) as H'x by lia.
    assert (S (pred y) = y) as H'y by lia.
    rewrite H'x in Hxlx. rewrite H'y in Hyly.
    subst. rewrite <- !lprod_app.
    intros E. apply prime_decomp_uniq in E; [|now rewrite Forall_app ..].
    apply (Permutation_count_occ p) in E. rewrite !count_occ_app in E. lia.
  Qed.

End Prime_factors.

Section Fractran_Facts.

  Lemma fractran_step_zero y l (Hl : l <> nil) (Hlreg : fractran_regular l) :
    l /F/ 0 → y <-> y = 0.
  Proof.
    split.
    - induction l as [|(c,d) l IHl]; [congruence|]. inversion 1; subst.
      + apply Forall_inv in Hlreg. simpl in Hlreg. lia.
      + apply IHl; auto.
        * intros H2; subst. inversion H6.
        * now apply Forall_inv_tail with (a:=(c,d)).
    - intros ->. destruct l as [|(p,q) l]; [congruence|].
      constructor. lia.
  Qed.

  Lemma fractran_steps_zero x l (Hl : l <> nil) (Hlreg : fractran_regular l) :
    forall n, fractran_steps l n 0 x <-> x = 0.
  Proof.
    induction n as [|n IHn]; simpl; [split; auto|]. split.
    - intros [y [Hy Hs]]. apply IHn. apply fractran_step_zero in Hy; subst; auto.
    - intros ->. exists 0. split; [|now apply IHn].
      apply fractran_step_zero; auto.
  Qed.

  Corollary fractran_nstop_zero l (Hl : l <> nil) (Hlreg : fractran_regular l) :
    ~ l /F/ 0 ↓.
  Proof.
    intros [y [[n Hy] Hstop]]. apply fractran_steps_zero in Hy; subst; auto.
    destruct l as [| (c,d) l]; subst; [congruence|].
    apply (Hstop 0). constructor. lia.
  Qed.

  Corollary fractran_singleton_steps_zero x c d (Hd : d <> 0) :
    forall n, fractran_steps [(c,d)] n 0 x <-> x = 0.
  Proof.
    apply fractran_steps_zero; [congruence|].
    constructor; auto.
  Qed.

  Corollary fractran_singleton_nstop_zero c d (Hd : d <> 0) : ~ [(c,d)] /F/ 0 ↓.
  Proof.
    apply fractran_nstop_zero; [congruence|].
    apply Forall_cons; auto.
  Qed.

  Lemma fractran_step_nzero x y c d (Hx : x <> 0) (Hc : c <> 0) (Hd : d <> 0) :
    [(c,d)] /F/ x → y -> y <> 0.
  Proof.
    inversion 1; subst.
    - lia.
    - inversion H6.
  Qed.

  Lemma fractran_singleton_ndiv_stop_S x c d (Hx : x <> 0) (Hc : c <> 0) (Hd : d <> 0) :
    ~ divides d c -> [(c,d)] /F/ x ↓.
  Proof.
    intros Hndiv%prime_key_div'; [|exact Hc|exact Hd].
    destruct Hndiv as [p H]. revert Hx.
    induction on x as IH with measure (count_pow p (pred x)).
    intros Hx. destruct (fractran_step_dec [(c,d)] x) as [[y Hxy]|Hs].
    - assert (Hy : y <> 0) by (apply (fractran_step_nzero x _ c d); auto).
      inversion Hxy; subst.
      + specialize (H x y Hx Hy ltac: (lia)). specialize (IH y).
        apply IH in H as [y' [[n Hyy'] Hs']]; [|exact Hy]. exists y'. split; [|exact Hs'].
        exists (1+n). simpl. exists y. auto.
      + inversion H6.
    - exists x. split; [|exact Hs].
      exists 0. now simpl.
  Qed.

  Lemma redundant_fractran_step l1 l2 l3 c1 d1 c2 d2 x y : divides d1 d2 ->
    l1 ++ [(c1,d1)] ++ l2 ++ [(c2,d2)] ++ l3 /F/ x → y <-> l1 ++ [(c1,d1)] ++ l2 ++ l3 /F/ x → y.
  Proof.
  Admitted.

  (* forall l, if l is not redundant -> length l >= 2 -> not_reversible l *)
  (* forall l, length l >= 2 -> reversible l -> redundant_fractran l *)

End Fractran_Facts.

Section Small_fractran_halt_dec.

  Variable (c d : nat) (Hd : d <> 0).

  Lemma fractran_empty_halt_dec : decidable (fun x => [] /F/ x ↓).
  Proof.
    exists (fun _ => true). intros x. split; [easy|].
    intros _. exists x. split; [now exists 0|].
    intros z H. inversion H.
  Qed.

  Lemma fractran_singleton_halt_dec : decidable (fun x => [(c,d)] /F/ x ↓).
  Proof.
    exists (fun x => match x, c with
                       0, _ => false
                     | _, 0 => false
                     | _, _ => if divides_dec c d then false else true
                     end).
    intros x. split.
    - intros [y [[n Hy] Hstop]]. destruct x as [| x].
      + apply fractran_steps_zero in Hy; subst; [|congruence|].
        * specialize (Hstop 0). exfalso. apply Hstop. constructor. lia.
        * apply Forall_cons; auto.
      + destruct c as [| c'] eqn:Hc.
        * specialize (Hstop 0). exfalso. apply Hstop. constructor. lia.
        * destruct (divides_dec c d) as [[k Hk] | Hndiv] eqn:H; subst; [|now rewrite H].
          exfalso. apply (Hstop (k*y)). constructor. lia.
    - destruct x as [| x]; [congruence|].
      destruct c as [| c'] eqn:Hc; [congruence|].
      destruct (divides_dec c d) as [[k Hk] | Hndiv] eqn:H; subst.
      + now rewrite H.
      + intros _. apply fractran_singleton_ndiv_stop_S; auto.
  Qed.

End Small_fractran_halt_dec.

Theorem fractran_halt_dec_le2 l (Hl : fractran_regular l) :
  (length l = 0 \/ length l = 1) -> decidable (fun x => l /F/ x ↓).
Proof.
  intros [ H%length_zero_iff_nil | H%length_one_iff_singleton ]; subst.
  - exact fractran_empty_halt_dec.
  - destruct H as [(c,d) H]. subst. apply Forall_inv in Hl. simpl in Hl.
    now apply fractran_singleton_halt_dec.
Qed.

Section Redundant_fractran.

  Definition fractran_redundant (l : list (nat * nat)) := exists l1 l2 l3 c1 d1 c2 d2,
    l = l1 ++ [(c1,d1)] ++ l2 ++ [(c2,d2)] ++ l3 /\ divides d1 d2.

End Redundant_fractran.

Section Large_fractran_not_reversible.

  Variable (l : list (nat * nat)) (Hreg : fractran_regular l) (Hlen : length l > 1).

  Lemma large_fractran_not_reversible :
    (forall s t u, l /F/ s → u -> l /F/ t → u -> s = t) -> fractran_redundant l.
  Admitted.

End Large_fractran_not_reversible.
