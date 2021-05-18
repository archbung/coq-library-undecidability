Require Import List Arith Lia Permutation.
Import ListNotations.

From Undecidability.Shared.Libs.DLW
     Require Import gcd prime Utils.utils_tac.

From Undecidability.FRACTRAN
     Require Import FRACTRAN fractran_utils.

From Undecidability.Synthetic
     Require Import Definitions.

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

Section Fractran_facts.

  (* If computation starts from 0, it will stay at 0 *)
  Lemma fractran_step_zero_input y l (Hl : l <> nil) (Hlreg : fractran_regular l) :
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

  Lemma fractran_compute_zero_input x l (Hl : l <> nil) (Hlreg : fractran_regular l) :
    forall n, fractran_steps l n 0 x <-> x = 0.
  Proof.
    induction n as [|n IHn]; simpl; [split; auto|]. split.
    - intros [y [Hy Hs]]. apply IHn. apply fractran_step_zero_input in Hy; subst; auto.
    - intros ->. exists 0. split; [|now apply IHn].
      apply fractran_step_zero_input; auto.
  Qed.

  (* A computation that starts from 0 does not terminate *)
  Corollary fractran_nstop_zero_input l (Hl : l <> nil) (Hlreg : fractran_regular l) :
    ~ l /F/ 0 ↓.
  Proof.
    intros [y [[n Hy] Hstop]]. apply fractran_compute_zero_input in Hy; subst; auto.
    destruct l as [| (c,d) l]; subst; [congruence|].
    apply (Hstop 0). constructor. lia.
  Qed.

  Lemma fractran_step_zero_num_1 d l s u (Hd : d <> 0) : (0,d) :: l /F/ s → u <-> u = 0.
  Proof.
    constructor; [|intros ->; now constructor].
    inversion 1; subst; [lia|]. exfalso. apply H5. now exists 0.
  Qed.

  Corollary fractran_nstop_zero_num_1 d l s : ~ (0,d) :: l /F/ s ↓.
  Proof.
    destruct d as [|d]; simpl; intros [y [_ Hs]]; apply (Hs 0); now constructor.
  Qed.

  Lemma fractran_nstop_zero_num_2 a b d l x : ~ (S a, b) :: (0, d) :: l /F/ x ↓.
  Proof.
    destruct (divides_dec (S a) b) as [[k Hd]|_]; intros [y [[_ _] Hs]].
    - apply (Hs (k*y)). constructor. lia.
    - destruct (divides_dec (S a*y) b) as [[k Hd]|Hd].
      + apply (Hs k). constructor. lia.
      + apply (Hs 0). apply in_fractran_1; auto.
        now constructor.
  Qed.

  Lemma fractran_step_zero_den_1 c l s u : l /F/ s → u -> (c,0) :: l /F/ s → u.
  Proof.
    intros H. destruct c as [|c]; [now constructor|].
    destruct s as [|s]; [now constructor|].
    apply in_fractran_1; [|auto]. intros [k Hd]. lia.
  Qed.

  Lemma fractran_stop_zero_den_1 c s (Hc : c <> 0) : [(c, 0)] /F/ s ↓.
  Proof.
    destruct s as [|s]; simpl.
    - exists 1. constructor.
      + exists 1. simpl. exists 1. constructor; [|reflexivity].
        now constructor.
      + intros z H. inversion H; subst; [lia|inversion H6].
    - exists (S s). constructor.
      + now exists 0.
      + intros z H. inversion H; subst; [lia|inversion H6].
  Qed.

  Lemma fractran_stop_ndiv_singleton x c d (Hx : x <> 0) (Hc : c <> 0) (Hd : d <> 0) :
    ~ divides d c -> [(c,d)] /F/ x ↓.
  Proof.
    intros Hndiv%prime_key_div'; [|exact Hc|exact Hd].
    destruct Hndiv as [p H]. revert Hx.
    induction on x as IH with measure (count_pow p (pred x)).
    intros Hx. destruct (fractran_step_dec [(c,d)] x) as [[y Hxy]|Hs].
    - assert (Hy : y <> 0) by (inversion Hxy; subst; [lia|inversion H6]).
      inversion Hxy; subst.
      + specialize (H x y Hx Hy ltac: (lia)). specialize (IH y).
        apply IH in H as [y' [[n Hyy'] Hs']]; [|exact Hy]. exists y'. split; [|exact Hs'].
        exists (1+n). simpl. exists y. auto.
      + inversion H6.
    - exists x. split; [|exact Hs].
      exists 0. now simpl.
  Qed.

  Lemma fractran_step_suffix l x y : l /F/ x → y -> forall s, l ++ s /F/ x → y.
  Proof.
    intros H. destruct s as [|(c,d) t]; [now rewrite app_nil_r|].
    induction l as [|(p,q) l IHl]; [inversion H|].
    inversion H; subst; [now constructor|].
    rewrite <- app_comm_cons. apply in_fractran_1; [exact H5|].
    apply IHl, H6.
  Qed.

  Lemma fractran_compute_suffix l x y n :
    fractran_steps l n x y -> forall s, fractran_steps (l ++ s) n x y.
  Proof.
    revert x. induction n as [|n IHn]; simpl; [easy|].
    intros x [y' [Hy' Hs]] s. exists y'. constructor; [|now apply IHn].
    now apply fractran_step_suffix.
  Qed.

  Lemma fractran_stop_inv_ndiv l x : fractran_stop l x -> Forall (fun '(a,b) => ~ divides b (a*x)) l.
  Proof.
    induction l as [|(c,d) t IHl]; intros H; [constructor|].
    apply fractan_stop_cons_inv in H. destruct H as [H1 H2].
    constructor; [auto|]. apply IHl, H2.
  Qed.

  Lemma fractran_step_prefix l s x y : fractran_stop l x -> s /F/ x → y -> (l ++ s) /F/ x → y.
  Proof.
    intros Hns%fractran_stop_inv_ndiv Hs. induction l as [|(c,d) t IHl]; simpl; [exact Hs|].
    apply in_fractran_1.
    - now apply Forall_inv in Hns.
    - apply IHl. now apply Forall_inv_tail in Hns.
  Qed.

End Fractran_facts.

Section Small_fractran_halt_dec.

  Lemma fractran_empty_halt_dec : decidable (fun x => [] /F/ x ↓).
  Proof.
    exists (fun _ => true). intros x. split; [easy|].
    intros _. exists x. split; [now exists 0|].
    intros z H. inversion H.
  Qed.

  Lemma fractran_singleton_halt_dec_regular c d (Hd : d <> 0) :
    decidable (fun x => [(c,d)] /F/ x ↓).
  Proof.
    exists (fun x => match x, c with
                       0, _ => false
                     | _, 0 => false
                     | _, _ => if divides_dec c d then false else true
                     end).
    split.
    - destruct x as [| x].
      + intros H%fractran_nstop_zero_input; [auto|congruence|].
        constructor; auto.
      + destruct c as [| c'] eqn:Hc.
        * now intros H%fractran_nstop_zero_num_1.
        * destruct (divides_dec c d) as [[k Hk] | Hndiv] eqn:H; subst; [|now rewrite H].
          intros [y [[n Hn] Hstop]]. exfalso. apply (Hstop (k*y)). constructor. lia.
    - destruct x as [| x]; [congruence|].
      destruct c as [| c'] eqn:Hc; [congruence|].
      destruct (divides_dec c d) as [[k Hk] | Hndiv] eqn:H; subst; [now rewrite H|].
      intros _. apply fractran_stop_ndiv_singleton; auto.
  Qed.

  Lemma fractran_singleton_halt_dec c d : decidable (fun x => [(c,d)] /F/ x ↓).
  Proof.
    destruct d as [|d]; simpl.
    - destruct c as [|c]; simpl.
      + exists (fun _ => false). constructor; [|now intros].
        now intros H%fractran_nstop_zero_num_1.
      + exists (fun _ => true). constructor; [now intros|].
        intros _. now apply fractran_stop_zero_den_1.
    - apply fractran_singleton_halt_dec_regular. auto.
  Qed.

End Small_fractran_halt_dec.

Section Redundant_fractran.

  (* for a/b, c/d the fraction c/d may be redundant (and removed) *)
  Lemma redundant_spec a b c d :
    is_gcd d c 1 -> divides b d ->
    forall x, divides d (c*x) -> divides b (a*x).
  Proof.
    intros Hdc [k1 Hbd] x Hd.
    apply (is_rel_prime_div _ Hdc) in Hd as [k2 ?].
    exists (k1*k2*a). nia.
  Qed.

  Lemma fractran_step_redundant a b c d l :
    is_gcd d c 1 -> divides b d ->
    forall s t, (a,b) :: (c,d) :: l /F/ s → t <-> (a,b) :: l /F/ s → t.
  Proof.
    intros Hdc [k1 Hbd] s t. constructor.
    - inversion 1; subst; [now constructor|].
      inversion H6; subst.
      + assert (Hd: divides (k1*b) (c*s)) by (exists t; lia).
        apply (redundant_spec a b) in Hd; auto; [now exfalso|now exists k1].
      + apply in_fractran_1; auto.
    - inversion 1; subst; [now constructor|].
      apply in_fractran_1; auto. apply in_fractran_1; auto.
      intros Hd. apply H5. apply (redundant_spec _ _ c (k1*b)); auto. now exists k1.
  Qed.

  (* if the second fraction is not redundant, then the program is not reversible *)
  Lemma fractran_step_contradict_reversible a b c d l :
    is_gcd b a 1 -> ~ divides b d ->
    exists (s t u : nat),
      (a,b) :: (c,d) :: l /F/ s → u /\ (a,b) :: (c,d) :: l /F/ t → u /\ s <> t.
  Proof.
    intros Hba Hbd. exists (c*b), (a*d), (a*c).
    constructor; [constructor; lia|].
    constructor. apply in_fractran_1.
    - intros Hb. now do 2 apply (is_rel_prime_div _ Hba) in Hb.
    - constructor. lia.
    - intros E. apply Hbd. apply (is_rel_prime_div _ Hba). now exists c.
  Qed.

End Redundant_fractran.

Definition fractran_reversible (l : list (nat * nat)) :=
  forall s t u, l /F/ s → u -> l /F/ t → u -> s = t.

Lemma fractran_reversible_neg (l : list (nat * nat)) :
  (exists s t u, l /F/ s → u /\ l /F/ t → u /\ s <> t) -> ~ fractran_reversible l.
Proof.
  unfold fractran_reversible.
  intros (s & t & u & Hsu & Htu & ?) Hrev. apply H, (Hrev _ _ u); auto.
Qed.

Lemma fractran_step_iff_reversible l1 l2 :
  (forall s t, l1 /F/ s → t <-> l2 /F/ s → t) -> fractran_reversible l1 -> fractran_reversible l2.
Proof.
  unfold fractran_reversible.
  intros H Hrev s t u Hsu%H Htu%H. now apply Hrev with (u:=u).
Qed.

Lemma fractran_step_iff_halt l1 l2 :
  (forall s t, l1 /F/ s → t <-> l2 /F/ s → t) -> (forall x, l1 /F/ x ↓ -> l2 /F/ x ↓).
Proof.
  intros H x. intros [y [[n Hn] Hs]]. exists y. constructor.
  - exists n. revert x Hn. induction n as [|n IHn]; simpl; auto.
    intros x [y' [Hy' Hs']]. exists y'. constructor; [now apply H|now apply IHn].
  - intros z Hs'. now apply (Hs z), H.
Qed.

Corollary fractran_step_iff_halt_dec l1 l2 :
  (forall s t, l1 /F/ s → t <-> l2 /F/ s → t) ->
  decidable (fun x => l1 /F/ x ↓) -> decidable (fun x => l2 /F/ x ↓).
Proof.
  intros H [f Hdec]. exists f. intros x.
  assert (l2 /F/ x ↓ -> l1 /F/ x ↓) by now apply fractran_step_iff_halt.
  constructor; intros; [now apply Hdec, H0|].
  apply (fractran_step_iff_halt l1 l2); auto. now apply Hdec.
Qed.

Lemma fractran_reversible_halt_dec_cons a b c d l (Ha : a <> 0) (Hc : c <> 0) :
  (forall y, length y < length ((a,b) :: (c,d) :: l) -> fractran_reversible y -> decidable (fun x => y /F/ x ↓))
  -> fractran_reversible ((a,b) :: (c,d) :: l) -> decidable (fun x => (a,b) :: (c,d) :: l /F/ x ↓).
Proof.
  intros IH.
  destruct (bezout_generalized a b) as (_ & _ & gab & _ & _ & Hgab & _).
  apply is_gcd_rel_prime in Hgab. destruct Hgab as (na & nb & (Hna & Hnb & Hab)).
  destruct (bezout_generalized c d) as (_ & _ & gcd & _ & _ & Hgcd & _).
  apply is_gcd_rel_prime in Hgcd. destruct Hgcd as (nc & nd & (Hnc & Hnd & Hcd)).
  pose (l2 := ((na,nb) :: (nc,nd) :: l)).
  assert (H: forall s t, (a,b) :: (c,d) :: l /F/ s → t <-> (na,nb) :: (nc,nd) :: l /F/ s → t).
  { intros s t. constructor.
    - inversion 1; subst; [constructor; nia|].
      apply in_fractran_1.
      + contradict H5. destruct H5 as [k H5]. exists k. nia.
      + inversion H6; subst; [constructor; nia|].
        apply in_fractran_1; [|exact H8].
        contradict H7. destruct H7 as [k H7]. exists k. nia.
    - inversion 1; subst; [constructor; nia|].
      apply in_fractran_1.
      + contradict H5. destruct H5 as [k H5]. exists k. nia.
      + inversion H6; subst; [constructor; nia|].
        apply in_fractran_1; [|exact H8].
        contradict H7. destruct H7 as [k H7]. exists k. nia.
  }
  intros Hrev%(fractran_step_iff_reversible _ l2); [|apply H].
  apply (fractran_step_iff_halt_dec l2 _).
  - intros s t. apply iff_sym, H.
  - destruct (divides_dec nd nb) as [[k Hd]|Hd].
    + pose (l3 := (na,nb) :: l).
      apply (fractran_step_iff_reversible _ l3) in Hrev.
      * apply (fractran_step_iff_halt_dec l3 _).
        intros s t. apply iff_sym, fractran_step_redundant; [|now exists k].
        now apply is_gcd_sym. apply IH; auto.
      * intros s t. apply fractran_step_redundant; [|now exists k].
        now apply is_gcd_sym.
    + assert (Hr : ~ fractran_reversible l2).
      { apply fractran_reversible_neg, fractran_step_contradict_reversible; auto.
        now apply is_gcd_sym.
      }
      exfalso. now apply Hr.
Qed.

Theorem fractran_reversible_halt_dec (l : list (nat * nat)) :
  fractran_reversible l -> decidable (fun x => l /F/ x ↓).
Proof.
  induction on l as IH with measure (length l).
  destruct l as [|(a,b) l]; simpl; [intros _; apply fractran_empty_halt_dec|].
  destruct l as [|(c,d) l]; simpl; [intros _; apply fractran_singleton_halt_dec|].
  destruct a as [|a]; simpl.
  - intros _. exists (fun _ => false). split; [|now intros].
    now intros H%fractran_nstop_zero_num_1.
  - destruct c as [|c]; simpl.
    + intros _. exists (fun _ => false). constructor; [|now intros].
      now intros H%fractran_nstop_zero_num_2.
    + now apply fractran_reversible_halt_dec_cons.
Qed.
