Require Import List Arith Lia.
Import ListNotations.

From Undecidability.Shared.Libs.DLW
     Require Import gcd prime.

From Undecidability.FRACTRAN
     Require Import FRACTRAN.

From Undecidability.Synthetic
     Require Import Definitions.

Section ListFacts.

  (* Definition any := existsb id. *)

  (* Definition zipWith {X Y Z} (f : X*Y -> Z) xs ys := map f (combine xs ys). *)

  (* Lemma any_zipWith_p {X Y} (p : X*Y -> bool) (xs : list X) (ys : list Y) : *)
  (*   any (zipWith p xs ys) = true <-> *)
  (*     exists (i : nat) x y, nth_error xs i = Some x /\ nth_error ys i = Some y /\ p (x,y) = true. *)
  (* Admitted. *)

  Lemma length_one_iff_singleton {X} (l : list X) : length l = 1 <-> exists x, l = [x].
  Proof.
    destruct l; simpl; split.
    - intros H. congruence.
    - intros [x H]. congruence.
    - intros [=]. apply length_zero_iff_nil in H0. exists x. now rewrite H0.
    - intros [y]. now inversion H.
  Qed.

End ListFacts.

Section redundant_FRAC.

  Definition red_FRAC (l : list (nat * nat)) :=
    exists c1 d1 c2 d2 l1 l2 l3, l1 ++ [(c1, d1)] ++ l2 ++ [(c2, d2)] ++ l3 = l /\ divides d1 d2.

  Definition nred_FRAC (l : list (nat * nat)) :=
    forall c1 d1 c2 d2 l1 l2 l3, l1 ++ [(c1, d1)] ++ l2 ++ [(c2, d2)] ++ l3 = l -> ~ divides d1 d2.

  Lemma nred_not_red l : nred_FRAC l -> ~ red_FRAC l.
  Proof.
    unfold nred_FRAC.
    intros H [c1 [d1 [c2 [d2 [l1 [l2 [l3 [H1 H2]]]]]]]].
    eapply H.
    - exact H1.
    - exact H2.
  Qed.

  Lemma l0_nred l : length l = 0 -> nred_FRAC l.
  Proof.
    intros H%length_zero_iff_nil. rewrite H.
    intros c1 d1 c2 d2 l1 l2 l3 H1 Hdiv.
    do 3 rewrite app_assoc in H1.
    apply app_eq_nil in H1 as [H1 _].
    apply app_eq_nil in H1 as [_ H3].
    congruence.
  Qed.

  Lemma l1_nred l : length l = 1 -> nred_FRAC l.
  Proof.
    intros H%length_one_iff_singleton. destruct H as [x H]. rewrite H.
    intros c1 d1 c2 d2 l1 l2 l3 H1 Hdiv.
    do 3 rewrite app_assoc in H1.
    apply app_eq_unit in H1 as [[H1 _]|[H1 _]].
    - apply app_eq_nil in H1 as [_ H1]. congruence.
    - apply app_eq_unit in H1 as [[H1 _]|[_ H3]].
      + apply app_eq_nil in H1 as [H1 _].
        apply app_eq_nil in H1 as [_ H1]. congruence.
      + congruence.
  Qed.

End redundant_FRAC.

Definition reg_frac '(c,d) := c <> 0 /\ d <> 0.

Section Small_FRAC_halt_dec.

  Variable (l : list (nat * nat)) (Hreg : Forall reg_frac l).

  Lemma fractran_halt_dec_l0 : length l = 0 -> decidable (fractran_terminates l).
  Proof.
    intros H%length_zero_iff_nil.
    exists (fun _ => true). intros x. split.
    - now intros Hf.
    - intros _.
      exists x. split.
      + now exists 0.
      + intros z H2. now destruct H2.
  Qed.

  Lemma fractran_halt_dec_l1 : length l = 1 -> decidable (fractran_terminates l).
  Proof.
    intros H%length_one_iff_singleton. destruct H as [(c,d) H]. rewrite H.
    exists (fun x => match x with 0 => false | _ => if divides_dec c d then false else true end).
    intros x. split.
    - intros [y [[n Hy] Hs]].
      destruct (divides_dec c d) as [[k Hk] | Hndiv].
      + exfalso. apply Hs with (z:=k*y). constructor. lia.
      + destruct x.
        * exfalso. apply Hs with (z:=0). enough (y = 0) by (subst; constructor; lia).
          induction n as [|n IHn].
          -- now simpl in Hy.
          -- apply IHn. simpl in Hy. destruct Hy as [y0 [Hy1 Hy2]].
             enough (y0 = 0) by (subst; apply Hy2).
             inversion Hy1; subst. enough (d <> 0) by lia.
             ++ inversion Hreg. subst. apply H1.
             ++ inversion H6.
        * reflexivity.
    - destruct (divides_dec c d) as [[k Hk]|Hndiv].
      + destruct x; now intros.
      + destruct x.
        * now intros.
        * intros _. (pose proof (@prime_decomp c)).
  Admitted.

  (* Lemma foo : *)
  (*   exists (p k : nat), prime p -> divides (p^k) d -> ~ divides (p^k) c -> *)
  (*                       forall x y lx ly, l /F/ x → y -> x = fold_right mult 1 lx -> Forall prime lx -> *)
  (*                       y = fold_right mult 1 ly -> Forall prime ly -> count_occ ly p < count_occ lx p *)

  Lemma fractran_halt_dec_le2 : (length l = 0 \/ length l = 1) -> decidable (fractran_terminates l).
  Proof.
    intros [H|H]; revert H.
    - apply fractran_halt_dec_l0.
    - apply fractran_halt_dec_l1.
  Qed.

End Small_FRAC_halt_dec.

Section Large_FRAC_not_reversible.

  Variable (l : list (nat * nat)) (Hlen : length l > 1)
           (Hred : nred_FRAC l) (Hreg : Forall reg_frac l).

  Fact FRAC_not_rev : exists s t u, l /F/ s → u -> l /F/ t → u -> s <> t.
  Proof.

End Large_FRAC_not_reversible.
