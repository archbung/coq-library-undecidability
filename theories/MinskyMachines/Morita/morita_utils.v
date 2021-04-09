Require Import List Arith Lia.

From Undecidability.Shared.Libs.DLW
     Require Import pos vec sss.

From Undecidability.MinskyMachines
     Require Import morita_defs.

Set Implicit Arguments.

Section Morita_Utils.

  Variable (k : nat).

  (* bijection from nat * nat to nat *)
  Definition encode '(x, y) : nat :=
    y + (nat_rec _ 0 (fun i m => (S i) + m) (y + x)).

  (* bijection from nat to nat * nat *)
  Definition decode (n : nat) : nat * nat :=
    nat_rec _ (0, 0) (fun _ '(x, y) => match x with 0 => (S y, 0) | S x => (x, S y) end) n.

  Lemma decode_encode { p : nat * nat } : decode (encode p) = p.
  Proof.
    remember (encode p) eqn:H. revert p H. induction n as [|n IH].
    - destruct p as [[|?] [|?]]; now simpl.
    - destruct p as [x y]. destruct y; simpl.
      + destruct x; simpl; try congruence.
        intros [=]. rewrite (IH (0, x)); simpl.
        * reflexivity.
        * now rewrite H0, Nat.add_0_r.
      + intros [=]. rewrite (IH (S x, y)); simpl.
        * reflexivity.
        * now rewrite Nat.add_succ_r, H0.
  Qed.

End Morita_Utils.
