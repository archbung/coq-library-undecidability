(* A Coq computable reduction from n-registers MM termination
   to 2-registers reversible MMA termination.

   The reduction goes via 2-registers MMA termination.
 *)

Require Import Undecidability.Synthetic.Undecidability.
From Undecidability.MinskyMachines Require Import MM MM_to_MMA2 MMA2_to_MMA2_REVERSIBLE.

Set Implicit Arguments.

Corollary MM_MMA2_REVERSIBLE_HALTING : reduces MM_HALTING MMA2_REVERSIBLE_HALTING.
Proof.
  eapply reduces_transitive. exact MM_MMA2_HALTING.
  exact MMA2_MMA2_REVERSIBLE_HALTING.
Qed.
