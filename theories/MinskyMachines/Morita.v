Require Import List Arith Lia.

From Undecidability.Shared.Libs.DLW
     Require Import Vec.pos Vec.vec Code.sss.

Set Implicit Arguments.


Section Morita_Machine.

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

End Morita_Machine.
