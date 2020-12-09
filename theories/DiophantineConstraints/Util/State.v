Require Import Undecidability.DiophantineConstraints.Util.Class.
Require Import FunctionalExtensionality.

Definition State (S A : Type) := S -> A * S.

Definition evalState {S A : Type} (p : State S A) (s : S) :=
  fst (p s).

Definition execState {S A : Type} (p : State S A) (s : S) :=
  snd (p s).

Instance FuncInstState (S : Type) : Functor (State S).
refine {| fmap := fun _ _ f m s => let '(a, s') := m s in (f a, s') |}.
Proof.
  all: intros; apply functional_extensionality; intros.
  - unfold id. now destruct (x x0).
  - unfold compose. now destruct (x x0).
Defined.

Instance ApplInstState (S : Type) : Applicative (State S).
refine {| pure := fun _ x s => (x, s);
          splat := fun _ _ f m s => let '(f', s') := f s in let '(a, s'') := m s' in (f' a, s'')
       |}.
Proof.
  all: intros; apply functional_extensionality; intros.
  - unfold id. now destruct (v x).
  - reflexivity.
  - now destruct (u x).
  - unfold compose. now destruct (u x), (v s), (w s0).
Defined.

Instance MonadInstState (S : Type) : Monad (State S).
refine {| bind := fun _ _ m f s => let '(a, s') := m s in f a s' |}.
Proof.
  all: intros; apply functional_extensionality; intros; try now destruct (m x).
  reflexivity.
Defined.
