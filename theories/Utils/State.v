Require Import Undecidability.Utils.Monad.

Definition State (S A : Type) := S -> A * S.

Definition evalState {S A : Type} (p : State S A) (s : S) :=
  fst (p s).

Definition execState {S A : Type} (p : State S A) (s : S) :=
  snd (p s).

Instance State (S : Type) : Functor (State S) := {
  fmap (f : A -> B) m := fun s => let (a, s') := m s in (f a, s')
}.

Instance State (S : Type) : Applicative (State S) := {
  pure x := fun s => (x, s);
  f <*> x := fun s => let (a, s') := x s in let (f, s'') := f s in (f a, s'')
}.

Instance State (S : Type) : Monad (State S) := {
  x >>= f := fun s => let (a, s') := x s in f a s'
}
