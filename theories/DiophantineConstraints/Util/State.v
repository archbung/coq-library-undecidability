Require Import Undecidability.DiophantineConstraints.Util.Classes.
Require Import FunctionalExtensionality.
Require Import List.
Require Import Datatypes.
Require Import Basics.
Import ListNotations.

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

Definition liftA2 {F} `{Applicative F} {A B C : Type} (f : A -> B -> C) (x : F A) :=
  splat (fmap f x).

Definition traverse {F} `{Applicative F} {A B : Type} (f : A -> F B) :=
  fold_right (fun x ys => liftA2 (fun c cs => c :: cs) (f x) ys) (pure []).
