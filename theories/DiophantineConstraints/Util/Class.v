Require Import List.
Import ListNotations.

Definition id {A : Type} (x : A) := x.
Definition compose {A B C : Type} (f : B -> C) (g : A -> B) :=
  fun x => f (g x).

(* Equivalent to @$@ in Haskell*)
Definition ap {A B : Type} (f : A -> B) (x : A) := f x.
Notation "f $ y" := (ap f y) (at level 100, right associativity).

Class Functor F := {
  fmap : forall {A B : Type}, (A -> B) -> F A -> F B;

  (* Functor laws *)
  functor_id : forall {A : Type} (x : F A), fmap id x = id x;
  functor_comp : forall {A B C : Type} (f : B -> C) (g : A -> B) (x : F A),
      fmap (compose f g) x = compose (fmap f) (fmap g) x
}.
Notation "f <$> x" := (fmap f x) (at level 40, left associativity).

Class Applicative G `{Functor G} := {
  pure : forall {A : Type}, A -> G A;
  splat : forall {A B : Type}, G (A -> B) -> G A -> G B;

  (* Applicative laws *)
  applicative_id : forall {A : Type} (v : G A), splat (pure id) v = v;
  applicative_hom : forall {A B : Type} (f : A -> B) (x : A),
      splat (pure f) (pure x) = pure (f x);

  applicative_interchange : forall {A B : Type} (u : G (A -> B)) (y : A),
      splat u (pure y) = splat (pure (fun f => f $ y)) u;

  applicative_comp : forall {A B C : Type} (u : G (B -> C)) (v : G (A -> B)) w,
      splat u (splat v w) = splat (splat (splat (pure compose) u) v) w
}.
Notation "f <*> x" := (splat f x) (at level 40, left associativity).

Class Monad M `{Applicative M} := {
  bind : forall {A B : Type}, M A -> (A -> M B) -> M B;

  (* Monad laws *)
  monad_left_id : forall {A B : Type} (x : A) (f : A -> M B), bind (pure x) f = f x;
  monad_right_id : forall {A : Type} (m : M A), bind m pure = m;
  monad_assoc : forall {A B C : Type} (m : M A) (f : A -> M B) (g : B -> M C),
      bind (bind m f) g = bind m (fun x => bind (f x) g)
}.
Notation "x >>= f" := (bind x f) (at level 10, left associativity).
