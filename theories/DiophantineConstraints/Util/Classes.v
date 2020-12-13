Require Import Datatypes. (* for @id@ *)
Require Import Program.Basics. (* for @compose@ and @apply@ *)
Require Import FunctionalExtensionality.
Require Import List.
Import ListNotations.

(* Equivalent to @$@ in Haskell*)
Notation "f $ y" := (apply f y) (at level 100, right associativity).

Class Functor (F : Type -> Type) := {
  fmap : forall {A B : Type}, (A -> B) -> F A -> F B;

  (* Functor laws *)
  functor_id : forall {A : Type} (x : F A), fmap id x = id x;
  functor_comp : forall {A B C : Type} (f : B -> C) (g : A -> B) (x : F A),
      fmap (compose f g) x = compose (fmap f) (fmap g) x
}.

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

Class Semigroup {A : Type} := {
  sconcat : A -> A -> A;
  sconcat_assoc : forall x y z, sconcat (sconcat x y) z = sconcat x (sconcat y z)
}.

Class Monoid {A : Type} `{Semigroup A} := {
  one : A;
  monoid_left_id : forall x, sconcat one x = x;
  monoid_right_id : forall x, sconcat x one = x
}.

Class Foldable T := {
  foldr : forall {A B : Type}, (A -> B -> B) -> B -> T A -> B
}.

(* The identity functor *)
Inductive Id (A : Type) :=
| mkId (x : A) : Id A.

Arguments mkId {A}.

Instance FuncInstId : Functor Id.
refine {| fmap := fun _ _ f m => match m with mkId y => mkId (f y) end |}.
Proof.
  all: intros; now destruct x.
Defined.

Instance ApplInstId : Applicative Id.
refine {| pure := fun _ x => mkId x;
          splat := fun _ _ f m => match f, m with mkId f, mkId x => mkId (f x) end
       |}.
Proof.
  all: intros.
  - now destruct v.
  - reflexivity.
  - now destruct u.
  - now destruct u, v, w.
Defined.

Instance MonadInstId : Monad Id.
refine {| bind := fun _ _ m f => match m with mkId x => f x end |}.
Proof.
  all: intros.
  - reflexivity.
  - now destruct m.
  - now destruct m, (f x).
Qed.

Instance FuncInstList : Functor list.
refine {| fmap := map |}.
Proof.
  all: intros.
  - induction x.
    + reflexivity.
    + simpl. now rewrite IHx.
  - induction x.
    + reflexivity.
    + simpl. now rewrite IHx.
Defined.

(* Composition of any two functors is a functor *)
Instance FuncInstCompose {F G : Type -> Type} `{HF : Functor F} `{HG : Functor G} : Functor (fun (A : Type) => G (F A)).
Proof.
  unshelve refine {| fmap := _ |}.
  - intros. now apply (fmap (fmap X)).
  - intros. simpl. assert (@fmap F HF A A id = id).
    + apply functional_extensionality. apply functor_id.
    + rewrite H. apply functor_id.
  - intros. simpl. assert (@fmap F HF A C (compose f g) = compose (@fmap F HF B C f) (@fmap F HF A B g)).
    + apply functional_extensionality. apply functor_comp.
    + rewrite H. apply functor_comp.
Defined.

Class Traversable T `{Functor T} `{Foldable T} := {
  traverse : forall {F} `{Applicative F} {A B : Type}, (A -> F B) -> T A -> F (T B);

  (* Traversable laws *)
  traversable_id : forall {A : Type} (x : T A), traverse mkId x = mkId x;
  (* traversable_compose : forall {F G A B},
         traverse (mkCompose ∘ fmap g ∘ f) = mkCompose ∘ fmap (traverse g) ∘ traverse f *)
}.
