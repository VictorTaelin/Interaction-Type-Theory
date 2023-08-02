module Base where

open import Agda.Builtin.Bool public
open import Agda.Builtin.Char public
open import Agda.Builtin.Equality public renaming ( _≡_ to _==_ )
open import Agda.Builtin.List public renaming ( [] to nil ; _∷_ to _#_ )
open import Agda.Builtin.Maybe public renaming ( just to some ; nothing to none )
open import Agda.Builtin.Nat public renaming ( suc to succ ; _==_ to eq )
open import Agda.Builtin.String public
open import Agda.Builtin.Sigma public renaming ( Σ to S )
open import Agda.Builtin.TrustMe public
open import Agda.Builtin.Unit public renaming ( ⊤ to Unit ; tt to unit )
open import Agda.Primitive public

data Empty : Set where

data Pair (a b : Set) : Set where
  pair : a -> b -> Pair a b

Not : {a : Level} -> Set a -> Set a
Not a = a -> Empty

_!=_ : {a : Level} {A : Set a} -> A -> A -> Set a
x != y = Not (x == y)

if : ∀ {a : Set} -> Bool -> a -> a -> a
if true  t f = t
if false t f = f

may : ∀ {a b : Set} -> Maybe b -> (b -> a) -> a -> a
may (some x) s n = s x
may none     s n = n

pred : Nat -> Nat
pred zero     = zero
pred (succ x) = x

max : Nat -> Nat -> Nat
max zero     b        = b
max a        zero     = a
max (succ a) (succ b) = succ (max a b)

len : ∀ {a : Set} -> List a -> Nat
len nil      = 0
len (x # xs) = succ (len xs)

foldr : ∀ {a b : Set} -> (a -> b -> b) -> b -> List a -> b
foldr f z nil      = z
foldr f z (x # xs) = f x (foldr f z xs)

mmap : ∀ {a b : Set} -> (a -> b) -> Maybe a -> Maybe b
mmap f none     = none
mmap f (some x) = some (f x)

when : ∀ {a b : Set} -> Maybe a -> (a -> b) -> b -> b
when none     s n = n
when (some x) s n = s x

Unwrap : ∀ {a : Set} -> Maybe a -> (a -> Set) -> Set
Unwrap none     f = Unit
Unwrap (some x) f = f x

sym : ∀ {a} {A : Set a} {x y : A} -> x == y -> y == x
sym refl = refl

apl : ∀ {a b} {A : Set a} {B : Set b} (f : A -> B) {x y : A} -> x == y -> f x == f y
apl f refl = refl

rwt : ∀ {a} {A : Set a} {P : A → Set} {x y : A} -> x == y -> P x -> P y
rwt refl px = px

IsSome : {a : Set} -> (x : Maybe a) -> Set
IsSome none     = Empty
IsSome (some x) = Unit

absurd : {a : Set} -> Empty -> a
absurd ()

foo : ∀ x y -> succ x != succ y -> x != y
foo x y nsxy xy = nsxy (apl succ xy)

