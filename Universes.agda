{-
 Dependently typed programming in Agda
 3.2 Universes
-}
module Universes where

-- A familiar universe

-- The universe of decidable propositions
data   False : Set where
record True  : Set where

-- Bool is a code
data Bool : Set where
  true false : Bool

-- decoder
isTrue : Bool → Set
isTrue true  = True
isTrue false = False

infix 30 not_
infixr 25 _and_

not_ : Bool → Bool
not true  = false
not false = true

_and_ : Bool → Bool → Bool
true  and x = x
false and _ = false

notNotId : (a : Bool) → isTrue (not not a) → isTrue a
notNotId true x = x
notNotId false ()

{-
open import Relation.Binary.PropositionalEquality
notNotId' : (a : Bool) → (not not a) ≡ a
notNotId' true = refl
notNotId' false = refl
-}

open import Data.Nat using (zero;suc;_+_) renaming (ℕ to Nat)
nonZero : Nat → Bool
nonZero zero = false
nonZero (suc _) = true

postulate
  _div_ : Nat → (m : Nat){p : isTrue (nonZero m)} → Nat

--three : Nat
three = 16 div 5

-- Universes for generic programming

-- type of codes for polynomial functors
data Functor : Set1 where
  |Id| : Functor        -- identity
  |K|  : Set → Functor  -- constant
  _|+|_ : Functor → Functor → Functor -- disjoint
  _|x|_ : Functor → Functor → Functor -- cartesian product

data _⊕_ (A B : Set) : Set where
  inl : A → A ⊕ B
  inr : B → A ⊕ B

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

infixr 50 _|+|_ _⊕_
infixr 60 _|x|_ _×_

-- decoding function
[_] : Functor → Set → Set
[ |Id|    ] X = X
[ |K| A   ] X = A
[ F |+| G ] X = [ F ] X ⊕ [ G ] X
[ F |x| G ] X = [ F ] X × [ G ] X

map : (F : Functor){X Y : Set} → (X → Y) → [ F ] X → [ F ] Y
map |Id|      f x       = f(x)
map (|K| A)   f c       = c
map (F |+| G) f (inl x) = inl (map F f x)
map (F |+| G) f (inr y) = inr (map G f y)
map (F |x| G) f (x , y) = map F f x , map G f y

data μ_ (F : Functor) : Set where
  <_> : [ F ] (μ F) → μ F

f : Functor
f = |K| Nat

hoge : μ f
hoge = < zero >

{-
fold' : (F : Functor){A : Set} → ([ F ] A → A) → μ F → A
fold' F φ < x > = φ (map F (fold' F φ) x)
-}
mapFold : ∀ {X} F G → ([ G ] X → X) → [ F ] (μ G) → [ F ] X
mapFold |Id|        G φ < x >   = φ (mapFold G G φ x)
mapFold (|K| A)     G φ c       = c
mapFold (F₁ |+| F₂) G φ (inl x) = inl (mapFold F₁ G φ x)
mapFold (F₁ |+| F₂) G φ (inr y) = inr (mapFold F₂ G φ y)
mapFold (F₁ |x| F₂) G φ (x , y) = mapFold F₁ G φ x , mapFold F₂ G φ y

fold : {F : Functor}{A : Set} → ([ F ] A → A) → μ F → A
fold {F} φ < x > = φ (mapFold F F φ x)

-- examples.
-- see(Japanese): http://nineties.github.io/category-seminar/7.html#/59

NatF : Functor
NatF = |K| True |+| |Id|

NAT : Set
NAT = μ NatF

Z : NAT -- Z means zero
Z = < inl _ >

S : NAT → NAT -- S means successor
S n = < (inr n) >

ListF : (A : Set) → Functor
ListF = λ A → |K| True |+| |K| A |x| |Id|

LIST : (A : Set) → Set
LIST = λ A → μ (ListF A)

nil : {A : Set} → LIST A
nil = < (inl _) >

cons : {A : Set} → A → LIST A → LIST A
cons x xs = < (inr (x , xs)) >

[_||_] : {A B C : Set} → (A → C) → (B → C) → A ⊕ B → C
[ f || g ] (inl x) = f x
[ f || g ] (inr y) = g y

uncurry : {A B C : Set} → (A → B → C) → A × B → C
uncurry f (x , y) = f x y

const : {A B : Set} → A → B → A
const x y = x

foldr : {A B : Set} → (A → B → B) → B → LIST A → B
foldr {A}{B} f z = fold [ const z || uncurry f ] 

plus : NAT → NAT → NAT
plus n m = fold [ const m || S ] n

-- Universes for overloading

open import Data.List using (List;[];_∷_)

data Type : Set where
  bool : Type
  nat  : Type
  list : Type → Type
  pair : Type → Type → Type

El : Type → Set
El bool       = Bool
El nat        = Nat
El (list a)   = List (El a)
El (pair a b) = El a × El b

infix 30 _==_
_==_ : {a : Type} → El a → El a → Bool

_==_ {bool} true y  = y
_==_ {bool} false y = not y

_==_ {nat}  zero    zero   = true
_==_ {nat}  zero   (suc y) = false
_==_ {nat} (suc x)  zero   = false
_==_ {nat} (suc x) (suc y) = x == y

_==_ {list a} []       []       = true
_==_ {list a} []       (x ∷ xs) = false
_==_ {list a} (x ∷ xs) []       = false
_==_ {list a} (x ∷ xs) (y ∷ ys) = x == y and xs == ys 

_==_ {pair a b} (x₁ , y₁) (x₂ , y₂) = x₁ == x₂ and y₁ == y₂

example₁ : isTrue ((2 + 2) == 4)
example₁ = _

example₂ : isTrue (not ((true ∷ false ∷ []) == (true ∷ true ∷ [])))
example₂ = record {}

module Exercises where


