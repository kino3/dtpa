module View where
-- Dependently typed programming in Agda
-- 3 Programming Techniques

-- 3.1 Views

-- Natural number parity

open import Data.Nat renaming (ℕ to Nat) hiding (erase)

data Parity : Nat → Set where
  even : (k : Nat) → Parity (k * 2)
  odd  : (k : Nat) → Parity (1 + k * 2)

parity : (n : Nat) → Parity n
parity zero    = even zero
parity (suc n) with parity n
parity (suc .(k * 2))       | even k = odd k
parity (suc .(suc (k * 2))) | odd  k = even (suc k)

{-
parity2 : (n : Nat) → Parity n
parity2 zero    = even zero
parity2 (suc n) with parity2 n
parity2 (suc .(k * 2))       | even k = {!!}
parity2 (suc .(suc (k * 2))) | odd k  = {!!}
-}

half : Nat → Nat
half n with parity n
half .(k * 2)       | even k = k
half .(suc (k * 2)) | odd  k = k

open import Data.Bool renaming (T to isTrue)
isEven : Nat → Bool
isEven n with parity n
isEven .(k * 2)       | even k = true
isEven .(suc (k * 2)) |  odd k = false


-- Finding an element in a list

open import Function using (_∘_)
open import Data.List hiding (filter)


infixr 30 _:all:_
data All {A : Set}(P : A → Set) : List A → Set where
  all[]   : All P []
  _:all:_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)


satisfies : {A : Set} → (A → Bool) → A → Set
satisfies p x = isTrue (p x)

data Find {A : Set}(p : A → Bool) : List A → Set where
  found     : (xs : List A)(y : A) → satisfies p y → (ys : List A) 
              → Find p (xs ++ y ∷ ys)
  not-found : ∀ {xs} → All (satisfies (not ∘ p)) xs 
              → Find p xs

sample : List Nat
sample = 3 ∷ 5 ∷ 2 ∷ 1 ∷ 4 ∷ []

prop : Nat → Bool
prop 2 = true
prop 4 = true
prop _ = false

open import Data.Unit
open import Data.Empty

p : Nat → Set
p 2 = ⊤ --isTrue (prop n)
p _ = ⊥
{-
ponyo : All p sample
ponyo = {!!} :all: {!!} :all: tt :all: {!!} :all: {!!} :all: all[]
-}
findsample : Find prop sample
findsample = found (3 ∷ 5 ∷ []) 2 tt (1 ∷ 4 ∷ [])

sample2 : List Nat
sample2 = 3 ∷ 5 ∷ 1 ∷ []

findsample2 : Find prop sample2
findsample2 = not-found (tt :all: (tt :all: (tt :all: all[])))

{-
find₁ : {A : Set}(p : A → Bool)(xs : List A) → Find p xs
find₁ p []       = not-found all[]
find₁ p (x ∷ xs) with p x
find₁ p (x ∷ xs) | true  = found [] x {!!} xs
find₁ p (x ∷ xs) | false = {!!}
-}

data _==_ {A : Set}(x : A) : A → Set where
  refl : x == x

data Inspect {A : Set}(x : A) : Set where
  it : (y : A) → x == y → Inspect x

inspect : {A : Set}(x : A) → Inspect x
inspect x = it x refl

trueIsTrue : {x : Bool} → x == true → isTrue x
trueIsTrue refl = tt

harada : Inspect 3
harada = it 3 refl

isFalse : Bool → Set
isFalse x = isTrue (not x)

falseIsFalse : {x : Bool} → x == false → isFalse x
falseIsFalse refl = tt

find : {A : Set}(p : A → Bool)(xs : List A) → Find p xs
find p []       = not-found all[]
find p (x ∷ xs) with inspect (p x)
... | it true  prf = found [] x (trueIsTrue prf) xs
... | it false prf with find p xs
find p (x ∷ .(xs ++ y ∷ ys)) | it false prf | found xs y py ys 
  = found (x ∷ xs) y py ys
find p (x ∷ xs)              | it false prf | not-found npxs     
  = not-found (falseIsFalse prf :all: npxs)



-- Indexing into a list
data _∈_ {A : Set}(x : A) : List A → Set where
  hd : ∀ {xs}   → x ∈ x ∷ xs
  tl : ∀ {y xs} → x ∈ xs     → x ∈ y ∷ xs
infix 4 _∈_

index : ∀ {A}{x : A}{xs} → x ∈ xs → Nat
index hd     = zero
index (tl p) = suc (index p) 

data Lookup {A : Set}(xs : List A) : Nat → Set where
  inside : (x : A)(p : x ∈ xs) → Lookup xs (index p)
  outside : (m : Nat) → Lookup xs (length xs + m)

lkpsample : Lookup sample 0
lkpsample = inside 3 hd

lkpsample2 : Lookup sample 1
lkpsample2 = inside 5 (tl hd)

lkpsample3 : Lookup sample 2
lkpsample3 = inside 2 (tl (tl hd))

lkpsample4 : Lookup sample 5
lkpsample4 = outside 0

lkpsample5 : Lookup sample 8
lkpsample5 = outside 3

_!_ : {A : Set}(xs : List A)(n : Nat) → Lookup xs n
[] ! n = outside n
(x ∷ xs) ! zero  = inside x hd
(x ∷ xs) ! suc n with xs ! n
(x ∷ xs) ! suc .(index p)       | inside y p = inside y (tl p)
(x ∷ xs) ! suc .(length xs + m) | outside m  = outside m

module lambda where

  -- A type checker for λ-calculus
  infixr 30 _⇒_
  data Type : Set where
    ı   : Type
    _⇒_ : Type → Type → Type

  data Equal? : Type → Type → Set where
    yes : ∀ {τ}   → Equal? τ τ
    no  : ∀ {σ τ} → Equal? σ τ

  _=?=_ : (σ τ : Type) → Equal? σ τ
  ı       =?= ı       = yes
  ı       =?= (_ ⇒ _) = no
  (_ ⇒ _) =?= ı       = no
  σ₁ ⇒ τ₁ =?= σ₂ ⇒ τ₂ with σ₁ =?= σ₂ | τ₁ =?= τ₂
  σ₁ ⇒ τ₁ =?= .σ₁ ⇒ .τ₁ | yes | yes = yes
  σ₁ ⇒ τ₁ =?= σ₂ ⇒ τ₂   | _   | _   = no

  infixl 80 _$_
  data Raw : Set where
    var : Nat → Raw
    _$_ : Raw → Raw → Raw -- function application
    lam : Type → Raw → Raw

  t1 : Type
  t1 = ı

  v1 : Raw
  v1 = var 3

  v2 : Raw
  v2 = lam t1 v1

  Cxt = List Type
  {-
  v3 : Raw
  v3 = lam (ı ⇒ ı) {!!} $ var 3

  succ : Raw
  succ = lam {!!} (lam {!!} (lam {!!} (var 1 $ (var 2 $ var 1 $ var 0))))
  -}

  data Term (Γ : Cxt) : Type → Set where
    var : ∀ {τ} → τ ∈ Γ → Term Γ τ
    _$_ : ∀ {σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
    lam : ∀ σ {τ} → Term (σ ∷ Γ) τ → Term Γ (σ ⇒ τ)

  erase : ∀ {Γ τ} → Term Γ τ → Raw
  erase (var x)   = var (index x)
  erase (t $ u)   = erase t $ erase u
  erase (lam σ t) = lam σ (erase t)

  data Infer (Γ : Cxt) : Raw → Set where
    ok  : (τ : Type)(t : Term Γ τ) → Infer Γ (erase t)
    bad : {e : Raw} → Infer Γ e

  infer : (Γ : Cxt)(e : Raw) → Infer Γ e
   -- var
  infer Γ (var n) with Γ ! n
  infer Γ (var .(index i))      | inside σ i = ok σ (var i)
  infer Γ (var .(length Γ + n)) | outside n  = bad
   -- apply
  infer Γ (e1 $ e2) with infer Γ e1 | infer Γ e2
  infer Γ (e1 $ e2)         | bad          | _   = bad
  infer Γ (.(erase t) $ e2) | ok ı t       | _   = bad
  infer Γ (.(erase t) $ e2) | ok (σ ⇒ τ) t | bad = bad
  infer Γ (.(erase t1) $ .(erase t2)) | ok (σ ⇒ τ) t1 | ok σ' t2 with σ =?= σ'
  infer Γ (.(erase t1) $ .(erase t2)) | ok (σ ⇒ τ) t1 | ok σ' t2 | no  = bad
  infer Γ (.(erase t1) $ .(erase t2)) | ok (σ ⇒ τ) t1 | ok .σ t2 | yes = ok τ (t1 $ t2)
   -- lambda
  infer Γ (lam σ e) with infer (σ ∷ Γ) e
  infer Γ (lam σ .(erase t)) | ok τ t = ok (σ ⇒ τ) (lam σ t)
  infer Γ (lam σ e)          | bad    = bad

module Exercise3-2 where

  infixr 30 _⇒_
  data Type : Set where
    ı   : Type
    _⇒_ : Type → Type → Type

  data _≠_ : Type → Type → Set where

  data Equal? : Type → Type → Set where
    yes : ∀ {τ}   → Equal? τ τ
    no  : ∀ {σ τ} → σ ≠ τ → Equal? σ τ
  {-
  _=?=_ : (σ τ : Type) → Equal? σ τ
  ı       =?= ı       = yes
  ı       =?= (_ ⇒ _) = no {!!}
  (_ ⇒ _) =?= ı       = no {!!}
  σ₁ ⇒ τ₁ =?= σ₂ ⇒ τ₂ with σ₁ =?= σ₂ | τ₁ =?= τ₂
  σ₁ ⇒ τ₁ =?= .σ₁ ⇒ .τ₁ | yes | yes = yes
  σ₁ ⇒ τ₁ =?= σ₂ ⇒ τ₂   | _   | _   = no {!!}

  infixl 80 _$_
  data Raw : Set where
    var : Nat → Raw
    _$_ : Raw → Raw → Raw -- function application
    lam : Type → Raw → Raw

  Cxt = List Type

  data Term (Γ : Cxt) : Type → Set where
    var : ∀ {τ} → τ ∈ Γ → Term Γ τ
    _$_ : ∀ {σ τ} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
    lam : ∀ σ {τ} → Term (σ ∷ Γ) τ → Term Γ (σ ⇒ τ)

  erase : ∀ {Γ τ} → Term Γ τ → Raw
  erase (var x)   = var (index x)
  erase (t $ u)   = erase t $ erase u
  erase (lam σ t) = lam σ (erase t)

  data BadTerm (Γ : Cxt) : Set where
    bvar : (n : Nat) → BadTerm Γ

  eraseBad : {Γ : Cxt} → BadTerm Γ → Raw
  eraseBad (bvar n) = var n
  --eraseBad

  data Infer (Γ : Cxt) : Raw → Set where
    ok  : (τ : Type)(t : Term Γ τ) → Infer Γ (erase t)
    bad : (b : BadTerm Γ) → Infer Γ (eraseBad b)

  infer : (Γ : Cxt)(e : Raw) → Infer Γ e
  infer Γ (var n) with Γ ! n
  infer Γ (var .(index i))      | inside σ i = ok σ (var i)
  infer Γ (var .(length Γ + n)) | outside n  = bad (bvar (length Γ + n))
  infer Γ (e $ e₁) = {!!}
  infer Γ (lam x e) = {!!}
  -}
{-
   -- var
  infer Γ (var n) with Γ ! n
  infer Γ (var .(index i))      | inside σ i = ok σ (var i)
  infer Γ (var .(length Γ + n)) | outside n  = ? --bad ?
   -- apply
  infer Γ (e1 $ e2) with infer Γ e1 | infer Γ e2
  infer Γ (e1 $ e2)         | _        | _   = bad 
  infer Γ (.(erase t) $ e2) | ok ı t       | _   = bad 
  infer Γ (.(erase t) $ e2) | ok (σ ⇒ τ) t | bad b  = bad
  infer Γ (.(erase t1) $ .(erase t2)) | ok (σ ⇒ τ) t1 | ok σ' t2 with σ =?= σ'
  infer Γ (.(erase t1) $ .(erase t2)) | ok (σ ⇒ τ) t1 | ok σ' t2 | no prf = bad
  infer Γ (.(erase t1) $ .(erase t2)) | ok (σ ⇒ τ) t1 | ok .σ t2 | yes = ok τ (t1 $ t2)  
 -- lambda
  infer Γ (lam σ e) with infer (σ ∷ Γ) e
  infer Γ (lam σ .(erase t)) | ok τ t = ok (σ ⇒ τ) (lam σ t)
  infer Γ (lam σ e)          | bad    = bad
-}

module Exercise3-3 where
  filter : {A : Set} → (A → Bool) → List A → List A
  filter p []        = []
  filter p (x ∷ xs) with p x
  ... | true  = x ∷ filter p xs
  ... | false = filter p xs

  lemma-All-∈ : ∀ {A x xs} {P : A → Set} → All P xs → x ∈ xs → P x
  lemma-All-∈ all[] ()
  lemma-All-∈ (px :all: pxs) hd        = px
  lemma-All-∈ (px :all: pxs) (tl x∈xs) = lemma-All-∈ pxs x∈xs

  lem-filter-sound : {A : Set}(p : A → Bool)(xs : List A) → All (satisfies p) (filter p xs)
  lem-filter-sound p []       = all[]
  lem-filter-sound p (x ∷ xs) with inspect (p x)
  lem-filter-sound p (x ∷ xs) | it y prf with p x | prf
  lem-filter-sound p (x ∷ xs) | it .true  prf | true  | refl = trueIsTrue prf :all: lem-filter-sound p xs
  lem-filter-sound p (x ∷ xs) | it .false prf | false | refl = lem-filter-sound p xs

  lem-filter-complete : {A : Set}(p : A → Bool)(x : A){xs : List A} → x ∈ xs → satisfies p x → x ∈ filter p xs
  lem-filter-complete p x {[]} () px
  lem-filter-complete p x {.x ∷ xs} hd       px with inspect (p x)
  lem-filter-complete p x {.x ∷ xs} hd px | it b prf with p x | prf
  lem-filter-complete p x {.x ∷ xs} hd px | it .true prf  | true  | refl = hd
  lem-filter-complete p x {.x ∷ xs} hd () | it .false prf | false | refl
  lem-filter-complete p x {y ∷ xs} (tl x∈xs) px with inspect (p x)
  lem-filter-complete p x {y ∷ xs} (tl x∈xs) px | it z prf with p x | prf 
  lem-filter-complete p x {y ∷ xs} (tl x∈xs) px | it .true prf  | true  | refl with inspect (p y)
  lem-filter-complete p x {y ∷ xs} (tl x∈xs) px | it .true prf  | true  | refl | it z2 prf2 with p y | prf2
  lem-filter-complete p x {y ∷ xs} (tl x∈xs) px | it .true prf  | true  | refl | it .true  prf2 | true  | refl 
    = tl (lem-filter-complete p x {xs} x∈xs (trueIsTrue prf))
  lem-filter-complete p x {y ∷ xs} (tl x∈xs) px | it .true prf  | true  | refl | it .false prf2 | false | refl 
    = lem-filter-complete p x {xs} x∈xs (trueIsTrue prf)
  lem-filter-complete p x {y ∷ xs} (tl x∈xs) () | it .false prf | false | refl

module Exercise3-4 where
  open import Data.String renaming (_++_ to _+++_)
  Tag = String
  
  mutual
    data Schema : Set where
      tag : Tag → List Child → Schema

    data Child : Set where
      text : Child
      elem : Nat → Nat → Schema → Child

  data BList (A : Set) : Nat → Set where
    [] : ∀ {n} → BList A n
    _::_ : ∀ {n} → A → BList A n → BList A (suc n)

  data Cons (A B : Set) : Set where
    _::_ : A → B → Cons A B

  FList : Set → Nat → Nat → Set
  FList A zero m          = BList A m
  FList A (suc n) zero    = ⊥
  FList A (suc n) (suc m) = Cons A (FList A n m)

  mutual
    data XML : Schema → Set where
      element : ∀ {kids}{t : Tag} → All Element kids → XML (tag t kids)

    Element : Child → Set
    Element text = String
    Element (elem n m s) = FList (XML s) n m

  schema1 : Schema
  schema1 = tag "Root" (text ∷ elem 0 1 (tag "Leaf" []) ∷ [])

  sampleXML : XML schema1
  sampleXML = element ("piyo" :all: (element all[] :: []) :all: all[])

  mutual
    printXML : {s : Schema} → XML s → String
    printXML {tag t kids} (element {.kids} {.t} elements) 
      = "<" +++ t +++ ">" +++ printChildren elements +++ "</" +++ t +++ ">"

    printChildren : {kids : List Child} → All Element kids → String
    printChildren all[] = ""
    printChildren {text ∷ xs}                   (str :all: cs) = str +++ printChildren cs
    printChildren {elem zero     zero   s ∷ xs} ([] :all: cs)  = printChildren cs
    printChildren {elem zero    (suc m) s ∷ xs} ([] :all: cs)  = printChildren cs
    printChildren {elem zero    (suc m) s ∷ xs} ((x :: bl) :all: cs) = printXML x +++ printChildren {elem zero m s ∷ xs} (bl :all: cs)
    printChildren {elem (suc n)  zero   s ∷ xs} (() :all: cs)
    printChildren {elem (suc n) (suc m) s ∷ xs} ((x :: fl) :all: cs) = printXML x +++ printChildren {elem n m s ∷ xs} (fl :all: cs)

open Exercise3-4 public

