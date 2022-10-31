open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Bool

list-add : List Nat → List Nat → List Nat
list-add [] ls₂ = ls₂
list-add ls₁ [] = ls₁
list-add (x₁ ∷ ls₁) (x₂ ∷ ls₂) = (x₁ + x₂) ∷ list-add ls₁ ls₂

data Vec : (n : Nat) (a : Set) → Set where
  [] : ∀ {a} → Vec 0 a
  _::_ : ∀ {a n} → a → Vec n a → Vec (1 + n) a 

vec-op : ∀ {n} → (Nat → Nat → Nat) → Vec n Nat → Vec n Nat → Vec n Nat
vec-op _ [] [] = []
vec-op f (x₁ :: v₁) (x₂ :: v₂) = (f x₁ x₂) :: vec-op f v₁ v₂


vec-con : ∀ {m n} → Vec m Nat → Vec n Nat → Vec (m + n) Nat
vec-con [] v₂ = v₂
vec-con (x :: v₁) v₂ = x :: vec-con v₁ v₂


infixr 10 _::_

vec1 = 1 :: 2 :: 3 :: 4 :: []
vec2 = 5 :: 6 :: 7 :: 8 :: []

vec-add :  ∀ {n} → Vec n Nat → Vec n Nat → Vec n Nat
vec-add = vec-op _+_

_++_ = vec-add
infixr 8 _++_

vec-dot : ∀ {n} → Vec n Nat → Vec n Nat → Nat
vec-dot [] [] = 0
vec-dot (x₁ :: v₁) (x₂ :: v₂) = x₁ * x₂ + vec-dot v₁ v₂

_∙_ = vec-dot
infixr 9 _∙_

_+++_ = vec-con
infixr 10 _+++_

vec-ap : ∀ {a b n} → Vec n (a → b) → Vec n a → Vec n b
vec-ap [] [] = []
vec-ap (f :: fs) (x :: ele) = f x :: vec-ap fs ele

vec-pure : ∀{n a} → a → Vec n a
vec-pure {zero} _ = []
vec-pure {suc n} e = e :: vec-pure e

fmap : ∀{a b n} → (a → b) → Vec n a → Vec n b
fmap f = vec-ap (vec-pure f)

-- assignment:
--   1. reimplement all vector functions using vec-ap and vec-pure
--   2. to reimplement vec-dot, implement vec-fold function first  
        
