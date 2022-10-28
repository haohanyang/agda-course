open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Bool

add : Nat → Nat → Nat
add x y = x + y

mul : Nat → Nat → Nat
mul m zero = zero
mul m (suc n) = m + mul m n

fac : Nat → Nat
fac zero = 1
fac (suc m) = (m + 1) * fac m


xs = 1 ∷ 3 ∷ 5 ∷ 7 ∷ []
ys = 2 ∷ 4 ∷ 6 ∷ 8 ∷ []


concat : ∀ {a : Set} → List a → List a → List a
concat [] ls₂ = ls₂
concat (x₁ ∷ ls₁) ls₂ = x₁ ∷ (concat ls₁ ls₂)

if_then_else_ :  Bool → List Nat → List Nat →  List Nat
if true then t else e = t
if false then t else e = e

merge : List Nat → List Nat → List Nat
merge []  ls₂ = ls₂
merge ls₁ [] = ls₁
merge (x₁ ∷ ls₁) (x₂ ∷ ls₂) =
  if (x₁ < x₂) then (x₁ ∷ (merge ls₁ (x₂ ∷ ls₂))) else (x₂ ∷ merge(x₁ ∷ ls₁) ls₂)

_++_ = concat
infixr 2 _++_

data Tree (a : Set) : Set where
    Leaf : a → Tree a
    Node : a → Tree a → Tree a → Tree a

tree = Node 2 (Leaf 3) (Leaf 4)

inorder : ∀ {a : Set} → Tree a → List a
inorder (Leaf x₁) = x₁ ∷ []
inorder (Node x₁ t t₁) = inorder t ++ x₁ ∷ inorder t₁

vec-add : List Nat → List Nat → List Nat
vec-add [] ls₂ = ls₂
vec-add ls₁ [] = ls₁
vec-add (x₁ ∷ ls₁) (x₂ ∷ ls₂) = (x₁ + x₂) ∷ vec-add ls₁ ls₂


data Vec : (n : Nat) → Set where
  [] : Vec 0
  _::_ : ∀ {n} → Nat → Vec n → Vec (1 + n)

infixr 10 _::_

vec1 = 1 :: 2 :: 3 :: 4 :: []
vec2 = 5 :: 6 :: 7 :: 8 :: []

vec-add2 : ∀ {n} → Vec n → Vec n → Vec n
vec-add2 [] [] = []
vec-add2 (x₁ :: v₁) (x₂ :: v₂) = (x₁ + x₂) :: vec-add2 v₁ v₂

vec-dot : ∀ {n} → Vec n → Vec n → Nat
vec-dot [] [] = 0
vec-dot (x₁ :: v₁) (x₂ :: v₂) = x₁ * x₂ + vec-dot v₁ v₂

vec-con : ∀ {m n} → Vec m → Vec n → Vec (m + n)
vec-con [] v₂ = v₂
vec-con (x :: v₁) v₂ = x :: vec-con v₁ v₂

-- assignments:
-- 1. use infix operators for vec-add, vec-dot and vec-con
-- 2. make Vec polymorphic
