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
ys = 2 ∷ 4 ∷ 6 ∷ []


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
