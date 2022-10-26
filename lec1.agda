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


concat : List Nat → List Nat → List Nat
concat [] ls2 = ls2
concat (x₁ ∷ ls1) ls2 =  x₁ ∷ (concat ls1 ls2)
