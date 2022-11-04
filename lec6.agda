open import Agda.Builtin.Nat
infix 2 _≤_
infixr 20 _∘_

data _≤_ : Nat → Nat → Set where    -- IsLessEqThan
    z : ∀ {n} → zero ≤ n                -- zero-leq-any
    s : ∀{m n} → m ≤ n → suc m ≤ suc n  -- succ

_∘_ : ∀{a b c} → a ≤ b → b ≤ c → a ≤ c  -- ax3
z ∘ _ = z
s a≤b ∘ s b≤c = s (a≤b ∘ b≤c)

n≤n+a : ∀ a n → n ≤ n + a   -- ax4
n≤n+a _ zero = z
n≤n+a a (suc n) = s (n≤n+a a n)

a+b≤b+a : ∀ a b → a + b ≤ b + a -- ax5
a+b≤b+a zero zero = z
a+b≤b+a zero (suc b) = s (a+b≤b+a zero b)
a+b≤b+a (suc a) zero = s (a+b≤b+a a zero)
a+b≤b+a (suc a) (suc b) = s (a+b≤b+a a (suc b) ∘ s (a+b≤b+a b a) ∘ a+b≤b+a (suc a) b)

proof1 : ∀ m n a → m ≤ n → m ≤ a + n
proof1 m n a m≤n = m≤n ∘ n≤n+a a n ∘ a+b≤b+a n a
