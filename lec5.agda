open import Agda.Builtin.Nat

data IsLessEqThan : Nat → Nat → Set where
  zero-leq-any : ∀ n → IsLessEqThan 0 n
  succ : ∀ m n → IsLessEqThan m n → IsLessEqThan (1 + m) (1 + n)
  
0<4 : IsLessEqThan 0 4
0<4 = zero-leq-any 4

1<4 : IsLessEqThan 1 4
1<4 = succ 0 3 (zero-leq-any 3)

-- m ≤ n → m ≤ a + n 
proof1 : ∀ m n a → IsLessEqThan m n → IsLessEqThan m (a + n)
proof1 m n zero p = p
proof1 m n (suc a) p = {!!}

-- m ≤ m
ax1 : ∀ m → IsLessEqThan m m
ax1 zero = zero-leq-any zero
ax1 (suc m) = succ m m (ax1 m)
