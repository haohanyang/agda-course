open import Agda.Builtin.Nat

data IsLessEqThan : Nat → Nat → Set where
  zero-leq-any : ∀ n → IsLessEqThan 0 n
  succ : ∀ m n → IsLessEqThan m n → IsLessEqThan (1 + m) (1 + n)
  
0<4 : IsLessEqThan 0 4
0<4 = zero-leq-any 4

1<4 : IsLessEqThan 1 4
1<4 = succ 0 3 (zero-leq-any 3)

-- m ≤ m
ax1 : ∀ m → IsLessEqThan m m
ax1 zero = zero-leq-any zero
ax1 (suc m) = succ m m (ax1 m)

-- m ≤ n, n ≤ p → m ≤ p
ax2 : ∀ m n p → IsLessEqThan m n → IsLessEqThan n p → IsLessEqThan m p
ax2 .0 n p (zero-leq-any .n) np =  zero-leq-any p
ax2 _ _ (suc p) (succ m n mn) (succ .n .p np) = succ m p (ax2 _ _ _ mn np)

-- m ≤ a + m
ax3 : ∀ m a → IsLessEqThan m (m + a)
ax3 zero a = zero-leq-any a
ax3 (suc m) a = succ _ _ (ax3 _ _)

-- m <= n + a -> m <= a + n
ax4 : ∀ n a → IsLessEqThan (a + n) (n + a) 
ax4 n zero = ax3 _ _
ax4 zero (suc a) = succ _ _ (ax4 zero a)
ax4 (suc n) (suc a) = succ _ _ {!ax4 (suc n) a!}

ax5 : ∀ m n a → IsLessEqThan m n → IsLessEqThan (a + m) (a + n) 
ax5 m n zero mn = mn
ax5 m n (suc a) mn = succ _ _ (ax5 _ _ a mn)

-- m ≤ n → m ≤ a + n 
proof1 : ∀ m n a → IsLessEqThan m n → IsLessEqThan m (a + n)
proof1 m n zero p = p
proof1 m n (suc a) p = ax2 _ _ _ (ax3 m (suc a)) (ax2 _ _ _ (ax4 (suc a) m) (succ _ _ (ax5 m n a p)))

