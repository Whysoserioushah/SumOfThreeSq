import SumOfThreeSq.ForwardDirection
import SumOfThreeSq.InverseDirection

theorem Nat.sum_threeSq_iff (n : ℕ) : ∃ a b c : ℤ, n = a ^ 2 + b ^ 2 + c ^ 2 ↔
    ∀ a k : ℕ, n ≠ 4 ^ a * (8 * k + 7) := by
  sorry
