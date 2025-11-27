import SumOfThreeSq.Mathlib.LinearAlgebra.QuadraticForm.Tenary
import SumOfThreeSq.Mathlib.LinearAlgebra.QuadraticForm.Binary

lemma Nat.quadResidue_to_sum_threeSq (n : ℕ) (hn1 : 2 ≤ n) (hn2 : ∃ d' : ℕ,
    0 < d ∧ IsSquare (-d' : ZMod (d' * n - 1))) :
    ∃ a b c : ℤ, n = a ^ 2 + b ^ 2 + c ^ 2 := by
  sorry

lemma Nat.mod_four_eq_two_to_sum_threeSq (n : ℕ) (hn : n % 4 = 2) :
    ∃ a b c : ℤ, n = a ^ 2 + b ^ 2 + c ^ 2 := by
  sorry

lemma Nat.mod_four_odd_not_five_to_sum_threeSq (n : ℕ) (hn : n % 4 = 1 ∨ n % 4 = 3 ∨ n % 4 = 5) :
    ∃ a b c : ℤ, n = a ^ 2 + b ^ 2 + c ^ 2 := by
  sorry

-- final theorem goes here
