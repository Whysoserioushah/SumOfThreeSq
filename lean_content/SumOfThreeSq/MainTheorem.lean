import SumOfThreeSq.ForwardDirection
import SumOfThreeSq.InverseDirection

theorem Nat.sum_threeSq_iff (n : ℕ) : (∃ a b c : ℤ, n = a ^ 2 + b ^ 2 + c ^ 2) ↔
    ∀ a k : ℕ, n ≠ 4 ^ a * (8 * k + 7) := by
  constructor
  · intro h
    by_contra! h'
    have := Nat.not_sum_of_three_sq _ h'
    tauto
  · intro h1
    have : n % 8 ≠ 7 := by
      specialize h1 0
      simp at h1
      intro h
      simp [Nat.mod_eq_iff] at h
      tauto
    let d := n / (4 ^ n.factorization 4)
    have hn : n = d * 4 ^ n.factorization 4 := mul_comm d _ ▸
      (Nat.mul_div_cancel' (ordProj_dvd n 4)).symm
    have hd1 : ¬ 4 ∣ d := by sorry
    rcases (by grind : d % 8 = 1 ∨ d % 8 = 2 ∨ d % 8 = 3 ∨ d % 8 = 5 ∨ d % 8 = 6 ∨
      d % 8 = 7) with h | h | h | h | h | h
    · obtain ⟨a0, b0, c0, habc⟩ := Nat.sum_threeSq_of_mod_eight_eq_one h
      use a0 * 2 ^ n.factorization 4, b0 * 2 ^ n.factorization 4, c0 * 2 ^ n.factorization 4
      simp [mul_pow]
      nth_rw 1 [hn, show (4 ^ n.factorization 4) = (2 ^ n.factorization 4) ^ 2 by
        rw [show 4 = 2 ^ 2 by rfl, ← pow_mul, mul_comm 2, pow_mul], Nat.cast_mul, habc]
      rw [← add_mul, ← add_mul]
      congr
    · have hdd : d % 4 = 2 := by grind
      obtain ⟨a0, b0, c0, habc⟩ := Nat.mod_four_eq_two_to_sum_threeSq _ hdd
      use a0 * 2 ^ n.factorization 4, b0 * 2 ^ n.factorization 4, c0 * 2 ^ n.factorization 4
      simp [mul_pow]
      nth_rw 1 [hn, show (4 ^ n.factorization 4) = (2 ^ n.factorization 4) ^ 2 by
        rw [show 4 = 2 ^ 2 by rfl, ← pow_mul, mul_comm 2, pow_mul], Nat.cast_mul, habc]
      rw [← add_mul, ← add_mul]
      congr
    · obtain ⟨a0, b0, c0, habc⟩ := Nat.sum_threeSq_of_mod_eight_eq_three h
      use a0 * 2 ^ n.factorization 4, b0 * 2 ^ n.factorization 4, c0 * 2 ^ n.factorization 4
      simp [mul_pow]
      nth_rw 1 [hn, show (4 ^ n.factorization 4) = (2 ^ n.factorization 4) ^ 2 by
        rw [show 4 = 2 ^ 2 by rfl, ← pow_mul, mul_comm 2, pow_mul], Nat.cast_mul, habc]
      rw [← add_mul, ← add_mul]
      congr
    · obtain ⟨a0, b0, c0, habc⟩ := Nat.sum_threeSq_of_mod_eight_eq_five h
      use a0 * 2 ^ n.factorization 4, b0 * 2 ^ n.factorization 4, c0 * 2 ^ n.factorization 4
      simp [mul_pow]
      nth_rw 1 [hn, show (4 ^ n.factorization 4) = (2 ^ n.factorization 4) ^ 2 by
        rw [show 4 = 2 ^ 2 by rfl, ← pow_mul, mul_comm 2, pow_mul], Nat.cast_mul, habc]
      rw [← add_mul, ← add_mul]
      congr
    · have hdd : d % 4 = 2 := by grind
      obtain ⟨a0, b0, c0, habc⟩ := Nat.mod_four_eq_two_to_sum_threeSq _ hdd
      use a0 * 2 ^ n.factorization 4, b0 * 2 ^ n.factorization 4, c0 * 2 ^ n.factorization 4
      simp [mul_pow]
      nth_rw 1 [hn, show (4 ^ n.factorization 4) = (2 ^ n.factorization 4) ^ 2 by
        rw [show 4 = 2 ^ 2 by rfl, ← pow_mul, mul_comm 2, pow_mul], Nat.cast_mul, habc]
      rw [← add_mul, ← add_mul]
      congr
    · obtain ⟨k, hk⟩ := by simpa [Nat.mod_eq_iff] using h
      specialize h1 (n.factorization 4) k
      grind
