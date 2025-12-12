import SumOfThreeSq.ForwardDirection
import SumOfThreeSq.InverseDirection

-- I made a stupid mistake here, `n.factorization 4` is `0` since `4` is not prime.
theorem Nat.sum_threeSq_iff (n : ℕ) : (∃ a b c : ℤ, n = a ^ 2 + b ^ 2 + c ^ 2) ↔
    ∀ a k : ℕ, n ≠ 4 ^ a * (8 * k + 7) := by
  constructor
  · intro h
    by_contra! h'
    absurd h; push_neg; exact Nat.not_sum_of_three_sq _ h'
  · intro h1
    if hn1 : n = 0 then exact ⟨0, 0, 0, by simpa⟩ else
    have hn2 : n % 8 ≠ 7 := by
      specialize h1 0
      simp at h1
      intro h
      simp [Nat.mod_eq_iff] at h
      tauto
    set d := n / (2 ^ n.factorization 2) with d_def
    have hn : n = d * 2 ^ n.factorization 2 := mul_comm d _ ▸
      (Nat.mul_div_cancel' (ordProj_dvd n 2)).symm
    if hn3 : Even (n.factorization 2) then
    have : ¬ 2 ∣ d := @Nat.not_dvd_ordCompl n 2 prime_two hn1
    have : d % 8 ≠ 7 := fun h ↦ by
      obtain ⟨k, hk⟩ : ∃ k, d = 8 * k + 7 := Nat.mod_eq_iff.1 h|>.resolve_left (by grind)|>.2
      have := h1 (n.factorization 2 / 2) k
      rw [show 4 = 2 ^ 2 by rfl, ← pow_mul, Nat.mul_div_cancel' (even_iff_two_dvd.mp hn3),
        ← hk, mul_comm] at this
      exact this hn
    rcases (by grind : d % 8 = 1 ∨ d % 8 = 3 ∨ d % 8 = 5) with h | h | h
    · obtain ⟨a0, b0, c0, habc⟩ := Nat.sum_threeSq_of_mod_eight_eq_one h
      use a0 * 2 ^ (n.factorization 2 / 2), b0 * 2 ^ (n.factorization 2 / 2),
        c0 * 2 ^ (n.factorization 2 / 2)
      simp only [mul_pow, ← add_mul]
      nth_rw 1 [hn]
      simp only [cast_mul, habc, cast_pow, cast_ofNat, mul_eq_mul_left_iff]
      left; rw [← pow_mul]; grind
    · obtain ⟨a0, b0, c0, habc⟩ := Nat.sum_threeSq_of_mod_eight_eq_three h
      use a0 * 2 ^ (n.factorization 2 / 2), b0 * 2 ^ (n.factorization 2 / 2),
        c0 * 2 ^ (n.factorization 2 / 2)
      simp only [mul_pow, ← add_mul]
      nth_rw 1 [hn]
      simp only [cast_mul, habc, cast_pow, cast_ofNat, mul_eq_mul_left_iff]
      left; rw [← pow_mul]; grind
    · obtain ⟨a0, b0, c0, habc⟩ := Nat.sum_threeSq_of_mod_eight_eq_five h
      use a0 * 2 ^ (n.factorization 2 / 2), b0 * 2 ^ (n.factorization 2 / 2),
        c0 * 2 ^ (n.factorization 2 / 2)
      simp only [mul_pow, ← add_mul]
      nth_rw 1 [hn]
      simp only [cast_mul, habc, cast_pow, cast_ofNat, mul_eq_mul_left_iff]
      left; rw [← pow_mul]; grind
    else
    set d' := n / (2 ^ (n.factorization 2 - 1)) with d'_def
    simp at hn3
    have hd' : n = d' * 2 ^ (n.factorization 2 - 1) := mul_comm d' _ ▸
      (Nat.mul_div_cancel' (dvd_trans (pow_dvd_pow 2 (by omega)) <| ordProj_dvd n 2)).symm
    have hd'1 : 2 ∣ d' := ⟨d, by
      rw [d_def, d'_def]
      obtain ⟨k, hk⟩ := ordProj_dvd n 2
      nth_rw 1 [hk]; nth_rw 3 [hk]
      simp only [mul_comm, ne_eq, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, false_and,
        not_false_eq_true, mul_div_cancel_right₀]
      rw [Nat.mul_div_assoc k (pow_dvd_pow 2 (by omega)), Nat.pow_div (by omega) (by decide),
        Nat.sub_sub_self (by grind)]⟩
    have hd'2 : ¬ 4 ∣ d' := fun h ↦ by
      obtain ⟨k, hk⟩ := h
      rw [hk, show 4 = 2 * 2 by rfl, mul_assoc 2] at hd'; nth_rw 1 [hn] at hd'
      rw [mul_comm 2 k, ← mul_assoc, mul_assoc, ← pow_add_one', sub_one_add_one hn3.pos.ne'] at hd'
      simp only [mul_eq_mul_right_iff, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, ne_eq, false_and,
        or_false] at hd'
      exact @Nat.not_dvd_ordCompl n 2 prime_two hn1 ⟨k, hd'⟩
    have hdd : d' % 4 = 2 := by grind
    obtain ⟨a0, b0, c0, habc⟩ := Nat.mod_four_eq_two_to_sum_threeSq _ hdd
    use a0 * 2 ^ ((n.factorization 2 - 1) / 2), b0 * 2 ^ ((n.factorization 2 - 1) / 2),
      c0 * 2 ^ ((n.factorization 2 - 1) / 2)
    simp only [mul_pow, ← add_mul]
    nth_rw 1 [hd']
    simp only [cast_mul, habc, cast_pow, cast_ofNat, mul_eq_mul_left_iff]
    left; rw [← pow_mul]; grind
