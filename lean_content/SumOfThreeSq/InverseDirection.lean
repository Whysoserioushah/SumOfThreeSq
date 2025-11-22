import Mathlib.Data.ZMod.Basic

lemma sum_of_three_sq_even_iff (x1 x2 x3 : ℤ) :
    (4 ∣ x1 ^ 2 + x2 ^ 2 + x3 ^ 2) ↔ Even x1 ∧ Even x2 ∧ Even x3 := by
  have (n : ℤ) : Even n ↔ ZMod.castHom (show 2 ∣ 4 by decide) (ZMod 2) n = 0 := by
    simp [ZMod.intCast_eq_zero_iff_even]
  simp_rw [show (4 : ℤ) = (4 : ℕ) from rfl, ← ZMod.intCast_zmod_eq_zero_iff_dvd,
    Int.cast_add, Int.cast_pow, this]
  generalize ((_ : ℤ) : ZMod 4) = a
  generalize ((_ : ℤ) : ZMod 4) = b
  generalize ((_ : ℤ) : ZMod 4) = c
  decide +revert

theorem Int.not_sum_of_three_sq (x : ℤ) (hx : ∃ a k : ℕ, x = 4 ^ a * (8 * k + 7)) :
    ∀ x1 x2 x3 : ℤ, x ≠ x1 ^ 2 + x2 ^ 2 + x3 ^ 2 := fun x1 x2 x3 h ↦ by
  obtain ⟨a, k, rfl⟩ := hx
  induction a generalizing x1 x2 x3 with
  | zero =>
    replace h := congr(($h : ZMod 8))
    simp only [pow_zero, one_mul, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
      show (8 : ZMod 8) = 0 from rfl, Int.cast_natCast, zero_mul, zero_add, Int.cast_pow] at h
    generalize (x1 : ZMod 8) = x1, (x2 : ZMod 8) = x2, (x3 : ZMod 8) = x3 at h
    revert x1 x2 x3
    decide
  | succ a ih =>
    rw [Int.pow_succ', mul_assoc] at h
    have := (sum_of_three_sq_even_iff _ _ _).mp (h ▸ dvd_mul_right _ _)
    simp_rw [even_iff_two_dvd] at this
    obtain ⟨⟨x1, rfl⟩, ⟨x2, rfl⟩, ⟨x3, rfl⟩⟩ := this
    conv_rhs at h => equals 4 * (x1 ^ 2 + x2 ^ 2 + x3 ^ 2) => grind
    rw [mul_right_inj' (by decide)] at h
    tauto
