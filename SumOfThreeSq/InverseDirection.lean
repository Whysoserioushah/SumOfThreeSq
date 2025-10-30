import Mathlib

lemma Int.sq_mod_eight (n : ℤ) : n ^ 2 ≡ 0 [ZMOD 8] ∨ n ^ 2 ≡ 1 [ZMOD 8] ∨ n ^ 2 ≡ 4 [ZMOD 8] := by
  if hn1 : Odd n then
  right; left
  change _ ≡ 1 [ZMOD 8]
  rw [Int.modEq_iff_dvd, dvd_sub_comm]
  exact_mod_cast (eight_dvd_sq_sub_one_of_odd hn1)
  else if hn2 : Odd (n / 2) then
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, n = 2 * (2 * k + 1) := ⟨n / 4, by grind⟩
  right; right
  ring_nf
  change _ ≡ 4 [ZMOD 8]
  rw [Int.modEq_iff_dvd, dvd_sub_comm, add_assoc, add_comm, Int.add_sub_cancel, ← add_mul]
  exact dvd_trans (by decide : (8 : ℤ) ∣ 16) <| Int.dvd_mul_left _ _
  else
  left
  obtain ⟨k, hk⟩ := by simpa [Even, ← two_mul] using hn2
  exact (by grind : n = 2 * (n / 2)) ▸ hk ▸ by ring_nf; grind [Int.ModEq]

lemma Nat.sq_mod_eight (n : ℕ) : n ^ 2 % 8 = 0 ∨ n ^ 2 % 8 = 1 ∨ n ^ 2 % 8 = 4 := by
  exact_mod_cast Int.sq_mod_eight n

@[grind →]
lemma sum_three_sqaure_mod_four1 {x1 x2 x3 : ℤ} (h1 : Even x1) (h2 : Even x2) (h3 : Odd x3) :
    x1 ^ 2 + x2 ^ 2 + x3 ^ 2 ≡ 1 [ZMOD 4] := add_comm _ (x3 ^ 2) ▸ (dvd_add (pow_dvd_pow_of_dvd
  (by grind : (2 : ℤ) ∣ x1) 2) <| pow_dvd_pow_of_dvd (by grind : (2 : ℤ) ∣ x2) 2).choose_spec ▸
  (Int.modEq_add_fac_self.trans <|Int.sq_mod_four_eq_one_of_odd h3)

@[grind →]
lemma sum_three_square_mod_four2 {x1 x2 x3 : ℤ} (h1 : Odd x1) (h2 : Odd x2) (h3 : Even x3) :
    x1 ^ 2 + x2 ^ 2 + x3 ^ 2 ≡ 2 [ZMOD 4] := pow_dvd_pow_of_dvd (by grind : (2 : ℤ) ∣ x3) 2
  |>.choose_spec ▸ Int.modEq_add_fac_self.trans <| show _ ≡ 1 + 1 [ZMOD 4] from
  Int.ModEq.add (Int.sq_mod_four_eq_one_of_odd h1) <| Int.sq_mod_four_eq_one_of_odd h2

lemma sum_of_three_sq_even_iff (x x1 x2 x3 : ℤ) (hx : x = x1 ^ 2 + x2 ^ 2 + x3 ^ 2) :
    (4 ∣ x) ↔ Even x1 ∧ Even x2 ∧ Even x3 := ⟨hx ▸ fun h ↦ by
  replace h := Int.modEq_zero_iff_dvd.2 h
  rcases x1.even_or_odd with h1 | h1 <;> rcases x2.even_or_odd with h2 | h2 <;>
  rcases x3.even_or_odd with h3 | h3
  · exact ⟨h1, h2, h3⟩
  all_goals exfalso
  all_goals try exact zero_ne_one <| h.symm.trans <| (by grind : _ ≡ 1 [ZMOD 4])
  all_goals try exact two_ne_zero <| eq_comm.2 (by grind : _ ≡ 2 [ZMOD 4])|>.trans h
  exact three_ne_zero <| eq_comm.2 (Int.ModEq.add (Int.ModEq.add (Int.sq_mod_four_eq_one_of_odd h1)
    (Int.sq_mod_four_eq_one_of_odd h2)) (Int.sq_mod_four_eq_one_of_odd h3) :
    _ ≡ 1 + 1 + 1 [ZMOD 4])|>.trans h ,
  fun ⟨h1, h2, h3⟩ ↦ hx ▸ by
  refine Int.dvd_add (Int.dvd_add ?_ ?_) ?_ <;>
  exact (by omega : (4 : ℤ) = 2 ^ 2) ▸ pow_dvd_pow_of_dvd (by grind : (2 : ℤ) ∣ _) 2⟩

lemma Int.div_pow {a b : ℤ} (n : ℕ) (hxy : b ∣ a) : (a / b) ^ n = a ^ n / b ^ n := by
  obtain ⟨c, rfl⟩ := hxy
  obtain rfl | hb := eq_or_ne b 0
  · obtain rfl | hn := eq_or_ne n 0 <;> simp [*]
  · simp [hb, mul_pow]

theorem Nat.not_sum_of_three_sq (x : ℤ) (hx : ∃ a k : ℕ, x = 4 ^ a * (8 * k + 7)) :
    ∀ x1 x2 x3 : ℤ, x ≠ x1 ^ 2 + x2 ^ 2 + x3 ^ 2 := fun x1 x2 x3 h ↦ by
  obtain ⟨a, k, rfl⟩ := hx
  have h0 := congr((· % 8) $h)
  revert h0 h k x1 x2 x3
  induction a with
  | zero =>
    intro x1 x2 x3 k h h0
    simp at h
    rcases Int.sq_mod_eight x1 with h1 | h1 | h1
    <;> rcases Int.sq_mod_eight x2 with h2 | h2 | h2
    <;> rcases Int.sq_mod_eight x3 with h3 | h3 | h3
    <;> simp only [pow_zero, one_mul, Int.mul_add_emod_self_left, Int.reduceMod] at h0
    <;> rw [Int.ModEq.add (Int.ModEq.add h1 h2) h3] at h0
    <;> simp_all
  | succ n ih =>
    intro x1 x2 x3 k h h0
    have hdiv4 : 4 ∣ x1 ^ 2 + x2 ^ 2 + x3 ^ 2 := by
      rw [← h, Int.pow_succ', mul_assoc]; exact Int.dvd_mul_right _ _
    obtain ⟨hev1, hev2, hev3⟩ := (sum_of_three_sq_even_iff _ _ _ _ rfl).1 hdiv4
    have : 4 ^ n * (8 * ↑k + 7) = (x1 / 2) ^ 2 + (x2 / 2) ^ 2 + (x3 / 2) ^ 2 := by
      rw [even_iff_two_dvd] at hev1 hev2 hev3
      rw [Int.div_pow 2 hev1, Int.div_pow 2 hev2, Int.div_pow 2 hev3,
        ← Int.add_ediv_of_dvd_left (pow_dvd_pow_of_dvd hev1 2),
        ← Int.add_ediv_of_dvd_right (pow_dvd_pow_of_dvd hev3 2)]
      apply mul_right_injective₀ (by omega : (4 : ℤ) ≠ 0); convert h using 1
      <;> simp only [Int.reducePow, Int.mul_ediv_cancel' hdiv4]; ring
    exact ih (x1 / 2) (x2 / 2) (x3 / 2) k this congr((· %8) $this)

