import SumOfThreeSq.Mathlib.LinearAlgebra.QuadraticForm.Tenary
import SumOfThreeSq.Mathlib.LinearAlgebra.QuadraticForm.Binary

-- #help tactic grw (transparency )
lemma Nat.quadResidue_to_sum_threeSq (n : ℕ) (hn1 : 2 ≤ n) (hn2 : ∃ d' : ℕ,
    0 < d' ∧ IsSquare (-d' : ZMod (d' * n - 1))) :
    ∃ a b c : ℤ, n = a ^ 2 + b ^ 2 + c ^ 2 := by
  obtain ⟨d', hdpos, ha⟩ := hn2
  obtain ⟨a12', ha⟩ := ZMod.exists.1 ha
  haveI := mul_comm n _ ▸ mul_one 2 ▸ mul_le_mul hn1 hdpos (by grind) (by grind)
  haveI : NeZero (d' * n - 1) := ⟨ne_of_gt <| lt_of_lt_of_le (by decide : 0 < 1) (by omega)⟩
  rw [← Int.cast_natCast, ← Int.cast_neg, ZMod.intCast_eq_iff] at ha
  obtain ⟨a11', ha11⟩ := ha
  rw [neg_eq_iff_add_eq_zero, ← add_assoc, add_comm (d' : ℤ), ← eq_neg_iff_add_eq_zero,
    ← mul_neg, ZMod.val_mul, Nat.mod_eq_sub_div_mul] at ha11
  rw [Nat.cast_sub (div_mul_le_self ..)] at ha11
  simp only [cast_mul, ZMod.natCast_val, Int.natCast_ediv] at ha11
  rw [add_comm, add_sub, sub_eq_iff_eq_add, mul_comm _ ((d' * n - 1 : ℕ) : ℤ), ← mul_add,
    mul_comm ((d' * n - 1 : ℕ) : ℤ), add_comm] at ha11
  set a12 := (a12' : ZMod (d' * n - 1)).cast (R := ℤ) with a12_eq
  set a11 := (-a11' + a12 * a12 / ↑(d' * n - 1)) with a11_eq
  set a22 := ((d' * n - 1 : ℕ) : ℤ) with a22_eq

  -- set k := ((a12 : ZMod (d' * n - 1)).cast * (a12 : ZMod (d' * n - 1)).cast) /
  --   ((d' * n - 1 : ℕ) : ℤ) with k_eq
  -- rw [← k_eq] at ha11
  -- obtain ⟨a11, a12, ha'⟩ : ∃ a11 a12 : ℤ, a12 ^ 2 + d'
  sorry

lemma Nat.mod_four_eq_two_to_sum_threeSq (n : ℕ) (hn : n % 4 = 2) :
    ∃ a b c : ℤ, n = a ^ 2 + b ^ 2 + c ^ 2 := by
  sorry

lemma Nat.mod_four_odd_not_five_to_sum_threeSq (n : ℕ) (hn : n % 4 = 1 ∨ n % 4 = 3 ∨ n % 4 = 5) :
    ∃ a b c : ℤ, n = a ^ 2 + b ^ 2 + c ^ 2 := by
  sorry

-- final theorem goes here
