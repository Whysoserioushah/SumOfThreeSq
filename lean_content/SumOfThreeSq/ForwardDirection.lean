import SumOfThreeSq.Mathlib.LinearAlgebra.QuadraticForm.Tenary
import SumOfThreeSq.Mathlib.LinearAlgebra.QuadraticForm.Binary

-- def A (n : ℕ) (hn1 : 2 ≤ n) (d' : ℕ) (hdpos : 0 < d')
--     (ha : IsSquare (-d' : ZMod (d' * n - 1))) (a12' : ℤ) (this_1 : 2 ≤ d' * n)
--     [NeZero (d' * n - 1)] (a11' : ℤ)
--     (ha11 : (a12' : ZMod (d' * n - 1)).cast * (a12' : ZMod (d' * n - 1)).cast + ↑d' =
--     (-a11' + (a12' : ZMod (d' * n - 1)).cast * (a12' : ZMod (d' * n - 1)).cast /
--     ↑(d' * n - 1)) * ↑(d' * n - 1)) :

private def A (n : ℕ) (d' : ℕ) (a12' : ℤ) (a11' : ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  ![![(-a11' + (a12' : ZMod (d' * n - 1)).cast * (a12' : ZMod (d' * n - 1)).cast / ↑(d' * n - 1)),
    (a12' : ZMod (d' * n - 1)).cast, 1], ![(a12' : ZMod (d' * n - 1)).cast,
    ((d' * n - 1 : ℕ) : ℤ), 0], ![1, 0, n]]

lemma A_isSymm (n d' : ℕ) (a12' a11' : ℤ) : Matrix.IsSymm (A n d' a12' a11') := by
  simp [Matrix.IsSymm.ext_iff, Fin.forall_fin_succ, A]

lemma A_det_eq_one (n d' : ℕ) (a12' a11' : ℤ) (ha11 : (a12' : ZMod (d' * n - 1)).cast *
    (a12' : ZMod (d' * n - 1)).cast + ↑d' = (-a11' + (a12' : ZMod (d' * n - 1)).cast *
    (a12' : ZMod (d' * n - 1)).cast / ↑(d' * n - 1)) * ↑(d' * n - 1)) (hdn : 2 ≤ d' * n) :
    Matrix.det (A n d' a12' a11') = 1 := by
  simp [A, Matrix.det_fin_three, ← ha11]
  ring_nf; omega

lemma A_PosDef (n d' : ℕ) (a12' a11' : ℤ)
    (ha11 : (a12' : ZMod (d' * n - 1)).cast * (a12' : ZMod (d' * n - 1)).cast + ↑d' =
    (-a11' + (a12' : ZMod (d' * n - 1)).cast * (a12' : ZMod (d' * n - 1)).cast /
    ↑(d' * n - 1)) * ↑(d' * n - 1)) (hdn : 2 ≤ d' * n) :
    (A n d' a12' a11').toQuadraticMap'.PosDef :=
  QuadraticMap.Tenary.PosDef_iff (A n d' a12' a11') (A_isSymm n d' a12' a11')|>.2
  ⟨by simp [A, -le_neg_add_iff_add_le]; sorry, by sorry,
    by simp [A_det_eq_one n d' a12' a11' ha11 hdn]⟩

def A_toPosDefQuad (n d' : ℕ) (a12' a11' : ℤ)
    (ha11 : (a12' : ZMod (d' * n - 1)).cast * (a12' : ZMod (d' * n - 1)).cast + ↑d' =
    (-a11' + (a12' : ZMod (d' * n - 1)).cast * (a12' : ZMod (d' * n - 1)).cast /
    ↑(d' * n - 1)) * ↑(d' * n - 1)) (hdn : 2 ≤ d' * n) :
    PosDefQuadMap 3 :=
  ⟨A n d' a12' a11', A_isSymm n d' a12' a11', A_PosDef n d' a12' a11' ha11 hdn⟩

def PosDefQuad.one (n : ℕ) : PosDefQuadMap n where
  matrix := 1
  isSymm := by simp
  posDef v hv := by
    simp [Matrix.toQuadraticMap'_apply', Matrix.one_apply]
    apply lt_of_le_of_ne
    · apply Finset.sum_nonneg
      intros i hi
      simp only [mul_self_nonneg]
    · intro h2
      rw [eq_comm, Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ by simp [mul_self_nonneg])] at h2
      apply hv
      ext i
      specialize h2 i (Finset.mem_univ i)
      simp_all

-- #help tactic grw (transparency )
open Matrix.SpecialLinearGroup in
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
  have : n.IsRepresentedBy (A_toPosDefQuad n d' a12' a11' ha11 (by omega)).1.toQuadraticMap' :=
    ⟨![0, 0, 1], by simp [A_toPosDefQuad, A, Matrix.toQuadraticMap'_apply', Fin.sum_univ_three]⟩
  obtain ⟨v, hv⟩ : n.IsRepresentedBy (PosDefQuad.one 3).1.toQuadraticMap' :=
    Nat.IsRepresentedBy.of_equiv _ _ (EquivalentQuad_iff.2 <| QuadraticMap.Tenary.det_eq_one
      (A_toPosDefQuad n d' a12' a11' ha11 (by omega))
      (A_det_eq_one n d' a12' a11' ha11 (by omega))) this
  use v 0, v 1, v 2
  simp [PosDefQuad.one, Matrix.toQuadraticMap'_apply', Matrix.one_apply,
    eq_comm, Fin.sum_univ_three, ← pow_two] at hv
  exact hv


lemma Nat.mod_four_eq_two_to_sum_threeSq (n : ℕ) (hn : n % 4 = 2) :
    ∃ a b c : ℤ, n = a ^ 2 + b ^ 2 + c ^ 2 := by
  sorry

lemma Nat.mod_four_odd_not_five_to_sum_threeSq (n : ℕ) (hn : n % 4 = 1 ∨ n % 4 = 3 ∨ n % 4 = 5) :
    ∃ a b c : ℤ, n = a ^ 2 + b ^ 2 + c ^ 2 := by
  sorry

-- final theorem goes here
