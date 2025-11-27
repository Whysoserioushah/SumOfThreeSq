import SumOfThreeSq.Mathlib.SpecialLinearGroup.Basic

lemma binaryQuadMap_bound1 (d : ℤ) :
    ∃ Q : PosDefQuadMap 2, Q.matrix.det = d ∧
    2 * |Q.matrix 0 1| ≤ Q.matrix 0 0 ∧ Q.matrix 0 0 ≤ (2 / (Real.sqrt 3)) * Real.sqrt d := by
  sorry

open Matrix.SpecialLinearGroup in
theorem binaryQuadMap_of_det_eq_one (Q : PosDefQuadMap 2) (hQ : Q.matrix.det = 1) :
    rel Q.matrix 1 := by
  sorry
