import SumOfThreeSq.Mathlib.SpecialLinearGroup.Basic

open Matrix.SpecialLinearGroup

lemma binaryQuadMap_bound1 (d : ℤ) (x : Quotient (EquivalentQuad 2)) (hx : ∀ Q : PosDefQuadMap 2,
    Quotient.mk'' Q = x → Q.matrix.det = d) : ∃ Q : PosDefQuadMap 2, x = Quotient.mk'' Q ∧
    2 * |Q.matrix 0 1| ≤ Q.matrix 0 0 ∧ Q.matrix 0 0 ≤ (2 / (Real.sqrt 3)) * Real.sqrt d := by
  sorry

theorem binaryQuadMap_of_det_eq_one (Q : PosDefQuadMap 2) (hQ : Q.matrix.det = 1) :
    rel Q.matrix 1 := by
  sorry
