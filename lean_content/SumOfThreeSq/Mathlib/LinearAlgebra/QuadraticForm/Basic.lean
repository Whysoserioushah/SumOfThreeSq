import Mathlib.LinearAlgebra.QuadraticForm.Basic

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

lemma toQuadraticMap'_apply {A : Matrix n n R} (v : n → R) :
    A.toQuadraticMap' v = v ⬝ᵥ (A *ᵥ v) := by
  simp [toQuadraticMap', toLinearMap₂'_apply, dotProduct, mulVec, Finset.mul_sum, mul_comm]

lemma toQuadraticMap'_apply' {A : Matrix n n R} (v : n → R) :
    A.toQuadraticMap' v = ∑ i : n, ∑ j : n, A i j * v i * v j := by
  simpa [toQuadraticMap', toLinearMap₂'_apply] using Finset.sum_congr rfl
    fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring

-- lemma toQuadraticMap'_id (v : n → R) : (1 : Matrix n n R).toQuadraticMap' v = ∑ i, v i ^ 2 := by
--   sorry

end Matrix
