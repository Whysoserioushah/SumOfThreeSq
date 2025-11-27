import Mathlib.LinearAlgebra.QuadraticForm.Basic

def Int.IsRepresentedBy {n : ℤ} {ι} [Fintype ι] (Q : QuadraticMap ℤ (ι → ℤ) ℤ) : Prop :=
  ∃ v : ι → ℤ, Q v = n

lemma Int.isRepresentedBy_iff {n : ℤ} {ι} [Fintype ι] (Q : QuadraticMap ℤ (ι → ℤ) ℤ) :
    n.IsRepresentedBy Q ↔ ∃ v : ι → ℤ, Q v = n := Iff.rfl

namespace Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

lemma toQuadraticMap'_apply {A : Matrix n n R} (v : n → R) :
    A.toQuadraticMap' v = v ⬝ᵥ (A *ᵥ v) := by
  simp [toQuadraticMap', toLinearMap₂'_apply, dotProduct, mulVec, Finset.mul_sum, mul_comm]

-- lemma toQuadraticMap'_apply {A : Matrix n n R} (v : n → R) :
--     A.toQuadraticMap' v = ∑ i : n, ∑ j : n, A i j * v i * v j := by
--   sorry

-- lemma toQuadraticMap'_id (v : n → R) : (1 : Matrix n n R).toQuadraticMap' v = ∑ i, v i ^ 2 := by
--   sorry

end Matrix
