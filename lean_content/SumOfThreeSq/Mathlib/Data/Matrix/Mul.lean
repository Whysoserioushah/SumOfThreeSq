import Mathlib.Data.Matrix.Mul

variable {m n R : Type*} [Fintype m] [Fintype n] [CommSemiring R]

namespace Matrix

variable {x : m → R} {y : n → R} {M : Matrix m n R}

lemma dotProduct_mulVec_eq : x ⬝ᵥ (M *ᵥ y) = (Mᵀ *ᵥ x) ⬝ᵥ y := by
  simp [dotProduct_mulVec, mulVec_transpose]

lemma mulVec_dotProduct_eq : (M *ᵥ y) ⬝ᵥ x = y ⬝ᵥ (Mᵀ *ᵥ x) := by
  rw [dotProduct_mulVec_eq, transpose_transpose]

end Matrix
