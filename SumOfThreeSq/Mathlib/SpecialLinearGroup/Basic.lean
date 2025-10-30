-- import Mathlib

-- variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

-- open Matrix

-- instance : SMul (SpecialLinearGroup n R) (Matrix n n R) where
--   smul U A := U.1 * A * Uᵀ

-- namespace SpecialLinearGroup

-- lemma smul_eq (U : SpecialLinearGroup n R) (A : Matrix n n R) :
--     U • A = U.1 * A * Uᵀ := rfl

-- @[simp, grind =]
-- lemma one_smul' (A : Matrix n n R) : (1 : SpecialLinearGroup n R) • A = A := by
--   simp [smul_eq]

-- @[simp, grind =]
-- lemma mul_smul' (U V : SpecialLinearGroup n R) (A : Matrix n n R) :
--     (U * V) • A = U • (V • A) := by
--   simp only [smul_eq, SpecialLinearGroup.coe_mul, transpose_mul]
--   rw [← mul_assoc, mul_assoc U.1 V.1, mul_assoc U.1]

-- instance : MulAction (SpecialLinearGroup n R) (Matrix n n R) where
--   one_smul := one_smul'
--   mul_smul := mul_smul'

-- end SpecialLinearGroup

-- namespace Matrix

-- def conjTransposeEquivAux : Matrix n n R → Matrix n n R → Prop :=
--   fun A B ↦ ∃ U : SpecialLinearGroup n R, U • A = B

-- end Matrix
