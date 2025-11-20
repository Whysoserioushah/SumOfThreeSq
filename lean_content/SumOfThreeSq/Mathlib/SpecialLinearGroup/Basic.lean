import Mathlib

-- #check ConjAct

-- import Mathlib

variable (n : ℕ) in
#check (@Matrix.toQuadraticMap' ℤ (Fin n) _ _ _ 1).toFun

-- import Mathlib

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

open Matrix

instance : SMul (SpecialLinearGroup n R) (Matrix n n R) where
  smul U A := U.1 * A * Uᵀ

namespace SpecialLinearGroup

lemma smul_eq (U : SpecialLinearGroup n R) (A : Matrix n n R) :
    U • A = U.1 * A * U.1ᵀ := rfl

@[simp, grind =]
lemma one_smul' (A : Matrix n n R) : (1 : SpecialLinearGroup n R) • A = A := by
  simp [smul_eq]

@[simp, grind =]
lemma mul_smul' (U V : SpecialLinearGroup n R) (A : Matrix n n R) :
    (U * V) • A = U • (V • A) := by
  simp only [smul_eq, Matrix.SpecialLinearGroup.coe_mul, transpose_mul]
  rw [← mul_assoc, mul_assoc U.1 V.1, mul_assoc U.1]

instance : MulAction (SpecialLinearGroup n R) (Matrix n n R) where
  one_smul := one_smul'
  mul_smul := mul_smul'

end SpecialLinearGroup

namespace Matrix

def conjTransposeEquiv : Matrix n n R → Matrix n n R → Prop :=
  fun A B ↦ ∃ U : SpecialLinearGroup n R, U • A = B

lemma conjTransposeEquiv.refl (A : Matrix n n R) : conjTransposeEquiv A A :=
  sorry

lemma conjTransposeEquiv.symm {A B : Matrix n n R} (h : conjTransposeEquiv A B) :
    conjTransposeEquiv B A := by
  sorry

lemma conjTransposeEquiv.trans {A B C : Matrix n n R} (hAB : conjTransposeEquiv A B)
    (hBC : conjTransposeEquiv B C) : conjTransposeEquiv A C := by
  sorry

lemma conjTranspose_isEquiv : Equivalence (conjTransposeEquiv (n := n) (R := R)) where
  refl := .refl
  symm := .symm
  trans := .trans

lemma conjTransposeEquiv_iff {A B : Matrix n n R} : conjTransposeEquiv A B ↔
    ∃ U : SpecialLinearGroup n R, U • A = B := Iff.rfl

lemma conjTransposeEquiv_det {A B : Matrix n n R} (h : conjTransposeEquiv A B) :
    A.det = B.det := by
  sorry

lemma conjTransposeEquiv_isSymm {A B : Matrix n n R} (h : conjTransposeEquiv A B) :
    A.IsSymm ↔ B.IsSymm := sorry

end Matrix
