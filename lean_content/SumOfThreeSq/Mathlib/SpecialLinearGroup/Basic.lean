import Mathlib

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

lemma toQuadraticMap'_apply {A : Matrix n n R} (v : n → R) :
    A.toQuadraticMap' v = ∑ i : n, ∑ j : n, A i j * v i * v j := by
  sorry

lemma toQuadraticMap'_id (v : n → R) : (1 : Matrix n n R).toQuadraticMap' v = ∑ i, v i ^ 2 := by
  sorry

noncomputable def toQuadraticMap'EquivOfEquiv {A B : Matrix n n R} (hA : A.IsSymm) (hB : B.IsSymm)
    (h : conjTransposeEquiv A B) : A.toQuadraticMap'.IsometryEquiv B.toQuadraticMap' where
  toFun v := h.choose.1ᵀ⁻¹ • v
  map_add' := by simp
  map_smul' := by simp [mulVec_smul]
  invFun v := h.choose.1ᵀ • v
  left_inv v := by
    simp only [← MulAction.mul_smul]
    simp
  right_inv v := by
    simp only [← MulAction.mul_smul]
    simp
  map_app' v := by
    -- have hU := h.choose_spec
    -- set U := h.choose with hU_def
    -- rw [SpecialLinearGroup.smul_eq] at hU
    -- -- rw [toQuadraticMap', LinearMap.BilinMap.toQuadraticMap_apply, toLinearMap₂'_apply']
    -- -- rw [smul_dotProduct U.1ᵀ⁻¹ v, dotProduct_smul]
    -- nth_rw 2 [toQuadraticMap']
    -- rw [LinearMap.BilinMap.toQuadraticMap_apply, toLinearMap₂'_apply']
    -- rw [← hA.eq] at hU
    -- apply_fun (U.1⁻¹ * ·) at hU
    -- rw [← mul_assoc, ← mul_assoc] at hU
    -- simp at hU
    sorry

lemma _root_.QuadraticMap.PosDef_ofEquiv {M1 M2} [AddCommGroup M1] [AddCommGroup M2] [Module R M1]
    [Module R M2] {Q1 Q2 : QuadraticMap R M1 M2} [PartialOrder M2] (h : Q1.IsometryEquiv Q2)
    (hQ1 : Q1.PosDef) : Q2.PosDef := by
  sorry

lemma Binary.PosDef_iff {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.IsSymm) : A.toQuadraticMap'.PosDef ↔
    1 ≤ A 0 0 ∧ 1 ≤ A.det := by
  sorry

end Matrix
