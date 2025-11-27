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

lemma conjTransposeEquiv.refl (A : Matrix n n R) : conjTransposeEquiv A A := by
  use 1
  rw [SpecialLinearGroup.one_smul']

lemma conjTransposeEquiv.symm {A B : Matrix n n R} (h : conjTransposeEquiv A B) :
  conjTransposeEquiv B A := by
  obtain ⟨U, hU⟩ := h
  use U⁻¹
  rw [← hU, ← MulAction.mul_smul, inv_mul_cancel, one_smul]

lemma conjTransposeEquiv.trans {A B C : Matrix n n R} (hAB : conjTransposeEquiv A B)
    (hBC : conjTransposeEquiv B C) : conjTransposeEquiv A C := by
    obtain ⟨U, hU⟩ := hAB
    obtain ⟨V, hV⟩ := hBC
    use V * U
    rw [MulAction.mul_smul, hU, hV]

lemma conjTranspose_isEquiv : Equivalence (conjTransposeEquiv (n := n) (R := R)) where
  refl := .refl
  symm := .symm
  trans := .trans

lemma conjTransposeEquiv_iff {A B : Matrix n n R} : conjTransposeEquiv A B ↔
    ∃ U : SpecialLinearGroup n R, U • A = B := Iff.rfl

lemma conjTransposeEquiv_det {A B : Matrix n n R} (h : conjTransposeEquiv A B) :
    A.det = B.det := by
    obtain ⟨U, hU⟩ := h
    rw [← hU, SpecialLinearGroup.smul_eq, det_mul, det_transpose, U.2]
    simp

lemma conjTransposeEquiv_isSymm_right {A B : Matrix n n R} (h : conjTransposeEquiv A B) :
    A.IsSymm → B.IsSymm := by
    obtain ⟨U, hU⟩ := h
    intro hA
    rw [IsSymm, ← hU,SpecialLinearGroup.smul_eq]
    repeat rw [transpose_mul]
    rw [transpose_transpose, hA, mul_assoc]

lemma conjTransposeEquiv_isSymm {A B : Matrix n n R} (h : conjTransposeEquiv A B) :
    A.IsSymm ↔ B.IsSymm := by
    constructor
    ·exact conjTransposeEquiv_isSymm_right h

    have h' : conjTransposeEquiv B A := by
      exact conjTransposeEquiv.symm h
    exact conjTransposeEquiv_isSymm_right h'

lemma toQuadraticMap'_apply {A : Matrix n n R} (v : n → R) :
    A.toQuadraticMap' v = ∑ i : n, ∑ j : n, A i j * v i * v j := by
  simp [toQuadraticMap', toLinearMap₂'_apply]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  linear_combination


lemma toQuadraticMap'_id (v : n → R) : (1 : Matrix n n R).toQuadraticMap' v = ∑ i, v i ^ 2 := by
  simp [toQuadraticMap'_apply, one_apply, pow_two]

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
    [Module R M2] {Q1 Q2 : QuadraticMap R M1 M2} [PartialOrder M2] (e : Q1.IsometryEquiv Q2)
    (hQ1 : Q1.PosDef) : Q2.PosDef := fun x hx ↦ by
  obtain ⟨e, he⟩ := e
  simp at he
  rw [← e.apply_symm_apply x, he (e.symm x)]
  exact hQ1 (e.symm x) (fun h ↦ hx (e.symm.injective (h.trans (map_zero e.symm).symm)))



lemma Binary.PosDef_iff {A : Matrix (Fin 2) (Fin 2) ℤ} (hA : A.IsSymm) : A.toQuadraticMap'.PosDef ↔
    1 ≤ A 0 0 ∧ 1 ≤ A.det := sorry
end Matrix
