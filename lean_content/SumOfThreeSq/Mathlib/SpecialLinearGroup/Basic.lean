import Mathlib.Data.Matrix.Action
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import SumOfThreeSq.Mathlib.Data.Matrix.Mul
import SumOfThreeSq.Mathlib.LinearAlgebra.QuadraticForm.Basic

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

namespace Matrix

section Meta

scoped notation "SL(" n ", " R ")" => SpecialLinearGroup n R
scoped notation "M(" n ", " R ")" => Matrix n n R

open Lean PrettyPrinter Delaborator SubExpr
@[scoped app_delab Matrix] def delabMatrix : Delab := do
  let n₁ ← withNaryArg 0 getExpr
  let n₂ ← withNaryArg 1 getExpr
  if n₁ != n₂ then failure
  let nD ← withNaryArg 0 delab
  let rD ← withNaryArg 2 delab
  `(M($nD,$rD))

end Meta

namespace SpecialLinearGroup
variable {U U₁ U₂ V : SL(n, R)} {A B : Matrix n n R} {v v₁ v₂ : n → R}

lemma coe_inv' {A : SL(n, R)} : A⁻¹.1 = A.1⁻¹ := by simp [Matrix.inv_def]

attribute [-simp] coe_inv
attribute [simp] coe_inv'

@[simps! (isSimp := false)] instance : SMul SL(n, R) M(n, R) where
  smul U A := U.1 * A * U.1.transpose

instance : MulAction (SpecialLinearGroup n R) (Matrix n n R) where
  one_smul := by simp [smul_def]
  mul_smul := by simp [smul_def, mul_assoc]

@[simp] theorem smul_transpose : (U • A)ᵀ = U • Aᵀ := by simp [smul_def, mul_assoc]

instance : MulAction (SpecialLinearGroup n R) (n → R) := .compHom _ toGL

theorem smul_def' : U • v = U *ᵥ v := rfl

theorem smul_add' : U • (v₁ + v₂) = U • v₁ + U • v₂ := by simp [smul_def', mulVec_add]

instance : SMulCommClass SL(n,R) R (n → R) where
  smul_comm := by simp [smul_def', mulVec_smul]

def rel : Setoid (Matrix n n R) := MulAction.orbitRel (SpecialLinearGroup n R) (Matrix n n R)

theorem rel_def' : rel A B ↔ ∃ U : SpecialLinearGroup n R, U • B = A := Iff.rfl

theorem rel_def : rel A B ↔ ∃ U : SpecialLinearGroup n R, U • A = B := by rw [rel.comm']; rfl
alias ⟨of_rel, _⟩ := rel_def

lemma det_eq_det_of_rel (h : rel A B) : A.det = B.det := by
  obtain ⟨U, hU⟩ := h
  subst hU
  simp [smul_def]

lemma isSymm_of_rel (h : rel A B) (ha : A.IsSymm) : B.IsSymm := by
  obtain ⟨U, hU⟩ := of_rel h
  subst hU
  simpa [IsSymm]

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
