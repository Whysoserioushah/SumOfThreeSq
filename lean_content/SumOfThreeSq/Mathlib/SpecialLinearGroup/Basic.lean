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

lemma isSymm_iff_isSymm_of_rel (h : rel A B) : A.IsSymm ↔ B.IsSymm :=
  ⟨isSymm_of_rel h, isSymm_of_rel <| Setoid.symm' _ h⟩

def toQuadraticMap'EquivSMul (A : M(n, R)) (U : SL(n, R)) :
    A.toQuadraticMap'.IsometryEquiv (U • A).toQuadraticMap' where
  __ := MulAction.toPerm (Uᵀ⁻¹)
  map_add' := by simp [smul_add']
  map_smul' := by simp [smul_comm]
  map_app' v := by simp [toQuadraticMap'_apply, smul_def', smul_def, dotProduct_mulVec_eq]

theorem nonempty_isometryEquiv_of_rel {A B : M(n, R)} (h : rel A B) :
    Nonempty (A.toQuadraticMap'.IsometryEquiv B.toQuadraticMap') :=
  let ⟨U, hU⟩ := of_rel h
  hU ▸ ⟨toQuadraticMap'EquivSMul A U⟩

lemma _root_.QuadraticMap.PosDef_ofEquiv {M1 M2} [AddCommGroup M1] [AddCommGroup M2] [Module R M1]
    [Module R M2] {Q1 Q2 : QuadraticMap R M1 M2} [PartialOrder M2] (h : Q1.IsometryEquiv Q2)
    (hQ1 : Q1.PosDef) : Q2.PosDef := by
  intro x hx
  rw [←QuadraticMap.IsometryEquiv.map_app h.symm]
  apply hQ1
  simpa

lemma PosDef_if_PosDef_of_rel {A B : M(n, ℤ)} (h : rel A B) (hA : A.toQuadraticMap'.PosDef)
    : B.toQuadraticMap'.PosDef := by
  obtain ⟨U⟩ := nonempty_isometryEquiv_of_rel h
  exact QuadraticMap.PosDef_ofEquiv U hA

lemma _root_.QuadraticMap.Binary.PosDef_iff {A : M(Fin 2, ℤ)} (hA : A.IsSymm) :
    A.toQuadraticMap'.PosDef ↔ 1 ≤ A 0 0 ∧ 1 ≤ A.det := by
  have h1 : A.toQuadraticMap' ![1, 0] = A 0 0 := by
    simp [Matrix.toQuadraticMap'_apply, vecHead, mulVec]
  constructor
  · intro h
    have h4: 1 ≤ A 0 0 := by
      rw [←h1]
      apply h
      simp
    constructor
    · exact h4
    · have h3: A.toQuadraticMap' ![-A 0 1, A 0 0] = (A 0 0) * A.det := by
        rw [Matrix.toQuadraticMap'_apply]
        simp [vecHead, vecTail, mulVec, det_fin_two]
        ring
      have h2: (A 0 0) * A.det ≥ 1 := by
        rw [←h3]
        apply h
        simp [← h1]
        have : 0 < A.toQuadraticMap' ![1, 0] := by
          apply h
          simp
        intro
        apply ne_of_gt
        exact this
      nlinarith
  · intro h
    have h2: ∀ v, (A 0 0) * (A.toQuadraticMap' v) = (A 0 0 * v 0
        + A 0 1 * v 1)^2 + A.det * (v 1)^2 := by
      intro v
      rw [Matrix.toQuadraticMap'_apply]
      simp [mulVec, det_fin_two]
      have : A 1 0 = A 0 1 := by
        apply Matrix.IsSymm.apply
        exact hA
      rw [this]
      ring
    have h3: ∀ v, 0 ≤ (A 0 0) * (A.toQuadraticMap' v) := by
      intro v
      rw [h2]
      nlinarith
    have h4: ∀ v, 0 ≤ A.toQuadraticMap' v := by
      intro v
      specialize h3 v
      nlinarith
    rw [QuadraticMap.PosDef]
    intro x hx
    by_contra h5
    have : A.toQuadraticMap' x = 0 := by
      apply eq_of_le_of_not_lt'
      · specialize h4 x
        exact h4
      · exact h5
    specialize h2 x
    rw [this] at h2
    simp at h2
    have h6: A 0 0 * x 0 + A 0 1 * x 1 = 0 := by
      rw [eq_comm, add_eq_zero_iff_of_nonneg] at h2
      · simp at h2
        exact h2.1
      · nlinarith
      · nlinarith
    have h7: A.det * x 1^2 = 0 := by
      rw [eq_comm, add_eq_zero_iff_of_nonneg] at h2
      · exact h2.2
      · nlinarith
      · nlinarith
    simp at h7
    obtain _ | h7 := h7
    · linarith
    · simp[h7] at h6
      obtain _ | h6 := h6
      · linarith
      · apply hx
        ext i
        fin_cases i
        · exact h6
        · exact h7

structure _root_.PosDefQuadMap (n : ℕ) where
  matrix : Matrix (Fin n) (Fin n) ℤ
  isSymm : matrix.IsSymm
  posDef : matrix.toQuadraticMap'.PosDef

@[simp]
lemma _root_.Matrix.add_toQuadraticMap' {R n : Type*} [Fintype n] [DecidableEq n] [CommRing R]
    (M N : Matrix n n R) : (M + N).toQuadraticMap' = M.toQuadraticMap' + N.toQuadraticMap' := by
  simp [toQuadraticMap']

@[simp]
lemma _root_.Matrix.zero_toQuadraticMap' {R n : Type*} [Fintype n] [DecidableEq n]
    [CommRing R] : (0 : Matrix n n R).toQuadraticMap' = 0 := by
  simp [toQuadraticMap']

instance (n : ℕ) : Add (PosDefQuadMap n) where
  add Q1 Q2 := .mk (Q1.1 + Q2.1) (by simp [Q1.2, Q2.2])
    (Matrix.add_toQuadraticMap' Q1.1 Q2.1 ▸ .add _ _ Q1.3 Q2.3)

@[reducible, inline]
def EquivalentQuad (n : ℕ) : Setoid (PosDefQuadMap n) where
  r Q1 Q2 := rel Q1.matrix Q2.matrix
  iseqv.refl _ := rel.refl _
  iseqv.symm := rel.symm
  iseqv.trans := rel.trans

lemma det_eq_of_equiv_quadMap {n : ℕ} {Q1 Q2 : PosDefQuadMap n}
    (h : EquivalentQuad n Q1 Q2) : Q1.matrix.det = Q2.matrix.det :=
  det_eq_det_of_rel h

end Matrix.SpecialLinearGroup
