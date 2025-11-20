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
