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
  sorry

lemma _root_.QuadraticMap.Binary.PosDef_iff {A : M(Fin 2, ℤ)} (hA : A.IsSymm) :
    A.toQuadraticMap'.PosDef ↔ 1 ≤ A 0 0 ∧ 1 ≤ A.det := by
  sorry

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

lemma binaryQuadMap_bound1 (d : ℕ) (x : Quotient (EquivalentQuad 2)) :
    ∃ Q : PosDefQuadMap 2, Quotient.mk'' Q = x ∧ Q.matrix.det ≤ d ∧
    2 * |Q.matrix 0 1| ≤ Q.matrix 0 0 ∧ Q.matrix 0 0 ≤ (2 / (Real.sqrt 3)) * Real.sqrt d := by
  sorry

theorem binaryQuadMap_of_det_eq_one (Q : PosDefQuadMap 2) :
    rel Q.matrix 1 := by
  sorry

end Matrix.SpecialLinearGroup

section tenaryQuad

open Matrix

@[simp]
def G (A : Matrix (Fin 3) (Fin 3) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  ![![A 0 0 * A 1 1 - A 0 1 ^ 2, A 0 0 * A 1 2 - A 0 1 * A 0 2],
    ![A 0 0 * A 1 2 - A 0 1 * A 0 2, A 0 0 * A 2 2 - (A 0 2)^2]]

lemma G_def (A : Matrix (Fin 3) (Fin 3) ℤ) (hA : A.IsSymm) :
    (G A).det = A 0 0 * A.det := by
  -- simp [Matrix.det_apply]
  sorry

-- lemma 1.3 (1)
lemma QuadraticMap.Tenary.apply (A : Matrix (Fin 3) (Fin 3) ℤ) (v : Fin 3 → ℤ) :
    A.toQuadraticMap' v = (A 0 0 * v 0 + A 0 1 * v 1 + A 0 2 * v 2) ^ 2 +
      (G A).toQuadraticMap' ![v 1, v 2] := by
  sorry

lemma G_posDef {A : M((Fin 3), ℤ)} (hA : A.IsSymm)
    (hApos : A.toQuadraticMap'.PosDef) : (G A).toQuadraticMap'.PosDef := by
  sorry

-- lemma 1.3 (2)
lemma QuadraticMap.Tenary.PosDef_iff (A : M((Fin 3), ℤ)) (hA : A.IsSymm) :
    A.toQuadraticMap'.PosDef ↔ 1 ≤ A 0 0 ∧ 1 ≤ A 0 0 * A 1 1 - (A 0 1) ^ 2 ∧ 1 ≤ A.det := by
  sorry

def Matrix.mkFin3OfFin2 (V : SL(Fin 2, ℤ)) (r s : ℤ) : SL(Fin 3, ℤ) where
  val := ![![1, r, s], ![0, V 0 0, V 0 1], ![0, V 1 0, V 1 1]]
  property := by
    simpa [Matrix.det_fin_three] using Matrix.det_fin_two V.1 ▸ V.2

lemma Quadratic.Tenary.lemma4a (B : PosDefQuadMap 3) (V : SL(Fin 2, ℤ)) (r s : ℤ) :
    B.1 0 0 = ((mkFin3OfFin2 V r s) • B.1) 0 0 := by
  sorry

lemma Quadratic.Tenary.lemma4b (B : PosDefQuadMap 3) (V : SL(Fin 2, ℤ)) (r s : ℤ) (v : Fin 3 → ℤ) :
    (B.1 0 0) * ((mkFin3OfFin2 V r s) • B.1).toQuadraticMap' v =
    (((mkFin3OfFin2 V r s) • B.1) 0 0 * v 0 + ((mkFin3OfFin2 V r s) • B.1) 0 1 * v 1 +
    ((mkFin3OfFin2 V r s) • B.1) 0 2 * v 2) ^ 2 + (V • (G B.1)).toQuadraticMap' ![v 1, v 2] := by
  sorry

end tenaryQuad
