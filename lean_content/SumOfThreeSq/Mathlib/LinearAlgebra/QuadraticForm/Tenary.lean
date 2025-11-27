import SumOfThreeSq.Mathlib.SpecialLinearGroup.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Matrix

namespace QuadraticMap.Tenary

def G (A : Matrix (Fin 3) (Fin 3) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  ![![A 0 0 * A 1 1 - A 0 1 ^ 2, A 0 0 * A 1 2 - A 0 1 * A 0 2],
    ![A 0 0 * A 1 2 - A 0 1 * A 0 2, A 0 0 * A 2 2 - (A 0 2)^2]]

lemma G_det (A : Matrix (Fin 3) (Fin 3) ℤ) (hA : A.IsSymm) :
    (G A).det = A 0 0 * A.det := by
  simp [Matrix.det_fin_three, Matrix.det_fin_two, Matrix.IsSymm.ext_iff.1 hA, G]
  ring

-- lemma 1.3 (1)
lemma apply (A : Matrix (Fin 3) (Fin 3) ℤ) (hA : A.IsSymm) (v : Fin 3 → ℤ) :
    A 0 0 * A.toQuadraticMap' v = (A 0 0 * v 0 + A 0 1 * v 1 + A 0 2 * v 2) ^ 2 +
      (G A).toQuadraticMap' ![v 1, v 2] := by
  simp [Matrix.toQuadraticMap'_apply', pow_two, mul_add, add_mul,
    Fin.sum_univ_three, Matrix.IsSymm.ext_iff.1 hA, G]
  ring

lemma G_posDef {A : M((Fin 3), ℤ)} (hA : A.IsSymm)
    (hApos : A.toQuadraticMap'.PosDef) : (G A).toQuadraticMap'.PosDef := by
  intro v hv
  by_contra! hG
  -- have : (G A).toQuadraticMap' ![A 0 0 * v 0, A 0 0 * v 1] ≤ 0 := by
  --   sorry
  let x1 := -(A 0 1 * v 0 + A 0 2 * v 1)
  have := apply A hA ![-(A 0 1 * v 0 + A 0 2 * v 1), A 0 0 * v 0, A 0 0 * v 1]
  have H : A 0 0 * x1 + A 0 1 * A 0 0 * v 0 + A 0 2 * A 0 0 * v 1 =0 := by ring
  have H' : A 0 0 * A.toQuadraticMap' ![x1, A 0 0 * v 0, A 0 0 * v 1] ≤ 0 :=
  calc
    _ = (A 0 0 * x1 + A 0 1 * A 0 0 * v 0 + A 0 2 * A 0 0 * v 1 )^2
     + (G A).toQuadraticMap' ![A 0 0 * v 0,A 0 0 * v 1]:= by rw [apply A hA]; simp; ring
    _ = (G A).toQuadraticMap' ![A 0 0 * v 0, A 0 0 * v 1] := by
      rw[H]
      simp
    _ = (G A).toQuadraticMap' (A 0 0 • v) := by
        congr
        ext i
        fin_cases i <;> simp
    _ = (A 0 0 * A 0 0) • (G A).toQuadraticMap' v :=
        QuadraticMap.map_smul (G A).toQuadraticMap' (A 0 0) v
    _ ≤ _ := by
      apply mul_nonpos_of_nonneg_of_nonpos
      · exact mul_self_nonneg (A 0 0)
      · assumption
  have hA00 : 0 < A 0 0 :=
    calc A 0 0 = A.toQuadraticMap' ![1,0,0] := by
          simp [Matrix.toQuadraticMap',  Matrix.toLinearMap₂'_apply, Fin.sum_univ_succ]
    _ > 0 := by apply hApos; simp
  have : A.toQuadraticMap' ![x1, A 0 0 * v 0, A 0 0 * v 1] ≤ 0 := by
    exact Int.nonpos_of_mul_nonpos_right H' hA00
  have : A.toQuadraticMap' ![x1, A 0 0 * v 0, A 0 0 * v 1] = 0 := by
    apply le_antisymm
    · exact this
    · exact PosDef.nonneg hApos ![x1, A 0 0 * v 0, A 0 0 * v 1]
  have : ![x1, A 0 0 * v 0, A 0 0 * v 1] = 0 := by
    apply hApos.anisotropic
    exact this
  apply hv
  ext i
  fin_cases i
  · simp_all [hA00.ne']
  · simp_all [hA00.ne']

lemma Int.one_le_iff {n : ℤ} : 1 ≤ n ↔ 0 < n := .rfl

-- lemma 1.3 (2)
lemma PosDef_iff (A : M((Fin 3), ℤ)) (hA : A.IsSymm) :
    A.toQuadraticMap'.PosDef ↔ 1 ≤ A 0 0 ∧ 1 ≤ A 0 0 * A 1 1 - (A 0 1) ^ 2 ∧ 1 ≤ A.det := by
  constructor
  · intro (hApos : A.toQuadraticMap'.PosDef)
    have hA00 : 0 < A 0 0 :=
      calc A 0 0 = A.toQuadraticMap' ![1,0,0] := by
            simp [Matrix.toQuadraticMap',  Matrix.toLinearMap₂'_apply, Fin.sum_univ_succ]
      _ > 0 := by apply hApos; simp
    constructor
    · exact hA00
    constructor
    · have hGA00 : 0 < G A 0 0 :=
        calc G A 0 0 = (G A).toQuadraticMap' ![1,0] := by
              simp [Matrix.toQuadraticMap',  Matrix.toLinearMap₂'_apply, Fin.sum_univ_succ]
        _ > 0 := by
          apply G_posDef
          · assumption
          · assumption
          · simp
      simp only [G, Fin.isValue, cons_val', cons_val_zero, cons_val_fin_one] at hGA00
      exact hGA00
    have := G_posDef hA hApos
    rw [QuadraticMap.Binary.PosDef_iff, G_det] at this
    · have : 0 < A 0 0 * A.det := this.2
      change 0 < A.det
      exact Int.pos_of_mul_pos_right this hA00
    · assumption
    rw [IsSymm.ext_iff]
    intro i j
    fin_cases i
    · fin_cases j
      · rfl
      · rfl
    · fin_cases j
      · rfl
      · rfl
  intro hA1
  have ⟨h₁, h₂, h₃⟩ := hA1
  have: (G A).toQuadraticMap'.PosDef :=  by
    rw [QuadraticMap.Binary.PosDef_iff]
    constructor
    · simp[G]
      exact h₂
    · rw [G_det, Int.one_le_iff]
      · apply mul_pos
        · exact h₁
        · exact h₃
      assumption
    rw [IsSymm.ext_iff]
    intro i j
    fin_cases i
    · fin_cases j
      · rfl
      · rfl
    · fin_cases j
      · rfl
      · rfl


    -- convert this.2 using 1
  intro v hv
  by_contra! hw1
  have h5 := apply A hA v
  have h4 : 0 ≤ (A 0 0 * v 0 + A 0 1 * v 1 + A 0 2 * v 2) ^ 2 +
      (G A).toQuadraticMap' ![v 1, v 2] := by
    have h6 := this.nonneg ![v 1, v 2]
    nlinarith
  rw [← h5] at h4
  have h6 : 0 ≤ A.toQuadraticMap' v := by nlinarith
  have h7 : A.toQuadraticMap' v = 0 := by linarith
  rw [h7, mul_zero, eq_comm,
    add_eq_zero_iff_of_nonneg (by nlinarith) (this.nonneg _), sq_eq_zero_iff] at h5
  have h8 : v 1 = 0 ∧ v 2 = 0 := by
    have := this.anisotropic _ h5.2
    simpa
  have : v 0 = 0 := by
    rw [h8.1, h8.2] at h5
    simp at h5
    obtain ⟨_ | h9, _⟩ := h5
    · linarith
    · exact h9
  simp [funext_iff, Fin.forall_fin_succ, this, h8] at hv

def _root_.Matrix.SpecialLinearGroup.mkFin3OfFin2 (V : SL(Fin 2, ℤ)) (r s : ℤ) : SL(Fin 3, ℤ) where
  val := ![![1, r, s], ![0, V 0 0, V 0 1], ![0, V 1 0, V 1 1]]
  property := by
    simpa [Matrix.det_fin_three] using Matrix.det_fin_two V.1 ▸ V.2

open Matrix.SpecialLinearGroup in
lemma lemma4a (B : PosDefQuadMap 3) (V : SL(Fin 2, ℤ)) (r s : ℤ) :
    B.1 0 0 = ((mkFin3OfFin2 V r s) • B.1) 0 0 := by
  sorry

open Matrix.SpecialLinearGroup in
lemma lemma4b (B : PosDefQuadMap 3) (V : SL(Fin 2, ℤ)) (r s : ℤ) (v : Fin 3 → ℤ) :
    (B.1 0 0) * ((mkFin3OfFin2 V r s) • B.1).toQuadraticMap' v =
    (((mkFin3OfFin2 V r s) • B.1) 0 0 * v 0 + ((mkFin3OfFin2 V r s) • B.1) 0 1 * v 1 +
    ((mkFin3OfFin2 V r s) • B.1) 0 2 * v 2) ^ 2 + (V • (G B.1)).toQuadraticMap' ![v 1, v 2] := by
  sorry

def _root_.Matrix.SpcecialLinearGroup.mkFin3FromInt (u11 u21 u31 : ℤ)
    (hu : Finset.gcd {u11, u21, u31} id = 1) : SpecialLinearGroup (Fin 3) ℤ where
  val := ![![u11, u11.gcdB u21, (u11 / (u11.gcd u21)) * (Int.gcdB (u11.gcd u21) u31)],
      ![u21, u11.gcdA u21, (u21 / (u11.gcd u21)) * (Int.gcdB (u11.gcd u21) u31)],
      ![u31, 0, Int.gcdA (u11.gcd u21) u31]]
  property := by
    have : Int.gcd (u11.gcdB u21) u31 = 1 := by sorry
    sorry

lemma lemma6 (d : ℤ) : ∃ Q : PosDefQuadMap 3,
    Q.matrix.det = d ∧ 2 * max |Q.matrix 0 1| |Q.matrix 0 2| ≤ Q.matrix 0 0 ∧
    Q.matrix 0 0 ≤ (4 / (Real.sqrt 3)) * d ^ (1 / 3 : ℝ) := by
  sorry

open Matrix.SpecialLinearGroup in
lemma det_eq_one (Q : PosDefQuadMap 3) (hQ : Q.matrix.det = 1) :
    rel Q.matrix 1 := by
  sorry

end QuadraticMap.Tenary
