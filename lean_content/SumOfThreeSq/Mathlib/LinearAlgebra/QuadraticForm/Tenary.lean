import SumOfThreeSq.Mathlib.SpecialLinearGroup.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Matrix

namespace QuadraticMap.Tenary

@[simp]
def G (A : Matrix (Fin 3) (Fin 3) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  ![![A 0 0 * A 1 1 - A 0 1 ^ 2, A 0 0 * A 1 2 - A 0 1 * A 0 2],
    ![A 0 0 * A 1 2 - A 0 1 * A 0 2, A 0 0 * A 2 2 - (A 0 2)^2]]

lemma G_def (A : Matrix (Fin 3) (Fin 3) ℤ) (hA : A.IsSymm) :
    (G A).det = A 0 0 * A.det := by
  -- simp [Matrix.det_apply]
  sorry

-- lemma 1.3 (1)
lemma apply (A : Matrix (Fin 3) (Fin 3) ℤ) (v : Fin 3 → ℤ) :
    A.toQuadraticMap' v = (A 0 0 * v 0 + A 0 1 * v 1 + A 0 2 * v 2) ^ 2 +
      (G A).toQuadraticMap' ![v 1, v 2] := by
  sorry

lemma G_posDef {A : M((Fin 3), ℤ)} (hA : A.IsSymm)
    (hApos : A.toQuadraticMap'.PosDef) : (G A).toQuadraticMap'.PosDef := by
  sorry

-- lemma 1.3 (2)
lemma PosDef_iff (A : M((Fin 3), ℤ)) (hA : A.IsSymm) :
    A.toQuadraticMap'.PosDef ↔ 1 ≤ A 0 0 ∧ 1 ≤ A 0 0 * A 1 1 - (A 0 1) ^ 2 ∧ 1 ≤ A.det := by
  sorry

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
