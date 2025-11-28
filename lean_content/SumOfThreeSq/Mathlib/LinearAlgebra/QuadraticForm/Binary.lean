import SumOfThreeSq.Mathlib.SpecialLinearGroup.Basic

open Matrix.SpecialLinearGroup

def Nat.IsRepresentedBy {ι} [Fintype ι] (Q : QuadraticMap ℤ (ι → ℤ) ℤ) (n : ℕ) : Prop :=
  ∃ v : ι → ℤ, Q v = n

lemma exists_representedNat {ι} [Fintype ι] [Nonempty ι] {Q : QuadraticMap ℤ (ι → ℤ) ℤ}
    (hQ : Q.PosDef) : ∃ n : ℕ, n.IsRepresentedBy Q := ⟨(Q 1).natAbs,
  ⟨1, Int.eq_natAbs_of_nonneg (le_of_lt <| hQ 1 (by simp))⟩⟩

lemma binaryQuadMap_bound1 (d : ℤ) (Q' : PosDefQuadMap 2) (hQ' : Q'.matrix.det = d) :
    ∃ Q : PosDefQuadMap 2, EquivalentQuad 2 Q Q' ∧
    2 * |Q.matrix 0 1| ≤ Q.matrix 0 0 ∧ Q.matrix 0 0 ≤ (2 / (Real.sqrt 3)) * Real.sqrt d := by
  classical
  have ha11 := Nat.find_spec <| exists_representedNat Q'.3
  set a11 := Nat.find <| exists_representedNat Q'.3 with a11_eq

  sorry

theorem binaryQuadMap_of_det_eq_one (Q : PosDefQuadMap 2) (hQ : Q.matrix.det = 1) :
    rel Q.matrix 1 := by
  sorry
