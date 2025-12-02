import SumOfThreeSq.Mathlib.SpecialLinearGroup.Basic

open Matrix.SpecialLinearGroup

def Nat.IsRepresentedBy {ι} [Fintype ι] (Q : QuadraticMap ℤ (ι → ℤ) ℤ) (n : ℕ) : Prop :=
  ∃ v : ι → ℤ, Q v = n

lemma exists_representedPosNat {ι} [Fintype ι] [Nonempty ι] {Q : QuadraticMap ℤ (ι → ℤ) ℤ}
    (hQ : Q.PosDef) : ∃ n : ℕ, n.IsRepresentedBy Q ∧ 0 < n :=
    -- I changed the hypothesis to include 0 < n but don't know how to modify this.
    -- ⟨(Q 1).natAbs, ⟨1, Int.eq_natAbs_of_nonneg (le_of_lt <| hQ 1 (by simp))⟩⟩
  sorry

lemma binaryQuadMap_bound1 (d : ℤ) (Q' : PosDefQuadMap 2) (hQ' : Q'.matrix.det = d) :
    ∃ Q : PosDefQuadMap 2, EquivalentQuad 2 Q Q' ∧
    2 * |Q.matrix 0 1| ≤ Q.matrix 0 0 ∧ Q.matrix 0 0 ≤ (2 / (Real.sqrt 3)) * Real.sqrt d := by
  classical
  have ha11 := Nat.find_spec <| exists_representedPosNat Q'.3
  set a11 := Nat.find <| exists_representedPosNat Q'.3 with a11_eq
  have ha11_neq_zero : a11 ≠ 0 := by linarith
  rw [Nat.IsRepresentedBy] at ha11
  obtain ⟨v, hv⟩ := ha11.1
  have hgcd_eq_one : (v 0).gcd (v 1) = 1 := by
    rw [Int.gcd_eq_one_iff]
    intro c hc_div_v0 hc_div_v1
    have hc_neq_zero : c ≠ 0 := by
      by_contra hc_eq_zero
      rw [hc_eq_zero, Int.zero_dvd] at hc_div_v0 hc_div_v1
      rw [Matrix.toQuadraticMap'_apply] at hv
      simp [dotProduct, Matrix.mulVec, hc_div_v0, hc_div_v1] at hv
      linarith
    have hc_sq_le_one : c^2 ≤ 1:= by
      rw [Int.dvd_def] at hc_div_v0 hc_div_v1
      obtain ⟨c0, hc0⟩ := hc_div_v0
      obtain ⟨c1, hc1⟩ := hc_div_v1
      -- Q(c0, c1) is positive
      have hQc0c1_pos : 0 < Q'.matrix.toQuadraticMap' ![c0, c1] := by
        apply Q'.posDef
        by_contra h
        have : c0 = 0 ∧ c1 = 0 := by
          simp_all
        simp [this.1] at hc0
        simp [this.2] at hc1
        rw [Matrix.toQuadraticMap'_apply] at hv
        simp [dotProduct, Matrix.mulVec, hc0, hc1] at hv
        linarith
      -- a11 ≤ Q(c0, c1)
      have ha11_leq: a11 ≤ (Q'.matrix.toQuadraticMap' ![c0, c1]).natAbs := by
        rw [a11_eq]
        apply Nat.find_min' <| exists_representedPosNat Q'.3
        constructor
        · use ![c0, c1]
          apply Int.eq_natAbs_of_nonneg
          exact le_of_lt <| hQc0c1_pos
        · simp
          linarith
      -- c^2 * Q(c0, c1) = a11
      have heq : c^2 * Q'.matrix.toQuadraticMap' ![c0, c1] = a11 := by
        rw [← hv]
        repeat rw [Matrix.toQuadraticMap'_apply]
        simp [Matrix.vecHead, Matrix.vecTail, Matrix.mulVec, hc0, hc1]
        linarith
      rw [←Int.ofNat_le, ←Int.eq_natAbs_of_nonneg <| le_of_lt <| hQc0c1_pos] at ha11_leq
      nlinarith
    use c
    have : 0 < c^2 := by exact pow_two_pos_of_ne_zero <| hc_neq_zero
    nlinarith
  rw [← Int.isCoprime_iff_gcd_eq_one, IsCoprime] at hgcd_eq_one
  obtain ⟨a, b, hab⟩ := hgcd_eq_one
  set a12' := Q'.matrix 0 0 * v 0 * (-b) +
    Q'.matrix 0 1 * (v 0 * a) + Q'.matrix 1 0 * (v 1 * (-b)) + Q'.matrix 1 1 * v 1 * a with a12'_eq
  -- Exists t
  have ht : ∃ t, 2 * |a12' + a11 * t| ≤ a11 := by
    by_cases h : 2 * (a12' % a11) ≤ a11
    · use - (a12'/a11)
      nth_rewrite 1 [← Int.ediv_mul_add_emod a12' a11]
      have : |(a12' % ↑a11)| = a12' % ↑a11 := by
        apply abs_of_nonneg
        apply Int.emod_nonneg
        nlinarith
      simp
      nth_rewrite 2 [mul_comm]
      simp
      nlinarith
    · use -(a12'/a11) - 1
      nth_rewrite 1 [← Int.ediv_mul_add_emod a12' a11]
      apply le_of_not_ge at h
      have h : |(a12' % ↑a11 - ↑a11)| = -(a12' % ↑a11 - ↑a11) := by
        apply abs_of_nonpos
        have : a12' % ↑a11 < ↑a11 := by
          apply Int.emod_lt_of_pos
          nlinarith
        nlinarith
      rw [Int.sub_eq_add_neg, mul_add]
      have : a12' / ↑a11 * ↑a11 + a12' % ↑a11 + (↑a11 * -(a12' / ↑a11) + ↑a11 * -1) =
          a12' % ↑a11 - ↑a11 := by
        linarith
      rw [this, h]
      nlinarith
  obtain ⟨t, ht⟩ := ht
  set a12 := a12' + a11 * t with a12_eq
  set a21 := a12' + a11 * t with a21_eq
  set a22 := Q'.matrix.toQuadraticMap' ![-b + v 0 * t, a + v 1 * t] with a22_eq
  set A := !![(a11 : ℤ), a12; a21, a22] with A_eq
  have hrel : rel A Q'.matrix := by
    rw [rel_def']
    set U := !![v 0, v 1; -b + v 0 * t, a + v 1 * t] with U_eq
    use ⟨U, by
      rw [U_eq, Matrix.det_fin_two]
      simp
      linarith
    ⟩
    rw [smul_def, coe_mk]
    ext i j
    fin_cases i
    · fin_cases j
      · simp [Matrix.two_mul_expl]
        simp [U_eq, A_eq]
        rw [←hv, Matrix.toQuadraticMap'_apply]
        simp [Matrix.mulVec]
        linarith
      · simp [Matrix.two_mul_expl]
        simp [U_eq, A_eq]
        rw [a12_eq, a21_eq, a12'_eq, ←hv, Matrix.toQuadraticMap'_apply]
        simp [Matrix.mulVec]
        linarith
    · fin_cases j
      · simp [Matrix.two_mul_expl]
        simp [U_eq, A_eq]
        rw [a21_eq, a12'_eq, ←hv, Matrix.toQuadraticMap'_apply]
        simp [Matrix.mulVec]
        rw [Matrix.IsSymm.apply (Q'.isSymm) 0 1]
        linarith
      · simp [Matrix.two_mul_expl]
        simp [U_eq, A_eq]
        rw [a22_eq, Matrix.toQuadraticMap'_apply]
        simp [Matrix.vecHead, Matrix.vecTail, Matrix.mulVec]
        linarith
  set Q := PosDefQuadMap.mk A ((isSymm_iff_isSymm_of_rel hrel).2 Q'.isSymm) (PosDef_if_PosDef_of_rel
      (rel.symm hrel) Q'.posDef) with Q_eq
  use Q
  constructor
  · exact hrel
  · constructor
    · simp [Q_eq, A_eq]
      exact ht
    · simp [Q_eq, A_eq]
      have hd : d = a11 * a22 - a12^2 := by
        rw [←hQ', ←det_eq_det_of_rel hrel, A_eq, Matrix.det_fin_two, a12_eq]
        simp
        linarith
      have ineq0 : a11 ≤ a22 := by
        have hpos : 0 < a22 := by
          rw [a22_eq]
          apply Q'.posDef
          by_contra h
          have h: -b + v 0 * t = 0 ∧ a + v 1 * t = 0 := by
            simp_all
          have : v 0 * (a + v 1 * t) - v 1 * (-b + v 0 * t) = 1 := by
            linarith
          simp [h.1, h.2] at this
        have : a11 ≤ a22.natAbs := by
          rw [a11_eq]
          apply Nat.find_min' <| exists_representedPosNat Q'.3
          constructor
          · use ![-b + v 0 * t, a + v 1 * t]
            apply Int.eq_natAbs_of_nonneg
            exact le_of_lt <| hpos
          · simp
            linarith
        rw [←Int.ofNat_le, Int.ofNat_natAbs_of_nonneg <| le_of_lt hpos] at this
        exact this
      have ineq1 : 4 * a11^2 ≤ 4 * d + 4 * a12^2 := by
        rw [hd]
        nlinarith
      have ineq2 : (2 * a12)^2 ≤ a11^2 := by
        rw [sq_le_sq]
        nth_rewrite 2 [abs_of_nonneg (by exact Int.natCast_nonneg a11)]
        rw [abs_mul]
        simp
        exact ht
      have ineq3 : 4 * d + 4 * a12^2 ≤ 4 * d + a11^2 := by
        linarith
      have ineq4 : 3 * a11^2 ≤ 4 * d := by
        linarith
      apply le_of_sq_le_sq
      · have : 1 ≤ d := by
          rw [← hQ']
          exact ((QuadraticMap.Binary.PosDef_iff Q'.isSymm).1 Q'.posDef).2
        rw [mul_pow, div_pow, Real.sq_sqrt (by linarith),
        Real.sq_sqrt (by norm_cast; linarith), div_mul_eq_mul_div]
        have : 3 * (a11 : ℝ) ^ 2 ≤ 2 ^ 2 * d := by
          simp [pow_two]
          norm_cast
          simp
          rw [←pow_two]
          exact ineq4
        nlinarith
      · apply mul_nonneg
        · apply div_nonneg
          · linarith
          · exact Real.sqrt_nonneg 3
        · exact Real.sqrt_nonneg d


theorem binaryQuadMap_of_det_eq_one (Q : PosDefQuadMap 2) (hQ : Q.matrix.det = 1) :
    rel Q.matrix 1 := by
  obtain ⟨Q', hQ'1, hQ'2, hQ'3⟩ := binaryQuadMap_bound1 1 Q hQ
  have ineq1 : 2/√3 * √1 < 2 := by
    have ineq10 : |2/√3 * √1| < 2 := by
      apply abs_lt_of_sq_lt_sq
      · rw [mul_pow, div_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
        linarith
      · linarith
    have ineq11 : 2/√3 * √1 ≤ |2/√3 * √1| := by
      apply le_abs_self
    linarith
  have ineq2 : Q'.matrix 0 0 < 2 := by
    norm_cast at hQ'3
    have ineq : Q'.matrix 0 0 < (2 : ℝ) := by
      exact (lt_of_le_of_lt hQ'3 ineq1)
    norm_cast at ineq
  have ha11 : Q'.matrix 0 0 = 1 := by
    apply le_antisymm
    · linarith
    · exact ((QuadraticMap.Binary.PosDef_iff Q'.isSymm).1 Q'.posDef).1
  have ha12: Q'.matrix 0 1 = 0 := by
    simp [ha11] at hQ'2
    have nonneg : 0 ≤ |Q'.matrix 0 1| := by
      exact abs_nonneg (Q'.matrix 0 1)
    have nonpos : |Q'.matrix 0 1| ≤ 0 := by
      linarith
    have eqzero : |Q'.matrix 0 1| = 0 := by
      linarith
    rw [abs_eq_zero] at eqzero
    exact eqzero
  have ha21: Q'.matrix 1 0 = 0 := by
    rw [Matrix.IsSymm.apply (Q'.isSymm) 0 1]
    exact ha12
  have ha22: Q'.matrix 1 1 = 1 := by
    rw [←det_eq_det_of_rel hQ'1, Matrix.det_fin_two, ha11, ha12, ha21] at hQ
    simp at hQ
    exact hQ
  have hQ': Q'.matrix = 1 := by
    ext i j
    fin_cases i
    · fin_cases j
      · simp
        exact ha11
      · simp
        exact ha12
    · fin_cases j
      · simp
        exact ha21
      · simp
        exact ha22
  have : rel Q.matrix Q'.matrix := by
    simp [EquivalentQuad] at hQ'1
    exact rel.symm hQ'1
  rw [hQ'] at this
  exact this
