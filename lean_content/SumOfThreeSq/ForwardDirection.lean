import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import SumOfThreeSq.Mathlib.LinearAlgebra.QuadraticForm.Binary
import SumOfThreeSq.Mathlib.LinearAlgebra.QuadraticForm.Tenary
import Mathlib

private def A (n : ℕ) (d' : ℕ) (a12' : ℤ) (a11' : ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  ![![(-a11' + (a12' : ZMod (d' * n - 1)).cast * (a12' : ZMod (d' * n - 1)).cast / ↑(d' * n - 1)),
    (a12' : ZMod (d' * n - 1)).cast, 1], ![(a12' : ZMod (d' * n - 1)).cast,
    ((d' * n - 1 : ℕ) : ℤ), 0], ![1, 0, n]]

lemma A_isSymm (n d' : ℕ) (a12' a11' : ℤ) : Matrix.IsSymm (A n d' a12' a11') := by
  simp [Matrix.IsSymm.ext_iff, Fin.forall_fin_succ, A]

lemma A_det_eq_one (n d' : ℕ) (a12' a11' : ℤ) (ha11 : (a12' : ZMod (d' * n - 1)).cast *
    (a12' : ZMod (d' * n - 1)).cast + ↑d' = (-a11' + (a12' : ZMod (d' * n - 1)).cast *
    (a12' : ZMod (d' * n - 1)).cast / ↑(d' * n - 1)) * ↑(d' * n - 1)) (hdn : 2 ≤ d' * n) :
    Matrix.det (A n d' a12' a11') = 1 := by
  simp [A, Matrix.det_fin_three, ← ha11]
  ring_nf; omega

lemma A_PosDef (n d' : ℕ) (a12' a11' : ℤ) (hdpos : 0 < d')
    (ha11 : (a12' : ZMod (d' * n - 1)).cast * (a12' : ZMod (d' * n - 1)).cast + ↑d' =
    (-a11' + (a12' : ZMod (d' * n - 1)).cast * (a12' : ZMod (d' * n - 1)).cast /
    ↑(d' * n - 1)) * ↑(d' * n - 1)) (hdn : 2 ≤ d' * n) :
    (A n d' a12' a11').toQuadraticMap'.PosDef :=
  QuadraticMap.Tenary.PosDef_iff (A n d' a12' a11') (A_isSymm n d' a12' a11')|>.2
  ⟨by
    simp only [A, Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one];
    have : 0 < (-a11' + (↑a12' : ZMod (d' * n - 1)).cast * (↑a12' : ZMod (d' * n - 1)).cast /
      ↑(d' * n - 1)) * ((d' * n - 1 : ℕ) : ℤ) := ha11 ▸ Int.add_lt_add_of_le_of_lt
      (c := 0) (d := d') (mul_self_nonneg (a12' : ZMod (d' * n - 1)).cast) (by exact_mod_cast hdpos)
    exact Int.pos_of_mul_pos_left this (by omega), by simpa [A, ← ha11, pow_two],
  by simp [A_det_eq_one n d' a12' a11' ha11 hdn]⟩

def A_toPosDefQuad (n d' : ℕ) (a12' a11' : ℤ)
    (ha11 : (a12' : ZMod (d' * n - 1)).cast * (a12' : ZMod (d' * n - 1)).cast + ↑d' =
    (-a11' + (a12' : ZMod (d' * n - 1)).cast * (a12' : ZMod (d' * n - 1)).cast /
    ↑(d' * n - 1)) * ↑(d' * n - 1)) (hdn : 2 ≤ d' * n) :
    PosDefQuadMap 3 :=
  ⟨A n d' a12' a11', A_isSymm n d' a12' a11', A_PosDef n d' a12' a11' (lt_of_le_of_ne (zero_le _)
    (fun hd' ↦ by simp [← hd'] at hdn)) ha11 hdn⟩

def PosDefQuad.one (n : ℕ) : PosDefQuadMap n where
  matrix := 1
  isSymm := by simp
  posDef v hv := by
    simp [Matrix.toQuadraticMap'_apply', Matrix.one_apply]
    apply lt_of_le_of_ne
    · apply Finset.sum_nonneg
      intros i hi
      simp only [mul_self_nonneg]
    · intro h2
      rw [eq_comm, Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ by simp [mul_self_nonneg])] at h2
      apply hv
      ext i
      specialize h2 i (Finset.mem_univ i)
      simp_all

lemma Finset.prod_legendreSym {ι} [DecidableEq ι] {s : Finset ι} (f : ι → ℤ)
    {p : ℕ} [Fact p.Prime] : ∏ i ∈ s, legendreSym p (f i) = legendreSym p (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with simp [legendreSym.mul, *]

lemma Finsupp.prod_legendreSym {ι M} [DecidableEq ι] [Zero M] (f : ι →₀ M) (g : ι → M → ℤ)
    (p : ℕ) [Fact p.Prime] : legendreSym p (Finsupp.prod f g) =
    Finsupp.prod f (fun i _ ↦ legendreSym p (g i (f i))) := by
  rw [Finsupp.prod, ← Finset.prod_legendreSym, Finsupp.prod]

lemma legendreSym.pow {a : ℤ} {n : ℕ} (p : ℕ) [Fact p.Prime] :
    legendreSym p (a ^ n) = legendreSym p a ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, legendreSym.mul, ih, pow_succ]

lemma legendreSym.add_left_dvd_self (p : ℕ) [Fact p.Prime] {a b : ℤ} (h : (p : ℤ) ∣ a) :
    legendreSym p (a + b) = legendreSym p b := by
  obtain ⟨k, rfl⟩ := h
  rw [legendreSym.mod, add_comm, Int.add_mul_emod_self_left, ← legendreSym.mod]

lemma legendreSym.sub_left_dvd_self (p : ℕ) [Fact p.Prime] {a b : ℤ} (h : (p : ℤ) ∣ a) :
    legendreSym p (a - b) = legendreSym p (-b) := by
  rw [← Int.add_neg_eq_sub, legendreSym.add_left_dvd_self _ h]

open Matrix.SpecialLinearGroup in
lemma Nat.quadResidue_to_sum_threeSq (n : ℕ) (hn1 : 2 ≤ n) (hn2 : ∃ d' : ℕ,
    0 < d' ∧ IsSquare (-d' : ZMod (d' * n - 1))) :
    ∃ a b c : ℤ, n = a ^ 2 + b ^ 2 + c ^ 2 := by
  obtain ⟨d', hdpos, ha⟩ := hn2
  obtain ⟨a12', ha⟩ := ZMod.exists.1 ha
  have := mul_comm n _ ▸ mul_one 2 ▸ mul_le_mul hn1 hdpos (by grind) (by grind)
  have : NeZero (d' * n - 1) := ⟨ne_of_gt <| lt_of_lt_of_le (by decide : 0 < 1) (by omega)⟩
  rw [← Int.cast_natCast, ← Int.cast_neg, ZMod.intCast_eq_iff] at ha
  obtain ⟨a11', ha11⟩ := ha
  rw [neg_eq_iff_add_eq_zero, ← add_assoc, add_comm (d' : ℤ), ← eq_neg_iff_add_eq_zero,
    ← mul_neg, ZMod.val_mul, Nat.mod_eq_sub_div_mul] at ha11
  rw [Nat.cast_sub (div_mul_le_self ..)] at ha11
  simp only [cast_mul, ZMod.natCast_val, Int.natCast_ediv] at ha11
  rw [add_comm, add_sub, sub_eq_iff_eq_add, mul_comm _ ((d' * n - 1 : ℕ) : ℤ), ← mul_add,
    mul_comm ((d' * n - 1 : ℕ) : ℤ), add_comm] at ha11
  have : n.IsRepresentedBy (A_toPosDefQuad n d' a12' a11' ha11 (by omega)).1.toQuadraticMap' :=
    ⟨![0, 0, 1], by simp [A_toPosDefQuad, A, Matrix.toQuadraticMap'_apply', Fin.sum_univ_three]⟩
  obtain ⟨v, hv⟩ : n.IsRepresentedBy (PosDefQuad.one 3).1.toQuadraticMap' :=
    Nat.IsRepresentedBy.of_equiv _ _ (EquivalentQuad_iff.2 <| QuadraticMap.Tenary.det_eq_one
      (A_toPosDefQuad n d' a12' a11' ha11 (by omega))
      (A_det_eq_one n d' a12' a11' ha11 (by omega))) this
  use v 0, v 1, v 2
  simp [PosDefQuad.one, Matrix.toQuadraticMap'_apply', Matrix.one_apply,
    eq_comm, Fin.sum_univ_three, ← pow_two] at hv
  exact hv

lemma Nat.dvd_odd_mod_four (n d : ℕ) (hd : Odd d) (hn : n ∣ d) : n % 4 = 1 ∨ n % 4 = 3 := by
  haveI : Odd n := Odd.of_dvd_nat hd hn
  haveI : n % 4 < 4 := Nat.mod_lt n (by omega)
  by_contra! hnn
  exact (by interval_cases (n % 4) <;> simp_all : n % 4 = 0 ∨ n % 4 = 2).casesOn
    (fun h2 ↦ by grind) (fun h2 ↦ by grind)

-- open scoped Classical in
-- @[to_additive]
-- lemma Finset.prod_filter_eq_of_iff {ι M : Type*} [CommMonoid M] {s : Finset ι}
--     {p q : ι → Prop} (h : ∀ x ∈ s, p x ↔ q x) (f : ι → M) :
--     ∏ i ∈ s with p i, f i = ∏ i ∈ s with q i, f i := by
--   rw [Finset.filter_congr h]

lemma Nat.sub_one_coprime_self {n : ℕ} (hn : 0 < n) : (n - 1).Coprime n := by
  cases n with simp_all

lemma Nat.mod_four_eq_two_to_sum_threeSq (n : ℕ) (hn : n % 4 = 2) :
    ∃ a b c : ℤ, n = a ^ 2 + b ^ 2 + c ^ 2 := by
  haveI : 0 < n := by omega
  have hn1 : (n - 1).Coprime (4 * n) := by
    rw [mul_comm]
    refine Nat.Coprime.mul_right (Nat.sub_one_coprime_self this) ?_
    rw [Nat.Coprime, gcd_comm, gcd_rec]
    convert Nat.gcd_one_left _ ; omega
  obtain ⟨p, hp1, hp2, hp3⟩ := Nat.forall_exists_prime_gt_and_modEq (5 * n) (by omega) hn1
  have hj' := Nat.cast_sub (R := ℤ) (by grind : n - 1 ≤ p) ▸
    (dvd_sub_comm.1 <| Nat.modEq_iff_dvd.1 hp3)
  norm_cast at hj'
  obtain ⟨j, hj1⟩ := hj'
  rw [Nat.sub_eq_iff_eq_add (by grind), mul_assoc, mul_comm n, ← mul_assoc,
    ← Nat.add_sub_assoc (by omega), ← add_one_mul] at hj1
  have hj2 : 1 < j := by
    rw [hj1] at hp1
    have := Nat.mul_lt_mul_right (by omega)|>.1 <| hp1.trans
      (sub_one_lt (n := (4 * j + 1) * n) (by omega))
    grind
  set d' := 4 * j + 1 with d'_eq
  have hp4 : p % 4 = 1 := by
    simpa [hj1, d'_eq, add_mul, mul_assoc, @Nat.add_sub_assoc n 1 (by omega),
      ← Nat.mod_sub_of_le (by rw [hn]; omega : 1 ≤ n % 4)]
  refine Nat.quadResidue_to_sum_threeSq n (by omega) ⟨d', by omega, ?_⟩
  haveI : Fact ((d' * n - 1).Prime) := ⟨hj1 ▸ hp2⟩
  rw [← Int.cast_natCast, ← Int.cast_neg, ← legendreSym.eq_one_iff (d' * n - 1) (by
    simp only [Int.cast_neg, Int.cast_natCast, ne_eq, neg_eq_zero]
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    have : d' = 0 := Nat.eq_zero_of_dvd_of_lt h <| lt_of_lt_of_le (by grind)
      (by gcongr; omega : d' * 2 - 1 ≤ d' * n - 1)
    omega)]
  rw [← neg_one_mul, legendreSym.mul, legendreSym.at_neg_one (ne_of_gt (by omega)),
    ZMod.χ₄_nat_one_mod_four (by rw [← hj1, hp4]), one_mul]
  nth_rw 2 [← d'.factorization_prod_pow_eq_self (by omega)]
  rw [Nat.cast_finsuppProd, Finsupp.prod_legendreSym, Finsupp.prod]
  simp [legendreSym.pow]
  have hq1 (q) (hq : q ∈ d'.primeFactors) : q ≠ 2 := by
    rintro rfl
    have := mem_primeFactors_of_ne_zero (by omega) |>.1 hq
    omega
  have h (x) (hx : x ∈ d'.primeFactors) : legendreSym (d' * n - 1) x = ZMod.χ₄ x := by
    have : Fact (Prime x) := by simp_all
    rw [legendreSym.quadratic_reciprocity' (hq1 _ hx) (by omega),
      neg_one_pow_eq_one_iff_even (by omega)|>.2 (Even.mul_left (hj1 ▸ ⟨p / 4, by omega⟩) _),
      Nat.cast_sub (by omega), legendreSym.sub_left_dvd_self x
      (Nat.cast_mul (α := ℤ) .. ▸ Int.dvd_mul_of_dvd_left (by
      exact_mod_cast (mem_primeFactors_of_ne_zero (by omega)|>.1 hx).2)),
      cast_one, one_mul, legendreSym.at_neg_one (p := x) (hq1 x hx)]
  simp +contextual only [h]
  simp_rw [← map_pow, ← Nat.cast_pow, ← map_prod, ← Nat.cast_prod,
    d'.prod_primeFactors_prod_factorization]
  have : d' = (d'.factorization.prod fun p x ↦ p ^ d'.factorization p) := by
    nth_rw 1 [← d'.factorization_prod_pow_eq_self (by omega)]
    rfl
  rw [← this, ZMod.χ₄_nat_one_mod_four (by omega)]

lemma Int.coprime_mul_dvd_of_dvd_of_dvd {a b c : ℤ} (h1 : a.gcd b = 1) (h2 : a ∣ c) (h3 : b ∣ c) :
    (a * b) ∣ c := Int.natAbs_dvd_natAbs.1 <| Int.natAbs_mul _ _ ▸
  Nat.Coprime.mul_dvd_of_dvd_of_dvd h1 (Int.natAbs_dvd_natAbs.2 h2) (Int.natAbs_dvd_natAbs.2 h3)

lemma ZMod.isSquare_coprime_split {p : ℕ} (hp : Odd p) (n : ℤ) (hn : Odd n)
    (ha1 : IsSquare (n : ZMod p)) : IsSquare (n : ZMod (2 * p)) := by
  obtain ⟨a, ha⟩ := ZMod.exists.1 ha1
  if ha' : Odd a then
  use a
  rw [← sub_eq_zero, ← Int.cast_mul, ← Int.cast_sub,
    ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_mul]
  refine Int.coprime_mul_dvd_of_dvd_of_dvd ?_ ?_ ?_
  · exact_mod_cast Nat.coprime_two_left.mpr hp
  · simpa using even_iff_two_dvd.1 <| Odd.add_odd hn (by grind)
  · simpa [← ZMod.intCast_zmod_eq_zero_iff_dvd, sub_eq_zero] using ha
  else
  use a + p
  have ha' : Odd (a + p) := by grind
  rw [← sub_eq_zero, ← Int.cast_natCast, ← Int.cast_add, ← Int.cast_mul, ← Int.cast_sub,
    ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_mul]
  refine Int.coprime_mul_dvd_of_dvd_of_dvd ?_ ?_ ?_
  · exact_mod_cast Nat.coprime_two_left.mpr hp
  · simpa using even_iff_two_dvd.1 <| Odd.add_odd hn (by grind)
  · simpa [← ZMod.intCast_zmod_eq_zero_iff_dvd, sub_eq_zero] using ha

lemma Nat.coprime_lemma1 {n : ℕ} (hn : n % 8 = 1) :
    (4 * n).Coprime ((3 * n - 1) / 2) := by
  have h_gcd_dvd : (4 * n).gcd ((3 * n - 1) / 2) ∣ 4 := by
    rw [Nat.Coprime.gcd_mul_right_cancel _
      (Nat.Coprime.coprime_div_right _ (by grind))]
    · exact gcd_dvd_left 4 ((3 * n - 1) / 2)
    · refine Nat.coprime_sub_self_right (by grind) |>.1 <|
        Nat.coprime_sub_self_right (by grind) |>.1 ?_
      convert (Nat.sub_one_coprime_self (by grind : 0 < n)).symm using 1
      grind
  have h_gcd_odd : Odd ((4 * n).gcd ((3 * n - 1) / 2)) := Odd.of_dvd_nat
    (odd_iff.2 <| Nat.odd_of_mod_four_eq_one (by grind)) <| gcd_dvd_right _ _
  haveI := le_of_dvd (by omega) h_gcd_dvd
  haveI : 1 ≤ (4 * n).gcd ((3 * n - 1) / 2) := by grind
  rw [Nat.Coprime]
  interval_cases ((4 * n).gcd ((3 * n - 1) / 2))
  · rfl
  · norm_num at h_gcd_odd
  · omega
  · norm_num at h_gcd_odd

lemma Nat.coprime_lemma2 {n : ℕ} (hn : n % 8 = 3) :
    (4 * n).Coprime ((n - 1) / 2) := by
  have cop1 : n.Coprime (n - 1) := Nat.sub_one_coprime_self (by omega)|>.symm
  have cop2 : n.Coprime ((n - 1)/2) := Nat.Coprime.coprime_div_right cop1 (by omega)
  have hodd : Odd ((n - 1)/2) := by grind
  have cop3 : Nat.Coprime 4 ((n - 1)/ 2) := by
    have cop4 : Nat.Coprime 2 ((n - 1)/ 2) := by
      exact coprime_two_left.mpr hodd
    exact Nat.Coprime.pow_left 2 cop4
  exact Coprime.mul_left cop3 cop2

lemma Nat.coprime_lemma3 {n : ℕ} (hn : n % 8 = 5) :
   (4 * n).Coprime ((3 * n - 1) / 2) := by
  have A : n.Coprime (3 * n - 1) := by
    refine Nat.coprime_sub_self_right (by grind) |>.1 <|
      Nat.coprime_sub_self_right (by grind) |>.1 ?_
    convert (Nat.sub_one_coprime_self (by grind : 0 < n)).symm using 1
    grind
  have B : Odd ((3 * n - 1)/2) := by
    grind
  have C : n.Coprime ((3 * n - 1) / 2) := by
    refine Coprime.coprime_div_right A ?_
    grind
  have D : Nat.Coprime 4 ((3 * n - 1)/2) := by
    have := Nat.coprime_two_left (n := (3 * n - 1)/2) |>.2 B
    exact Nat.Coprime.pow_left 2 this
  exact Coprime.mul_left D C

lemma Nat.sum_threeSq_of_mod_eight_eq_one {n : ℕ} (hn : n % 8 = 1) :
    ∃ a b c : ℤ, n = a ^ 2 + b ^ 2 + c ^ 2 :=
  if hnn : n = 1 then ⟨1, 0, 0, by norm_num [hnn]⟩ else by
  have h1 : ((3 * n - 1) / 2) % 4 = 1 := by grind
  haveI : Odd ((3 * n - 1) / 2) := odd_iff.2 <| Nat.odd_of_mod_four_eq_one h1
  have h2 : (4 * n).Coprime ((3 * n - 1) / 2) := Nat.coprime_lemma1 hn
  obtain ⟨p, hp1, hp2, hp3⟩ := @Nat.forall_exists_prime_gt_and_modEq (7 * n) _ _ (by omega) h2.symm
  have hj' := dvd_sub_comm.1 <| Nat.modEq_iff_dvd.1 hp3
  rw [← Nat.cast_sub (Nat.div_le_of_le_mul <| by grw [hp1]; norm_num; linarith)] at hj'
  norm_cast at hj'
  obtain ⟨j, hj1⟩ := hj'
  rw [Nat.sub_eq_iff_eq_add (by grind)] at hj1
  have hp4 : Odd p := by grind
  have hj2 : 1 < j := by_contra fun hjj ↦ by
    interval_cases j <;> grind
  let d' := 8 * j + 3
  have hd1 : 2 * p = d' * n - 1 := by
    simp only [hj1, mul_add, Nat.mul_div_cancel_left' (by grind : 2 ∣ (3 * n - 1)), d']
    grind
  refine Nat.quadResidue_to_sum_threeSq n (by grind) ⟨d', by grind, hd1 ▸ ?_⟩
  have := ZMod.isSquare_coprime_split (p := p) hp4 (-d' : ℤ) (by grind) ?_
  · rwa [Int.cast_neg, Int.cast_natCast] at this

  sorry

lemma Nat.sum_threeSq_of_mod_eight_eq_three {n : ℕ} (hn : n % 8 = 3) :
    ∃ a b c : ℤ, n = a ^ 2 + b ^ 2 + c ^ 2 := by
  sorry

lemma Nat.sum_threeSq_of_mod_eight_eq_five {n : ℕ} (hn : n % 8 = 5) :
    ∃ a b c : ℤ, n = a ^ 2 + b ^ 2 + c ^ 2 := by
  sorry
