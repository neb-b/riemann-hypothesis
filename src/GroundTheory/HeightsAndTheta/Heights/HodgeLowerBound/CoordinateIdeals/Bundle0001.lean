module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLevi
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0002

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLeviGen
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi

open ReciprocityTheory.ChartRestriction.G.Geo

variable {J : Type} [Fintype J]

theorem lagrange_sum (z w : J → ℂ) :
    ∑ p, ∑ q, Complex.normSq (z p * w q - z q * w p) =
      2 * (sqSum z * sqSum w - (reInner z w ^ 2 + reInner z (Complex.I • w) ^ 2)) := by
  set r : J → ℝ := fun p => (z p).re * (w p).re + (z p).im * (w p).im with hr
  set s : J → ℝ := fun p => (z p).im * (w p).re - (z p).re * (w p).im with hs
  set G : J → J → ℝ := fun p q => ‖z p‖ ^ 2 * ‖w q‖ ^ 2 - r p * r q - s p * s q with hG
  have hrw : reInner z w = ∑ p, r p := by rw [reInner_apply]
  have hsw : reInner z (Complex.I • w) = ∑ p, s p := by
    rw [reInner_apply]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, hs]
    ring
  have key : ∀ p q, Complex.normSq (z p * w q - z q * w p) = G p q + G q p := by
    intro p q
    simp only [hG, hr, hs, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im]
    ring
  have hsym : ∑ p, ∑ q, G q p = ∑ p, ∑ q, G p q := Finset.sum_comm
  have hexp : sqSum z * sqSum w - (reInner z w ^ 2 + reInner z (Complex.I • w) ^ 2) = ∑ p, ∑ q, G p q := by
    rw [hrw, hsw, sqSum, sqSum, sq, sq, Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [hG]
    ring
  simp_rw [key, Finset.sum_add_distrib]
  rw [hsym, hexp]
  ring

theorem sqSum_ne_zero {z : J → ℂ} (hz : ∃ i, z i ≠ 0) : sqSum z ≠ 0 := by
  obtain ⟨i, hi⟩ := hz
  refine ne_of_gt (lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2) ?_)
  exact Finset.single_le_sum (f := fun p => ‖z p‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

theorem levi_phi_pos_of_ne {z w : J → ℂ} (hz : ∃ i, z i ≠ 0)
    (hw : ∀ c : ℂ, w ≠ fun p => c * z p) : 0 < leviForm phi z w := by
  have hS := sqSum_ne_zero hz
  rw [leviForm_phi hS]
  have hnum : 0 < sqSum z * sqSum w - (reInner z w ^ 2 + reInner z (Complex.I • w) ^ 2) := by
    have h2 := lagrange_sum z w
    have hnn : 0 ≤ ∑ p, ∑ q, Complex.normSq (z p * w q - z q * w p) :=
      Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => Complex.normSq_nonneg _
    rcases hnn.lt_or_eq with hlt | heq
    · linarith
    · exfalso
      obtain ⟨i, hi⟩ := hz
      have hall : ∀ p q, Complex.normSq (z p * w q - z q * w p) = 0 := by
        intro p q
        have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun p _ => Finset.sum_nonneg fun q _ =>
          Complex.normSq_nonneg (z p * w q - z q * w p))).1 heq.symm p (Finset.mem_univ _)
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => Complex.normSq_nonneg _)).1 h1 q
          (Finset.mem_univ _)
      apply hw (w i / z i)
      funext q
      have h := hall i q
      rw [Complex.normSq_eq_zero, sub_eq_zero] at h
      rw [div_mul_eq_mul_div, eq_div_iff hi]
      linear_combination h
  exact div_pos (by linarith) (by have := sqSum_nonneg z; positivity)

end GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.MemMCoordIdealOfAevalEqZero
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

section Homog

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] in
theorem isMultiHomog_zero (d : K → ℕ) : IsMultiHomog (0 : MRing ι) d := by
  intro m hm
  simp at hm

omit [Fintype K] in
theorem isMultiHomog_add {g h : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d)
    (hh : IsMultiHomog h d) : IsMultiHomog (g + h) d := by
  classical
  intro m hm
  rcases Finset.mem_union.mp (support_add hm) with hm | hm
  · exact hg m hm
  · exact hh m hm

omit [Fintype K] in
theorem isMultiHomog_mul {g h : MRing ι} {a b : K → ℕ} (hg : IsMultiHomog g a)
    (hh : IsMultiHomog h b) : IsMultiHomog (g * h) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m₁, hm₁, m₂, hm₂, rfl⟩ := Finset.mem_add.mp (support_mul g h hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply]
  rw [hg m₁ hm₁ k, hh m₂ hm₂ k]

theorem isMultiHomog_one : IsMultiHomog (1 : MRing ι) 0 := by
  simpa using isMultiHomog_C_zero (ι := ι) 1

end Homog

section Cone

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem mConeMap_of_isMultiHomog (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ}
    (hg : IsMultiHomog g d) :
    mConeMap y g = MvPolynomial.C (aeval y g) * ∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg := hg m hm
  simp only [mConeMap, aeval_monomial, map_mul]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]
  have hX : (∏ p : Σ k, ι k, (MvPolynomial.X p.1 : MvPolynomial K Ω) ^ m p) =
      ∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, (MvPolynomial.X k : MvPolynomial K Ω) ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hdeg k]
  rw [hX, MvPolynomial.algebraMap_apply]
  ring

theorem mem_mCoordIdeal_of_aeval_eq_zero (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ}
    (hg : IsMultiHomog g d) (h0 : aeval y g = 0) : g ∈ mCoordIdeal y := by
  show g ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  erw [mConeMap_of_isMultiHomog y hg, h0]
  simp

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem eval_eq_zero_of_mem_mcPts {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P)
    {g : MRing ι} (hg : g ∈ P) : eval z (map (Int.castRingHom ℂ) g) = 0 :=
  hz.2 g hg

theorem isValueAt_one {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y))
    {v : ℂ} (hv : IsValueAt y 1 z v) : v = 1 := by
  obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := hv
  have hsub : IsMultiHomog (g - h) d := by
    rw [sub_eq_add_neg]
    refine isMultiHomog_add hg ?_
    intro m hm
    exact hh m (by simpa using hm)
  have h0 : aeval y (g - h) = 0 := by rw [map_sub, heq, one_mul, sub_self]
  have := eval_eq_zero_of_mem_mcPts hz (mem_mCoordIdeal_of_aeval_eq_zero y hsub h0)
  rw [map_sub, map_sub, sub_eq_zero] at this
  rw [this, div_self hz0]

theorem isValueAt_zero {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y))
    {v : ℂ} (hv : IsValueAt y 0 z v) : v = 0 := by
  obtain ⟨d, g, h, hg, hh, hy, heq, hz0, rfl⟩ := hv
  rw [zero_mul] at heq
  rw [eval_eq_zero_of_mem_mcPts hz (mem_mCoordIdeal_of_aeval_eq_zero y hg heq), zero_div]

theorem isValueAt_one_self (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : IsValueAt y 1 z 1 :=
  ⟨0, 1, 1, isMultiHomog_one, isMultiHomog_one, by simp, by simp, by simp, by simp⟩

end Cone

section Trivial

variable {Ω : Type} [Field Ω] {κ : Type}

end Trivial

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

