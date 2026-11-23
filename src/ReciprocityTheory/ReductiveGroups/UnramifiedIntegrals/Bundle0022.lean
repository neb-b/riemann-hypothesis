module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0018
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle0004
public import Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsNoPrimeToPTorsion
public import Formalism.EllipticTorsion.EllipticTorsionProofs.Bundle0004

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorsUnit2
section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F WeierstrassCurve

namespace ReciprocityTheory.ChartRestriction.L1

theorem torsUnit2 (K : Type) [NormedField K] [IsUltrametricDist K] (g2 g3 : K) (h2 : ‖(2 : K)‖ = 1)
    (h3 : ‖(3 : K)‖ = 1) (hg2 : ‖g2‖ ≤ 1) (hg3 : ‖g3‖ < 1) (hΔ : ‖g2 ^ 3 - 27 * g3 ^ 2‖ = 1)
    (n : ℕ) (hn : ‖(n : K)‖ = 1) (hen : ¬ 2 ∣ n) (x y : K)
    (h : (Formalism.L2.Th1.A.shortW g2 g3).toAffine.Nonsingular x y) (hP : n • (Affine.Point.some x y h) = 0) : ‖x‖ = 1 := by
  have n4 : ‖(4 : K)‖ = 1 := by
    rw [show (4 : K) = 2 * 2 by norm_num, norm_mul, h2]; norm_num
  have h40 : (4 : K) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at n4; exact zero_ne_one n4
  have h20 : (2 : K) ≠ 0 := by
    intro h0; rw [h0, norm_zero] at h2; exact zero_ne_one h2
  have hW : Formalism.ELL.IntegralModel (Formalism.L2.Th1.A.shortW g2 g3) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [Formalism.L2.Th1.A.shortW, n4, hg2, hg3.le]
  have hD : ‖(Formalism.L2.Th1.A.shortW g2 g3).Δ‖ = 1 := by
    have : (Formalism.L2.Th1.A.shortW g2 g3).Δ = g2 ^ 3 - 27 * g3 ^ 2 := by
      simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆, WeierstrassCurve.b₈, Formalism.L2.Th1.A.shortW]
      field_simp
      ring
    rw [this, hΔ]

  have hNoTorsion : ∀ P : (Formalism.L2.Th1.A.shortW g2 g3).toAffine.Point,
      Formalism.ELL.InFormalGroupPoints P → n • P = 0 → P = 0 := by
    intro P hP' hnP'
    by_contra hP0
    obtain ⟨m, hm⟩ : ∃ m, n = m + 1 :=
      Nat.exists_eq_succ_of_ne_zero (by rintro rfl; simp at hn)
    subst n
    have h := (Formalism.ELL.FormalGroupPointsTorsion.mulz hW P hP' hP0 m).2
    rw [hnP', Affine.Point.zero_def] at h
    simp only [Formalism.ELL.FormalGroupPointsTorsion.zf, zero_sub, norm_neg,
      norm_mul, hn, one_mul] at h
    exact lt_irrefl _ h

  have n27 : ‖(27 : K)‖ = 1 := by
    rw [show (27 : K) = 3 * 3 * 3 by norm_num, norm_mul, norm_mul, h3]; norm_num
  have hg2' : ‖g2‖ = 1 := by
    have hs : ‖27 * g3 ^ 2‖ < 1 := by
      rw [norm_mul, n27, one_mul, norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hg3 (by norm_num)
    have h1 : ‖g2 ^ 3‖ = 1 := by
      have e : g2 ^ 3 = (g2 ^ 3 - 27 * g3 ^ 2) + 27 * g3 ^ 2 := by ring
      rw [e, Formalism.ELL.FormalGroupPointsTorsion.dom (by rw [hΔ]; exact hs), hΔ]
    rw [norm_pow] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h1
  have hx : ‖x‖ ≤ 1 := by
    by_contra hx
    push Not at hx
    exact Affine.Point.some_ne_zero h
      (hNoTorsion _ hx hP)
  by_contra hne
  have hx1 : ‖x‖ < 1 := lt_of_le_of_ne hx hne
  have heq : y ^ 2 = x ^ 3 - g2 / 4 * x - g3 / 4 := by
    have := (Affine.equation_iff x y).1 h.1
    simp only [Formalism.L2.Th1.A.shortW] at this
    linear_combination this
  have hy1 : ‖y‖ < 1 := by
    have : ‖y ^ 2‖ < 1 := by
      rw [heq]
      refine Formalism.ELL.FormalGroupPointsTorsion.sub_lt (Formalism.ELL.FormalGroupPointsTorsion.sub_lt ?_ ?_) ?_
      · rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hx1 (by norm_num)
      · rw [norm_mul, norm_div, n4, hg2']; simpa using hx1
      · rw [norm_div, n4]; simpa using hg3
    rw [norm_pow] at this
    by_contra hc
    push Not at hc
    exact absurd this (not_lt.2 (one_le_pow₀ hc))

  have hQ : Formalism.ELL.InFormalGroupPoints (Affine.Point.some x y h + Affine.Point.some x y h) := by
    by_cases hy : y = (Formalism.L2.Th1.A.shortW g2 g3).toAffine.negY x y
    · rw [Affine.Point.add_self_of_Y_eq hy, Affine.Point.zero_def]; trivial
    · rw [Affine.Point.add_self_of_Y_ne hy]
      show 1 < ‖_‖
      have hy0 : y ≠ 0 := by
        rintro rfl
        exact hy (by simp [Affine.negY, Formalism.L2.Th1.A.shortW])
      rw [Affine.slope_of_Y_ne rfl hy]
      simp only [Affine.addX, Affine.negY, Formalism.L2.Th1.A.shortW]
      have e : ((3 * x ^ 2 + 2 * 0 * x + -g2 / 4 - 0 * y) / (y - (-y - 0 * x - 0))) ^ 2 +
          0 * ((3 * x ^ 2 + 2 * 0 * x + -g2 / 4 - 0 * y) / (y - (-y - 0 * x - 0))) - 0 - x - x
          = ((-(g2 / 4) + 3 * x ^ 2) / (2 * y)) ^ 2 + (-x - x) := by
        have : y - (-y - 0 * x - 0) = 2 * y := by ring
        rw [this]; ring
      rw [e]
      have hnum : ‖-(g2 / 4) + 3 * x ^ 2‖ = 1 := by
        have ha : ‖-(g2 / 4)‖ = 1 := by rw [norm_neg, norm_div, n4, hg2']; norm_num
        rw [Formalism.ELL.FormalGroupPointsTorsion.dom, ha]
        rw [ha, norm_mul, h3, one_mul, norm_pow]
        exact pow_lt_one₀ (norm_nonneg _) hx1 (by norm_num)
      have hyp : 0 < ‖y‖ := norm_pos_iff.2 hy0
      have hl : 1 < ‖((-(g2 / 4) + 3 * x ^ 2) / (2 * y)) ^ 2‖ := by
        rw [norm_pow, norm_div, hnum, norm_mul, h2, one_mul]
        exact one_lt_pow₀ ((one_lt_div hyp).2 hy1) (by norm_num)
      have hs : ‖-x - x‖ < 1 :=
        Formalism.ELL.FormalGroupPointsTorsion.sub_lt (by rwa [norm_neg]) hx1
      rw [Formalism.ELL.FormalGroupPointsTorsion.dom (hs.trans hl)]
      exact hl
  have hQ0 : Affine.Point.some x y h + Affine.Point.some x y h = 0 := by
    apply hNoTorsion _ hQ
    rw [nsmul_add, hP, add_zero]
  obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := by
    have := Nat.odd_iff.2 (by omega : n % 2 = 1)
    exact this
  refine Affine.Point.some_ne_zero h ?_
  rw [add_nsmul, one_nsmul, mul_comm, mul_nsmul', two_nsmul, hQ0, nsmul_zero, zero_add] at hP
  exact hP

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorsUnit3
section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F WeierstrassCurve

namespace ReciprocityTheory.ChartRestriction.L1

namespace ThreeTorsionChord

open Formalism.ELL.FormalGroupPointsTorsion

variable {K : Type} [NormedField K] [IsUltrametricDist K]

lemma dbl {x y a l x2 y2 : K} (h2 : ‖(2 : K)‖ = 1) (hx : ‖x‖ < 1) (hy : ‖y‖ = 1) (ha : ‖a‖ < 1)
    (hl : l = (3 * x ^ 2 + a) / (2 * y)) (hx2 : x2 = l ^ 2 - x - x)
    (hy2 : y2 = -(l * (x2 - x) + y)) : ‖x2‖ < 1 ∧ ‖y2 + y‖ < 1 := by
  have hxx : ‖x ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hx (by norm_num)
  have hl1 : ‖l‖ < 1 := by
    rw [hl, norm_div, norm_mul, h2, hy, one_mul, div_one]
    exact add_lt ((mul_le_of_one three_le).trans_lt hxx) ha
  have hll : ‖l ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hl1 (by norm_num)
  have h1 : ‖x2‖ < 1 := by rw [hx2]; exact sub_lt (sub_lt hll hx) hx
  refine ⟨h1, ?_⟩
  have : y2 + y = -(l * (x2 - x)) := by rw [hy2]; ring
  rw [this, norm_neg]
  exact (mul_le_of_one hl1.le).trans_lt (sub_lt h1 hx)

lemma chordBig {x y x2 y2 m : K} (h2 : ‖(2 : K)‖ = 1) (hx : ‖x‖ < 1) (hy : ‖y‖ = 1)
    (hx2 : ‖x2‖ < 1) (hy2 : ‖y2 + y‖ < 1) (hne : x2 ≠ x) (hm : m = (y2 - y) / (x2 - x)) :
    1 < ‖m ^ 2 - x2 - x‖ := by
  have hn : ‖y2 - y‖ = 1 := by
    have : y2 - y = -(2 * y) + (y2 + y) := by ring
    rw [this, dom (by rw [norm_neg, norm_mul, h2, hy, one_mul]; exact hy2), norm_neg, norm_mul,
      h2, hy, one_mul]
  have hd : ‖x2 - x‖ < 1 := sub_lt hx2 hx
  have hd0 : 0 < ‖x2 - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hm1 : 1 < ‖m‖ := by
    rw [hm, norm_div, hn]; exact (one_lt_div hd0).mpr hd
  have hmm : 1 < ‖m ^ 2‖ := by rw [norm_pow]; exact one_lt_pow₀ hm1 (by norm_num)
  have : m ^ 2 - x2 - x = m ^ 2 + (-x2 - x) := by ring
  rw [this, dom ((sub_lt (by rwa [norm_neg]) hx).trans hmm)]
  exact hmm

end ThreeTorsionChord

theorem torsUnit3 (K : Type) [NormedField K] [IsUltrametricDist K] (g2 g3 : K) (h2 : ‖(2 : K)‖ = 1)
    (h3 : ‖(3 : K)‖ = 1) (hg2 : ‖g2‖ < 1) (hg3 : ‖g3‖ ≤ 1) (hΔ : ‖g2 ^ 3 - 27 * g3 ^ 2‖ = 1)
    (n : ℕ) (hn : ‖(n : K)‖ = 1) (hen : ¬ 3 ∣ n) (x y : K)
    (h : (Formalism.L2.Th1.A.shortW g2 g3).toAffine.Nonsingular x y) (hP : n • (Affine.Point.some x y h) = 0) : ‖x‖ = 1 := by
  have h20 : (2 : K) ≠ 0 := by intro h0; rw [h0, norm_zero] at h2; exact zero_ne_one h2
  have h4 : ‖(4 : K)‖ = 1 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this, norm_mul, h2, one_mul]
  have h27 : ‖(27 : K)‖ = 1 := by
    have : (27 : K) = 3 * 3 * 3 := by norm_num
    rw [this, norm_mul, norm_mul, h3, one_mul, one_mul]
  have hg3' : ‖g3‖ = 1 := by
    have hc : ‖g2 ^ 3‖ < 1 := by
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hg2 (by norm_num)
    by_contra hne
    have hlt : ‖g3‖ < 1 := lt_of_le_of_ne hg3 hne
    have : ‖g2 ^ 3 - 27 * g3 ^ 2‖ < 1 := by
      refine Formalism.ELL.FormalGroupPointsTorsion.sub_lt hc ?_
      rw [norm_mul, h27, one_mul, norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hlt (by norm_num)
    exact absurd hΔ this.ne
  have ha4 : ‖-g2 / 4‖ < 1 := by rw [norm_div, norm_neg, h4, div_one]; exact hg2
  have ha6 : ‖-g3 / 4‖ = 1 := by rw [norm_div, norm_neg, h4, div_one]; exact hg3'
  have hW : Formalism.ELL.IntegralModel (Formalism.L2.Th1.A.shortW g2 g3) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Formalism.L2.Th1.A.shortW, norm_zero, zero_le_one]
    · exact ha4.le
    · exact ha6.le
  have hD : ‖(Formalism.L2.Th1.A.shortW g2 g3).Δ‖ = 1 := by
    have : (Formalism.L2.Th1.A.shortW g2 g3).Δ = g2 ^ 3 - 27 * g3 ^ 2 := by
      simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
        WeierstrassCurve.b₈, Formalism.L2.Th1.A.shortW]
      have h40 : (4 : K) ≠ 0 := by intro h0; rw [h0, norm_zero] at h4; exact zero_ne_one h4
      field_simp
      ring
    rw [this, hΔ]
  have formalGroupTorsionFree : ∀ P : (Formalism.L2.Th1.A.shortW g2 g3).toAffine.Point,
      Formalism.ELL.InFormalGroupPoints P → n • P = 0 → P = 0 := by
    intro P hFormal hTorsion
    by_contra hNonzero
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
      Nat.exists_eq_succ_of_ne_zero (by rintro rfl; simp at hn)
    have hz := (Formalism.ELL.FormalGroupPointsTorsion.mulz hW P hFormal hNonzero m).2
    rw [hTorsion, Affine.Point.zero_def] at hz
    simp only [Formalism.ELL.FormalGroupPointsTorsion.zf, zero_sub, norm_neg, norm_mul, hn, one_mul] at hz
    exact lt_irrefl _ hz
  have hx1 : ‖x‖ ≤ 1 := by
    by_contra hx
    exact Affine.Point.some_ne_zero h (formalGroupTorsionFree _ (not_le.mp hx) hP)
  by_contra hne
  have hx : ‖x‖ < 1 := lt_of_le_of_ne hx1 hne
  have heq : y ^ 2 = -g3 / 4 + (x ^ 3 + -g2 / 4 * x) := by
    have := h.1
    rw [Affine.equation_iff] at this
    simp only [Formalism.L2.Th1.A.shortW] at this
    linear_combination this
  have hy : ‖y‖ = 1 := by
    have hs : ‖x ^ 3 + -g2 / 4 * x‖ < 1 := by
      refine Formalism.ELL.FormalGroupPointsTorsion.add_lt ?_ ((Formalism.ELL.FormalGroupPointsTorsion.mul_le_of_one ha4.le).trans_lt hx)
      rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hx (by norm_num)
    have : ‖y ^ 2‖ = 1 := by
      rw [heq, Formalism.ELL.FormalGroupPointsTorsion.dom (by rw [ha6]; exact hs), ha6]
    rw [norm_pow] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp this
  have h2y : ‖2 * y‖ = 1 := by rw [norm_mul, h2, hy, one_mul]
  have hneg : ∀ u v : K, (Formalism.L2.Th1.A.shortW g2 g3).toAffine.negY u v = -v := by
    intro u v; simp [Affine.negY, Formalism.L2.Th1.A.shortW]
  have hyne : y ≠ (Formalism.L2.Th1.A.shortW g2 g3).toAffine.negY x y := by
    rw [hneg]; intro h0
    have : 2 * y = 0 := by linear_combination h0
    rw [this, norm_zero] at h2y; exact zero_ne_one h2y
  have hxy : ¬(x = x ∧ y = (Formalism.L2.Th1.A.shortW g2 g3).toAffine.negY x y) := fun hh => hyne hh.2

  have hE : Formalism.ELL.InFormalGroupPoints (3 • Affine.Point.some x y h) := by
    have e3 : 3 • Affine.Point.some x y h =
        (Affine.Point.some x y h + Affine.Point.some x y h) + Affine.Point.some x y h := by
      rw [succ_nsmul, two_nsmul]
    rw [e3, Affine.Point.add_some hxy]
    obtain ⟨l, hl⟩ : ∃ l, l = (Formalism.L2.Th1.A.shortW g2 g3).toAffine.slope x x y y := ⟨_, rfl⟩
    have hl' : l = (3 * x ^ 2 + -g2 / 4) / (2 * y) := by
      rw [hl, Affine.slope_of_Y_ne rfl hyne, hneg]
      simp only [Formalism.L2.Th1.A.shortW]
      congr 1 <;> ring
    obtain ⟨x2, hx2⟩ : ∃ x2, x2 = (Formalism.L2.Th1.A.shortW g2 g3).toAffine.addX x x l := ⟨_, rfl⟩
    obtain ⟨y2, hy2⟩ : ∃ y2, y2 = (Formalism.L2.Th1.A.shortW g2 g3).toAffine.addY x x y l := ⟨_, rfl⟩
    have hx2' : x2 = l ^ 2 - x - x := by
      rw [hx2]; simp only [Affine.addX, Formalism.L2.Th1.A.shortW]; ring
    have hy2' : y2 = -(l * (x2 - x) + y) := by
      rw [hy2, Affine.addY, hneg, Affine.negAddY, ← hx2]
    obtain ⟨hX2, hY2⟩ := ThreeTorsionChord.dbl h2 hx hy ha4 hl' hx2' hy2'
    simp only [← hl, ← hx2, ← hy2]
    by_cases hc : x2 = x ∧ y2 = (Formalism.L2.Th1.A.shortW g2 g3).toAffine.negY x y
    · rw [Affine.Point.add_of_Y_eq hc.1 hc.2, Affine.Point.zero_def]; trivial
    · rw [Affine.Point.add_some hc]
      have hxne : x2 ≠ x := by
        intro hxe
        have hq : (Formalism.L2.Th1.A.shortW g2 g3).toAffine.Equation x2 y2 := by
          rw [hx2, hy2, hl]; exact (Affine.nonsingular_add h h hxy).1
        have hye := Affine.Y_eq_of_Y_ne hq h.1 hxe (fun hh => hc ⟨hxe, hh⟩)
        rw [hye, ← two_mul, h2y] at hY2
        exact lt_irrefl _ hY2
      have hb := ThreeTorsionChord.chordBig h2 hx hy hX2 hY2 hxne rfl
      show 1 < ‖(Formalism.L2.Th1.A.shortW g2 g3).toAffine.addX x2 x _‖
      rw [Affine.slope_of_X_ne hxne]
      simp only [Affine.addX, Formalism.L2.Th1.A.shortW]
      convert hb using 2
      ring
  have h3P : 3 • Affine.Point.some x y h = 0 := by
    refine formalGroupTorsionFree _ hE ?_
    rw [smul_comm, hP, smul_zero]
  have hd1 : addOrderOf (Affine.Point.some x y h) ∣ 3 := addOrderOf_dvd_of_nsmul_eq_zero h3P
  have hd2 : addOrderOf (Affine.Point.some x y h) ∣ n := addOrderOf_dvd_of_nsmul_eq_zero hP
  have hcop : Nat.Coprime 3 n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hen
  have h1 : addOrderOf (Affine.Point.some x y h) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
  exact Affine.Point.some_ne_zero h (AddMonoid.addOrderOf_eq_one_iff.mp h1)

end ReciprocityTheory.ChartRestriction.L1
end
end

