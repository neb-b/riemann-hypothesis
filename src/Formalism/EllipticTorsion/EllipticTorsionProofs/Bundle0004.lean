module

public import Mathlib
public import Formalism.EllipticTorsion.Bundle0003
public import Formalism.EllipticTorsion.Bundle0002
public import Formalism.EllipticTorsion.EllipticTorsionProofs.Bundle0002

@[expose] public section

-- bundled from Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsSubgroupHolds
section
noncomputable section

universe u

namespace Formalism.ELL.FormalGroupPointsSubgroup

open WeierstrassCurve Polynomial

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

lemma add_le {a b : K} {c : ℝ} (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ c) : ‖a + b‖ ≤ c := by
  exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

lemma sub_le {a b : K} {c : ℝ} (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ c) : ‖a - b‖ ≤ c := by
  rw [sub_eq_add_neg]
  exact add_le ha (by rwa [norm_neg])

lemma le_sub_of_lt {a b : K} (h : ‖b‖ < ‖a‖) : ‖a‖ ≤ ‖a - b‖ := by
  have h1 : ‖a‖ ≤ max ‖a - b‖ ‖b‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (a - b) b
  rcases le_max_iff.mp h1 with h2 | h2
  · exact h2
  · exact absurd h2 (not_le.mpr h)

lemma mul_le {a b : K} {c d : ℝ} (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ d) : ‖a * b‖ ≤ c * d := by
  rw [norm_mul]
  exact mul_le_mul ha hb (norm_nonneg _) ((norm_nonneg _).trans ha)

lemma y_int (W : WeierstrassCurve K)
    (hW : IntegralModel W) {x y : K} (h : W.toAffine.Equation x y) (hx : ‖x‖ ≤ 1) : ‖y‖ ≤ 1 := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  have h' : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
    (WeierstrassCurve.Affine.equation_iff _ _).mp h
  by_contra hy
  push_neg at hy
  have hR : ‖x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆‖ ≤ 1 := by
    have hx2 : ‖x ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
    have hx3 : ‖x ^ 3‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
    refine add_le (add_le (add_le hx3 ?_) ?_) h6
    · simpa using mul_le h2 hx2
    · simpa using mul_le h4 hx
  have hT : ‖W.a₁ * x * y + W.a₃ * y‖ ≤ ‖y‖ := by
    refine add_le ?_ ?_
    · simpa using mul_le (mul_le h1 hx) (le_refl ‖y‖)
    · simpa using mul_le h3 (le_refl ‖y‖)
  have hlt : ‖-(W.a₁ * x * y + W.a₃ * y)‖ < ‖y ^ 2‖ := by
    rw [norm_neg, norm_pow]; nlinarith
  have key := le_sub_of_lt hlt
  rw [sub_neg_eq_add, ← add_assoc, h', norm_pow] at key
  nlinarith

lemma y_sq_le (W : WeierstrassCurve K) (hW : IntegralModel W) {x y : K}
    (h : W.toAffine.Equation x y) (hx : 1 < ‖x‖) : ‖y‖ ^ 2 ≤ ‖x‖ ^ 3 := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  have h' : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
    (WeierstrassCurve.Affine.equation_iff _ _).mp h
  by_contra hy
  push_neg at hy
  have hx0 : (0 : ℝ) < ‖x‖ := by linarith
  have hx2 : ‖x‖ ^ 2 < ‖x‖ ^ 3 := by
    nlinarith [mul_pos (mul_pos hx0 hx0) (by linarith : (0 : ℝ) < ‖x‖ - 1)]
  have hx1 : ‖x‖ ≤ ‖x‖ ^ 3 := by
    nlinarith [mul_pos hx0 (by linarith : (0 : ℝ) < ‖x‖ - 1)]
  have hxy : ‖x‖ < ‖y‖ := by
    by_contra hc
    push_neg at hc
    have := mul_le_mul hc hc (norm_nonneg y) hx0.le
    nlinarith
  have hR : ‖x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆‖ ≤ ‖x‖ ^ 3 := by
    refine add_le (add_le (add_le (le_of_eq (norm_pow _ _)) ?_) ?_) ?_
    · exact (mul_le h2 (le_of_eq (norm_pow x 2))).trans (by linarith)
    · exact (mul_le h4 (le_refl ‖x‖)).trans (by linarith)
    · exact h6.trans (one_le_pow₀ hx.le)
  have hT : ‖W.a₁ * x * y + W.a₃ * y‖ ≤ ‖x‖ * ‖y‖ := by
    refine add_le ?_ ?_
    · simpa using mul_le (mul_le h1 (le_refl ‖x‖)) (le_refl ‖y‖)
    · exact (mul_le h3 (le_refl ‖y‖)).trans (by nlinarith [norm_nonneg y])
  have hlt : ‖-(W.a₁ * x * y + W.a₃ * y)‖ < ‖y ^ 2‖ := by
    rw [norm_neg, norm_pow]; nlinarith [norm_nonneg y]
  have key := le_sub_of_lt hlt
  rw [sub_neg_eq_add, ← add_assoc, h', norm_pow] at key
  linarith

lemma addX_norm [DecidableEq K] (W : WeierstrassCurve K) (hW : IntegralModel W)
    {x₁ x₂ y₁ y₂ : K} (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂)) (hx₁ : 1 < ‖x₁‖) (hx₂ : 1 < ‖x₂‖) :
    1 < ‖W.toAffine.addX x₁ x₂ (W.toAffine.slope x₁ x₂ y₁ y₂)‖ := by
  set ℓ := W.toAffine.slope x₁ x₂ y₁ y₂ with hℓ
  set x₃ := W.toAffine.addX x₁ x₂ ℓ with hx₃
  set y₃ := W.toAffine.negAddY x₁ x₂ y₁ ℓ with hy₃
  by_contra hC
  push Not at hC
  have h₃ : W.toAffine.Equation x₃ y₃ := Affine.equation_negAdd h₁ h₂ hxy
  have hy3 : ‖y₃‖ ≤ 1 := y_int W hW h₃ hC
  have hpoly := Affine.addPolynomial_slope h₁ h₂ hxy
  rw [← hℓ] at hpoly
  have hev := congrArg (Polynomial.eval (x₃ + 1)) hpoly
  simp only [Affine.addPolynomial, Affine.linePolynomial, Affine.polynomial] at hev
  simp at hev
  have hx3def : x₃ = ℓ ^ 2 + W.toAffine.a₁ * ℓ - W.toAffine.a₂ - x₁ - x₂ := by simp [hx₃]
  rw [← hx3def] at hev
  obtain ⟨a1, a2, a3, a4, a6⟩ := hW

  have hy3def : y₃ = ℓ * (x₃ - x₁) + y₁ := by simp [hy₃, hx₃]
  have hx0 : 0 ≤ ‖x₁‖ := norm_nonneg _
  have hℓ0 : 0 ≤ ‖ℓ‖ := norm_nonneg _
  have hsq := y_sq_le W ⟨a1, a2, a3, a4, a6⟩ h₁ hx₁
  have hd : ‖x₁‖ ≤ ‖x₁ - x₃‖ := le_sub_of_lt (by linarith)
  have hlin : ‖ℓ‖ * ‖x₁‖ ≤ max ‖y₁‖ 1 := by
    have e : ℓ * (x₁ - x₃) = y₁ - y₃ := by rw [hy3def]; ring
    have : ‖ℓ * (x₁ - x₃)‖ ≤ max ‖y₁‖ 1 := by
      rw [e]; exact sub_le (le_max_left _ _) (hy3.trans (le_max_right _ _))
    rw [norm_mul] at this
    nlinarith
  have hℓsq : ‖ℓ‖ ^ 2 ≤ ‖x₁‖ := by
    have hm : (max ‖y₁‖ 1) ^ 2 ≤ ‖x₁‖ ^ 3 := by
      rcases le_total ‖y₁‖ 1 with h | h
      · rw [max_eq_right h, one_pow]; exact one_le_pow₀ hx₁.le
      · rw [max_eq_left h]; exact hsq
    have : (‖ℓ‖ * ‖x₁‖) ^ 2 ≤ ‖x₁‖ ^ 3 :=
      (pow_le_pow_left₀ (by positivity) hlin 2).trans hm
    have hx1p : 0 < ‖x₁‖ ^ 2 := by positivity
    nlinarith

  set M := max 1 ‖ℓ‖ with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hMℓ : ‖ℓ‖ ≤ M := le_max_right _ _
  have hMsq : M ^ 2 ≤ ‖x₁‖ := by
    rcases le_total 1 ‖ℓ‖ with h | h
    · rw [hM, max_eq_right h]; exact hℓsq
    · rw [hM, max_eq_left h]; nlinarith
  have ht : ‖x₃ + 1‖ ≤ 1 := add_le hC (by simp)
  have hu : ‖ℓ * (x₃ + 1 - x₁) + y₁‖ ≤ M := by
    have e : ℓ * (x₃ + 1 - x₁) + y₁ = y₃ + ℓ := by rw [hy3def]; ring
    rw [e]; exact add_le (hy3.trans hM1) hMℓ
  have hM2 : M ≤ M ^ 2 := by nlinarith
  have hLHS : ‖(ℓ * (x₃ + 1 - x₁) + y₁) ^ 2 + W.a₁ * (x₃ + 1) * (ℓ * (x₃ + 1 - x₁) + y₁)
      + W.a₃ * (ℓ * (x₃ + 1 - x₁) + y₁)
      - ((x₃ + 1) ^ 3 + W.a₂ * (x₃ + 1) ^ 2 + W.a₄ * (x₃ + 1) + W.a₆)‖ ≤ ‖x₁‖ := by
    have ht2 : ‖(x₃ + 1) ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ht
    have ht3 : ‖(x₃ + 1) ^ 3‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ht
    have hc : ‖(x₃ + 1) ^ 3 + W.a₂ * (x₃ + 1) ^ 2 + W.a₄ * (x₃ + 1) + W.a₆‖ ≤ 1 := by
      refine add_le (add_le (add_le ht3 ?_) ?_) a6
      · simpa using mul_le a2 ht2
      · simpa using mul_le a4 ht
    refine sub_le (add_le (add_le ?_ ?_) ?_) (hc.trans (by nlinarith))
    · rw [norm_pow]; exact (pow_le_pow_left₀ (norm_nonneg _) hu 2).trans hMsq
    · have := mul_le (mul_le a1 ht) hu
      linarith
    · have := mul_le a3 hu
      linarith

  have hRHS : ‖x₁‖ * ‖x₂‖ ≤ ‖(x₃ + 1 - x₁) * (x₃ + 1 - x₂) * (x₃ + 1 - x₃)‖ := by
    have e1 : ‖x₁‖ ≤ ‖x₃ + 1 - x₁‖ := by
      rw [norm_sub_rev]; exact le_sub_of_lt (by linarith)
    have e2 : ‖x₂‖ ≤ ‖x₃ + 1 - x₂‖ := by
      rw [norm_sub_rev]; exact le_sub_of_lt (by linarith)
    have e3 : x₃ + 1 - x₃ = 1 := by ring
    rw [e3, mul_one, norm_mul]
    exact mul_le_mul e1 e2 (norm_nonneg _) (norm_nonneg _)
  have heq : (ℓ * (x₃ + 1 - x₁) + y₁) ^ 2 + W.a₁ * (x₃ + 1) * (ℓ * (x₃ + 1 - x₁) + y₁)
      + W.a₃ * (ℓ * (x₃ + 1 - x₁) + y₁)
      - ((x₃ + 1) ^ 3 + W.a₂ * (x₃ + 1) ^ 2 + W.a₄ * (x₃ + 1) + W.a₆) =
      -((x₃ + 1 - x₁) * (x₃ + 1 - x₂) * (x₃ + 1 - x₃)) := by
    linear_combination hev
  rw [heq, norm_neg] at hLHS
  have := hRHS.trans hLHS
  nlinarith

end Formalism.ELL.FormalGroupPointsSubgroup

namespace Formalism.ELL

open WeierstrassCurve

open Classical in
theorem formal_group_points_subgroup_holds : Formalism.ELL.FormalGroupPointsSubgroup' := by
  intro K _ _ W hW _ P Q hP hQ
  refine ⟨?_, ?_⟩
  · rcases P with _ | @⟨x₁, y₁, h₁⟩
    · rw [show (Affine.Point.zero : W.toAffine.Point) = 0 from rfl, zero_add]; exact hQ
    rcases Q with _ | @⟨x₂, y₂, h₂⟩
    · rw [show (Affine.Point.zero : W.toAffine.Point) = 0 from rfl, add_zero]; exact hP
    by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
    · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2]
      trivial
    · rw [Affine.Point.add_some hxy]
      exact FormalGroupPointsSubgroup.addX_norm W hW h₁.1 h₂.1 hxy hP hQ
  · rcases P with _ | @⟨x, y, h⟩
    · trivial
    · simpa [InFormalGroupPoints] using hP

end Formalism.ELL
end
end

-- bundled from Formalism.EllipticTorsion.EllipticTorsionProofs.Legendre
section
namespace Formalism.ELL

namespace LegendreModelEllipticTorsion

open Polynomial

noncomputable def legPoly {K : Type*} [Field K] (j : K) : K[X] :=
  C 256 * (X ^ 2 - X + 1) ^ 3 - C j * (X * (X - 1)) ^ 2

theorem legPoly_natDegree {K : Type*} [Field K] (h : (256 : K) ≠ 0) (j : K) :
    (legPoly j).natDegree = 6 := by
  unfold legPoly
  compute_degree!

theorem norm_one_add {K : Type*} [NormedField K] [IsUltrametricDist K] {t : K} (ht : ‖t‖ ≠ 1) :
    ‖1 + t‖ = max 1 ‖t‖ := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := (1 : K)) (y := t)
    (by rw [norm_one]; exact fun h => ht h.symm)
  simpa using this

end LegendreModelEllipticTorsion

open LegendreModelEllipticTorsion Polynomial in
theorem legendre_model : ModelLegendre := by
  intro K _ _ _ h2 j hj
  have h16 : ‖(16 : K)‖ = 1 := by
    have : (16 : K) = 2 ^ 4 := by norm_num
    rw [this, norm_pow, h2, one_pow]
  have h256 : ‖(256 : K)‖ = 1 := by
    have : (256 : K) = 2 ^ 8 := by norm_num
    rw [this, norm_pow, h2, one_pow]
  have h256ne : (256 : K) ≠ 0 := by
    intro h; rw [h, norm_zero] at h256; exact zero_ne_one h256
  have hdeg : (legPoly j).degree ≠ 0 := by
    rw [degree_eq_natDegree, legPoly_natDegree h256ne]
    · decide
    · intro h0
      have := legPoly_natDegree h256ne j
      rw [h0, natDegree_zero] at this
      exact absurd this (by decide)
  obtain ⟨l, hl⟩ := IsAlgClosed.exists_root _ hdeg
  have hroot : (256 : K) * (l ^ 2 - l + 1) ^ 3 = j * (l * (l - 1)) ^ 2 := by
    have := hl.eq_zero
    simp only [legPoly, eval_sub, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one] at this
    exact sub_eq_zero.mp this
  set t := l * (l - 1) with ht
  have hu : l ^ 2 - l + 1 = 1 + t := by rw [ht]; ring
  rw [hu] at hroot
  have hnorm := congrArg norm hroot
  simp only [norm_mul, norm_pow, h256, one_mul] at hnorm

  have htn : ‖t‖ = 1 := by
    by_contra hne
    have e := norm_one_add hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [e, max_eq_left hlt.le, one_pow] at hnorm
      have : ‖j‖ * ‖t‖ ^ 2 < 1 := by
        calc ‖j‖ * ‖t‖ ^ 2 ≤ 1 * ‖t‖ ^ 2 := by gcongr
          _ < 1 := by rw [one_mul]; exact pow_lt_one₀ (norm_nonneg _) hlt (by norm_num)
      linarith
    · rw [e, max_eq_right hgt.le] at hnorm
      have hpos : 0 < ‖t‖ ^ 2 := by positivity
      have : ‖t‖ ^ 3 ≤ ‖t‖ ^ 2 := by
        rw [hnorm]; calc ‖j‖ * ‖t‖ ^ 2 ≤ 1 * ‖t‖ ^ 2 := by gcongr
          _ = ‖t‖ ^ 2 := one_mul _
      have : ‖t‖ ^ 2 * ‖t‖ ≤ ‖t‖ ^ 2 * 1 := by nlinarith
      have := le_of_mul_le_mul_left this hpos
      linarith
  have hprod : ‖l‖ * ‖l - 1‖ = 1 := by rw [← norm_mul, ← ht, htn]
  have hle1 : ‖l - 1‖ ≤ max ‖l‖ 1 := by
    have := IsUltrametricDist.norm_add_le_max l (-1 : K)
    simpa [← sub_eq_add_neg] using this
  have hle2 : ‖l‖ ≤ max ‖l - 1‖ 1 := by
    have := IsUltrametricDist.norm_add_le_max (l - 1) (1 : K)
    simpa using this
  have hl1 : ‖l‖ = 1 := by
    rcases lt_trichotomy ‖l‖ 1 with h | h | h
    · exfalso
      rw [max_eq_right h.le] at hle1
      have : ‖l‖ * ‖l - 1‖ < 1 := by
        calc ‖l‖ * ‖l - 1‖ ≤ ‖l‖ * 1 := by gcongr
          _ < 1 := by rw [mul_one]; exact h
      linarith
    · exact h
    · exfalso
      have hpos : 0 < ‖l‖ := by linarith
      have hlt : ‖l - 1‖ < 1 := by
        by_contra hc
        rw [not_lt] at hc
        nlinarith
      rw [max_eq_right hlt.le] at hle2
      linarith
  have hl2 : ‖l - 1‖ = 1 := by rw [hl1, one_mul] at hprod; exact hprod
  obtain ⟨hΔ, hc4⟩ := legendre_invariant K l
  refine ⟨l, hl1, hl2, ?_, ?_⟩
  · rw [hΔ, hc4]
    have : (l ^ 2 - l + 1) = 1 + t := hu
    rw [this]
    have e2 : (16 : K) * l ^ 2 * (l - 1) ^ 2 = 16 * t ^ 2 := by rw [ht]; ring
    rw [e2]
    linear_combination 16 * hroot
  · rw [hΔ, norm_mul, norm_mul, h16, norm_pow, norm_pow, hl1, hl2]
    norm_num

end Formalism.ELL
end

-- bundled from Formalism.EllipticTorsion.EllipticTorsionProofs.TorInt
section
universe u

noncomputable section

namespace Formalism.ELL.TorsionIntegralEllipticTorsion

open WeierstrassCurve Formalism.ELL

lemma y_int {K : Type u} [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K)
    (hW : IntegralModel W) {x y : K} (h : W.toAffine.Equation x y) (hx : ‖x‖ ≤ 1) :
    ‖y‖ ≤ 1 := by
  have hW' := hW
  unfold IntegralModel at hW'
  have h' := h
  rw [WeierstrassCurve.Affine.equation_iff] at h'
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW'
  have hadd : ∀ a b : K, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖a + b‖ ≤ 1 := fun a b ha hb =>
    (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  have hmul : ∀ a b : K, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖a * b‖ ≤ 1 := fun a b ha hb => by
    rw [norm_mul]
    first
    | exact mul_le_one₀ ha (norm_nonneg _) hb
    | nlinarith [norm_nonneg a, norm_nonneg b]
  have hx2 : ‖x ^ 2‖ ≤ 1 := by
    rw [norm_pow]
    first
    | exact pow_le_one₀ (norm_nonneg _) hx
    | nlinarith [norm_nonneg x]
  have hx3 : ‖x ^ 3‖ ≤ 1 := by
    rw [norm_pow]
    first
    | exact pow_le_one₀ (norm_nonneg _) hx
    | nlinarith [norm_nonneg x, hx2]
  have hR : ‖x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆‖ ≤ 1 :=
    hadd _ _ (hadd _ _ (hadd _ _ hx3 (hmul _ _ h2 hx2)) (hmul _ _ h4 hx)) h6
  by_contra hy
  push_neg at hy
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg _
  have hm : ‖W.a₁ * x * y + W.a₃ * y‖ ≤ ‖y‖ := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖W.a₁ * x‖ * ‖y‖ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right (hmul _ _ h1 hx) hy0
        _ = ‖y‖ := one_mul _
    · rw [norm_mul]
      calc ‖W.a₃‖ * ‖y‖ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right h3 hy0
        _ = ‖y‖ := one_mul _
  have hy2 : y ^ 2 = (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) - (W.a₁ * x * y + W.a₃ * y) := by
    first
    | linear_combination h'
    | (rw [← h']; ring)
  have hsub : ‖(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) - (W.a₁ * x * y + W.a₃ * y)‖ ≤ ‖y‖ := by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hR.trans hy.le) ?_)
    rw [norm_neg]
    exact hm
  have hn : ‖y‖ ^ 2 ≤ ‖y‖ := by
    rw [← norm_pow, hy2]
    exact hsub
  nlinarith

end Formalism.ELL.TorsionIntegralEllipticTorsion

namespace Formalism.ELL

open WeierstrassCurve

theorem torsionIntegral_of (h : Formalism.ELL.FormalGroupPointsTorsionFree.{u}) : Formalism.ELL.TorsionIntegral.{u} := by
  intro K _ _ W hW hΔ n hn x y hxy hnP
  have hx : ‖x‖ ≤ 1 := by
    by_contra hx
    push Not at hx
    exact Affine.Point.some_ne_zero hxy (h K W hW hΔ n hn _ hx hnP)
  exact ⟨hx, TorsionIntegralEllipticTorsion.y_int W hW hxy.1 hx⟩

end Formalism.ELL
end
end

-- bundled from Formalism.EllipticTorsion.EllipticTorsionProofs.VeluInt
section
open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

namespace VeluIntegrality

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

def ball : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    rwa [norm_neg]

theorem veluGx_mem (W : WeierstrassCurve K) (hW : IntegralModel W) {x y : K}
    (hx : x ∈ (ball : Subring K)) (hy : y ∈ (ball : Subring K)) :
    veluGx W x y ∈ (ball : Subring K) := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  unfold veluGx
  refine sub_mem (add_mem (add_mem (mul_mem (ofNat_mem _ 3) (pow_mem hx 2))
    (mul_mem (mul_mem (ofNat_mem _ 2) h2) hx)) h4) (mul_mem h1 hy)

theorem veluGy_mem (W : WeierstrassCurve K) (hW : IntegralModel W) {x y : K}
    (hx : x ∈ (ball : Subring K)) (hy : y ∈ (ball : Subring K)) :
    veluGy W x y ∈ (ball : Subring K) := by
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  unfold veluGy
  exact sub_mem (sub_mem (mul_mem (neg_mem (ofNat_mem _ 2)) hy) (mul_mem h1 hx)) h3

theorem veluV_mem (W : WeierstrassCurve K) (hW : IntegralModel W) {x y : K}
    (hx : x ∈ (ball : Subring K)) (hy : y ∈ (ball : Subring K)) :
    veluV W x y ∈ (ball : Subring K) := by
  have gx := veluGx_mem W hW hx hy
  have gy := veluGy_mem W hW hx hy
  unfold veluV
  split_ifs
  · exact gx
  · exact sub_mem (mul_mem (ofNat_mem _ 2) gx) (mul_mem hW.1 gy)

theorem veluU_mem (W : WeierstrassCurve K) (hW : IntegralModel W) {x y : K}
    (hx : x ∈ (ball : Subring K)) (hy : y ∈ (ball : Subring K)) :
    veluU W x y ∈ (ball : Subring K) := by
  unfold veluU
  exact pow_mem (veluGy_mem W hW hx hy) 2

end VeluIntegrality

open VeluIntegrality in
theorem velu_integral_model : VeluIntegralModel := by
  intro K _ _ W k S hW hS
  have hx : ∀ i, (S i).1 ∈ (ball : Subring K) := fun i => (hS i).1
  have hy : ∀ i, (S i).2 ∈ (ball : Subring K) := fun i => (hS i).2
  have hv : (∑ i, veluV W (S i).1 (S i).2) ∈ (ball : Subring K) :=
    sum_mem fun i _ => veluV_mem W hW (hx i) (hy i)
  have hw : (∑ i, (veluU W (S i).1 (S i).2 + (S i).1 * veluV W (S i).1 (S i).2))
      ∈ (ball : Subring K) :=
    sum_mem fun i _ => add_mem (veluU_mem W hW (hx i) (hy i))
      (mul_mem (hx i) (veluV_mem W hW (hx i) (hy i)))
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · show W.a₄ - 5 * (∑ i, veluV W (S i).1 (S i).2) ∈ (ball : Subring K)
    exact sub_mem h4 (mul_mem (ofNat_mem _ 5) hv)
  · show W.a₆ - (W.a₁ ^ 2 + 4 * W.a₂) * (∑ i, veluV W (S i).1 (S i).2)
      - 7 * (∑ i, (veluU W (S i).1 (S i).2 + (S i).1 * veluV W (S i).1 (S i).2)) ∈ (ball : Subring K)
    exact sub_mem (sub_mem h6 (mul_mem (add_mem (pow_mem h1 2) (mul_mem (ofNat_mem _ 4) h2)) hv))
      (mul_mem (ofNat_mem _ 7) hw)

end Formalism.ELL
end
end

