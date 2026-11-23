module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0013
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTPiB
public import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.Bundle0007
public import Mathlib

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTPiA
section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet ArithmeticFunction

def cAP (M b n : ℕ) : ℝ := if n ≡ b [MOD M] then Λ n else 0

theorem vonMangoldtAP_nonneg (M b n : ℕ) : 0 ≤ cAP M b n := by
  unfold cAP
  split_ifs
  · exact vonMangoldt_nonneg
  · exact le_refl _

theorem vonMangoldtAP_le (M b n : ℕ) : cAP M b n ≤ Λ n := by
  unfold cAP
  split_ifs
  · exact le_refl _
  · exact vonMangoldt_nonneg

theorem sum_cAP (M b : ℕ) (t : ℝ) : ∑ n ∈ Icc 0 ⌊t⌋₊, cAP M b n = psiAP M b t := by
  unfold cAP Formalism.ZeroFreeDirichlet.psiAP
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_subset
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_Icc] at hx ⊢
    exact ⟨⟨Nat.zero_le _, hx.1.2⟩, hx.2⟩
  · intro x hx hnx
    simp only [Finset.mem_filter, Finset.mem_Icc] at hx hnx
    have hx0 : x = 0 := by
      by_contra h
      exact hnx ⟨⟨Nat.pos_of_ne_zero h, hx.1.2⟩, hx.2⟩
    subst hx0
    simp

theorem abs_piAP_sub_le (M b : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    |(piAP X M b : ℝ) - ∑ n ∈ Icc 0 ⌊X⌋₊, (Real.log n)⁻¹ * cAP M b n| ≤ 4 * √X * Real.log X := by
  have hpi : (piAP X M b : ℝ) = ∑ n ∈ Icc 0 ⌊X⌋₊, (if n.Prime ∧ n % M = b % M then (1 : ℝ) else 0) := by
    unfold piAP
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_subset (Finset.Icc_subset_Icc (by norm_num) le_rfl)
    intro n hn hn'
    have : n = 0 := by
      rw [Finset.mem_Icc] at hn hn'
      omega
    subst this
    simp [Nat.not_prime_zero]
  have hl2 := Real.log_two_gt_d9
  have hterm : ∀ n : ℕ, 0 ≤ (Real.log n)⁻¹ * cAP M b n - (if n.Prime ∧ n % M = b % M then (1 : ℝ) else 0) ∧
      (Real.log n)⁻¹ * cAP M b n - (if n.Prime ∧ n % M = b % M then (1 : ℝ) else 0) ≤
        2 * (if ¬ n.Prime then Λ n else 0) := by
    intro n
    by_cases hp : n.Prime
    · have hlog : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
      by_cases hm : n % M = b % M
      · have hm' : n ≡ b [MOD M] := hm
        simp [cAP, hp, hm, hm', vonMangoldt_apply_prime hp, hlog]
      · have hm' : ¬ n ≡ b [MOD M] := hm
        simp [cAP, hp, hm, hm']
    · simp only [hp, false_and, if_false, sub_zero, not_false_eq_true, if_true]
      rcases Nat.lt_or_ge n 2 with h2 | h2
      · have h0 : Λ n = 0 := by
          interval_cases n <;> simp
        have h0' : cAP M b n = 0 := le_antisymm (h0 ▸ vonMangoldtAP_le M b n) (vonMangoldtAP_nonneg M b n)
        simp [h0, h0']
      · have hln : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast h2)
        have hpos : 0 < Real.log n := by linarith
        have hinv : (Real.log n)⁻¹ ≤ 2 := by
          rw [inv_le_comm₀ hpos (by norm_num)]; linarith
        constructor
        · exact mul_nonneg (inv_nonneg.2 hpos.le) (vonMangoldtAP_nonneg M b n)
        · exact mul_le_mul hinv (vonMangoldtAP_le M b n) (vonMangoldtAP_nonneg M b n) (by norm_num)
  have hsum : ∑ n ∈ Icc 0 ⌊X⌋₊, (if ¬ n.Prime then Λ n else 0) = Chebyshev.psi X - Chebyshev.theta X := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Finset.sum_filter]
    symm
    apply Finset.sum_subset
    · intro n hn
      rw [Finset.mem_Ioc] at hn
      exact Finset.mem_Icc.2 ⟨by omega, hn.2⟩
    · intro n hn hn'
      have : n = 0 := by
        rw [Finset.mem_Icc] at hn
        rw [Finset.mem_Ioc] at hn'
        omega
      subst this
      simp
  have hpt := Chebyshev.psi_sub_theta_le hX
  rw [hpi, abs_sub_comm, ← Finset.sum_sub_distrib, abs_of_nonneg (Finset.sum_nonneg fun n _ => (hterm n).1)]
  calc _ ≤ ∑ n ∈ Icc 0 ⌊X⌋₊, 2 * (if ¬ n.Prime then Λ n else 0) := Finset.sum_le_sum fun n _ => (hterm n).2
    _ = 2 * (Chebyshev.psi X - Chebyshev.theta X) := by rw [← Finset.mul_sum, hsum]
    _ ≤ _ := by linarith

theorem abs_psiAP_sub_le (M : ℕ) [NeZero M] (b : ℕ) (hb : b.Coprime M) (e : Option (DirichletCharacter ℂ M × ℝ))
    (θ β t : ℝ)
    (hmain : ∑ χ : DirichletCharacter ℂ M, χ ((b : ZMod M)⁻¹) * mainPsi e χ t =
      ((t - θ * t ^ β / β : ℝ) : ℂ)) :
    |psiAP M b t - Fm (1 / (M.totient : ℝ)) θ β t| ≤
      (∑ χ : DirichletCharacter ℂ M, ‖psiChi χ t - mainPsi e χ t‖) / (M.totient : ℝ) := by
  have hφ : (0 : ℝ) < M.totient := by exact_mod_cast Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne M))
  have hid := chebyshev_progression_orthogonality M b hb t
  have h1 : (((M.totient : ℝ) * psiAP M b t - (t - θ * t ^ β / β) : ℝ) : ℂ) =
      ∑ χ : DirichletCharacter ℂ M, χ ((b : ZMod M)⁻¹) * (psiChi χ t - mainPsi e χ t) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← hid, hmain]
    push_cast
    ring
  have h2 : |(M.totient : ℝ) * psiAP M b t - (t - θ * t ^ β / β)| ≤
      ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ t - mainPsi e χ t‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real, h1]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => ?_)
    rw [norm_mul]
    calc ‖χ ((b : ZMod M)⁻¹)‖ * ‖psiChi χ t - mainPsi e χ t‖ ≤ 1 * ‖psiChi χ t - mainPsi e χ t‖ := by
          gcongr
          exact χ.norm_le_one _
      _ = _ := one_mul _
  rw [le_div_iff₀ hφ]
  have h3 : (psiAP M b t - Fm (1 / (M.totient : ℝ)) θ β t) * (M.totient : ℝ) =
      (M.totient : ℝ) * psiAP M b t - (t - θ * t ^ β / β) := by
    unfold Fm
    field_simp
  calc |psiAP M b t - Fm (1 / (M.totient : ℝ)) θ β t| * (M.totient : ℝ)
      = |(psiAP M b t - Fm (1 / (M.totient : ℝ)) θ β t) * (M.totient : ℝ)| := by
        rw [abs_mul, abs_of_pos hφ]
    _ ≤ _ := by rw [h3]; exact h2

theorem mainPsi_sum_none (M : ℕ) [NeZero M] (b : ℕ) (hb : b.Coprime M) (t β : ℝ) :
    ∑ χ : DirichletCharacter ℂ M, χ ((b : ZMod M)⁻¹) * mainPsi none χ t = ((t - 0 * t ^ β / β : ℝ) : ℂ) := by
  have hu : IsUnit ((b : ZMod M)⁻¹) := by
    have h1 : IsUnit (b : ZMod M) := (ZMod.isUnit_iff_coprime b M).mpr hb
    obtain ⟨u, hu⟩ := h1
    rw [← hu, ZMod.inv_coe_unit]
    exact Units.isUnit _
  simp only [mainPsi]
  simp [Finset.sum_ite_eq', MulChar.one_apply hu]

theorem mainPsi_sum_some (M : ℕ) [NeZero M] (b : ℕ) (hb : b.Coprime M) (χ₁ : DirichletCharacter ℂ M)
    (β t : ℝ) (ht : 0 ≤ t) (hχ : χ₁ (b : ZMod M) = 1 ∨ χ₁ (b : ZMod M) = -1) :
    ∑ χ : DirichletCharacter ℂ M, χ ((b : ZMod M)⁻¹) * mainPsi (some (χ₁, β)) χ t =
      ((t - (χ₁ (b : ZMod M)).re * t ^ β / β : ℝ) : ℂ) := by
  have hbu : (b : ZMod M) * (b : ZMod M)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one b hb
  have hunit : IsUnit ((b : ZMod M)⁻¹) :=
    ⟨⟨(b : ZMod M)⁻¹, (b : ZMod M), by rw [mul_comm]; exact hbu, hbu⟩, rfl⟩
  have h1 : (1 : DirichletCharacter ℂ M) ((b : ZMod M)⁻¹) = 1 := MulChar.one_apply hunit
  have h2 : χ₁ ((b : ZMod M)⁻¹) = χ₁ (b : ZMod M) := by
    have h3 := congrArg χ₁ hbu
    rw [map_mul, map_one] at h3
    rcases hχ with h | h
    · rw [h, one_mul] at h3
      rw [h3, h]
    · rw [h] at h3 ⊢
      linear_combination -h3
  have hre : ((χ₁ (b : ZMod M)).re : ℂ) = χ₁ (b : ZMod M) := by
    rcases hχ with h | h <;> simp [h]
  simp only [mainPsi, mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, h1, h2]
  push_cast
  rw [hre, Complex.ofReal_cpow ht]
  ring

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTRangeA
section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem rangeA_card_char_le (M : ℕ) [NeZero M] :
    ((Finset.univ : Finset (DirichletCharacter ℂ M)).card : ℝ) ≤ M := by
  have h : (Finset.univ : Finset (DirichletCharacter ℂ M)).card = M.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ M]
  rw [h]
  exact_mod_cast Nat.totient_le M

theorem rangeA_far_term (M : ℕ) (hM : 8 ≤ M) (y cA β : ℝ) (hy : 2 ≤ y) (hcA : cA ≤ cZ)
    (hl : Real.log M ≤ cA * Real.sqrt (Real.log y)) (hβ : 1 / 2 ≤ β)
    (hr : ¬ InRegion cZ M (β : ℂ)) :
    ‖(y : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤ 2 * y * Real.exp (-(Real.sqrt (Real.log y) / 2)) := by
  have hy0 : 0 < y := by linarith
  have hL : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  set s := Real.sqrt (Real.log y) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s * s = Real.log y := Real.mul_self_sqrt hL
  have hMr : (8 : ℝ) ≤ M := by exact_mod_cast hM
  have hZ := cZ_pos
  unfold InRegion at hr
  simp only [Complex.ofReal_im, abs_zero, zero_add, Complex.ofReal_re, not_le] at hr
  set l := Real.log ((M : ℝ) * 2) with hl'
  have hl0 : 0 < l := Real.log_pos (by linarith)
  have hl2 : l ≤ 2 * Real.log M := by
    rw [hl', Real.log_mul (by linarith) (by norm_num)]
    have : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hl3 : l ≤ 2 * cZ * s := by nlinarith
  have h1 : cZ < (1 - β) * l := by
    have : cZ / l < 1 - β := by linarith
    rwa [div_lt_iff₀ hl0] at this
  have hb1 : 0 < 1 - β := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  have h2 : s / 2 ≤ (1 - β) * Real.log y := by
    have h3 : cZ * s ≤ (1 - β) * (2 * cZ * s) * s := by
      have : (1 - β) * l ≤ (1 - β) * (2 * cZ * s) := mul_le_mul_of_nonneg_left hl3 hb1.le
      nlinarith
    have h4 : cZ * (s / 2) ≤ cZ * ((1 - β) * (s * s)) := by nlinarith
    rw [← hss]
    exact le_of_mul_le_mul_left h4 hZ
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy0, Complex.ofReal_re, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < β)]
  have h5 : y ^ β = y * Real.exp (-((1 - β) * Real.log y)) := by
    rw [Real.rpow_def_of_pos hy0]
    nth_rewrite 2 [← Real.exp_log hy0]
    rw [← Real.exp_add]
    congr 1
    ring
  have h6 : Real.exp (-((1 - β) * Real.log y)) ≤ Real.exp (-(s / 2)) :=
    Real.exp_le_exp.mpr (by linarith)
  rw [div_le_iff₀ (by linarith), h5]
  have h7 : 0 < Real.exp (-(s / 2)) := Real.exp_pos _
  have : y * Real.exp (-((1 - β) * Real.log y)) ≤ y * Real.exp (-(s / 2)) :=
    mul_le_mul_of_nonneg_left h6 hy0.le
  have h8 : 0 ≤ y * Real.exp (-(s / 2)) := by positivity
  nlinarith

theorem rangeA_excZeros_empty (M : ℕ) [NeZero M] (hM : 2 ≤ M) (χ : DirichletCharacter ℂ M)
    (h : ∀ β : ℝ, eOf M = some (χ, β) → ¬ InRegion cZ M (β : ℂ)) : ExcZeros cZ χ ∅ := by
  refine ⟨by simp, by simp, ?_⟩
  intro s hs hz
  obtain ⟨β₁, h1, h2, -⟩ := zero_in_region M hM χ s hs hz
  exact absurd (h2 ▸ hs) (h β₁ h1)

theorem rangeA_excZeros_single (M : ℕ) [NeZero M] (hM : 2 ≤ M) (χ : DirichletCharacter ℂ M) (β : ℝ)
    (h : eOf M = some (χ, β)) (hr : InRegion cZ M (β : ℂ)) : ExcZeros cZ χ {β} := by
  have he := eOf_exc M _ h
  have hz : IsLZero χ (β : ℂ) := ⟨Or.inl he.2.1, he.2.2.1⟩
  obtain ⟨-, -, -, hd⟩ := zero_in_region M hM χ _ hr hz
  refine ⟨by simp, ?_, ?_⟩
  · intro b hb
    rw [Finset.mem_singleton] at hb
    subst hb
    exact ⟨he.2.1, hr, he.2.2.1, hd⟩
  · intro s hs hz'
    obtain ⟨β₁, h1, h2, -⟩ := zero_in_region M hM χ s hs hz'
    rw [h] at h1
    have : β = β₁ := by simpa using h1
    exact ⟨β, by simp, by rw [h2, this]⟩

theorem rangeA_one_char (c C cA : ℝ)
    (H : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (B : Finset ℝ) (x : ℝ), ExcZeros cZ χ B → 2 ≤ x →
      (q : ℝ) ≤ Real.exp (c * Real.sqrt (Real.log x)) →
      ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0) + ∑ β ∈ B, (x : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤
        C * x * Real.exp (-c * Real.sqrt (Real.log x)))
    (hcA : cA ≤ cZ) (hcA' : cA ≤ c) (M : ℕ) [NeZero M] (hM : 8 ≤ M) (y : ℝ) (hy : 2 ≤ y)
    (hl : Real.log M ≤ cA * Real.sqrt (Real.log y)) (χ : DirichletCharacter ℂ M) :
    ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      C * y * Real.exp (-c * Real.sqrt (Real.log y)) + 2 * y * Real.exp (-(Real.sqrt (Real.log y) / 2)) := by
  have hM2 : 2 ≤ M := by omega
  have hMr : (8 : ℝ) ≤ M := by exact_mod_cast hM
  have hs0 : 0 ≤ Real.sqrt (Real.log y) := Real.sqrt_nonneg _
  have hq : (M : ℝ) ≤ Real.exp (c * Real.sqrt (Real.log y)) := by
    rw [← Real.exp_log (by linarith : (0 : ℝ) < M)]
    exact Real.exp_le_exp.mpr (hl.trans (mul_le_mul_of_nonneg_right hcA' hs0))
  have hE : 0 ≤ 2 * y * Real.exp (-(Real.sqrt (Real.log y) / 2)) := by positivity
  have H' : ∀ B : Finset ℝ, ExcZeros cZ χ B →
      ‖psiChi χ y - mainPsi none χ y + ∑ β ∈ B, (y : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤
        C * y * Real.exp (-c * Real.sqrt (Real.log y)) := by
    intro B hB
    have h0 := H M χ B y hB hy hq
    simp only [mainPsi, sub_zero]
    convert h0
  have hsome : ∀ (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ), mainPsi (some (χ₁, β₁)) χ y =
      mainPsi none χ y - (if χ = χ₁ then (y : ℂ) ^ (β₁ : ℂ) / (β₁ : ℂ) else 0) := by
    intro χ₁ β₁
    simp only [mainPsi, sub_zero]
    congr
  rcases he : eOf M with _ | ⟨χ₁, β₁⟩
  · have h0 := H' ∅ (rangeA_excZeros_empty M hM2 χ (by intro β hβ; rw [he] at hβ; simp at hβ))
    simp only [Finset.sum_empty, add_zero] at h0
    linarith
  · rw [hsome]
    by_cases hχ : χ = χ₁
    · subst hχ
      rw [if_pos rfl, ← sub_add]
      by_cases hr : InRegion cZ M (β₁ : ℂ)
      · have h0 := H' {β₁} (rangeA_excZeros_single M hM2 χ β₁ he hr)
        simp only [Finset.sum_singleton] at h0
        linarith
      · have h0 := H' ∅ (rangeA_excZeros_empty M hM2 χ (by
          intro β hβ; rw [he] at hβ
          have : β₁ = β := by simpa using hβ
          rw [← this]; exact hr))
        simp only [Finset.sum_empty, add_zero] at h0
        have hex := eOf_exc M _ he
        have hβ : 1 / 2 ≤ β₁ := by
          have h1 := hex.2.2.2.1
          have hlog : 1 ≤ Real.log M := by
            rw [Real.le_log_iff_exp_le (by linarith)]
            have := Real.exp_one_lt_d9
            linarith
          have : 1 / (8 * Real.log M) ≤ 1 / 8 := by
            apply one_div_le_one_div_of_le (by norm_num) (by linarith)
          simp only at h1
          linarith
        have h1 := rangeA_far_term M hM y cA β₁ hy hcA hl hβ hr
        exact (norm_add_le _ _).trans (add_le_add h0 h1)
    · have h0 := H' ∅ (rangeA_excZeros_empty M hM2 χ (by
          intro β hβ; rw [he] at hβ
          have : χ₁ = χ := by
            have := Option.some.inj hβ
            exact (Prod.mk.inj this).1
          exact absurd this.symm hχ))
      simp only [Finset.sum_empty, add_zero] at h0
      rw [if_neg hχ, sub_zero]
      linarith

theorem psi_relative_near_range : PsiRelA := by
  obtain ⟨c, C, hc, H⟩ := psiChiBound cZ cZ_pos cZ_le
  obtain ⟨c₁, hc₁, H₁⟩ := etaOf_lower 1 one_pos
  have hZ := cZ_pos
  have hZ' := cZ_le
  refine ⟨min (c / 4) cZ, min (c / 2) (2 / 5), (|C| + 2) / c₁, lt_min (by linarith) hZ,
    lt_min (by linarith) (by norm_num), ?_⟩
  intro M _ h8 y hy hl
  have hM : 8 ≤ M := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) h8
  have hMr : (8 : ℝ) ≤ M := by exact_mod_cast hM
  have hy0 : 0 < y := by linarith
  set cA := min (c / 4) cZ with hcA
  set c' := min (c / 2) (2 / 5 : ℝ) with hc'
  set s := Real.sqrt (Real.log y) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hA1 : cA ≤ c / 4 := min_le_left _ _
  have hA2 : cA ≤ cZ := min_le_right _ _
  have hc1 : c' ≤ c / 2 := min_le_left _ _
  have hc2 : c' ≤ 2 / 5 := min_le_right _ _
  have hsum : ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖ ≤
      (M : ℝ) * (|C| * y * Real.exp (-c * s) + 2 * y * Real.exp (-(s / 2))) := by
    have hb : 0 ≤ |C| * y * Real.exp (-c * s) + 2 * y * Real.exp (-(s / 2)) := by positivity
    calc ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi (eOf M) χ y‖
        ≤ ∑ _χ : DirichletCharacter ℂ M, (|C| * y * Real.exp (-c * s) + 2 * y * Real.exp (-(s / 2))) := by
          apply Finset.sum_le_sum
          intro χ _
          have h0 := rangeA_one_char c C cA H hA2 (by linarith) M hM y hy hl χ
          have h1 : C * y * Real.exp (-c * s) ≤ |C| * y * Real.exp (-c * s) := by
            have : 0 ≤ y * Real.exp (-c * s) := by positivity
            have h2 := mul_le_mul_of_nonneg_right (le_abs_self C) this
            linarith
          linarith
      _ = ((Finset.univ : Finset (DirichletCharacter ℂ M)).card : ℝ) *
            (|C| * y * Real.exp (-c * s) + 2 * y * Real.exp (-(s / 2))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (rangeA_card_char_le M) hb
  have heta : c₁ ≤ etaOf M * M := by
    have h0 := H₁ M (by omega)
    rw [Real.rpow_neg_one] at h0
    have h1 := mul_le_mul_of_nonneg_right h0 (by linarith : (0 : ℝ) ≤ M)
    rwa [mul_assoc, inv_mul_cancel₀ (by linarith), mul_one] at h1
  have hMe : (M : ℝ) ≤ Real.exp (cA * s) := by
    rw [← Real.exp_log (by linarith : (0 : ℝ) < M)]
    exact Real.exp_le_exp.mpr hl
  have hMM : (M : ℝ) * M ≤ Real.exp (2 * cA * s) := by
    have : Real.exp (2 * cA * s) = Real.exp (cA * s) * Real.exp (cA * s) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]
    exact mul_le_mul hMe hMe (by linarith) (Real.exp_pos _).le
  have e1 : (M : ℝ) * M * Real.exp (-c * s) ≤ Real.exp (-(c' * s)) := by
    calc (M : ℝ) * M * Real.exp (-c * s) ≤ Real.exp (2 * cA * s) * Real.exp (-c * s) :=
          mul_le_mul_of_nonneg_right hMM (Real.exp_pos _).le
      _ = Real.exp (2 * cA * s + -c * s) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have e2 : (M : ℝ) * M * Real.exp (-(s / 2)) ≤ Real.exp (-(c' * s)) := by
    calc (M : ℝ) * M * Real.exp (-(s / 2)) ≤ Real.exp (2 * cA * s) * Real.exp (-(s / 2)) :=
          mul_le_mul_of_nonneg_right hMM (Real.exp_pos _).le
      _ = Real.exp (2 * cA * s + -(s / 2)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  refine hsum.trans ?_
  set X := Real.exp (-(c' * s)) with hX
  have hX0 : 0 < X := Real.exp_pos _
  have hM0 : (0 : ℝ) < M := by linarith

  have key : (M : ℝ) * ((M : ℝ) * (|C| * y * Real.exp (-c * s) + 2 * y * Real.exp (-(s / 2)))) ≤
      (|C| + 2) * y * X := by
    have a1 : |C| * y * ((M : ℝ) * M * Real.exp (-c * s)) ≤ |C| * y * X :=
      mul_le_mul_of_nonneg_left e1 (by positivity)
    have a2 : 2 * y * ((M : ℝ) * M * Real.exp (-(s / 2))) ≤ 2 * y * X :=
      mul_le_mul_of_nonneg_left e2 (by positivity)
    nlinarith
  have key2 : (|C| + 2) * y * X ≤ (M : ℝ) * ((|C| + 2) / c₁ * y * etaOf M * X) := by
    have : (M : ℝ) * ((|C| + 2) / c₁ * y * etaOf M * X) = (|C| + 2) * y * X * ((etaOf M * M) / c₁) := by
      field_simp
    rw [this]
    have h1 : 1 ≤ (etaOf M * M) / c₁ := by rwa [le_div_iff₀ hc₁, one_mul]
    have h2 : 0 ≤ (|C| + 2) * y * X := by positivity
    nlinarith
  exact le_of_mul_le_mul_left (key.trans key2) hM0

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

