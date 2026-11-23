module

public import Mathlib
public import Formalism.MirabolicMackeyTheory.Bundle0001
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic

@[expose] public section

-- bundled from Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.IdxPsiGood
section
open Module NumberField IsDedekindDomain

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

theorem mem_sc {K : Type} [Field K] {Z : Type} [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] (a : K) (A : Submodule (𝓞 K) Z) (x : Z) :
    x ∈ sc a A ↔ ∃ y ∈ A, a • y = x := by
  unfold sc
  rw [Submodule.mem_map]
  rfl

theorem idxPsiGood_of (hMono : IdxMono) (hSc : IdxScaleIn) (hCut : IdxCutLe) (hInt : LatInter) :
    IdxPsiGood := by
  unfold IdxPsiGood
  intro K _ _ _ Z _ _ _ _ _ w Zψ V₀ M Th ThK Th0 hM hTh hThK hThM hTh0fg hTh0Z σ hσ hThσ u hu
    hucut a E r ha hE hr δ hδ hδi
  have hcc : ∀ (W W' : Submodule K Z) (A : Submodule (𝓞 K) Z), W' ≤ W →
      cut W' (cut W A) = cut W' A := by
    intro W W' A hWW
    ext x
    simp only [cut, Submodule.mem_inf, Submodule.restrictScalars_mem]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨⟨h1, hWW h3⟩, h3⟩
  set L : Submodule K Z := Zψ ⊓ V₀ with hL
  have hLZ : L ≤ Zψ := inf_le_left
  set N : Submodule (𝓞 K) Z := M ⊓ sc a⁻¹ Th with hN
  have hNl : IsLatIn ⊤ N := hInt K Z M Th hM hTh a⁻¹ (inv_ne_zero ha)
  have hNM : N ≤ M := inf_le_left
  have hX : IsLatIn L (cut L M) := (hCut K Z w ⊤ L M M hM hM le_rfl le_top).1
  have hB0 : IsLatIn L (cut L N) := (hCut K Z w ⊤ L N N hNl hNl le_rfl le_top).1
  have hMψ : IsLatIn Zψ (cut Zψ M) := (hCut K Z w ⊤ Zψ M M hM hM le_rfl le_top).1
  have hNψ : IsLatIn Zψ (cut Zψ N) := (hCut K Z w ⊤ Zψ N N hNl hNl le_rfl le_top).1
  have hThKψ : IsLatIn Zψ (cut Zψ ThK) := (hCut K Z w ⊤ Zψ ThK ThK hThK hThK le_rfl le_top).1
  have hu' : (u : K) ≠ 0 := by exact_mod_cast hu
  have hc : a * σ⁻¹ ≠ 0 := mul_ne_zero ha (inv_ne_zero hσ)

  have hTh0 : IsLatIn Zψ Th0 := by
    show Th0.FG ∧ Submodule.span K (Th0 : Set Z) = Zψ
    refine ⟨hTh0fg, le_antisymm ?_ ?_⟩
    · exact Submodule.span_le.mpr (fun x hx => hTh0Z hx)
    · have h1 := (hSc K Z w Zψ (cut Zψ ThK) (cut Zψ ThK) hThKψ hThKψ (u : K) hu').1
      have h2 : Submodule.span K ((sc (u : K) (cut Zψ ThK) : Submodule (𝓞 K) Z) : Set Z) = Zψ :=
        h1.2
      rw [← h2]
      exact Submodule.span_mono (SetLike.coe_subset_coe.mpr hucut)
  have hcutTh0 : cut V₀ Th0 = cut L Th0 := by
    ext x
    simp only [cut, Submodule.mem_inf, Submodule.restrictScalars_mem, hL]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, hTh0Z h1, h2⟩
    · rintro ⟨h1, _, h2⟩
      exact ⟨h1, h2⟩
  have hT : IsLatIn L (cut V₀ Th0) := by
    rw [hcutTh0]
    exact (hCut K Z w Zψ L Th0 Th0 hTh0 hTh0 le_rfl hLZ).1
  refine ⟨hT, ?_⟩
  have hB1 := hSc K Z w L (cut L M) (cut L N) hX hB0 (a * σ⁻¹) hc
  have hB2 := hSc K Z w L (cut L M) (sc (a * σ⁻¹) (cut L N)) hX hB1.1 (u : K) hu'

  have hle2 : sc (u : K) (sc (a * σ⁻¹) (cut L N)) ≤ cut V₀ Th0 := by
    intro x hx
    rw [mem_sc] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [mem_sc] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    simp only [cut, Submodule.mem_inf, Submodule.restrictScalars_mem, hN, hL] at hz ⊢
    obtain ⟨⟨_, hz2⟩, hzψ, hzV⟩ := hz
    rw [mem_sc] at hz2
    obtain ⟨t, ht, rfl⟩ := hz2
    obtain ⟨k, hk, rfl⟩ := (mem_sc σ ThK t).1 (hThσ ht)
    have hkey : (a * σ⁻¹) • a⁻¹ • σ • k = k := by
      rw [smul_smul, smul_smul]
      have h1 : a * σ⁻¹ * a⁻¹ * σ = 1 := by field_simp
      rw [h1, one_smul]
    have hkψ : k ∈ Zψ := by
      have h1 := Zψ.smul_mem (a * σ⁻¹) hzψ
      rwa [hkey] at h1
    have hkV : k ∈ V₀ := by
      have h1 := V₀.smul_mem (a * σ⁻¹) hzV
      rwa [hkey] at h1
    rw [hkey]
    have hkc : k ∈ cut Zψ ThK := by
      simp only [cut, Submodule.mem_inf, Submodule.restrictScalars_mem]
      exact ⟨hk, hkψ⟩
    exact ⟨hucut ((mem_sc _ _ _).2 ⟨k, hkc, rfl⟩), V₀.smul_mem _ hkV⟩
  have hmono := hMono K Z w L (cut L M) (sc (u : K) (sc (a * σ⁻¹) (cut L N))) (cut V₀ Th0)
    hX hB2.1 hT hle2
  have hNMψ : cut Zψ N ≤ cut Zψ M := by
    unfold cut
    exact inf_le_inf_right _ hNM
  have hcut2 := (hCut K Z w Zψ L (cut Zψ M) (cut Zψ N) hMψ hNψ hNMψ hLZ).2.2
  rw [hcc Zψ L M hLZ, hcc Zψ L N hLZ] at hcut2
  have hv : vw w (a * σ⁻¹) = (E : ℤ) - vw w σ := by
    rw [ValuationRepresentative.vw_mul w a σ⁻¹ ha (inv_ne_zero hσ),
      ValuationRepresentative.vw_inv w σ, hE, sub_eq_add_neg]
  rw [hB2.2, hB1.2, hv] at hmono
  have h1 : (δ : ℝ) * (lix w (cut Zψ M) (cut Zψ N) : ℝ) ≤
      (lix w M N : ℝ) + (finrank K Z : ℝ) * (vw w (u : K) : ℝ) := by
    exact_mod_cast hδi
  have hJ : (lix w (cut Zψ M) (cut Zψ N) : ℝ) ≤
      (r + (finrank K Z : ℝ) * (vw w (u : K) : ℝ)) / (δ : ℝ) := by
    rw [le_div_iff₀ (by exact_mod_cast hδ)]
    linarith
  have hm : (lix w (cut L M) (cut V₀ Th0) : ℝ) ≤ (lix w (cut L M) (cut L N) : ℝ) +
      (finrank K L : ℝ) * ((E : ℝ) - (vw w σ : ℝ)) + (finrank K L : ℝ) * (vw w (u : K) : ℝ) := by
    exact_mod_cast hmono
  have hc2 : (lix w (cut L M) (cut L N) : ℝ) ≤ lix w (cut Zψ M) (cut Zψ N) := by
    exact_mod_cast hcut2
  nlinarith

end Formalism.EigenvalueLevelCeiling
end

-- bundled from Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.UnipotentNumeric
section
namespace Formalism.EigenvalueLevelCeiling

theorem depth_cases : DepthCases := by
  unfold DepthCases
  intro e ec F
  refine ⟨fun a h1 h2 => by linarith, fun h1 h2 h3 => by linarith,
    fun s T β h1 h2 h3 h4 => by linarith, fun s T h1 h2 h3 => by linarith,
    fun T nn nnc g2 h1 h2 h3 => by linarith⟩

theorem budget_numeric : BudgetNum := by
  unfold BudgetNum
  intro dK δq D B hδ hD hB hq
  rw [div_le_iff₀ (mul_pos hδ hD)]
  have h1 : dK ≤ 3 * D * δq := (div_le_iff₀ hδ).mp hq
  have h2 : dK * B ≤ 3 * D * δq * B := mul_le_mul_of_nonneg_right h1 hB
  linarith

theorem share_numeric : ShareNum := by
  unfold ShareNum
  intro dK d0 d U δq ep y del hU hδ hdK hd0 hep hey hy hdel hdel' h1 h2 h3
  rw [div_le_iff₀ hδ]
  have k1 : 7 / 8 * dK ≤ U * d0 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 / 8 - ep) hdK]
  have k2 : 7 / 8 * U ≤ δq := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 / 8 - y) hU.le]
  have k3 : 3 / 4 * d0 ≤ d := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 / 4 - del) hd0]
  have hd : 0 ≤ d := by linarith
  have k4 : d * (7 / 8 * U) ≤ d * δq := mul_le_mul_of_nonneg_left k2 hd
  have k5 : 3 / 4 * d0 * U ≤ d * U := mul_le_mul_of_nonneg_right k3 hU.le
  nlinarith

end Formalism.EigenvalueLevelCeiling
end

