module

public import Formalism.MirabolicMackeyTheory.Bundle0002
public import Formalism.MirabolicMackeyTheory.MirabolicIsMackey
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.LocalConditionsGlobalForm
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Mathlib
public import Formalism.MirabolicMackeyTheory.Bundle0001
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0005
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle0002
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0002

@[expose] public section

-- bundled from Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.GlobalBoundRefinements
section
open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

theorem enlarge_initial_lattice : EnlargeInitialLattice := by
  intro K _ _ _ Z _ _ _ _ _ w M Th1 Th hM h1 hT h1T hTM E r h W
  have a := (idxCutLe K Z w ⊤ W M Th hM hT hTM le_top).1
  have b := (idxCutLe K Z w ⊤ W Th Th1 hT h1 h1T le_top).1
  have c := (idxCutLe K Z w ⊤ W Th1 Th1 h1 h1 le_rfl le_top).1
  have d : cut W Th1 ≤ cut W Th := inf_le_inf_right _ h1T
  have e := idxMono K Z w W (cut W M) (cut W Th1) (cut W Th) a c b d
  have e' : (lix w (cut W M) (cut W Th) : ℝ) ≤ (lix w (cut W M) (cut W Th1) : ℝ) := by exact_mod_cast e
  exact le_trans e' (h W)

theorem twist_chain : TwChain := by
  intro K _ _ _ Z _ _ _ _ _ w W e A Th0 ThJ X₃ hA h0 hJ hle ε h
  have a := idxMono K Z w W A _ _ hA h0 hJ (Submodule.map_mono hle)
  have a' : (lix w A (ThJ.map (e.restrictScalars (𝓞 K))) : ℝ) ≤
      (lix w A (Th0.map (e.restrictScalars (𝓞 K))) : ℝ) := by exact_mod_cast a
  linarith

theorem local_conditions_family : OnLocalJ := by
  intro K _ _ _ Z _ _ _ _ _ w P _ _ ρ U ψ hMk V₀ e he hr M Th ThK Th0 ThJ X₃ X₄ hM hTh hThK hle hFG hEig hMs hTs
    σ hσ hsc hdata a E r ha hE hT0 h0 hJ h0J h3 h4 h34 ε hTW d φ hinj hrng Mj Tj hMj hTj
  exact onLocal K Z w P ρ U ψ hMk V₀ e he hr M Th ThK Th0 X₃ X₄ hM hTh hThK hle hFG hEig hMs hTs σ hσ hsc hdata
    a E r ha hE hT0 h0 h3 h4 h34 ε
    (twist_chain K Z w _ e _ Th0 ThJ X₃ (idxCutLe K Z w ⊤ _ M Th hM hTh hle le_top).1 h0 hJ h0J ε hTW)
    d φ hinj hrng Mj Tj hMj hTj

theorem theta_identity : ThetaIdentity := by
  intro R X Y _ _ _ _ _ θ eX pr e hc hk Mt
  have key : ∀ m, θ (pr (eX m)) = e (θ m) := by
    intro m
    have h1 := hk (eX m) (LinearMap.mem_range_self eX m)
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h1
    rw [← h1, ← LinearMap.comp_apply θ eX, hc, LinearMap.comp_apply]
  ext y
  simp only [Submodule.mem_map]
  constructor
  · rintro ⟨z, ⟨x, ⟨m, hm, rfl⟩, rfl⟩, rfl⟩
    exact ⟨θ m, ⟨m, hm, rfl⟩, (key m).symm⟩
  · rintro ⟨z, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨pr (eX m), ⟨eX m, ⟨m, hm, rfl⟩, rfl⟩, key m⟩

theorem theta_identity_orthogonal : ThetaIdentityOrth := by
  intro R X Y A _ _ _ _ _ _ θ eX p e h hc hsym hp hker hrange
  have hkerθ : ∀ k ∈ LinearMap.ker θ, eX k ∈ LinearMap.ker θ := by
    intro k hk
    rw [LinearMap.mem_ker] at hk ⊢
    rw [← LinearMap.comp_apply θ eX, hc, LinearMap.comp_apply, hk, map_zero]
  have hpp : ∀ x, p (p x) = p x := fun x => by rw [← LinearMap.comp_apply p p, hp]
  have hrp : ∀ x, p x ∈ LinearMap.range p := fun x => LinearMap.mem_range_self p x
  have hsub : ∀ x, x - p x ∈ LinearMap.ker θ := fun x => by
    rw [← hker, LinearMap.mem_ker, map_sub, hpp, sub_self]
  have hEr : ∀ x ∈ LinearMap.range p, eX x ∈ LinearMap.range p := by
    intro x hx
    rw [hrange] at hx ⊢
    intro k hk
    rw [← hsym]
    exact hx _ (hkerθ k hk)
  have hfix : ∀ y ∈ LinearMap.range p, p y = y := by
    rintro y ⟨z, rfl⟩
    exact hpp z
  have hcomm : ∀ x, p (eX x) = eX (p x) := by
    intro x
    have h1 : eX x = eX (p x) + eX (x - p x) := by
      rw [← map_add (f := _)]
      congr 1
      abel
    have h2 : p (eX (x - p x)) = 0 := by
      rw [← LinearMap.mem_ker, hker]
      exact hkerθ _ (hsub x)
    rw [h1, map_add (f := _), h2, add_zero, hfix _ (hEr _ (hrp x))]
  refine ⟨LinearMap.ext hcomm, fun x hx => ⟨?_, hsub x, fun k hk => (hrange (p x)).1 (hrp x) k hk⟩, fun Mt => ?_⟩
  · obtain ⟨y, rfl⟩ := hx
    rw [hcomm]
    exact LinearMap.mem_range_self eX (p y)
  · have key : ∀ m, θ (eX (p m)) = e (θ m) := by
      intro m
      have hm : θ (p m) = θ m := by
        have := hsub m
        rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
        exact this.symm
      rw [← LinearMap.comp_apply θ eX, hc, LinearMap.comp_apply, hm]
    ext y
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨z, ⟨x, ⟨m, hm, rfl⟩, rfl⟩, rfl⟩
      exact ⟨θ m, ⟨m, hm, rfl⟩, (key m).symm⟩
    · rintro ⟨z, ⟨m, hm, rfl⟩, rfl⟩
      exact ⟨eX (p m), ⟨p m, ⟨m, hm, rfl⟩, rfl⟩, key m⟩

private theorem vw_mul_lemma (K : Type) [Field K] [NumberField K] [StarRing K] (w : HeightOneSpectrum (𝓞 K))
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) : vw w (a * b) = vw w a + vw w b := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton]
  apply FractionalIdeal.count_mul <;> rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]

theorem constant_b_bound : ConstB := by
  intro RR PP DF d' n1 nW g' qmin hRR hDF hd hn1 hn hq hqg hPP
  have hg : 0 < g' := lt_of_lt_of_le hq hqg
  have hnW : 0 ≤ nW := le_trans hn1 hn
  have hd3 : 0 ≤ d' ^ 3 := pow_nonneg hd 3
  have hd4 : 0 ≤ d' ^ 4 := pow_nonneg hd 4
  have hPP0 : 0 ≤ PP := by nlinarith [mul_nonneg hd4 hnW]
  have hDF2 : 1 ≤ DF ^ 2 := by nlinarith
  have k1 : 0 ≤ RR * DF ^ 2 * (PP - (d' ^ 4 * nW + 2 * d' ^ 3)) :=
    mul_nonneg (mul_nonneg hRR (sq_nonneg DF)) (by linarith)
  have k2 : 0 ≤ RR * d' ^ 4 * (nW * DF ^ 2 - n1 / 4) :=
    mul_nonneg (mul_nonneg hRR hd4) (by nlinarith)
  have hC : n1 * d' * (RR * d' ^ 3) / 4 + 2 * (RR * d' ^ 3) * DF ^ 2 ≤ RR * PP * DF ^ 2 := by
    nlinarith [k1, k2]
  have hN : 0 ≤ RR * PP * DF ^ 2 := mul_nonneg (mul_nonneg hRR hPP0) (sq_nonneg DF)
  have hinv : g'⁻¹ ≤ qmin⁻¹ := by
    first
      | exact inv_anti₀ hq hqg
      | exact inv_le_inv_of_le hq hqg
      | exact (inv_le_inv hg hq).2 hqg
  calc n1 * d' * (RR * d' ^ 3) / (4 * g') + 2 * (RR * d' ^ 3) * DF ^ 2 / g'
      = (n1 * d' * (RR * d' ^ 3) / 4 + 2 * (RR * d' ^ 3) * DF ^ 2) * g'⁻¹ := by
        first
          | ring
          | (field_simp; ring)
    _ ≤ RR * PP * DF ^ 2 * g'⁻¹ := mul_le_mul_of_nonneg_right hC (inv_nonneg.mpr hg.le)
    _ ≤ RR * PP * DF ^ 2 * qmin⁻¹ := mul_le_mul_of_nonneg_left hinv hN
    _ = RR * PP * DF ^ 2 / qmin := by rw [div_eq_mul_inv]

theorem local_conditions_weighted : LocalConditionsWeighted := by
  intro K _ _ _ Z _ _ _ _ _ w P _ _ ρ U ψ hMk V₀ e he hr M Th1 Th ThK Th0 ThJ X₃ hM hTh1 hTh hThK h1le hle hFG hEig
    hMs hTs σ hσ hsc hdata a E r ha hE hT0 h0 hJ h0J h3 X _ _ _ _ θ' eX pr Mt hc hk h4 h34 ε hTW d φ hinj hrng
    Mj Tj hMj hTj
  have hT0' := enlarge_initial_lattice K Z w M Th1 Th hM hTh1 hTh h1le hle (E : ℝ) r hT0
  have hc' : (θ'.restrictScalars (𝓞 K)) ∘ₗ (eX.restrictScalars (𝓞 K)) =
      (e.restrictScalars (𝓞 K)) ∘ₗ (θ'.restrictScalars (𝓞 K)) :=
    LinearMap.ext fun x => LinearMap.congr_fun hc x
  have hk' : ∀ x ∈ LinearMap.range (eX.restrictScalars (𝓞 K)),
      x - (pr.restrictScalars (𝓞 K)) x ∈ LinearMap.ker (θ'.restrictScalars (𝓞 K)) := by
    intro x hx
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hx
    exact LinearMap.mem_ker.2 (LinearMap.mem_ker.1 (hk _ (LinearMap.mem_range_self eX y)))
  have hid := theta_identity (𝓞 K) X Z (θ'.restrictScalars (𝓞 K)) (eX.restrictScalars (𝓞 K))
    (pr.restrictScalars (𝓞 K)) (e.restrictScalars (𝓞 K)) hc' hk' Mt
  exact local_conditions_family K Z w P ρ U ψ hMk V₀ e he hr M Th ThK Th0 ThJ X₃
    ((Mt.map (θ'.restrictScalars (𝓞 K))).map (e.restrictScalars (𝓞 K))) hM hTh hThK hle hFG hEig hMs hTs
    σ hσ hsc hdata a E r ha hE hT0' h0 hJ h0J h3 h4 h34 ε hTW d φ hinj hrng Mj Tj hMj (hTj.trans hid)

theorem gapConditions_of_largeGaps : GapNum := by
  intro T D nW r t h0 c hD hr ht hnW hT
  have h2 : 2 * (D + 2) ≤ (D + 2) * nW := by nlinarith
  have hb : 0 ≤ T + D + 2 + r := by linarith
  have hle : T + D + 2 + r ≤ 3 / 2 * T := by linarith
  have hsq := mul_self_le_mul_self hb hle
  have key : (T + D + 2) * (T + D + 2 + 2 * r) ≤ 9 / 4 * T ^ 2 := by nlinarith [sq_nonneg r]
  have e : (3.75 : ℝ) = 15 / 4 := by norm_num
  rw [e]
  exact ⟨by nlinarith [sq_nonneg T], fun hh hc => by nlinarith [sq_nonneg T]⟩


section Instance

variable (K : Type) [Field K] [NumberField K] [StarRing K]

def unitLat : Submodule (𝓞 K) K := Submodule.span (𝓞 K) {(1 : K)}

end Instance

end Formalism.EigenvalueLevelCeiling
end
end

-- bundled from Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.LocalConditionsComposeGeneral
section
open Module NumberField IsDedekindDomain

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

theorem chebyshev_theta_log_four : ThetaLog4 := by
  classical
  intro Y hY Q hQ
  refine le_trans ?_ (Chebyshev.theta_le_log4_mul_x hY)
  unfold Chebyshev.theta
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hp
    obtain ⟨h1, h2⟩ := hQ p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨h1.pos, Nat.le_floor h2⟩, h1⟩
  · intro p _ _
    exact Real.log_natCast_nonneg p

end Formalism.EigenvalueLevelCeiling
end

