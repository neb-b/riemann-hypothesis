module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.AutomorphicTheory.ThetaDilations.Nuabs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0001

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FourierTransformLatticeIndicator
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core

theorem fou_indicator_coset :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V),
      NADual V χ μ → ∀ L : AddSubgroup V, IsCompact (L : Set V) → IsOpen (L : Set V) → ∀ a y : V,
        fou χ μ (Set.indicator {x | x - a ∈ L} (fun _ => (1 : ℂ))) y =
          ((μ L).toReal : ℂ) * χ a y * Set.indicator (perp χ L) (fun _ => (1 : ℂ)) y := by
  intro V _ _ _ χ μ h L _ hLo a y
  obtain ⟨hTG, _, _, hSC, hB, hH, _, _, _, _, _, hadd, _⟩ := h
  have hLm : MeasurableSet (L : Set V) := hLo.measurableSet

  have key : ∫ x, Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y ∂μ =
      ((μ L).toReal : ℂ) * Set.indicator (perp χ L) (fun _ => (1 : ℂ)) y := by
    by_cases hy : y ∈ perp χ L
    · have h1 : (fun x => Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y) =
          fun x => Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x := by
        funext x
        by_cases hx : x ∈ (L : Set V)
        · simp [Set.indicator_of_mem hx, hy x hx]
        · simp [Set.indicator_of_notMem hx]
      rw [h1, integral_indicator_const _ hLm, Set.indicator_of_mem hy]
      simp [Measure.real]
    · obtain ⟨l, hl, hne⟩ : ∃ l ∈ (L : Set V), χ l y ≠ 1 := by
        simpa [perp] using hy
      set J := ∫ x, Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y ∂μ with hJ
      have hshift : J = χ l y * J := by
        have h2 := integral_add_right_eq_self (μ := μ)
          (fun x => Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y) l
        refine h2.symm.trans ?_
        rw [hJ, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        have hmem : x + l ∈ (L : Set V) ↔ x ∈ (L : Set V) := L.add_mem_cancel_right hl
        by_cases hx : x ∈ (L : Set V)
        · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.2 hx), hadd]
          ring
        · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hmem.1 h))]
      have hJ0 : J = 0 := by
        have h3 : (1 - χ l y) * J = 0 := by
          rw [sub_mul, one_mul, ← hshift, sub_self]
        rcases mul_eq_zero.1 h3 with h4 | h4
        · exact absurd (sub_eq_zero.1 h4).symm hne
        · exact h4
      rw [hJ0, Set.indicator_of_notMem hy, mul_zero]

  unfold fou
  have h5 := integral_add_right_eq_self (μ := μ)
    (fun x => Set.indicator {x | x - a ∈ L} (fun _ => (1 : ℂ)) x * χ x y) a
  rw [← h5]
  have h6 : (fun x => Set.indicator {x | x - a ∈ L} (fun _ => (1 : ℂ)) (x + a) * χ (x + a) y) =
      fun x => χ a y * (Set.indicator (L : Set V) (fun _ => (1 : ℂ)) x * χ x y) := by
    funext x
    have hmem : x + a ∈ {x | x - a ∈ L} ↔ x ∈ (L : Set V) := by simp
    by_cases hx : x ∈ (L : Set V)
    · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.2 hx), hadd]
      ring
    · simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hmem.1 h))]
  rw [h6, integral_const_mul, key]
  ring

end GlobalTheory.CompanionTheory.SW.Core
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FundamentalDomainOfSubgroupFromCosetReps
section
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic

theorem unfold_coset_sum_fundamentalDomain : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (Γ Γ' : Subgroup G) [Countable Γ], Γ' ≤ Γ → ∀ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ → ∀ (Q : Type) (r : Q → G), (∀ q, r q ∈ Γ) → (∀ γ ∈ Γ, ∃! q, γ * (r q)⁻¹ ∈ Γ') → ∃ 𝓕' : Set G, IsFundamentalDomain Γ' 𝓕' μ ∧ ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ h in 𝓕, ∑' q, f (r q * h) ∂μ = ∫⁻ h in 𝓕', f h ∂μ :=
  CompanionTheory.PlacePermOperatorBicommutantSpan.unf

end GlobalTheory.CompanionTheory.Adelic
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussianSumOfCounting
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic

noncomputable def wt (c : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 1 else Real.exp (-(c * 4 ^ j / 4))

lemma wt_nonneg (c : ℝ) (j : ℕ) : 0 ≤ wt c j := by
  unfold wt; split_ifs
  · exact zero_le_one
  · exact (Real.exp_pos _).le

lemma exists_dyadic {c u : ℝ} (hc : 0 < c) (hu : 0 ≤ u) :
    ∃ j : ℕ, u ≤ 2 ^ j ∧ Real.exp (-(c * u ^ 2)) ≤ wt c j := by
  classical
  have hex : ∃ j : ℕ, u ≤ 2 ^ j := by
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt u (one_lt_two : (1 : ℝ) < 2)
    exact ⟨j, hj.le⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases hj : Nat.find hex with _ | k
  · simp only [wt, if_true]
    rw [Real.exp_le_one_iff]
    have : 0 ≤ c * u ^ 2 := by positivity
    linarith
  · have hlt : ¬ u ≤ 2 ^ k := Nat.find_min hex (by omega)
    push_neg at hlt
    have hsq : (4 : ℝ) ^ k ≤ u ^ 2 := by
      have h1 : ((2 : ℝ) ^ k) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by positivity) hlt.le 2
      have h2 : ((2 : ℝ) ^ k) ^ 2 = 4 ^ k := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      linarith
    simp only [wt, Nat.succ_ne_zero, if_false]
    apply Real.exp_le_exp.mpr
    have h3 : c * 4 ^ (k + 1) / 4 = c * 4 ^ k := by rw [pow_succ]; ring
    rw [h3]
    have := mul_le_mul_of_nonneg_left hsq hc.le
    linarith

lemma summable_wt {c : ℝ} (hc : 0 < c) (n : ℕ) :
    Summable fun j : ℕ => wt c j * ((4 : ℝ) ^ n) ^ j := by
  set K : ℝ := ((n + 1).factorial : ℝ) * (4 / c) ^ (n + 1) with hK
  have hK0 : 0 ≤ K := by positivity
  have hgeo : Summable fun j : ℕ => (K + 1) * ((1 : ℝ) / 4) ^ j :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  refine Summable.of_nonneg_of_le (fun j => mul_nonneg (wt_nonneg c j) (by positivity)) ?_ hgeo
  intro j
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [wt]; linarith
  · have hj0 : j ≠ 0 := by omega
    simp only [wt, hj0, if_false]
    set y : ℝ := 4 ^ j with hy
    have hy0 : 0 < y := by positivity
    have hx0 : 0 ≤ c * y / 4 := by positivity
    have hb := Real.pow_div_factorial_le_exp (c * y / 4) hx0 (n + 1)
    have hfac : (0 : ℝ) < ((n + 1).factorial : ℝ) := by positivity
    have hxp : 0 < (c * y / 4) ^ (n + 1) := by positivity
    have hexp : Real.exp (-(c * y / 4)) ≤ ((n + 1).factorial : ℝ) / (c * y / 4) ^ (n + 1) := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
      exact hb
    have hswap : ((4 : ℝ) ^ n) ^ j = y ^ n := by rw [hy, ← pow_mul, ← pow_mul, mul_comm]
    rw [hswap]
    calc Real.exp (-(c * y / 4)) * y ^ n
        ≤ ((n + 1).factorial : ℝ) / (c * y / 4) ^ (n + 1) * y ^ n :=
          mul_le_mul_of_nonneg_right hexp (by positivity)
      _ = K * (1 / 4) ^ j := by
          have : ((1 : ℝ) / 4) ^ j = y⁻¹ := by rw [hy, one_div, inv_pow]
          rw [this, hK, div_pow, div_pow, mul_pow, pow_succ y n]
          field_simp
      _ ≤ (K + 1) * (1 / 4) ^ j := by
          apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)

lemma radius_bound (n j : ℕ) {t₀ t : ℝ} (ht₀ : 0 < t₀) (ht : t₀ ≤ t) :
    (2 ^ j / Real.sqrt t) ^ n + (2 ^ j / Real.sqrt t) ^ (2 * n) ≤
      ((4 : ℝ) ^ n) ^ j * ((1 + (Real.sqrt t₀ ^ n)⁻¹) * (Real.sqrt t ^ n)⁻¹) := by
  have hs₀ : 0 < Real.sqrt t₀ := Real.sqrt_pos.mpr ht₀
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr (ht₀.trans_le ht)
  have hle : Real.sqrt t₀ ≤ Real.sqrt t := Real.sqrt_le_sqrt ht
  set A : ℝ := ((2 : ℝ) ^ j) ^ n with hA
  set B : ℝ := (Real.sqrt t ^ n)⁻¹ with hB
  set B₀ : ℝ := (Real.sqrt t₀ ^ n)⁻¹ with hB₀
  have hA1 : 1 ≤ A := one_le_pow₀ (one_le_pow₀ (by norm_num))
  have hBpos : 0 < B := by positivity
  have hBB : B ≤ B₀ := inv_anti₀ (by positivity) (pow_le_pow_left₀ hs₀.le hle n)
  have e1 : (2 ^ j / Real.sqrt t) ^ n = A * B := by
    rw [div_pow, hA, hB, div_eq_mul_inv]
  have e2 : (2 ^ j / Real.sqrt t) ^ (2 * n) = (A * B) ^ 2 := by
    rw [mul_comm 2 n, pow_mul, e1]
  have e3 : ((4 : ℝ) ^ n) ^ j = A ^ 2 := by
    rw [hA, ← pow_mul, ← pow_mul, ← pow_mul]
    have : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [this, ← pow_mul]; congr 1; ring
  rw [e1, e2, e3]
  have h1 : A * B ≤ A ^ 2 * B := by
    apply mul_le_mul_of_nonneg_right _ hBpos.le
    nlinarith
  have h2 : (A * B) ^ 2 ≤ A ^ 2 * (B₀ * B) := by
    have : (A * B) ^ 2 = A ^ 2 * (B * B) := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_right hBB hBpos.le
  nlinarith

lemma gaussian_le_tsum {X : Type} (c t : ℝ) (hc : 0 < c) (ht : 0 < t) (s : X → ℝ) (p : X → Prop)
    (hs : ∀ x, 0 ≤ s x) (x : X) :
    Set.indicator {x | p x} (fun x => ENNReal.ofReal (Real.exp (-(c * t * s x ^ 2)))) x ≤
      ∑' j : ℕ, ENNReal.ofReal (wt c j) *
        Set.indicator {x | p x ∧ s x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x := by
  classical
  by_cases hp : p x
  · have hq : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    obtain ⟨j, hj, hexp⟩ := exists_dyadic (c := c) (u := Real.sqrt t * s x) hc
      (mul_nonneg hq.le (hs x))
    have hmem : x ∈ {x | p x ∧ s x ≤ 2 ^ j / Real.sqrt t} :=
      ⟨hp, by rw [le_div_iff₀ hq, mul_comm]; exact hj⟩
    have heq : c * (Real.sqrt t * s x) ^ 2 = c * t * s x ^ 2 := by
      rw [mul_pow, Real.sq_sqrt ht.le]; ring
    rw [heq] at hexp
    rw [Set.indicator_of_mem (show x ∈ {x | p x} from hp)]
    refine le_trans ?_ (ENNReal.le_tsum j)
    rw [Set.indicator_of_mem hmem, mul_one]
    exact ENNReal.ofReal_le_ofReal hexp
  · rw [Set.indicator_of_notMem (show x ∉ {x | p x} from hp)]
    exact zero_le

theorem gaussian_sum_le (n : ℕ) (c t₀ C : ℝ) (hc : 0 < c) (ht₀ : 0 < t₀) :
    ∀ (X Ω : Type) [MeasurableSpace Ω] [Countable X] (Pr : Measure Ω)
      (s : Ω → X → ℝ) (p : Ω → X → Prop), (∀ x, Measurable fun ω => s ω x) →
      (∀ x, MeasurableSet {ω | p ω x}) → (∀ ω x, 0 ≤ s ω x) →
      (∀ R : ℝ, 0 < R → ∫⁻ ω, ∑' x, Set.indicator {x | p ω x ∧ s ω x ≤ R}
          (fun _ => (1 : ℝ≥0∞)) x ∂Pr ≤ ENNReal.ofReal (C * (R ^ n + R ^ (2 * n)))) →
      ∀ t : ℝ, t₀ ≤ t → ∫⁻ ω, ∑' x, Set.indicator {x | p ω x}
          (fun x => ENNReal.ofReal (Real.exp (-(c * t * s ω x ^ 2)))) x ∂Pr ≤
        ENNReal.ofReal ((|C| * (1 + (Real.sqrt t₀ ^ n)⁻¹) *
          ∑' j : ℕ, wt c j * ((4 : ℝ) ^ n) ^ j) * (Real.sqrt t ^ n)⁻¹) := by
  intro X Ω _ _ Pr s p hsm hpm hs0 hcount t ht
  have htpos : 0 < t := ht₀.trans_le ht
  have hq : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
  set B : ℝ := (Real.sqrt t ^ n)⁻¹ with hB
  set D : ℝ := 1 + (Real.sqrt t₀ ^ n)⁻¹ with hD
  have hB0 : 0 ≤ B := by positivity
  have hD0 : 0 ≤ D := by positivity
  set E : ℝ := |C| * D * B with hE
  have hE0 : 0 ≤ E := by positivity
  have hmeas : ∀ j : ℕ, Measurable fun ω => ∑' x, Set.indicator
      {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x := by
    intro j
    refine Measurable.tsum fun x => ?_
    have hset : MeasurableSet {ω | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} :=
      (hpm x).inter (measurableSet_le (hsm x) measurable_const)
    have heq : (fun ω => Set.indicator {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t}
        (fun _ => (1 : ℝ≥0∞)) x) =
        Set.indicator {ω | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) := by
      funext ω
      classical
      by_cases h : p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t
      · rw [Set.indicator_of_mem (show x ∈ {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} from h),
          Set.indicator_of_mem (show ω ∈ {ω | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} from h)]
      · rw [Set.indicator_of_notMem (show x ∉ {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} from h),
          Set.indicator_of_notMem (show ω ∉ {ω | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} from h)]
    rw [heq]
    exact measurable_const.indicator hset
  have hpt : ∀ ω, ∑' x, Set.indicator {x | p ω x}
      (fun x => ENNReal.ofReal (Real.exp (-(c * t * s ω x ^ 2)))) x ≤
      ∑' j : ℕ, ENNReal.ofReal (wt c j) * ∑' x, Set.indicator
        {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x := by
    intro ω
    calc _ ≤ ∑' x, ∑' j : ℕ, ENNReal.ofReal (wt c j) * Set.indicator
            {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x :=
          ENNReal.tsum_le_tsum fun x =>
            gaussian_le_tsum c t hc htpos (s ω) (p ω) (hs0 ω) x
      _ = ∑' j : ℕ, ∑' x, ENNReal.ofReal (wt c j) * Set.indicator
            {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x :=
          ENNReal.tsum_comm
      _ = _ := by simp_rw [ENNReal.tsum_mul_left]
  have hterm : ∀ j : ℕ, ENNReal.ofReal (wt c j) * ∫⁻ ω, ∑' x, Set.indicator
      {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x ∂Pr ≤
      ENNReal.ofReal (wt c j * ((4 : ℝ) ^ n) ^ j * E) := by
    intro j
    have hR : (0 : ℝ) < 2 ^ j / Real.sqrt t := by positivity
    have hr := radius_bound n j ht₀ ht
    have hb : C * ((2 ^ j / Real.sqrt t) ^ n + (2 ^ j / Real.sqrt t) ^ (2 * n)) ≤
        ((4 : ℝ) ^ n) ^ j * E := by
      have h0 : 0 ≤ (2 ^ j / Real.sqrt t) ^ n + (2 ^ j / Real.sqrt t) ^ (2 * n) := by positivity
      calc _ ≤ |C| * ((2 ^ j / Real.sqrt t) ^ n + (2 ^ j / Real.sqrt t) ^ (2 * n)) :=
            mul_le_mul_of_nonneg_right (le_abs_self C) h0
        _ ≤ |C| * (((4 : ℝ) ^ n) ^ j * (D * B)) :=
            mul_le_mul_of_nonneg_left hr (abs_nonneg C)
        _ = _ := by rw [hE]; ring
    calc _ ≤ ENNReal.ofReal (wt c j) * ENNReal.ofReal (((4 : ℝ) ^ n) ^ j * E) := by
          gcongr
          exact (hcount _ hR).trans (ENNReal.ofReal_le_ofReal hb)
      _ = _ := by
          rw [← ENNReal.ofReal_mul (wt_nonneg c j), mul_assoc]
  have hsum : Summable fun j : ℕ => wt c j * ((4 : ℝ) ^ n) ^ j * E :=
    (summable_wt hc n).mul_right E
  calc _ ≤ ∫⁻ ω, ∑' j : ℕ, ENNReal.ofReal (wt c j) * ∑' x, Set.indicator
          {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x ∂Pr :=
        lintegral_mono hpt
    _ = ∑' j : ℕ, ∫⁻ ω, ENNReal.ofReal (wt c j) * ∑' x, Set.indicator
          {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x ∂Pr :=
        lintegral_tsum fun j => ((hmeas j).const_mul _).aemeasurable
    _ = ∑' j : ℕ, ENNReal.ofReal (wt c j) * ∫⁻ ω, ∑' x, Set.indicator
          {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x ∂Pr := by
        congr 1; funext j
        exact lintegral_const_mul _ (hmeas j)
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (wt c j * ((4 : ℝ) ^ n) ^ j * E) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' j : ℕ, wt c j * ((4 : ℝ) ^ n) ^ j * E) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun j => mul_nonneg (mul_nonneg (wt_nonneg c j) (by positivity)) hE0) hsum).symm
    _ = _ := by
        rw [tsum_mul_right, hE]
        congr 1
        ring

theorem gaussian_sum_of_counting :
    ∀ (n : ℕ) (c t₀ C : ℝ), 0 < c → 0 < t₀ → ∃ C' : ℝ, ∀ (X Ω : Type) [MeasurableSpace Ω]
      [Countable X] (Pr : Measure Ω) (s : Ω → X → ℝ) (p : Ω → X → Prop),
      (∀ x, Measurable fun ω => s ω x) → (∀ x, MeasurableSet {ω | p ω x}) →
      (∀ ω x, 0 ≤ s ω x) →
      (∀ R : ℝ, 0 < R → ∫⁻ ω, ∑' x, Set.indicator {x | p ω x ∧ s ω x ≤ R}
          (fun _ => (1 : ℝ≥0∞)) x ∂Pr ≤ ENNReal.ofReal (C * (R ^ n + R ^ (2 * n)))) →
      ∀ t : ℝ, t₀ ≤ t → ∫⁻ ω, ∑' x, Set.indicator {x | p ω x}
          (fun x => ENNReal.ofReal (Real.exp (-(c * t * s ω x ^ 2)))) x ∂Pr ≤
        ENNReal.ofReal (C' * (Real.sqrt t ^ n)⁻¹) :=
  fun n c t₀ C hc ht₀ => ⟨_, gaussian_sum_le n c t₀ C hc ht₀⟩

end GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMeasureIwasawaDecomposition
section
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic

theorem tripleProduct_map_leftInvariant : ∀ (G N H T : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableSpace N] [Group H] [MeasurableSpace H] [MeasurableMul H] [CommGroup T] [MeasurableSpace T] [MeasurableMul T] (μN : Measure N) [SFinite μN] (μH : Measure H) [SFinite μH] [μH.IsMulLeftInvariant] (μT : Measure T) [SFinite μT] [μT.IsMulLeftInvariant] (nn : N → G) (ι : H →* G) (mm : T →* G) (χ : T →* ℝ≥0), Measurable nn → Measurable ι → Measurable mm → Measurable χ → (∀ p, ∃ L : N → N, MeasurePreserving L μN μN ∧ ∀ x, nn p * nn x = nn (L x)) → (∀ u, ∃ L : N → N, MeasurePreserving L μN μN ∧ ∀ x, ι u * nn x = nn (L x) * ι u) → (∀ t, ∃ L : N → N, Measurable L ∧ μN.map L = χ t • μN ∧ ∀ x, mm t * nn x = nn (L x) * mm t) → (∀ u t, mm t * ι u = ι u * mm t) → ∀ (p : N) (u : H) (t : T), ((μN.prod (μH.prod (μT.withDensity fun s => (χ s : ℝ≥0∞)))).map fun z => nn z.1 * ι z.2.1 * mm z.2.2).map (fun g => nn p * ι u * mm t * g) = (μN.prod (μH.prod (μT.withDensity fun s => (χ s : ℝ≥0∞)))).map fun z => nn z.1 * ι z.2.1 * mm z.2.2 := by
  exact CompanionTheory.PlacePermOperatorBicommutantSpan.nuabs

end GlobalTheory.CompanionTheory.Adelic
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductRenormalization
section
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.TailConst

theorem tail_eq_mul_tail_insert {ι : Type} [DecidableEq ι] (a : ι → ℝ)
    (hs : Summable (fun v => |a v - 1|)) (S : Finset ι) (v : ι) (hv : v ∉ S) :
    ∏' w : {w // w ∉ S}, a w.1 = a v * ∏' w : {w // w ∉ insert v S}, a w.1 := by
  have h := (_root_.GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod {w // w ∉ S} (fun w => a w.1)
    (hs.comp_injective Subtype.val_injective)).2.1 {⟨v, hv⟩}
  rw [h.2, Finset.prod_singleton]
  congr 1
  let e : {w : {w // w ∉ S} // w ∉ ({⟨v, hv⟩} : Finset {w // w ∉ S})} ≃
      {w // w ∉ insert v S} :=
    { toFun := fun x => ⟨x.1.1, by
        have h1 := x.1.2
        have h2 := x.2
        simp only [Finset.mem_singleton] at h2
        simp only [Finset.mem_insert, not_or]
        exact ⟨fun h3 => h2 (Subtype.ext h3), h1⟩⟩
      invFun := fun y => ⟨⟨y.1, fun h3 => y.2 (Finset.mem_insert_of_mem h3)⟩, by
        simp only [Finset.mem_singleton]
        intro h3
        exact y.2 (by
          have := congrArg Subtype.val h3
          simp only at this
          simp [this])⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  exact e.tprod_eq (fun w => a w.1)

theorem tail_pos {ι : Type} (a : ι → ℝ) (hs : Summable (fun v => |a v - 1|)) (S : Finset ι)
    (hpos : ∀ v, v ∉ S → 0 < a v) : 0 < ∏' w : {w // w ∉ S}, a w.1 :=
  (_root_.GlobalTheory.CompanionTheory.SW.AbsTprod.abs_tprod {w // w ∉ S} (fun w => a w.1)
    (hs.comp_injective Subtype.val_injective)).2.2.1 (fun w => hpos w.1 w.2)

theorem exists_const_mul_tail : ∀ (ι : Type) [DecidableEq ι] (a : ι → ℝ) (c : Finset ι → ℝ≥0) (S₁ : Finset ι), (∀ v, 0 ≤ a v) → Summable (fun v => |a v - 1|) → (∀ S, S₁ ⊆ S → ∀ v, v ∉ S → (c S : ℝ) = c (insert v S) * a v) → ∃ (c₀ : ℝ≥0) (S₀ : Finset ι), S₁ ⊆ S₀ ∧ ∀ S, S₀ ⊆ S → (0 < ∏' v : {v // v ∉ S}, a v.1) ∧ (c S : ℝ) = c₀ * ∏' v : {v // v ∉ S}, a v.1 := by
  intro ι _ a c S₁ _ hs hc
  have hev : ∀ᶠ v in Filter.cofinite, |a v - 1| < 1 / 2 :=
    hs.tendsto_cofinite_zero.eventually (Iio_mem_nhds (by norm_num))
  have hfin : {v | ¬ |a v - 1| < 1 / 2}.Finite := Filter.eventually_cofinite.1 hev
  let S₀ : Finset ι := S₁ ∪ hfin.toFinset
  have hS₀ : ∀ v, v ∉ S₀ → 0 < a v := by
    intro v hv
    have h1 : |a v - 1| < 1 / 2 := by
      by_contra h2
      exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 h2))
    have h2 := (abs_lt.1 h1).1
    linarith
  have hposS : ∀ S, S₀ ⊆ S → 0 < ∏' v : {v // v ∉ S}, a v.1 := fun S hS =>
    tail_pos a hs S (fun v hv => hS₀ v (fun h => hv (hS h)))
  have hP₀ := hposS S₀ (Finset.Subset.refl _)
  refine ⟨⟨(c S₀ : ℝ) / ∏' v : {v // v ∉ S₀}, a v.1, div_nonneg (c S₀).2 hP₀.le⟩, S₀,
    Finset.subset_union_left, fun S hS => ⟨hposS S hS, ?_⟩⟩
  have key : ∀ T : Finset ι, (c (S₀ ∪ T) : ℝ) =
      ((c S₀ : ℝ) / ∏' v : {v // v ∉ S₀}, a v.1) * ∏' v : {v // v ∉ S₀ ∪ T}, a v.1 := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      rw [Finset.union_empty]
      field_simp
    | insert v T _ ih =>
      by_cases hv : v ∈ S₀ ∪ T
      · have h1 : S₀ ∪ insert v T = S₀ ∪ T := by
          rw [Finset.union_insert, Finset.insert_eq_of_mem hv]
        rw [h1]
        exact ih
      · have h1 : S₀ ∪ insert v T = insert v (S₀ ∪ T) := Finset.union_insert _ _ _
        have hsub : S₀ ⊆ S₀ ∪ T := Finset.subset_union_left
        have hav : 0 < a v := hS₀ v (fun h => hv (hsub h))
        have h2 := hc (S₀ ∪ T) (Finset.Subset.trans Finset.subset_union_left hsub) v hv
        have h3 := tail_eq_mul_tail_insert a hs (S₀ ∪ T) v hv
        rw [h1]
        rw [h2, h3] at ih
        have h4 : (c (insert v (S₀ ∪ T)) : ℝ) * a v = (((c S₀ : ℝ) / ∏' v : {v // v ∉ S₀}, a v.1) * ∏' w : {w // w ∉ insert v (S₀ ∪ T)}, a w.1) * a v := by
          rw [ih]; ring
        exact mul_right_cancel₀ hav.ne' h4
  have h := key S
  rw [Finset.union_eq_right.2 hS] at h
  exact h

end GlobalTheory.CompanionTheory.SW.TailConst
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InvariantMeasureCompactCoverBound
section
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic

theorem integral_fundamentalDomain_le_siegel : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (P : Subgroup G) (ν : Measure G) [SFinite ν], (∀ p ∈ P, ν.map (fun g => p * g) = ν) → (∀ U ∈ 𝓝 (1 : G), ν U ≠ 0) → ∀ C : Set G, IsCompact C → ∃ (C' : Set G) (K : ℝ≥0∞), IsCompact C' ∧ K < ⊤ ∧ ∀ (Γ : Subgroup G) [Countable Γ], Γ ≤ P → ∀ 𝓕 : Set G, IsFundamentalDomain Γ 𝓕 μ → ∀ S : Set G, MeasurableSet S → (∀ᵐ p ∂ν, ∃ γ ∈ Γ, γ * p ∈ S) → ∀ f g : G → ℝ≥0∞, Measurable f → Measurable g → (∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) → (∀ x, f x ≠ 0 → ∃ p ∈ P, ∃ c ∈ C, x = p * c) → (∀ p ∈ S, ∀ c ∈ C', f (p * c) ≤ g p) → ∫⁻ x in 𝓕, f x ∂μ ≤ K * ∫⁻ p in S, g p ∂ν := by
  first | exact CompanionTheory.PlacePermOperatorBicommutantSpan.cover | exact @CompanionTheory.PlacePermOperatorBicommutantSpan.cover

end GlobalTheory.CompanionTheory.Adelic
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TprodComplementSplitFinset
section
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.TailCut

theorem tprod_tail_cut : ∀ (ι : Type) [DecidableEq ι] (a : ι → ℝ) (S S' : Finset ι),
    Summable (fun v => |a v - 1|) → S ⊆ S' →
      ∏' v : {v // v ∉ S}, a v.1 = (∏ v ∈ S' \ S, a v) * ∏' v : {v // v ∉ S'}, a v.1 := by
  intro ι _ a S S' hsum hSS'
  have hmul : ∀ T : Set ι, Multipliable (T.mulIndicator a) := by
    intro T
    have hs : Summable fun v => ‖T.mulIndicator a v - 1‖ := by
      refine Summable.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => ?_) hsum
      by_cases hv : v ∈ T
      · simp [Set.mulIndicator_of_mem hv, Real.norm_eq_abs]
      · simp [Set.mulIndicator_of_notMem hv]
    have h := multipliable_one_add_of_summable hs
    simpa using h
  have e1 : (∏' v : {v // v ∉ S}, a v.1) = ∏' v, Set.mulIndicator {v | v ∉ S} a v :=
    tprod_subtype {v | v ∉ S} a
  have e2 : (∏' v : {v // v ∉ S'}, a v.1) = ∏' v, Set.mulIndicator {v | v ∉ S'} a v :=
    tprod_subtype {v | v ∉ S'} a
  have hsplit : (∏' v, Set.mulIndicator {v | v ∉ S} a v) =
      ∏' v, (Set.mulIndicator (↑(S' \ S) : Set ι) a v * Set.mulIndicator {v | v ∉ S'} a v) := by
    refine tprod_congr fun v => ?_
    by_cases h1 : v ∈ S
    · have h2 : v ∈ S' := hSS' h1
      simp [Set.mulIndicator, h1, h2]
    · by_cases h2 : v ∈ S'
      · simp [Set.mulIndicator, h1, h2]
      · simp [Set.mulIndicator, h1, h2]
  have hfin : (∏' v, Set.mulIndicator (↑(S' \ S) : Set ι) a v) = ∏ v ∈ S' \ S, a v := by
    rw [tprod_eq_prod (s := S' \ S)]
    · exact Finset.prod_congr rfl fun v hv => Set.mulIndicator_of_mem (Finset.mem_coe.mpr hv) a
    · intro v hv
      exact Set.mulIndicator_of_notMem (by rwa [Finset.mem_coe]) a
  rw [e1, e2, hsplit, Multipliable.tprod_mul (hmul _) (hmul _), hfin]

end GlobalTheory.CompanionTheory.SW.TailCut
end

