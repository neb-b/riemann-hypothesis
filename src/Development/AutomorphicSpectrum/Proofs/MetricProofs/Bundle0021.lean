module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle0004
public import ReciprocityTheory.AnalyticForms.LeviForms.RegChartC
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.FderivAffCoordZero
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0017
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticSystemRegularityProperties
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open scoped ContDiff

theorem GlobalTheory.CompanionTheory.Ar.PB.anSys_open_basics : ∀ (e : ℕ) (σ : Type) (S : AnSys e σ), IsOpen S.open' ∧ IsNull S.A S.open'ᶜ ∧ (∀ a, ∀ x ∈ S.open', IsTwiceDifferentiableAt S.A (S.potH a) x) ∧ (∀ a t, 0 < t → t ≤ S.t₀ → IsPotential S.A (S.potT a t)) ∧ ∀ y ∈ S.open', Real.exp 1 ≤ rW S.L S.s y := by
  intro e σ S
  have hcl : IsClosed (bdry S.s) := LeviFormBoundaryTopology.isClosed_bdry S.sec
  refine ⟨hcl.isOpen_compl, ?_, ?_, ?_, fun y _ => rW_ge S.L S.s S.norm_le y⟩
  · have hAn : S.A.IsAnalyticSubset (bdry S.s) := by
      intro x
      refine ⟨S.L.U x, S.L.isOpen_U x, S.L.mem_U x, 1, fun _ => S.s x, fun _ => S.sec.1 x, ?_⟩
      ext z
      constructor
      · rintro ⟨hz, hzU⟩
        exact ⟨hzU, fun _ => (LeviFormBoundaryTopology.bdry_iff S.sec hzU).1 hz⟩
      · rintro ⟨hzU, hz⟩
        exact ⟨(LeviFormBoundaryTopology.bdry_iff S.sec hzU).2 (hz 0), hzU⟩
    have hInt := LeviFormBoundaryTopology.interior_bdry_eq_empty S.sec S.snc
    intro j
    have h := analyticNull S.A (bdry S.s) hAn hInt j
    have hc : S.open'ᶜ = bdry S.s := compl_compl _
    rw [hc]
    rw [Set.inter_comm, (S.A.chart j).image_source_inter_eq'] at h
    exact h
  · intro a x hx j hj
    obtain ⟨hth, hph, -, -⟩ := S.sing a
    have h1 := hth.1 x j
    have h2 := hph j
    have hO1 : IsOpen ((S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' (S.th a).U x) :=
      (S.A.chart j).isOpen_inter_preimage_symm ((S.th a).isOpen_U x)
    have hO2 : IsOpen ((S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' (bdry S.s)ᶜ) :=
      (S.A.chart j).isOpen_inter_preimage_symm hcl.isOpen_compl
    have hm1 : S.A.chart j x ∈ (S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' (S.th a).U x :=
      ⟨(S.A.chart j).map_source hj, by
        simpa [(S.A.chart j).left_inv hj] using (S.th a).mem_U x⟩
    have hm2 : S.A.chart j x ∈ (S.A.chart j).target ∩ (S.A.chart j).symm ⁻¹' (bdry S.s)ᶜ :=
      ⟨(S.A.chart j).map_source hj, by
        have hx' : x ∈ (bdry S.s)ᶜ := hx
        simpa [(S.A.chart j).left_inv hj] using hx'⟩
    have hle : (2 : WithTop ℕ∞) ≤ ∞ := ENat.LEInfty.out
    have hA := (h1.contDiffAt (hO1.mem_nhds hm1)).of_le hle
    have hB := (h2.contDiffAt (hO2.mem_nhds hm2)).of_le hle
    exact hA.add hB
  · intro a t ht ht'
    exact isPotentialAdd S.A _ _ (S.sing a).1 (isPotential_ofFun S.A _ ((S.reg a).2.2 t ht ht').1)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.C2TendstoPullbackThroughChart
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric.ChartPullBack

theorem comp_symm_eventuallyEq {e : ℕ} {X : Type} [TopologicalSpace X]
    (c : OpenPartialHomeomorph X (Fin e → ℂ)) (f : (Fin e → ℂ) → ℝ) {z : Fin e → ℂ}
    (hz : z ∈ c.target) : ((f ∘ c) ∘ c.symm) =ᶠ[𝓝 z] f := by
  filter_upwards [c.open_target.mem_nhds hz] with y hy
  simp [Function.comp, c.right_inv hy]

theorem fderiv_comp_symm_eq {e : ℕ} {X : Type} [TopologicalSpace X]
    (c : OpenPartialHomeomorph X (Fin e → ℂ)) (f : (Fin e → ℂ) → ℝ) {z : Fin e → ℂ}
    (hz : z ∈ c.target) : fderiv ℝ ((f ∘ c) ∘ c.symm) z = fderiv ℝ f z :=
  (comp_symm_eventuallyEq c f hz).fderiv_eq

theorem fderiv_comp_symm_eventuallyEq {e : ℕ} {X : Type} [TopologicalSpace X]
    (c : OpenPartialHomeomorph X (Fin e → ℂ)) (f : (Fin e → ℂ) → ℝ) {z : Fin e → ℂ}
    (hz : z ∈ c.target) : fderiv ℝ ((f ∘ c) ∘ c.symm) =ᶠ[𝓝 z] fderiv ℝ f := by
  filter_upwards [c.open_target.mem_nhds hz] with y hy
  exact fderiv_comp_symm_eq c f hy

theorem fderiv_fderiv_comp_symm_eq {e : ℕ} {X : Type} [TopologicalSpace X]
    (c : OpenPartialHomeomorph X (Fin e → ℂ)) (f : (Fin e → ℂ) → ℝ) {z : Fin e → ℂ}
    (hz : z ∈ c.target) :
    fderiv ℝ (fderiv ℝ ((f ∘ c) ∘ c.symm)) z = fderiv ℝ (fderiv ℝ f) z :=
  (fderiv_comp_symm_eventuallyEq c f hz).fderiv_eq

theorem C2_tendsto_chart_pullback : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (c : OpenPartialHomeomorph X (Fin e → ℂ)) (g : ℝ → (Fin e → ℂ) → ℝ) (p : (Fin e → ℂ) → ℝ) (K' : Set (Fin e → ℂ)), K' ⊆ c.target → (TendstoUniformlyOn g p (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (g t)) (fderiv ℝ p) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (g t))) (fderiv ℝ (fderiv ℝ p)) (𝓝[>] 0) K' ∧ ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K', ‖fderiv ℝ (g t) z - fderiv ℝ p z‖ ≤ M * t) → (TendstoUniformlyOn (fun t => (g t ∘ c) ∘ c.symm) p (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ ((g t ∘ c) ∘ c.symm)) (fderiv ℝ p) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ ((g t ∘ c) ∘ c.symm))) (fderiv ℝ (fderiv ℝ p)) (𝓝[>] 0) K' ∧ ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K', ‖fderiv ℝ ((g t ∘ c) ∘ c.symm) z - fderiv ℝ p z‖ ≤ M * t) := by
  intro e X _ c g p K' hK h
  obtain ⟨h0, h1, h2, M, hM⟩ := h
  refine ⟨h0.congr (Eventually.of_forall fun t z hz => ?_),
    h1.congr (Eventually.of_forall fun t z hz => ?_),
    h2.congr (Eventually.of_forall fun t z hz => ?_),
    M, hM.mono fun t ht z hz => ?_⟩
  · exact ((comp_symm_eventuallyEq c (g t) (hK hz)).eq_of_nhds).symm
  · exact (fderiv_comp_symm_eq c (g t) (hK hz)).symm
  · exact (fderiv_fderiv_comp_symm_eq c (g t) (hK hz)).symm
  · rw [fderiv_comp_symm_eq c (g t) (hK hz)]
    exact ht z hz

end GlobalTheory.CompanionTheory.Metric.ChartPullBack
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.EmbeddedResolutionAmpleMetric
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem exists_smooth_hermLine_posPot_of_isEmbedded : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P J e), IsEmbedded R.A P R.U R.lift → ∃ Amp : HermLine ι, IsSmoothHerm Amp ∧ IsPotential R.A (potOf R Amp) ∧ IsPosPot R.A (potOf R Amp) :=
  @PositivityTheory.UnitarySelfGeneration.g_pos

end GlobalTheory.CompanionTheory.Ar.Cmp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.EpsilonScheduleProperties
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem log_div_self_anti (a b : ℝ) (ha : Real.exp 1 ≤ a) (hab : a ≤ b) :
    Real.log b / b ≤ Real.log a / a :=
  Real.log_div_self_antitoneOn ha (show Real.exp 1 ≤ b from ha.trans hab) hab

theorem epsT_mono (C t t' : ℝ) (hC : 0 ≤ C) (ht : 0 < t) (htt : t ≤ t')
    (ht' : t' ≤ Real.exp (-Real.exp 1)) : epsT C t ≤ epsT C t' := by
  have ht'0 : 0 < t' := ht.trans_le htt
  have h1 := (GlobalTheory.CompanionTheory.Ar.Giv.log_inv_bounds ht'0 ht').1
  have h2 : Real.log (1 / t') ≤ Real.log (1 / t) := by
    rw [one_div, one_div, Real.log_inv, Real.log_inv]
    linarith [Real.log_le_log ht htt]
  rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul, GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul]
  exact mul_le_mul_of_nonneg_left (log_div_self_anti _ _ h1 h2) hC

theorem le_epsT (C t : ℝ) (hC : 1 ≤ C) (ht : 0 < t) (hte : t ≤ Real.exp (-Real.exp 1)) :
    t ≤ epsT C t := by
  obtain ⟨h1, h2⟩ := GlobalTheory.CompanionTheory.Ar.Giv.log_inv_bounds ht hte
  set ℓ := Real.log (1 / t) with hℓ
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le (Real.exp_pos 1) h1
  have hle : ℓ ≤ 1 / t := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 / t by positivity)
    linarith
  have htl : t * ℓ ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hle ht.le
    rwa [mul_one_div_cancel ht.ne'] at this
  have hA : t ≤ 1 / ℓ := by rw [le_div_iff₀ hℓ0]; exact htl
  have hB : 1 / ℓ ≤ Real.log ℓ / ℓ := div_le_div_of_nonneg_right h2 hℓ0.le
  have hq : 0 ≤ Real.log ℓ / ℓ := div_nonneg (by linarith) hℓ0.le
  have hC' : Real.log ℓ / ℓ ≤ C * (Real.log ℓ / ℓ) := le_mul_of_one_le_left hq hC
  rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul]
  linarith

theorem epsT_tendsto (C : ℝ) : Tendsto (epsT C) (𝓝[>] 0) (𝓝 0) := by
  have hl : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    have := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa using this
  have hL : Tendsto (fun t : ℝ => Real.log (1 / t)) (𝓝[>] 0) atTop := by
    have := Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
    simpa [Function.comp_def, one_div] using this
  have h := (hl.comp hL).const_mul C
  rw [mul_zero] at h
  have e : epsT C = fun t => C * ((fun x : ℝ => Real.log x / x) ∘ (fun t : ℝ => Real.log (1 / t))) t := by
    funext t
    rw [GlobalTheory.CompanionTheory.Ar.Giv.epsT_eq_mul]
    rfl
  rw [e]
  exact h

theorem epsT_le_one (C : ℝ) : ∃ a : ℝ, 0 < a ∧ ∀ t, 0 < t → t ≤ a → epsT C t ≤ 1 := by
  have hev : {t : ℝ | epsT C t < 1} ∈ 𝓝[>] (0 : ℝ) :=
    (epsT_tendsto C) (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hu0 : (0 : ℝ) < u := hu
  refine ⟨u / 2, by linarith, fun t ht hta => ?_⟩
  exact (hsub ⟨ht, by linarith⟩ : epsT C t < 1).le

theorem fin_pos_lower (n : ℕ) (a : Fin n → ℝ) (ha : ∀ j, 0 < a j) :
    ∃ b : ℝ, 0 < b ∧ ∀ j, b ≤ a j := by
  by_cases h : Nonempty (Fin n)
  · refine ⟨Finset.univ.inf' Finset.univ_nonempty a,
      (Finset.lt_inf'_iff _).2 (fun j _ => ha j), fun j => Finset.inf'_le _ (Finset.mem_univ j)⟩
  · exact ⟨1, one_pos, fun j => (h ⟨j⟩).elim⟩

theorem epsT_numerics :
    (∀ a b : ℝ, Real.exp 1 ≤ a → a ≤ b → Real.log b / b ≤ Real.log a / a) ∧
    (∀ C t t' : ℝ, 0 ≤ C → 0 < t → t ≤ t' → t' ≤ Real.exp (-Real.exp 1) → epsT C t ≤ epsT C t') ∧
    (∀ C t : ℝ, 1 ≤ C → 0 < t → t ≤ Real.exp (-Real.exp 1) → t ≤ epsT C t) ∧
    (∀ C : ℝ, Tendsto (epsT C) (𝓝[>] 0) (𝓝 0)) ∧
    (∀ C : ℝ, ∃ a : ℝ, 0 < a ∧ ∀ t, 0 < t → t ≤ a → epsT C t ≤ 1) ∧
    (∀ (n : ℕ) (a : Fin n → ℝ), (∀ j, 0 < a j) → ∃ b : ℝ, 0 < b ∧ ∀ j, b ≤ a j) :=
  ⟨log_div_self_anti, epsT_mono, le_epsT, epsT_tendsto, epsT_le_one, fin_pos_lower⟩

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LeviNonnegInChartOfPsh
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LeviChart

theorem levi_nonneg_of_compat_fixedBase : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A B : FinHolAtlas e X)
    (th : LocPot X) (ph : X → ℝ) (U : Set X) (x₀ : X) (j : Fin B.n), A.Compatible B →
    IsPotential A th → IsOpen U → A.SmoothOn U ph → IsPshOn A U (th + LocPot.ofFun ph) →
    (B.chart j).source ⊆ th.U x₀ → ∀ y ∈ (B.chart j).target ∩ (B.chart j).symm ⁻¹' U,
    ∀ w : Fin e → ℂ,
    0 ≤ levi (fun z => th.φ x₀ ((B.chart j).symm z) + ph ((B.chart j).symm z)) y w := by
  intro e X _ A B th ph U x₀ j hAB hth hU hph hpsh hsrc y hy w
  have hp : (B.chart j).symm y ∈ (B.chart j).source := (B.chart j).map_target hy.1
  obtain ⟨k, hk⟩ := A.cover ((B.chart j).symm y)
  have hτ : AnalyticAt ℂ (A.chart k ∘ (B.chart j).symm) y := hAB.2 j k y ⟨hy.1, hk⟩
  have hsymm : (A.chart k).symm ((A.chart k ∘ (B.chart j).symm) y) = (B.chart j).symm y :=
    (A.chart k).left_inv hk
  have htgt : (A.chart k ∘ (B.chart j).symm) y ∈ (A.chart k).target := (A.chart k).map_source hk
  have hthU : (B.chart j).symm y ∈ th.U x₀ := hsrc hp
  have hO1 : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' th.U x₀) :=
    (A.chart k).isOpen_inter_preimage_symm (th.isOpen_U x₀)
  have hO2 : IsOpen ((A.chart k).target ∩ (A.chart k).symm ⁻¹' U) :=
    (A.chart k).isOpen_inter_preimage_symm hU
  have hm1 : (A.chart k ∘ (B.chart j).symm) y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' th.U x₀ :=
    ⟨htgt, by rw [Set.mem_preimage, hsymm]; exact hthU⟩
  have hm2 : (A.chart k ∘ (B.chart j).symm) y ∈ (A.chart k).target ∩ (A.chart k).symm ⁻¹' U :=
    ⟨htgt, by rw [Set.mem_preimage, hsymm]; exact hy.2⟩
  have h2 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)
  have hC1 : ContDiffAt ℝ 2 (th.φ x₀ ∘ (A.chart k).symm) ((A.chart k ∘ (B.chart j).symm) y) :=
    ((hth.1 x₀ k).contDiffAt (hO1.mem_nhds hm1)).of_le h2
  have hC2 : ContDiffAt ℝ 2 (ph ∘ (A.chart k).symm) ((A.chart k ∘ (B.chart j).symm) y) :=
    ((hph k).contDiffAt (hO2.mem_nhds hm2)).of_le h2
  have hC : ContDiffAt ℝ 2 (fun z => th.φ x₀ ((A.chart k).symm z) + ph ((A.chart k).symm z))
      ((A.chart k ∘ (B.chart j).symm) y) := hC1.add hC2
  have hev : (fun z => th.φ x₀ ((B.chart j).symm z) + ph ((B.chart j).symm z)) =ᶠ[𝓝 y]
      ((fun z => th.φ x₀ ((A.chart k).symm z) + ph ((A.chart k).symm z)) ∘
        (A.chart k ∘ (B.chart j).symm)) := by
    have h1 : ∀ᶠ z in 𝓝 y, (B.chart j).symm z ∈ (A.chart k).source :=
      ((B.chart j).continuousAt_symm hy.1).eventually ((A.chart k).open_source.mem_nhds hk)
    filter_upwards [h1] with z hz
    simp only [Function.comp_apply, (A.chart k).left_inv hz]
  rw [levi_congr hev w, levi_comp w hτ hC]
  exact hpsh x₀ k _ ⟨htgt, ⟨hm1.2, Set.mem_univ _⟩, hm2.2⟩ _

end GlobalTheory.CompanionTheory.LeviChart
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalPshRegularizationLogBound
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

noncomputable section

lemma mollifier_bdd {D : ℕ} (ρ : ReciprocityTheory.AnForm.A.Mollifier D) : ∃ b : ℝ, ∀ w, ρ.toFun w ≤ b := by
  have hcs : HasCompactSupport ρ.toFun := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Fin D → ℂ) 1) ?_
    exact ρ.support_subset.trans ball_subset_closedBall
  obtain ⟨b, hb⟩ := ρ.contDiff.continuous.bounded_above_of_compact_support hcs
  exact ⟨b, fun w => (le_abs_self _).trans (hb w)⟩

lemma polyMax_le_pmoff_same {D : ℕ} {S : Finset (Fin D)} {u w : (Fin D → ℂ) → ℝ} {R B κ : ℝ}
    (hub : ∀ x ∈ ball (0 : Fin D → ℂ) R \ ReciprocityTheory.AnForm.A.coordDiv S, u x ≤ B)
    (hW1 : ReciprocityTheory.AnForm.A.IsPsh (ball 0 R) w)
    (hW3 : ∀ x ∈ ball (0 : Fin D → ℂ) R, ∀ δ > 0,
      ∃ y ∈ ball (0 : Fin D → ℂ) R \ ReciprocityTheory.AnForm.A.coordDiv S,
        dist y x < δ ∧ w x ≤ max (u y) (-κ) + δ)
    {z : Fin D → ℂ} {s R' : ℝ} (hs : 0 < s) (hsR : s < R') (hR' : closedBall z R' ⊆ ball 0 R) :
    ReciprocityTheory.AnForm.A.polyMax w z s ≤ max (RegularChartScaling.pmoff S u z s) (-κ) := by
  have hR'0 : 0 < R' := hs.trans hsR
  have hconv := (ReciprocityTheory.AnForm.A.polyMaxLogConvex_thm D (ball 0 R) w z R' isOpen_ball hW1 hR'0 hR').1
  set g : ℝ → ℝ := fun σ => ReciprocityTheory.AnForm.A.polyMax w z (Real.exp σ) with hg
  have hconv' : ConvexOn ℝ (Set.Iio (Real.log R')) g :=
    hconv.subset Set.Iio_subset_Iic_self (convex_Iio _)
  have hcont : ContinuousOn g (Set.Iio (Real.log R')) := hconv'.continuousOn isOpen_Iio
  have hlog : Real.log s < Real.log R' := Real.log_lt_log hs hsR
  have hca : ContinuousAt g (Real.log s) := hcont.continuousAt (Iio_mem_nhds hlog)
  have hsub : closedBall z s ⊆ ball 0 R := (closedBall_subset_closedBall hsR.le).trans hR'
  have hle : ∀ σ ∈ Set.Iio (Real.log s), g σ ≤ max (RegularChartScaling.pmoff S u z s) (-κ) := by
    intro σ hσ
    have hlt : Real.exp σ < s := by
      have := Real.exp_lt_exp.2 (Set.mem_Iio.1 hσ)
      rwa [Real.exp_log hs] at this
    exact RegularChartScaling.polyMax_le_pmo hub hW3 (Real.exp_pos σ).le hlt hsub
  have hfin : g (Real.log s) ≤ max (RegularChartScaling.pmoff S u z s) (-κ) :=
    le_of_tendsto (hca.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (Real.log s))))
      (by filter_upwards [self_mem_nhdsWithin] with σ hσ using hle σ hσ)
  simpa only [hg, Real.exp_log hs] using hfin

theorem molli_trunc_near_polyMax :
    ∀ (D : ℕ) (S : Finset (Fin D)) (m : Fin D → ℕ) (u : (Fin D → ℂ) → ℝ) (C₅ : ℝ) (ρ : ReciprocityTheory.AnForm.A.Mollifier D), ContinuousOn u (ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S) → ReciprocityTheory.AnForm.A.IsPsh (ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S) u → (∀ z ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S, -C₅ * Real.log (rLoc S m z) ≤ u z ∧ u z ≤ C₅) → ∃ (C t₀ : ℝ) (w : ℝ → (Fin D → ℂ) → ℝ), 1 ≤ C ∧ 0 < t₀ ∧ t₀ ≤ Real.exp (-Real.exp 1) ∧ t₀ ≤ 1 / 8 ∧ ∀ t, 0 < t → t ≤ t₀ → (∀ z ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S, w t z = max (u z) (-C * Real.log (Real.log (1 / t)))) ∧ ContDiffOn ℝ ∞ (ReciprocityTheory.AnForm.A.molli ρ t (w t)) (ball (0 : Fin D → ℂ) (5 / 4)) ∧ ReciprocityTheory.AnForm.A.IsLeviPsh (ball (0 : Fin D → ℂ) (5 / 4)) (ReciprocityTheory.AnForm.A.molli ρ t (w t)) ∧ (∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv S, u z ≤ ReciprocityTheory.AnForm.A.molli ρ t (w t) z) ∧ ∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4), -C * Real.log (Real.log (1 / t)) ≤ polyMaxOff S u z t ∧ polyMaxOff S u z t - epsT C t ≤ ReciprocityTheory.AnForm.A.molli ρ t (w t) z ∧ ReciprocityTheory.AnForm.A.molli ρ t (w t) z ≤ polyMaxOff S u z t := by
  intro D S m u C₅ ρ hc hp hb
  have hC₅ : 0 ≤ C₅ := RegularChartScaling.fifth_volume_constant_nonneg m (by norm_num) (by norm_num) hb
  have hub : ∀ x ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S, u x ≤ C₅ :=
    fun x hx => (hb x hx).2
  obtain ⟨C₀, ℓ₀, hC₀, hosc⟩ := RegularChartScaling.oscGen m (R := 3 / 2) (by norm_num) (by norm_num)
    hc hp hb (C₁ := 2) (by norm_num)
  obtain ⟨b, hbρ⟩ := mollifier_bdd ρ
  have hb0 : 0 ≤ b := (ρ.nonneg 0).trans (hbρ 0)
  set K : ℝ := Real.pi ^ D * (3 / 2 : ℝ) ^ (2 * D) * b with hK
  have hK0 : 0 ≤ K := by positivity
  set C : ℝ := C₀ * (K + 1) with hC
  have hCC₀ : C₀ ≤ C := by rw [hC]; nlinarith
  have hKC : K * C₀ ≤ C := by rw [hC]; nlinarith
  have hC1 : 1 ≤ C := hC₀.trans hCC₀
  refine ⟨C, min (min (Real.exp (-ℓ₀)) (Real.exp (-Real.exp 1))) (1 / 8),
    fun t => RegularChartScaling.extT S (3 / 2) u (C * Real.log (Real.log (1 / t))), hC1,
    lt_min (lt_min (Real.exp_pos _) (Real.exp_pos _)) (by norm_num),
    (min_le_left _ _).trans (min_le_right _ _), min_le_right _ _, fun t ht htt => ?_⟩
  beta_reduce
  have ht₁ : t ≤ Real.exp (-ℓ₀) := htt.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hℓ₀ : ℓ₀ ≤ Real.log (1 / t) := by
    have h1 : Real.log t ≤ -ℓ₀ := by
      have := Real.log_le_log ht ht₁
      rwa [Real.log_exp] at this
    rw [one_div, Real.log_inv]; linarith
  obtain ⟨he, hCt, hz⟩ := hosc t ht hℓ₀
  set ℓ := Real.log (1 / t) with hℓ
  have hlℓ : 1 ≤ Real.log ℓ := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) he
  have hℓ0 : 0 < ℓ := (Real.exp_pos 1).trans_le he
  set κ : ℝ := C * Real.log ℓ with hκ
  obtain ⟨w, hwe, hW1, hW2, hW3⟩ := RegularChartScaling.ext_exists S (R := 3 / 2) (by norm_num) hC₅ hc hp hub κ
  rw [← hwe]
  have hwu : ∀ x ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S, u x ≤ w x :=
    fun x hx => by rw [hW2 x hx]; exact le_max_left _ _
  have ht2 : 2 * t ≤ 1 / 8 := by linarith
  obtain ⟨-, hsm, hps, hbd⟩ := (ReciprocityTheory.AnForm.A.mollify_thm D ρ _ w isOpen_ball hW1).1 t ht
  have hsh : ball (0 : Fin D → ℂ) (5 / 4) ⊆ ReciprocityTheory.AnForm.A.shrink (ball (0 : Fin D → ℂ) (3 / 2)) t :=
    fun z hz' => RegularChartScaling.closedBall_sub_of hz' (by linarith)
  have hsm' := hsm.mono hsh
  refine ⟨fun z hz' => by rw [neg_mul]; exact hW2 z hz', hsm', ?_, ?_, ?_⟩
  · exact (ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm D _ _ isOpen_ball
      (hsm'.of_le (by norm_cast))).1 (RegularChartScaling.isPsh_mono hps hsh)
  · intro z hz'
    have hzB : z ∈ ball (0 : Fin D → ℂ) (3 / 2) :=
      ball_subset_ball (by norm_num) hz'.1
    exact (hwu z ⟨hzB, hz'.2⟩).trans (hbd z (hsh hz'.1)).1
  · intro z hzB
    obtain ⟨h16, hgap⟩ := hz z hzB
    have hsubR : ∀ s, s ≤ 1 / 4 → closedBall z s ⊆ ball 0 (3 / 2) := fun s hs =>
      RegularChartScaling.closedBall_sub_of hzB (by linarith)
    have hs16 : 0 < t / (8 * 2) := by positivity
    have hmono : ∀ s s', 0 < s → s ≤ s' → s' ≤ 1 / 4 →
        RegularChartScaling.pmoff S u z s ≤ RegularChartScaling.pmoff S u z s' := fun s s' h0 h1 h2 =>
      RegularChartScaling.pmo_mono hub h0 h1 (hsubR s' h2)
    have hκ' : -κ ≤ RegularChartScaling.pmoff S u z (t / (8 * 2)) := by
      have : C₀ * Real.log ℓ ≤ κ :=
        mul_le_mul_of_nonneg_right hCC₀ (by linarith)
      linarith
    have hlow : ∀ s, t / (8 * 2) ≤ s → s ≤ 1 / 4 → -κ ≤ RegularChartScaling.pmoff S u z s :=
      fun s h1 h2 => hκ'.trans (hmono _ _ hs16 h1 h2)
    have hPM : ∀ s, t / (8 * 2) ≤ s → s ≤ 1 / 8 →
        ReciprocityTheory.AnForm.A.polyMax w z s ≤ RegularChartScaling.pmoff S u z s := fun s h1 h2 => by
      have := polyMax_le_pmoff_same hub hW1 hW3 (hs16.trans_le h1)
        (by linarith : s < 1 / 4) (hsubR _ le_rfl)
      rwa [max_eq_left (hlow s h1 (by linarith))] at this
    have hMP : ∀ s, 0 < s → s ≤ 1 / 4 →
        RegularChartScaling.pmoff S u z s ≤ ReciprocityTheory.AnForm.A.polyMax w z s := fun s h0 h1 =>
      RegularChartScaling.pmo_le_polyMax hW1.1 hwu h0 (hsubR s h1)
    obtain ⟨-, hmp⟩ := hbd z (hsh hzB)
    have hlb := GroundTheory.Heights₂.Heights.Regular.MollifiedLowerBound.closed D ρ b _ w z t isOpen_ball hW1 ht
      (hsubR _ (by linarith)) hbρ
    have ht16 : t ≤ 1 / 16 := by linarith
    have hA := hPM (2 * t) (by rw [div_le_iff₀ (by norm_num)]; linarith) ht2
    have hB : RegularChartScaling.pmoff S u z (t / (4 * 2)) ≤ ReciprocityTheory.AnForm.A.polyMax w z (t / 4) :=
      (hmono _ _ (by positivity) (by linarith) (by linarith)).trans
        (hMP _ (by positivity) (by linarith))
    have hPA : RegularChartScaling.pmoff S u z t ≤ ReciprocityTheory.AnForm.A.polyMax w z (2 * t) :=
      (hmono _ _ ht (by linarith) (by linarith)).trans (hMP _ (by positivity) (by linarith))
    have hP2 := hMP (2 * t) (by positivity) (by linarith)
    have hq : 0 ≤ Real.log ℓ / ℓ := div_nonneg (by linarith) hℓ0.le
    have heps : K * epsT C₀ t ≤ epsT C t := by
      simp only [epsT, ← hℓ, mul_div_assoc]
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hKC hq
    have hgap' : ReciprocityTheory.AnForm.A.polyMax w z (2 * t) - ReciprocityTheory.AnForm.A.polyMax w z (t / 4) ≤
        epsT C₀ t := by linarith
    have hKg := mul_le_mul_of_nonneg_left hgap' hK0
    have hup := hPM t (by rw [div_le_iff₀ (by norm_num)]; linarith) (by linarith)
    show -C * Real.log ℓ ≤ RegularChartScaling.pmoff S u z t ∧
      RegularChartScaling.pmoff S u z t - epsT C t ≤ _ ∧ _ ≤ RegularChartScaling.pmoff S u z t
    refine ⟨?_, ?_, hmp.trans hup⟩
    · rw [neg_mul]
      exact hlow t (by rw [div_le_iff₀ (by norm_num)]; linarith) (by linarith)
    · linarith

end

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MollifyConvergesC2Rate
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem mollify_converges_C2_rate :
    ∀ (D : ℕ) (ρ : ReciprocityTheory.AnForm.A.Mollifier D) (V K : Set (Fin D → ℂ)) (u : (Fin D → ℂ) → ℝ) (w : ℝ → (Fin D → ℂ) → ℝ), IsOpen V → IsCompact K → K ⊆ V → ContDiffOn ℝ ∞ u V → (∀ᶠ t in 𝓝[>] (0 : ℝ), Set.EqOn (w t) u V) → TendstoUniformlyOn (fun t => ReciprocityTheory.AnForm.A.molli ρ t (w t)) (u) (𝓝[>] 0) K ∧ TendstoUniformlyOn (fun t => fderiv ℝ (ReciprocityTheory.AnForm.A.molli ρ t (w t))) (fderiv ℝ (u)) (𝓝[>] 0) K ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (ReciprocityTheory.AnForm.A.molli ρ t (w t)))) (fderiv ℝ (fderiv ℝ (u))) (𝓝[>] 0) K ∧ ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K, ‖fderiv ℝ (ReciprocityTheory.AnForm.A.molli ρ t (w t)) z - fderiv ℝ (u) z‖ ≤ M * t := by
  intro D ρ V K u w hV hK hKV hu hw
  obtain ⟨C, ε₀, hε₀, hC⟩ := ReciprocityTheory.AnForm.A.mollification_second_order D ρ V K u hV
    (by exact_mod_cast contDiffOn_infty.1 hu 3) hK hKV
  have hsmallt : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < ε₀ / 2 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by positivity))
  have key : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K,
      |ReciprocityTheory.AnForm.A.molli ρ t (w t) z - u z| ≤ C * t ∧
      ‖fderiv ℝ (ReciprocityTheory.AnForm.A.molli ρ t (w t)) z - fderiv ℝ u z‖ ≤ C * t ∧
      ‖fderiv ℝ (fderiv ℝ (ReciprocityTheory.AnForm.A.molli ρ t (w t))) z - fderiv ℝ (fderiv ℝ u) z‖
        ≤ C * t := by
    filter_upwards [self_mem_nhdsWithin, hsmallt, hw] with t ht htε hwt z hz
    have ht0 : 0 < t := ht
    have hz2 : z ∈ ReciprocityTheory.AnForm.A.shrink V (2 * t) :=
      (hC (2 * t) (by linarith) (by linarith) z hz).1
    obtain ⟨-, h0, h1, h2⟩ := hC t ht0 (by linarith) z hz
    have hev : ReciprocityTheory.AnForm.A.molli ρ t (w t) =ᶠ[𝓝 z] ReciprocityTheory.AnForm.A.molli ρ t u := by
      filter_upwards [ball_mem_nhds z ht0] with y hy
      refine ReciprocityTheory.AnForm.A.molli_congr ρ ht0 (U := V) ?_ hwt
      intro x hx
      apply hz2
      rw [mem_closedBall] at hx ⊢
      rw [mem_ball] at hy
      linarith [dist_triangle x y z]
    rw [hev.eq_of_nhds, hev.fderiv_eq, hev.fderiv.fderiv_eq]
    exact ⟨h0, h1, h2⟩
  have hsmall : ∀ δ : ℝ, 0 < δ → ∀ᶠ t in 𝓝[>] (0 : ℝ), C * t < δ := by
    intro δ hδ
    have h : Tendsto (fun t : ℝ => C * t) (𝓝[>] 0) (𝓝 0) := by
      have h' : Tendsto (fun t : ℝ => C * t) (𝓝 0) (𝓝 (C * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at h'
      exact h'.mono_left nhdsWithin_le_nhds
    exact h.eventually (Iio_mem_nhds hδ)
  refine ⟨?_, ?_, ?_, C, key.mono fun t ht z hz => (ht z hz).2.1⟩
  · rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    filter_upwards [key, hsmall δ hδ] with t ht htδ z hz
    rw [dist_comm, Real.dist_eq]
    exact lt_of_le_of_lt (ht z hz).1 htδ
  · rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    filter_upwards [key, hsmall δ hδ] with t ht htδ z hz
    rw [dist_comm, dist_eq_norm]
    exact lt_of_le_of_lt (ht z hz).2.1 htδ
  · rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    filter_upwards [key, hsmall δ hδ] with t ht htδ z hz
    rw [dist_comm, dist_eq_norm]
    exact lt_of_le_of_lt (ht z hz).2.2 htδ

end GlobalTheory.CompanionTheory.Ar.Giv
end

