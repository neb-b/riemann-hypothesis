module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PRiemannExtensionSlices
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ContDiffAtSmoothOnProj
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0006
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0008

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.ProdEqZeroIffCoordDiv
section
open Filter Topology Metric
open scoped ContDiff
open ReciprocityTheory.AnForm.A (coordDiv)

namespace LevelTowerAlt

variable {n : ℕ}

theorem frequently_ne (c y : Fin n → ℂ) : ∃ᶠ y' in 𝓝 y, ∀ k, y' k ≠ c k := by
  have h : Dense (Set.pi Set.univ fun k : Fin n => ({c k}ᶜ : Set ℂ)) :=
    dense_pi Set.univ fun k _ => dense_compl_singleton (c k)
  exact (mem_closure_iff_frequently.1 (h y)).mono fun y' hy' k => hy' k (Set.mem_univ k)

theorem eq_of_eventually_ne {β : Type*} [TopologicalSpace β] [T2Space β] {f g : (Fin n → ℂ) → β} (c : Fin n → ℂ)
    {y : Fin n → ℂ} (hf : ContinuousAt f y) (hg : ContinuousAt g y)
    (h : ∀ᶠ y' in 𝓝 y, (∀ k, y' k ≠ c k) → f y' = g y') : f y = g y :=
  tendsto_nhds_unique_of_frequently_eq hf hg (((frequently_ne c y).and_eventually h).mono fun _ h' => h'.2 h'.1)

theorem exists_div_coord {f : (Fin n → ℂ) → ℂ} {y₀ : Fin n → ℂ} (hf : AnalyticAt ℂ f y₀) (S : Finset (Fin n))
    (hz : ∀ᶠ y in 𝓝 y₀, y ∈ coordDiv S → f y = 0) :
    ∃ u : (Fin n → ℂ) → ℂ, AnalyticAt ℂ u y₀ ∧ ∀ᶠ y in 𝓝 y₀, f y = u y * ∏ i ∈ S, y i := by
  classical
  have hne : ∀ᶠ y in 𝓝 y₀, ∀ i, y₀ i ≠ 0 → y i ≠ 0 := by
    refine Filter.eventually_all.2 fun i => ?_
    by_cases h : y₀ i = 0
    · exact Filter.Eventually.of_forall fun _ h' => absurd h h'
    · exact ((continuous_apply i).continuousAt.eventually_ne h).mono fun _ h' _ => h'
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.1 (hf.eventually_analyticAt.and (hz.and hne))
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  let A : (Fin n → ℂ) → Fin n → ℂ := fun z => y₀ + (r : ℂ) • z
  have hAd : Differentiable ℂ A := (differentiable_const _).add (differentiable_id.const_smul (r : ℂ))
  have hA : ∀ z ∈ ball (0 : Fin n → ℂ) 1, A z ∈ ball y₀ r := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    rw [mem_ball_iff_norm, add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_of_nonneg hr.le]
    nlinarith
  have hkey : ∀ z ∈ ball (0 : Fin n → ℂ) 1, ∀ i, (y₀ i = 0 → z i ≠ 0) → A z i ≠ 0 := by
    intro z hz i hi
    by_cases h : y₀ i = 0
    · show y₀ i + (r : ℂ) * z i ≠ 0
      rw [h, zero_add]
      exact mul_ne_zero hr' (hi h)
    · exact (hb _ (hA z hz)).2.2 i h
  have hAa : ∀ z, AnalyticAt ℂ A z := fun z => by
    have h1 : AnalyticAt ℂ ((fun _ : Fin n → ℂ => (r : ℂ)) • id) z := analyticAt_const.smul analyticAt_id
    exact analyticAt_const.add h1
  have hpd : ∀ z, AnalyticAt ℂ (fun z => ∏ i ∈ S, A z i) z := fun z =>
    Finset.analyticAt_fun_prod (𝕜 := ℂ) S (f := fun i z => A z i) fun i _ => analyticAt_pi_iff.1 (hAa z) i
  obtain ⟨G, hG, hGe⟩ := GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices.proof n
    (fun z => f (A z) / ∏ i ∈ S, A z i)
    (fun z hz => (AnalyticAt.fun_div (f := fun z => f (A z)) (g := fun z => ∏ i ∈ S, A z i)
      (AnalyticAt.comp (g := f) (f := A) (hb _ (hA z hz.1)).1 (hAa z)) (hpd z)
      (Finset.prod_ne_zero_iff.2 fun i _ => hkey z hz.1 i fun _ => hz.2 i)).differentiableAt.differentiableWithinAt)
    (by
      intro z hz i hi
      have h0 : Function.update z i 0 ∈ ball (0 : Fin n → ℂ) 1 := by
        rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos] at hz ⊢
        intro k
        by_cases hk : k = i
        · subst hk
          simp
        · rw [Function.update_of_ne hk]
          exact hz k
      have hud : DifferentiableAt ℂ (Function.update z i) (0 : ℂ) := (hasFDerivAt_update z (0 : ℂ)).differentiableAt
      have hφ : DifferentiableAt ℂ (fun x : ℂ => f (A (Function.update z i x))) 0 :=
        DifferentiableAt.comp (g := fun w => f (A w)) 0
          ((hb _ (hA _ h0)).1.differentiableAt.comp _ (hAd _)) hud
      by_cases hc : i ∈ S ∧ y₀ i = 0
      · have hφ0 : f (A (Function.update z i 0)) = 0 :=
          (hb _ (hA _ h0)).2.1 ⟨i, hc.1, by simp [A, hc.2]⟩
        refine ⟨_, ((hasDerivAt_iff_tendsto_slope.1 hφ.hasDerivAt).div_const
          ((r : ℂ) * ∏ k ∈ S.erase i, A z k)).congr fun x => ?_⟩
        have h1 : ∏ k ∈ S.erase i, A (Function.update z i x) k = ∏ k ∈ S.erase i, A z k :=
          Finset.prod_congr rfl fun k hk => by
            simp only [A, Pi.add_apply, Pi.smul_apply, Function.update_of_ne (Finset.ne_of_mem_erase hk)]
        have h2 : A (Function.update z i x) i = r * x := by simp [A, hc.2]
        rw [← Finset.mul_prod_erase S _ hc.1, h1, h2, slope_def_field, hφ0, sub_zero, sub_zero, div_div]
        congr 1
        ring
      · refine ⟨_, tendsto_nhdsWithin_of_tendsto_nhds (ContinuousAt.tendsto
          (hφ.continuousAt.div ((hpd _).continuousAt.comp hud.continuousAt) ?_))⟩
        refine Finset.prod_ne_zero_iff.2 fun k hk => hkey _ h0 k fun h => ?_
        have hki : k ≠ i := fun e => hc ⟨e ▸ hk, e ▸ h⟩
        rw [Function.update_of_ne hki]
        exact hi k hki)
  let B : (Fin n → ℂ) → Fin n → ℂ := fun y => (r : ℂ)⁻¹ • (y - y₀)
  have hBa : ∀ y, AnalyticAt ℂ B y := fun y => by
    have h1 : AnalyticAt ℂ ((fun _ : Fin n → ℂ => (r : ℂ)⁻¹) • (id - fun _ : Fin n → ℂ => y₀)) y :=
      analyticAt_const.smul (analyticAt_id.sub analyticAt_const)
    exact h1
  have hAB : ∀ y, A (B y) = y := fun y => by
    simp only [A, B, smul_smul, mul_inv_cancel₀ hr', one_smul, add_sub_cancel]
  have hB : ∀ y ∈ ball y₀ r, B y ∈ ball (0 : Fin n → ℂ) 1 := by
    intro y hy
    rw [mem_ball_iff_norm] at hy
    rw [mem_ball_zero_iff, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr.le, inv_mul_lt_iff₀ hr,
      mul_one]
    exact hy
  have hu : ∀ y ∈ ball y₀ r, AnalyticAt ℂ (fun y => G (B y)) y := fun y hy =>
    AnalyticAt.comp (g := G) (f := B) (hG _ (hB y hy)) (hBa y)
  refine ⟨fun y => G (B y), hu _ (mem_ball_self hr), ?_⟩
  filter_upwards [ball_mem_nhds y₀ hr] with y hy
  refine eq_of_eventually_ne (f := f) (g := fun y => G (B y) * ∏ i ∈ S, y i) y₀ (hb y hy).1.continuousAt
    ((hu y hy).continuousAt.mul (continuous_finsetProd _ fun i _ => continuous_apply i).continuousAt) ?_
  filter_upwards [isOpen_ball.mem_nhds hy] with y' hy' hne'
  have h1 : ∀ i, B y' i ≠ 0 := fun i => mul_ne_zero (inv_ne_zero hr') (sub_ne_zero.2 (hne' i))
  have h2 : ∏ i ∈ S, y' i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => by
    have := hkey _ (hB y' hy') i fun _ => h1 i
    rwa [hAB] at this
  rw [hGe _ (hB y' hy') h1, hAB, div_mul_cancel₀ _ h2]

theorem prod_eq_zero_iff_coordDiv (S : Finset (Fin n)) (y : Fin n → ℂ) : ∏ i ∈ S, y i = 0 ↔ y ∈ coordDiv S :=
  Finset.prod_eq_zero_iff

theorem sum_log_eq (S : Finset (Fin n)) {y : Fin n → ℂ} (hy : y ∉ coordDiv S) :
    ∑ i ∈ S, Real.log (‖y i‖ ^ 2)⁻¹ = -2 * Real.log ‖∏ i ∈ S, y i‖ := by
  rw [norm_prod, Real.log_prod fun i hi => norm_ne_zero_iff.2 fun h => hy ⟨i, hi, h⟩, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.log_inv, Real.log_pow]
  push_cast
  ring

theorem exists_smooth_log_diff {Φ : (Fin n → ℂ) → Fin n → ℂ} {y₀ : Fin n → ℂ} (hΦ : AnalyticAt ℂ Φ y₀)
    {U : Set (Fin n → ℂ)} (hU : U ∈ 𝓝 y₀) (hinj : Set.InjOn Φ U) {S S' : Finset (Fin n)}
    (h : ∀ᶠ y in 𝓝 y₀, y ∈ coordDiv S ↔ Φ y ∈ coordDiv S') :
    ∃ q : (Fin n → ℂ) → ℝ, ContDiffAt ℝ ∞ q y₀ ∧ ∀ᶠ y in 𝓝 y₀, y ∉ coordDiv S →
      ∑ i ∈ S', Real.log (‖Φ y i‖ ^ 2)⁻¹ = ∑ i ∈ S, Real.log (‖y i‖ ^ 2)⁻¹ + q y := by
  obtain ⟨g, hga, hg0, hgr, hgl, -⟩ := exists_local_inverse hΦ hU hinj
  obtain ⟨u, hu, hue⟩ := exists_div_coord (f := fun y => ∏ i ∈ S', Φ y i)
    (Finset.analyticAt_fun_prod _ fun i _ => analyticAt_pi_iff.1 hΦ i) S
    (h.mono fun y hy hS => (prod_eq_zero_iff_coordDiv _ _).2 (hy.1 hS))
  have hgt : Tendsto g (𝓝 (Φ y₀)) (𝓝 y₀) := by
    have := hga.continuousAt.tendsto
    rwa [hg0] at this
  obtain ⟨v, hv, hve⟩ := exists_div_coord (f := fun x => ∏ i ∈ S, g x i)
    (Finset.analyticAt_fun_prod _ fun i _ => analyticAt_pi_iff.1 hga i) S'
    (by
      filter_upwards [hgt.eventually h, hgr] with x h1 h2 h3
      rw [h2] at h1
      exact (prod_eq_zero_iff_coordDiv _ _).2 (h1.2 h3))
  have h1 : v (Φ y₀) * u y₀ = 1 := by
    refine eq_of_eventually_ne (f := fun y => v (Φ y) * u y) (g := fun _ => 1) 0
      ((hv.continuousAt.comp hΦ.continuousAt).mul hu.continuousAt) continuousAt_const ?_
    filter_upwards [hue, hΦ.continuousAt.tendsto.eventually hve, hgl] with y e1 e2 e3 hy
    rw [e3, e1, ← mul_assoc] at e2
    have hp : ∏ i ∈ S, y i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hy i
    exact mul_right_cancel₀ hp (by rw [← e2, one_mul])
  have hu0 : u y₀ ≠ 0 := right_ne_zero_of_mul_eq_one h1
  have huR : AnalyticAt ℝ u y₀ := hu.restrictScalars
  refine ⟨fun y => -2 * Real.log ‖u y‖, contDiffAt_const.mul
    ((huR.contDiffAt.norm ℝ hu0).log (norm_ne_zero_iff.2 hu0)), ?_⟩
  filter_upwards [h, hue, hu.continuousAt.eventually_ne hu0] with y e1 e2 e3 hy
  have hp : ∏ i ∈ S, y i ≠ 0 := fun h0 => hy ((prod_eq_zero_iff_coordDiv _ _).1 h0)
  rw [sum_log_eq S' fun h' => hy (e1.2 h'), sum_log_eq S hy, e2, norm_mul,
    Real.log_mul (norm_ne_zero_iff.2 e3) (norm_ne_zero_iff.2 hp)]
  ring

theorem exists_smooth_glue {U : Set (Fin n → ℂ)} (hU : IsOpen U) (S : Finset (Fin n)) (E : (Fin n → ℂ) → ℝ)
    (h : ∀ y₀ ∈ U, ∃ q : (Fin n → ℂ) → ℝ, ContDiffAt ℝ ∞ q y₀ ∧ ∀ᶠ y in 𝓝 y₀, y ∉ coordDiv S → E y = q y) :
    ∃ f : (Fin n → ℂ) → ℝ, ContDiffOn ℝ ∞ f U ∧ ∀ y ∈ U, y ∉ coordDiv S → E y = f y := by
  choose! q hq hqe using h
  refine ⟨fun y => q y y, fun y₀ hy₀ => ((hq y₀ hy₀).congr_of_eventuallyEq ?_).contDiffWithinAt,
    fun y hy => (hqe y hy).self_of_nhds⟩
  have hc : ∀ᶠ y in 𝓝 y₀, ContinuousAt (q y₀) y :=
    (((hq y₀ hy₀).of_le (m := 1) (by exact_mod_cast le_top)).eventually (by simp)).mono fun _ h => h.continuousAt
  filter_upwards [hU.mem_nhds hy₀, hc, (hqe y₀ hy₀).eventually_nhds] with y hy h1 h2
  refine eq_of_eventually_ne (f := q y) (g := q y₀) 0 (hq y hy).continuousAt h1 ?_
  filter_upwards [h2, hqe y hy] with y' e1 e2 hy'
  have hn : y' ∉ coordDiv S := fun ⟨i, _, hi⟩ => hy' i hi
  rw [← e1 hn, ← e2 hn]

end LevelTowerAlt
end

-- bundled from Development.WeilBound.CoreStatements.PlurisubharmonicCones.TiedRegularizationAsymptotic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace LevelTowerAlt

section

open GroundTheory.Heights₂.Heights.Regular (PotentialCharts contDiffAt_comp_symm_of_smoothOn)

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ]
  {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : Ψ → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  (D : ComponentData II Ψ K J Ω W) (M : XModel D)

theorem eventually_mem (a : Fin D.nCharts) {t : Fin D.n → ℂ} (ht : t ∈ Metric.ball (0 : Fin D.n → ℂ) 1) :
    ∀ᶠ s : Fin D.n → ℂ in 𝓝 t, (D.chart a).γ s ∈ mcPts (mCoordIdeal D.y) := by
  filter_upwards [Metric.isOpen_ball.mem_nhds ht] with s hs using (D.chart a).mem s hs

theorem levi_chartFun_gen (P : PotentialCharts M.atlas) (ref : HermLine J) (hth : ThRef M ref P.th)
    {φ : M.Xc → ℝ} (hφ : M.atlas.Smooth φ) {g : (Fin D.n → ℂ) → (Σ k, J k) → ℂ} {t : Fin D.n → ℂ}
    (hg : AnalyticAt ℂ g t) (hm : ∀ᶠ s in 𝓝 t, g s ∈ mcPts (mCoordIdeal D.y)) (k : Fin P.N)
    (hk : M.proj (g t) ∈ (P.chart k).source) (v : Fin D.n → ℂ) :
    levi (fun s => Real.log (ref.h (g s)) + φ (M.proj (g s))) t v =
      levi (P.chartFun φ k) (P.chart k (M.proj (g t))) (fderiv ℂ (fun s => P.chart k (M.proj (g s))) t v) := by
  classical
  set y0 := M.proj (g t) with hy0
  obtain ⟨U, hUo, hyU, hUth, s, hs, hsholo, G1, hG1, hG1eq⟩ := hth y0 y0 (P.th.mem_U y0)
  obtain ⟨W', hWo, hyW, G2, hG2, hG2eq⟩ := P.q_th k y0 y0 ⟨P.th.mem_U y0, hk⟩
  set F : (Fin D.n → ℂ) → Fin D.n → ℂ := fun s' => P.chart k (M.proj (g s')) with hF
  have hFan : AnalyticAt ℂ F t := analyticAt_proj D M (P.compat k) hg hm hk
  have hpc : ContinuousAt (fun s' => M.proj (g s')) t := continuousAt_proj M hg.continuousAt hm
  have hev_set : ∀ᶠ s' in 𝓝 t, M.proj (g s') ∈ U ∩ W' ∩ P.th.U y0 ∩ (P.chart k).source :=
    hpc.preimage_mem_nhds (IsOpen.mem_nhds (((hUo.inter hWo).inter (P.th.isOpen_U y0)).inter (P.chart k).open_source)
      ⟨⟨⟨hyU, hyW⟩, P.th.mem_U y0⟩, hk⟩)
  have hsan : ∀ p, AnalyticAt ℂ (fun s' => s (M.proj (g s')) p) t := fun p =>
    analyticAt_holoOn_proj D M (hsholo p) hg hm hyU
  have hgan : ∀ p, AnalyticAt ℂ (fun s' => g s' p) t := fun p =>
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) p).analyticAt _).comp hg
  have hs0 := (hs y0 hyU).1
  choose i hi using hs0.1
  have hgt := (M.fibre (s y0) hs0 (g t) hm.self_of_nhds).1 (hs y0 hyU).2
  obtain ⟨c0, hc0, hgt_eq⟩ := hgt
  set c : (Fin D.n → ℂ) → K → ℂ := fun s' k' => g s' ⟨k', i k'⟩ / s (M.proj (g s')) ⟨k', i k'⟩ with hc
  have hct : ∀ k', c t k' = c0 k' := by
    intro k'
    show g t ⟨k', i k'⟩ / s y0 ⟨k', i k'⟩ = c0 k'
    rw [hgt_eq]
    simp only [torusSmul]
    field_simp [hi k']
  have hcan : ∀ k', AnalyticAt ℂ (fun s' => c s' k') t := fun k' => (hgan _).div (hsan _) (hi k')
  have hden : ∀ᶠ s' in 𝓝 t, ∀ k', s (M.proj (g s')) ⟨k', i k'⟩ ≠ 0 := by
    rw [Filter.eventually_all]
    intro k'
    exact (hsan _).continuousAt.eventually_ne (hi k')
  have hslit : ∀ᶠ s' in 𝓝 t, ∀ k', c s' k' / c t k' ∈ Complex.slitPlane := by
    rw [Filter.eventually_all]
    intro k'
    have hcont : ContinuousAt (fun s' => c s' k' / c t k') t := (AnalyticAt.div_const (hcan k') : AnalyticAt ℂ (fun s' => c s' k' / c t k') t).continuousAt
    have h1 : c t k' / c t k' ∈ Complex.slitPlane := by
      rw [div_self (by rw [hct]; exact hc0 k')]; exact Complex.one_mem_slitPlane
    exact hcont.preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds h1)
  set G : (Fin D.n → ℂ) → ℂ := fun s' => ∑ k', (ref.a k' : ℂ) * (Complex.log (c s' k' / c t k') + (Real.log ‖c t k'‖ : ℂ)) - G1 (M.proj (g s')) - G2 (M.proj (g s')) with hG
  have hGan : AnalyticAt ℂ G t := by
    have hsum : AnalyticAt ℂ (fun s' => ∑ k', (ref.a k' : ℂ) * (Complex.log (c s' k' / c t k') + (Real.log ‖c t k'‖ : ℂ))) t := by
      have hs' := Finset.analyticAt_sum (𝕜 := ℂ) (c := t)
        (f := fun k' (s' : Fin D.n → ℂ) => (ref.a k' : ℂ) * (Complex.log (c s' k' / c t k') + (Real.log ‖c t k'‖ : ℂ)))
        Finset.univ (fun k' _ => analyticAt_const.mul
          ((AnalyticAt.clog (AnalyticAt.div_const (hcan k')) (hslit.self_of_nhds k')).add analyticAt_const))
      convert hs' using 1
      funext s'
      simp [Finset.sum_apply]
    exact (hsum.sub (analyticAt_holoOn_proj D M hG1 hg hm hyU)).sub (analyticAt_holoOn_proj D M hG2 hg hm hyW)
  have hq : ContDiffAt ℝ 2 (P.chartFun φ k) (F t) := by
    have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (P.q k) (F t) :=
      (P.q_smooth k).contDiffAt ((P.chart k).open_target.mem_nhds ((P.chart k).map_source hk))
    have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ ∘ (P.chart k).symm) (F t) :=
      GroundTheory.Heights₂.Heights.Regular.contDiffAt_comp_symm_of_smoothOn (P.compat k) isOpen_univ hφ (Set.mem_univ _) hk
    exact (h1.add h2).of_le (WithTop.coe_le_coe.mpr (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤))
  have hcomp : ContDiffAt ℝ 2 (P.chartFun φ k ∘ F) t :=
    hq.comp t (hFan.contDiffAt.restrict_scalars ℝ)
  have hev : ∀ᶠ s' in 𝓝 t, Real.log (ref.h (g s')) + φ (M.proj (g s')) = (P.chartFun φ k ∘ F) s' + (G s').re := by
    filter_upwards [hev_set, hden, hm] with s' hset hd hms
    have hsz := hs _ hset.1.1.1
    obtain ⟨c', hc', hgeq⟩ := (M.fibre (s (M.proj (g s'))) hsz.1 (g s') hms).1 hsz.2
    have hcc : ∀ k', c s' k' = c' k' := fun k' => by
      have h := congrFun hgeq ⟨k', i k'⟩
      simp only [torusSmul] at h
      show g s' ⟨k', i k'⟩ / s (M.proj (g s')) ⟨k', i k'⟩ = c' k'
      rw [h]
      field_simp [hd k']
    have hlog := log_h_smul ref hsz.1.1 hc'
    rw [← hgeq] at hlog
    have e1 := hG1eq _ hset.1.1.1
    have e2 := hG2eq _ ⟨⟨hset.1.1.2, hset.1.2⟩, hset.2⟩
    have hsum : (∑ k', (ref.a k' : ℂ) * (Complex.log (c s' k' / c t k') + (Real.log ‖c t k'‖ : ℂ))).re =
        ∑ k', (ref.a k' : ℝ) * Real.log ‖c' k'‖ := by
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun k' _ => ?_
      rw [hcc, hct]
      simp only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.add_re, Complex.log_re,
        Complex.ofReal_re, zero_mul, sub_zero]
      rw [norm_div, Real.log_div (norm_ne_zero_iff.mpr (hc' k')) (norm_ne_zero_iff.mpr (hc0 k'))]
      ring
    have hch : (P.chartFun φ k ∘ F) s' = P.q k (F s') + φ (M.proj (g s')) := by
      simp only [Function.comp, GroundTheory.Heights₂.Heights.Regular.PotentialCharts.chartFun, hF]
      rw [(P.chart k).left_inv hset.2]
    rw [hch, hG]
    simp only [Complex.sub_re]
    rw [hsum, hlog]
    simp only [hF]
    linarith
  rw [levi_add_re hcomp hGan hev v, ReciprocityTheory.AnForm.levi_comp v hFan hq]

theorem exists_deriv_bound (P : PotentialCharts M.atlas) (a : Fin D.nCharts) :
    ∃ C : ℝ, ∀ t ∈ Metric.closedBall (0 : Fin D.n → ℂ) (1 / 2), ∃ k, M.proj ((D.chart a).γ t) ∈ P.mid k ∧
      ‖fderiv ℂ (fun s : Fin D.n → ℂ => P.chart k (M.proj ((D.chart a).γ s))) t‖ ≤ C := by
  have hball : ∀ t ∈ Metric.closedBall (0 : Fin D.n → ℂ) (1 / 2), t ∈ Metric.ball (0 : Fin D.n → ℂ) 1 := by
    intro t ht
    rw [Metric.mem_closedBall] at ht
    rw [Metric.mem_ball]
    linarith
  have hcont : ContinuousOn (fun t : Fin D.n → ℂ => M.proj ((D.chart a).γ t)) (Metric.closedBall 0 (1 / 2)) := by
    intro t ht
    have htb := hball t ht
    exact (continuousAt_proj M ((D.chart a).analytic t htb).continuousAt (eventually_mem D a htb)).continuousWithinAt
  have hk : ∀ k : Fin P.N, ∃ C : ℝ, ∀ t ∈ Metric.closedBall (0 : Fin D.n → ℂ) (1 / 2) ∩
      (fun t : Fin D.n → ℂ => M.proj ((D.chart a).γ t)) ⁻¹' closure (P.inner k),
      ‖fderiv ℂ (fun s : Fin D.n → ℂ => P.chart k (M.proj ((D.chart a).γ s))) t‖ ≤ C := by
    intro k
    have hcl : IsClosed (Metric.closedBall (0 : Fin D.n → ℂ) (1 / 2) ∩
        (fun t : Fin D.n → ℂ => M.proj ((D.chart a).γ t)) ⁻¹' closure (P.inner k)) :=
      hcont.preimage_isClosed_of_isClosed Metric.isClosed_closedBall isClosed_closure
    have hcpt := (isCompact_closedBall (0 : Fin D.n → ℂ) (1 / 2)).of_isClosed_subset hcl Set.inter_subset_left
    apply hcpt.exists_bound_of_continuousOn
    intro t ht
    have htb := hball t ht.1
    have hsrc : M.proj ((D.chart a).γ t) ∈ (P.chart k).source :=
      P.mid_subset_source k (P.closure_inner k ht.2)
    have hF := analyticAt_proj D M (P.compat k) ((D.chart a).analytic t htb) (eventually_mem D a htb) hsrc
    exact hF.fderiv.continuousAt.continuousWithinAt
  choose C hC using hk
  refine ⟨∑ k, |C k|, fun t ht => ?_⟩
  obtain ⟨k, hk⟩ := P.cover (M.proj ((D.chart a).γ t))
  refine ⟨k, P.closure_inner k (subset_closure hk), ?_⟩
  calc ‖fderiv ℂ (fun s : Fin D.n → ℂ => P.chart k (M.proj ((D.chart a).γ s))) t‖ ≤ C k :=
        hC k t ⟨ht, subset_closure hk⟩
    _ ≤ |C k| := le_abs_self _
    _ ≤ ∑ k, |C k| := Finset.single_le_sum (fun j _ => abs_nonneg (C j)) (Finset.mem_univ k)

theorem eventually_closedBall_subset (P : PotentialCharts M.atlas) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ j, ∀ x ∈ closure (P.mid j),
      Metric.closedBall (P.chart j x) t ⊆ (P.chart j).target := by
  have hK : ∀ j, ∃ ε > (0 : ℝ), Metric.cthickening ε (P.chart j '' closure (P.mid j)) ⊆ (P.chart j).target := by
    intro j
    have hc : IsCompact (P.chart j '' closure (P.mid j)) :=
      (isClosed_closure.isCompact).image_of_continuousOn ((P.chart j).continuousOn.mono (P.closure_mid j))
    have hsub : P.chart j '' closure (P.mid j) ⊆ (P.chart j).target := by
      rintro _ ⟨x, hx, rfl⟩
      exact (P.chart j).map_source (P.closure_mid j hx)
    exact hc.exists_cthickening_subset_open (P.chart j).open_target hsub
  choose ε hε hsub using hK
  rw [Filter.eventually_all]
  intro j
  filter_upwards [Ioo_mem_nhdsGT (hε j)] with t ht x hx
  exact (Metric.closedBall_subset_cthickening (Set.mem_image_of_mem _ hx) t).trans
    ((Metric.cthickening_mono ht.2.le _).trans (hsub j))

end

theorem tied_regularization_asymptotic : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M : XModel D) (w : ((Σ k, J k) → ℂ) → ℝ) (S' : BoundedRegularisationSetting M D.Xo Hd.aMu w), S'.IsTied → ∀ δ > (0 : ℝ), ∀ᶠ t' in 𝓝[>] (0 : ℝ), ∀ a, ∀ t : Fin D.n → ℂ, ‖t‖ ≤ 1 / 2 → ∀ v, -(δ * ‖v‖ ^ 2) ≤ levi (fun s : Fin D.n → ℂ => Real.log (S'.ref.h ((D.chart a).γ s)) + S'.bregWeight t' (M.proj ((D.chart a).γ s))) t v := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M w S' hT δ hδ
  have hC := fun a => exists_deriv_bound D M S'.B.toPotentialCharts a
  choose C hC using hC
  set C0 : ℝ := ∑ a, |C a| with hC0
  have hC0nn : 0 ≤ C0 := Finset.sum_nonneg fun a _ => abs_nonneg _
  have hCle : ∀ a, C a ≤ C0 := fun a =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun a => |C a|) (fun a _ => abs_nonneg _) (Finset.mem_univ a))
  set Cη : ℝ := max S'.Cη 0 with hCη
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), 4 * Cη * S'.e1 t * C0 ^ 2 < δ := by
    have h0 : Tendsto (fun t => 4 * Cη * S'.e1 t * C0 ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (4 * Cη * 0 * C0 ^ 2)) :=
      ((hT.e1_tendsto_zero.const_mul (4 * Cη)).mul_const (C0 ^ 2))
    rw [mul_zero, zero_mul] at h0
    exact (tendsto_order.1 h0).2 δ hδ
  filter_upwards [self_mem_nhdsWithin, hT.compare, eventually_closedBall_subset D M S'.B.toPotentialCharts, hsmall]
    with t' ht' hcmp hball hsm
  have hε : 0 < S'.e1 t' := lt_of_lt_of_le ht' (S'.e1_ge t' ht')
  obtain ⟨hsmooth, hlev⟩ := GroundTheory.Heights₂.Heights.Regular.BoundedGlue.proof M.Xc D.n M.atlas S'.B S'.ρ S'.η S'.Cη t'
    (S'.e1 t') S'.cutoff ht' hε hball hcmp
  intro a t ht v
  have htb : t ∈ Metric.ball (0 : Fin D.n → ℂ) 1 := by
    rw [mem_ball_zero_iff]
    linarith
  obtain ⟨k, hk, hbd⟩ := hC a t (mem_closedBall_zero_iff.2 ht)
  have hl : levi (fun s : Fin D.n → ℂ => Real.log (S'.ref.h ((D.chart a).γ s)) + S'.bregWeight t' (M.proj ((D.chart a).γ s))) t v =
      levi (S'.B.toPotentialCharts.chartFun (S'.bregWeight t') k) (S'.B.toPotentialCharts.chart k (M.proj ((D.chart a).γ t)))
        (fderiv ℂ (fun s => S'.B.toPotentialCharts.chart k (M.proj ((D.chart a).γ s))) t v) :=
    levi_chartFun_gen D M S'.B.toPotentialCharts S'.ref S'.th_ref hsmooth ((D.chart a).analytic t htb)
      (eventually_mem D a htb) k (GroundTheory.Heights₂.Heights.Regular.PotentialCharts.mid_subset_source _ k hk) v
  rw [hl]
  set X := fderiv ℂ (fun s => S'.B.toPotentialCharts.chart k (M.proj ((D.chart a).γ s))) t v with hX
  have hlow := hlev k _ hk X
  have hXn : ‖X‖ ≤ C0 * ‖v‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hbd.trans (hCle a)) (norm_nonneg _))
  have hX2 : ‖X‖ ^ 2 ≤ C0 ^ 2 * ‖v‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hXn 2
  have hCη1 : S'.Cη ≤ Cη := le_max_left _ _
  have hCη0 : 0 ≤ Cη := le_max_right _ _
  have h1 : 4 * S'.Cη * S'.e1 t' * ‖X‖ ^ 2 ≤ 4 * Cη * S'.e1 t' * ‖X‖ ^ 2 := by
    gcongr
  have h2 : 4 * Cη * S'.e1 t' * ‖X‖ ^ 2 ≤ 4 * Cη * S'.e1 t' * (C0 ^ 2 * ‖v‖ ^ 2) := by
    gcongr
  have h3 : 4 * Cη * S'.e1 t' * (C0 ^ 2 * ‖v‖ ^ 2) ≤ δ * ‖v‖ ^ 2 := by
    rw [← _root_.mul_assoc]
    exact mul_le_mul_of_nonneg_right hsm.le (sq_nonneg _)
  have h4 : -(δ * ‖v‖ ^ 2) ≤ -(4 * S'.Cη * S'.e1 t') * ‖X‖ ^ 2 := by
    nlinarith
  exact h4.trans hlow

end LevelTowerAlt
end

