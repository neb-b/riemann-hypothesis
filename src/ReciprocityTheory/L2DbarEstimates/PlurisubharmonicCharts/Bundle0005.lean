module

public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxB
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0001
public import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FamilyLeCoords

@[expose] public section

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxC
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal

noncomputable section

theorem leviV_const_mul {n : ℕ} {f : V n → ℝ} {x : V n} (hf : ContDiffAt ℝ 2 f x) (c d : ℝ)
    (ξ : Fin n → ℂ) :
    leviV n (fun y => ((c * f y + d : ℝ) : ℂ)) x ξ = c * leviV n (fun y => ((f y : ℝ) : ℂ)) x ξ := by
  have hk : ContDiffAt ℝ 2 (fun t : ℝ => c * t + d) (f x) :=
    ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const)
  have h := leviChain n (fun t : ℝ => c * t + d) f x ξ hf hk
  have hd : deriv (fun t : ℝ => c * t + d) = fun _ => c := by
    funext t; rw [deriv_add_const, deriv_const_mul_field', deriv_id'']; ring
  rw [h, hd]; simp

theorem contDiffAt_two_of_holo {n : ℕ} {g : V n → ℂ} {U : Set (V n)} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) {v : V n} (hv : v ∈ U) : ContDiffAt ℂ 2 g v :=
  ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n g U hU hg).contDiffAt (hU.mem_nhds hv)).of_le (by norm_cast)

namespace WeightedAtlas

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)

end WeightedAtlas

end

end ReciprocityTheory.L2DbarEstimates.Y
end

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.APrimeB
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal

noncomputable section

set_option synthInstance.maxHeartbeats 100000 in
theorem aprb_complement {n d : ℕ} (Lm : V n →L[ℂ] V d) (hs : Function.Surjective Lm) :
    ∃ A : V n ≃L[ℂ] V d × V (n - d), ∀ v, (A v).1 = Lm v := by
  classical
  let K := LinearMap.ker (Lm : V n →ₗ[ℂ] V d)
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl K
  let P : V n →ₗ[ℂ] K := Submodule.linearProjOfIsCompl K C hC
  have hrank : Module.finrank ℂ (V d) + Module.finrank ℂ K = Module.finrank ℂ (V n) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (Lm : V n →ₗ[ℂ] V d)
    rwa [LinearMap.range_eq_top.mpr hs, finrank_top] at h1
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hrank
  have hK : Module.finrank ℂ K = n - d := by omega
  let eK : K ≃ₗ[ℂ] V (n - d) := LinearEquiv.ofFinrankEq K (V (n - d)) (by rw [hK]; simp)
  let T : V n →ₗ[ℂ] V d × V (n - d) := LinearMap.prod (Lm : V n →ₗ[ℂ] V d) (eK.toLinearMap ∘ₗ P)
  have hT : Function.Injective T := by
    refine LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr fun v hv => ?_)
    have h1 : Lm v = 0 := by simpa [T] using congrArg Prod.fst hv
    have h2 : P v = 0 := by simpa [T] using congrArg Prod.snd hv
    have hvK : v ∈ K := by simpa [K] using h1
    have h3 := Submodule.linearProjOfIsCompl_apply_left hC ⟨v, hvK⟩
    have h4 : (⟨v, hvK⟩ : K) = 0 := h3.symm.trans h2
    simpa using congrArg Subtype.val h4
  have hdim : Module.finrank ℂ (V n) = Module.finrank ℂ (V d × V (n - d)) := by
    simp only [Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin]
    omega
  refine ⟨(LinearMap.linearEquivOfInjective T hT hdim).toContinuousLinearEquiv, fun v => ?_⟩
  rfl

theorem aprb_contDiffOn {n d : ℕ} {U : Set (V n)} (hU : IsOpen U) {p : V n → V d}
    (hp : DifferentiableOn ℂ p U) (k : ℕ) : ContDiffOn ℂ k p U := by
  rw [contDiffOn_euclidean]
  intro i
  have h1 : DifferentiableOn ℂ (fun x => p x i) U :=
    (EuclideanSpace.proj i : V d →L[ℂ] ℂ).differentiable.comp_differentiableOn hp
  exact (contDiffOn_of_differentiableOn n _ U hU h1).of_le (by exact_mod_cast le_top)

end

end ReciprocityTheory.L2DbarEstimates.Y
end

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.APrimeI
section
namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal

noncomputable section

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

theorem ap_lintegral_chart (A : WeightedAtlas n Y ι La) (i : ι) (g : Y → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y in (A.chart i).source, g y ∂A.mu =
      ∫⁻ v in (A.chart i).target, g ((A.chart i).symm v) *
        ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))) := by
  have htm : MeasurableSet (A.chart i).target := (A.chart i).open_target.measurableSet
  have hsm : MeasurableSet (A.chart i).source := (A.chart i).open_source.measurableSet
  have hsymm : AEMeasurable (A.chart i).symm (volume.restrict (A.chart i).target) :=
    (A.chart i).continuousOn_symm.aemeasurable htm
  have hρm : AEMeasurable (fun v => ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))))
      (volume.restrict (A.chart i).target) :=
    (ENNReal.continuous_ofReal.comp_continuousOn
      (Real.continuous_exp.comp_continuousOn (A.smooth_ph A.kap i).continuousOn)).aemeasurable htm
  have hsymm' : AEMeasurable (A.chart i).symm ((volume.restrict (A.chart i).target).withDensity
      (fun v => ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))))) :=
    hsymm.mono_ac (withDensity_absolutelyContinuous _ _)
  have hmeas : A.mu.restrict (A.chart i).source = Measure.map (A.chart i).symm
      ((volume.restrict (A.chart i).target).withDensity
        (fun v => ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))))) := by
    ext s hs
    rw [Measure.restrict_apply hs, Measure.map_apply_of_aemeasurable hsymm' hs,
      withDensity_apply' _ _, Measure.restrict_restrict' htm,
      A.mu_chart i _ (hs.inter hsm) Set.inter_subset_right, Set.inter_comm s (A.chart i).source,
      (A.chart i).image_source_inter_eq', Set.inter_comm (A.chart i).target]
  rw [hmeas, lintegral_map' hg.aemeasurable hsymm']
  refine (lintegral_withDensity_eq_lintegral_mul₀ hρm (hg.comp_aemeasurable hsymm)).trans
    (lintegral_congr fun v => ?_)
  simp only [Pi.mul_apply, Function.comp]
  ring

theorem ap_mu_compact (A : WeightedAtlas n Y ι La) (K : Set Y) (hK : IsCompact K) :
    A.mu K < ⊤ := by
  refine hK.measure_lt_top_of_nhdsWithin fun y _ => ?_
  set e := A.chart (A.pick y) with he
  have hys : y ∈ e.source := A.mem_pick y
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp e.open_target (e y) (e.map_source hys)
  have hδ : 0 < ε / 2 := by positivity
  have hcb : Metric.closedBall (e y) (ε / 2) ⊆ e.target :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hSo : IsOpen (e.source ∩ e ⁻¹' Metric.ball (e y) (ε / 2)) :=
    e.isOpen_inter_preimage Metric.isOpen_ball
  have hyS : y ∈ e.source ∩ e ⁻¹' Metric.ball (e y) (ε / 2) := ⟨hys, Set.mem_preimage.mpr (Metric.mem_ball_self hδ)⟩
  refine ⟨e.source ∩ e ⁻¹' Metric.ball (e y) (ε / 2),
    mem_nhdsWithin_of_mem_nhds (hSo.mem_nhds hyS), ?_⟩
  rw [A.mu_chart _ _ hSo.measurableSet Set.inter_subset_left]
  have himg : e '' (e.source ∩ e ⁻¹' Metric.ball (e y) (ε / 2)) ⊆ Metric.closedBall (e y) (ε / 2) := by
    rintro _ ⟨x, hx, rfl⟩
    exact Metric.ball_subset_closedBall hx.2
  have hcont : ContinuousOn (fun v => Real.exp (A.ph A.kap (A.pick y) (e.symm v)))
      (Metric.closedBall (e y) (ε / 2)) :=
    (Real.continuous_exp.comp_continuousOn (A.smooth_ph A.kap (A.pick y)).continuousOn).mono hcb
  obtain ⟨M, hM⟩ := (isCompact_closedBall (e y) (ε / 2)).exists_bound_of_continuousOn hcont
  calc _ ≤ ∫⁻ v in Metric.closedBall (e y) (ε / 2),
          ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick y) (e.symm v))) := lintegral_mono_set himg
    _ ≤ ∫⁻ v in Metric.closedBall (e y) (ε / 2), ENNReal.ofReal M := by
        apply setLIntegral_mono' Metric.isClosed_closedBall.measurableSet
        intro v hv
        apply ENNReal.ofReal_le_ofReal
        have h1 := hM v hv
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h1
        exact h1
    _ < ⊤ := by
        rw [setLIntegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top

theorem api_contOn_chart {E : Type*} [TopologicalSpace E] (A : WeightedAtlas n Y ι La)
    (φ : Y → E) {U : Set Y} (hU : IsOpen U)
    (h : ∀ i, ContinuousOn (φ ∘ (A.chart i).symm) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)) :
    ContinuousOn φ U := by
  intro x hx
  set e := A.chart (A.pick x) with he
  have hxs : x ∈ e.source := A.mem_pick x
  have hex : e x ∈ e.target := e.map_source hxs
  have hopen : IsOpen (e.target ∩ e.symm ⁻¹' U) := e.isOpen_inter_preimage_symm hU
  have hmem : e x ∈ e.target ∩ e.symm ⁻¹' U := by
    refine ⟨hex, ?_⟩
    show e.symm (e x) ∈ U
    rw [e.left_inv hxs]
    exact hx
  have h1 : ContinuousAt (φ ∘ e.symm) (e x) :=
    (h (A.pick x)).continuousAt (hopen.mem_nhds hmem)
  have h2 : ContinuousAt ((φ ∘ e.symm) ∘ e) x := h1.comp (e.continuousAt hxs)
  have h3 : (φ ∘ e.symm) ∘ e =ᶠ[𝓝 x] φ := by
    filter_upwards [e.eventually_left_inverse hxs] with y hy
    simp [hy]
  exact (h2.congr h3).continuousWithinAt

theorem api_nsq_eq (A : WeightedAtlas n Y ι La) {la : La} {U : Set Y} {F : ι → Y → ℂ}
    (hFs : A.IsSecOn la U F) {i : ι} {x : Y}
    (hxs : x ∈ (A.chart i).source) (hxU : x ∈ U) :
    ‖F i x‖ ^ 2 * Real.exp (-A.ph la i x) = A.nsq la F x := by
  unfold WeightedAtlas.nsq
  have hj : x ∈ (A.chart (A.pick x)).source := A.mem_pick x
  have hsec := hFs.2 i (A.pick x) x hxU hxs hj
  have hph := A.ph_trans la i (A.pick x) x hxs hj
  have hg := A.g_ne la i (A.pick x) x hxs hj
  have hgpos : 0 < ‖A.g la i (A.pick x) x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hg) 2
  rw [hsec, hph, norm_mul, mul_pow,
    show -(A.ph la i x - Real.log (‖A.g la i (A.pick x) x‖ ^ 2)) =
      Real.log (‖A.g la i (A.pick x) x‖ ^ 2) + -A.ph la i x by ring,
    Real.exp_add, Real.exp_log hgpos]
  ring

theorem api_nsq_contOn (A : WeightedAtlas n Y ι La) {la : La} {U : Set Y} (hU : IsOpen U)
    {F : ι → Y → ℂ} (hFs : A.IsSecOn la U F) : ContinuousOn (A.nsq la F) U := by
  apply api_contOn_chart A _ hU
  intro i
  set e := A.chart i with he
  have hF : ContinuousOn (F i ∘ e.symm) (e.target ∩ e.symm ⁻¹' U) := (hFs.1 i).continuousOn
  have hph : ContinuousOn (A.ph la i ∘ e.symm) (e.target ∩ e.symm ⁻¹' U) :=
    (A.smooth_ph la i).continuousOn.mono Set.inter_subset_left
  have hc : ContinuousOn (fun v => ‖F i (e.symm v)‖ ^ 2 * Real.exp (-A.ph la i (e.symm v)))
      (e.target ∩ e.symm ⁻¹' U) :=
    (hF.norm.pow 2).mul (Real.continuous_exp.comp_continuousOn hph.neg)
  refine hc.congr ?_
  intro v hv
  exact (api_nsq_eq A hFs (e.map_target hv.1) hv.2).symm

end

end ReciprocityTheory.L2DbarEstimates.Y
end

-- bundled from ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpaFderivCompApply
section
open Complex ComplexConjugate Filter Topology
open scoped ContDiff

namespace ReciprocityTheory.L2DbarEstimates.Y

noncomputable section

variable {n : ℕ}

private theorem I_pow_three' : I ^ 3 = -I := by
  rw [pow_succ, I_sq, neg_one_mul]

private theorem eq_sum_coord_smul_basis (w : V n) : w = ∑ j, w j • bas n j := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℂ).sum_repr w]
  simp [bas]

private theorem clm_apply_eq_sum_wd_wdb_basis (D : V n →L[ℝ] ℂ) (w : V n) :
    D w = ∑ b, (w b * ((D (bas n b) - I * D (I • bas n b)) / 2) +
      conj (w b) * ((D (bas n b) + I * D (I • bas n b)) / 2)) := by
  conv_lhs => rw [eq_sum_coord_smul_basis w]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  conv_lhs => rw [← Complex.re_add_im (w b), add_smul, mul_smul, Complex.coe_smul, Complex.coe_smul,
    map_add, map_smul, map_smul]
  conv_rhs => rw [← Complex.re_add_im (w b)]
  simp only [Complex.real_smul, map_add (f := _), map_mul, Complex.conj_ofReal, Complex.conj_I]
  linear_combination ((w b).im * D (I • bas n b)) * Complex.I_sq

private theorem fderiv_comp_holomorphic_apply {U : V n → ℂ} {G : V n → V n} {y : V n}
    (hU : DifferentiableAt ℝ U (G y)) (hG : DifferentiableAt ℂ G y) (v : V n) :
    fderiv ℝ (U ∘ G) y v = fderiv ℝ U (G y) (fderiv ℂ G y v) := by
  have hG' : HasFDerivAt G ((fderiv ℂ G y).restrictScalars ℝ) y := hG.hasFDerivAt.restrictScalars ℝ
  rw [(hU.hasFDerivAt.comp y hG').fderiv]
  rfl

private theorem wdb_comp_holomorphic_eq_sum_conj {U : V n → ℂ} {G : V n → V n} {y : V n}
    (hU : DifferentiableAt ℝ U (G y)) (hG : DifferentiableAt ℂ G y) (k : Fin n) :
    wdb n k (U ∘ G) y = ∑ b, wdb n b U (G y) * conj (fderiv ℂ G y (bas n k) b) := by
  unfold wdb
  rw [fderiv_comp_holomorphic_apply hU hG, fderiv_comp_holomorphic_apply hU hG, map_smul (fderiv ℂ G y),
    clm_apply_eq_sum_wd_wdb_basis (fderiv ℝ U (G y)) (fderiv ℂ G y (bas n k)),
    clm_apply_eq_sum_wd_wdb_basis (fderiv ℝ U (G y)) (I • fderiv ℂ G y (bas n k))]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul, map_mul, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq, I_pow_three']
  ring

private theorem wd_comp_holomorphic_eq_sum {U : V n → ℂ} {G : V n → V n} {y : V n}
    (hU : DifferentiableAt ℝ U (G y)) (hG : DifferentiableAt ℂ G y) (k : Fin n) :
    wd n k (U ∘ G) y = ∑ b, wd n b U (G y) * fderiv ℂ G y (bas n k) b := by
  unfold wd
  rw [fderiv_comp_holomorphic_apply hU hG, fderiv_comp_holomorphic_apply hU hG, map_smul (fderiv ℂ G y),
    clm_apply_eq_sum_wd_wdb_basis (fderiv ℝ U (G y)) (fderiv ℂ G y (bas n k)),
    clm_apply_eq_sum_wd_wdb_basis (fderiv ℝ U (G y)) (I • fderiv ℂ G y (bas n k))]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul, map_mul, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq, I_pow_three']
  ring

private theorem differentiableAt_fderiv_basis_coord_of_contDiffAt {G : V n → V n} {y : V n} (hG : ContDiffAt ℂ 2 G y) (k b : Fin n) :
    DifferentiableAt ℂ (fun v => fderiv ℂ G v (bas n k) b) y := by
  have h1 : ContDiffAt ℂ 1 (fderiv ℂ G) y := hG.fderiv_right (by norm_num)
  have h2 : ContDiffAt ℂ 1 (fun v => fderiv ℂ G v (bas n k)) y := h1.clm_apply contDiffAt_const
  have h3 : ContDiffAt ℂ 1 (fun v => (EuclideanSpace.proj b : V n →L[ℂ] ℂ) (fderiv ℂ G v (bas n k))) y :=
    (EuclideanSpace.proj b : V n →L[ℂ] ℂ).contDiff.contDiffAt.comp y h2
  exact h3.differentiableAt one_ne_zero

private theorem differentiableAt_wdb_of_contDiffAt {g : V n → ℂ} {y : V n} (hg : ContDiffAt ℝ 2 g y) (k : Fin n) :
    DifferentiableAt ℝ (wdb n k g) y := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ g) y := hg.fderiv_right (by norm_num)
  have hb : ∀ u : V n, DifferentiableAt ℝ (fun v => fderiv ℝ g v u) y := fun u =>
    (h1.clm_apply contDiffAt_const).differentiableAt one_ne_zero
  have := ((hb (bas n k)).add ((hb (I • bas n k)).const_mul I)).mul_const (2⁻¹ : ℂ)
  unfold wdb
  simp only [div_eq_mul_inv]
  exact this

private theorem wd_finset_sum {ι : Type*} (s : Finset ι) (Φ : ι → V n → ℂ) (y : V n)
    (hΦ : ∀ i ∈ s, DifferentiableAt ℝ (Φ i) y) (j : Fin n) :
    wd n j (fun w => ∑ i ∈ s, Φ i w) y = ∑ i ∈ s, wd n j (Φ i) y := by
  have hF : fderiv ℝ (fun w => ∑ i ∈ s, Φ i w) y = ∑ i ∈ s, fderiv ℝ (Φ i) y := by
    have H := HasFDerivAt.sum (u := s) (A := Φ) fun i hi => (hΦ i hi).hasFDerivAt
    try simp only [Finset.sum_fn] at H
    exact H.fderiv
  simp only [wd, hF, ContinuousLinearMap.sum_apply, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_div]

private theorem wd_mul_eq_leibniz {p q : V n → ℂ} {y : V n} (hp : DifferentiableAt ℝ p y)
    (hq : DifferentiableAt ℝ q y) (j : Fin n) :
    wd n j (fun w => p w * q w) y = wd n j p y * q y + p y * wd n j q y := by
  have hF : fderiv ℝ (fun w => p w * q w) y = p y • fderiv ℝ q y + q y • fderiv ℝ p y :=
    (hp.hasFDerivAt.mul hq.hasFDerivAt).fderiv
  simp only [wd, hF, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

private theorem wd_conj_holomorphic_eq_zero {h : V n → ℂ} {y : V n} (hh : DifferentiableAt ℂ h y) (j : Fin n) :
    wd n j (fun v => (starRingEnd ℂ) (h v)) y = 0 := by
  have H := (hh.hasFDerivAt.restrictScalars ℝ).star
  have H2 : fderiv ℝ (fun v => (starRingEnd ℂ) (h v)) y =
      ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ).comp ((fderiv ℂ h y).restrictScalars ℝ) := H.fderiv
  simp only [wd, H2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    map_smul, smul_eq_mul, ContinuousLinearEquiv.coe_coe, starL'_apply, star_mul', Complex.star_def,
    Complex.conj_I]
  ring_nf
  try simp only [Complex.I_sq]
  try ring

theorem cmpa_hess_comp {τ : V n → V n} {h : V n → ℂ} {x : V n} {U : Set (V n)} (hU : IsOpen U)
    (hxU : x ∈ U) (hτ : DifferentiableOn ℂ τ U) (hh : ContDiffAt ℝ 2 h (τ x)) (j k : Fin n) :
    wd n j (wdb n k (h ∘ τ)) x = ∑ m, ∑ l, wd n l (wdb n m h) (τ x) *
      (fderiv ℂ τ x (bas n j)) l * conj ((fderiv ℂ τ x (bas n k)) m) := by
  have hτc : ContDiffOn ℂ ∞ τ U := by
    rw [contDiffOn_piLp]
    intro i
    exact contDiffOn_of_differentiableOn n _ U hU
      ((EuclideanSpace.proj i : V n →L[ℂ] ℂ).differentiable.comp_differentiableOn hτ)
  have hG : ContDiffAt ℂ 2 τ x := (contDiffOn_infty.1 hτc 2).contDiffAt (hU.mem_nhds hxU)
  have hGd : ∀ᶠ v in 𝓝 x, DifferentiableAt ℂ τ v :=
    (hG.eventually (by simp)).mono fun v hv => hv.differentiableAt (by simp)
  have hUd : ∀ᶠ v in 𝓝 x, DifferentiableAt ℝ h (τ v) := by
    have h1 : ∀ᶠ w in 𝓝 (τ x), DifferentiableAt ℝ h w :=
      (hh.eventually (by simp)).mono fun w hw => hw.differentiableAt (by simp)
    exact Filter.Tendsto.eventually hG.continuousAt h1
  have ev : wdb n k (h ∘ τ) =ᶠ[𝓝 x]
      fun v => ∑ b, wdb n b h (τ v) * conj (fderiv ℂ τ v (bas n k) b) := by
    filter_upwards [hGd, hUd] with v h1 h2
    exact wdb_comp_holomorphic_eq_sum_conj h2 h1 k
  have hGy : DifferentiableAt ℂ τ x := hG.differentiableAt (by simp)
  have e1 : wd n j (wdb n k (h ∘ τ)) x = wd n j (fun v => ∑ b, wdb n b h (τ v) *
      conj (fderiv ℂ τ v (bas n k) b)) x := by
    simp only [wd, ev.fderiv_eq]
  have hp : ∀ b, DifferentiableAt ℝ (fun v => wdb n b h (τ v)) x := fun b =>
    (differentiableAt_wdb_of_contDiffAt hh b).comp x (hGy.restrictScalars ℝ)
  have hq : ∀ b, DifferentiableAt ℝ (fun v => conj (fderiv ℂ τ v (bas n k) b)) x :=
    fun b => ((differentiableAt_fderiv_basis_coord_of_contDiffAt hG k b).restrictScalars ℝ).star
  rw [e1, wd_finset_sum Finset.univ (fun b v => wdb n b h (τ v) * conj (fderiv ℂ τ v (bas n k) b))
      x (fun b _ => (hp b).mul (hq b)) j]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [wd_mul_eq_leibniz (hp b) (hq b) j, wd_conj_holomorphic_eq_zero (differentiableAt_fderiv_basis_coord_of_contDiffAt hG k b) j, mul_zero, add_zero]
  have e2 := wd_comp_holomorphic_eq_sum (U := wdb n b h) (differentiableAt_wdb_of_contDiffAt hh b) hGy j
  simp only [Function.comp_def] at e2
  rw [e2, Finset.sum_mul]

end

end ReciprocityTheory.L2DbarEstimates.Y
end

