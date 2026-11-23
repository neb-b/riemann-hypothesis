module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.IntSmooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0172
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0188
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.CechDifferentialPullback.Bridge

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnOfIteratedFDerivZero
section
noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ParamInt

variable {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [SecondCountableTopology X] {ν : Measure X} [IsFiniteMeasureOnCompacts ν]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem continuousOn_of_iteratedFDeriv_zero {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {U : Set E} {F : X → E → W}
    (h : ContinuousOn (fun p : X × E => iteratedFDeriv ℝ 0 (F p.1) p.2) (univ ×ˢ U)) :
    ContinuousOn (fun p : X × E => F p.1 p.2) (univ ×ˢ U) := by
  have e : (fun p : X × E => F p.1 p.2) =
      fun p => ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => E) W (fun _ => 0)
        (iteratedFDeriv ℝ 0 (F p.1) p.2) := by
    funext p; simp
  rw [e]
  exact (ContinuousLinearMap.continuous _).comp_continuousOn h

theorem continuousOn_iteratedFDeriv_fderiv {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {U : Set E} {F : X → E → W} (m : ℕ)
    (h : ContinuousOn (fun p : X × E => iteratedFDeriv ℝ (m + 1) (F p.1) p.2) (univ ×ˢ U)) :
    ContinuousOn (fun p : X × E => iteratedFDeriv ℝ m (fderiv ℝ (F p.1)) p.2) (univ ×ˢ U) := by
  have e : (fun p : X × E => iteratedFDeriv ℝ m (fderiv ℝ (F p.1)) p.2) =
      fun p : X × E => continuousMultilinearCurryRightEquiv' ℝ m E W
        (iteratedFDeriv ℝ (m + 1) (F p.1) p.2) := by
    funext p
    rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
      LinearIsometryEquiv.apply_symm_apply]
  rw [e]
  exact (LinearIsometryEquiv.continuous _).comp_continuousOn h

theorem integrable_bound {K : Set X} (hK : IsCompact K) (C : ℝ) :
    Integrable ((toMeasurable ν K).indicator fun _ => C) ν := by
  rw [integrable_indicator_iff (measurableSet_toMeasurable ν K)]
  refine integrableOn_const ?_
  rw [measure_toMeasurable]
  exact hK.measure_lt_top.ne

theorem le_bound {W : Type} [NormedAddCommGroup W] {K : Set X} {C : ℝ} {t : X} {w : W}
    (h1 : t ∈ K → ‖w‖ ≤ C) (h2 : t ∉ K → w = 0) :
    ‖w‖ ≤ (toMeasurable ν K).indicator (fun _ => max C 0) t := by
  by_cases ht : t ∈ K
  · rw [indicator_of_mem (subset_toMeasurable ν K ht)]
    exact (h1 ht).trans (le_max_left _ _)
  · rw [h2 ht, norm_zero]
    exact indicator_nonneg (fun _ _ => le_max_right _ _) _

theorem hasFDerivAt_integral {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {U : Set E} (hU : IsOpen U) {F : X → E → V}
    (h1 : ∀ t, ContDiffOn ℝ ∞ (F t) U)
    (h0 : ContinuousOn (fun p : X × E => F p.1 p.2) (univ ×ˢ U))
    (hd : ContinuousOn (fun p : X × E => fderiv ℝ (F p.1) p.2) (univ ×ˢ U))
    (h3 : ∀ x₀ ∈ U, ∃ U' ∈ 𝓝 x₀, ∃ K : Set X, IsCompact K ∧ ∀ t ∉ K, ∀ x ∈ U', F t x = 0)
    {x₀ : E} (hx : x₀ ∈ U) :
    HasFDerivAt (fun x => ∫ t, F t x ∂ν) (∫ t, fderiv ℝ (F t) x₀ ∂ν) x₀ := by
  obtain ⟨U', hU', K, hK, hz⟩ := h3 x₀ hx
  have hN : U ∩ interior U' ∈ 𝓝 x₀ := inter_mem (hU.mem_nhds hx) (interior_mem_nhds.2 hU')
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hN
  have hBc : IsCompact (Metric.closedBall x₀ r) := isCompact_closedBall x₀ r
  have hKB := hK.prod hBc
  have hsub : K ×ˢ Metric.closedBall x₀ r ⊆ univ ×ˢ U :=
    fun p hp => ⟨mem_univ _, (hball hp.2).1⟩
  obtain ⟨C, hC⟩ := hKB.exists_bound_of_continuousOn (hd.mono hsub)
  obtain ⟨C₀, hC₀⟩ := hKB.exists_bound_of_continuousOn (h0.mono hsub)
  have hx₀B : x₀ ∈ Metric.closedBall x₀ r := Metric.mem_closedBall_self hr.le
  have hdz : ∀ t ∉ K, ∀ x ∈ Metric.closedBall x₀ r, fderiv ℝ (F t) x = 0 := by
    intro t ht x hxB
    have : F t =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [isOpen_interior.mem_nhds (hball hxB).2] with y hy
      exact hz t ht y (interior_subset hy)
    rw [this.fderiv_eq]
    simp
  have hct : ∀ x ∈ U, Continuous fun t => F t x := fun x hxU =>
    h0.comp_continuous (continuous_id.prodMk continuous_const) fun t => ⟨mem_univ _, hxU⟩
  have hcd : ∀ x ∈ U, Continuous fun t => fderiv ℝ (F t) x := fun x hxU =>
    hd.comp_continuous (continuous_id.prodMk continuous_const) fun t => ⟨mem_univ _, hxU⟩
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x t => F t x)
    (F' := fun x t => fderiv ℝ (F t) x) (s := Metric.closedBall x₀ r)
    (bound := (toMeasurable ν K).indicator fun _ => max C 0)
    (Metric.closedBall_mem_nhds x₀ hr) ?_ ?_ ?_ ?_ (integrable_bound hK _) ?_
  · filter_upwards [hU.mem_nhds hx] with x hxU
    exact (hct x hxU).aestronglyMeasurable
  · refine Integrable.mono' (integrable_bound (ν := ν) hK (max C₀ 0))
      (hct x₀ hx).aestronglyMeasurable (ae_of_all _ fun t => ?_)
    exact le_bound (fun ht => hC₀ (t, x₀) ⟨ht, hx₀B⟩) (fun ht => hz t ht x₀ (interior_subset (hball hx₀B).2))
  · exact (hcd x₀ hx).aestronglyMeasurable
  · refine ae_of_all _ fun t x hxB => ?_
    exact le_bound (fun ht => hC (t, x) ⟨ht, hxB⟩) (fun ht => hdz t ht x hxB)
  · refine ae_of_all _ fun t x hxB => ?_
    exact (((h1 t).contDiffAt (hU.mem_nhds (hball hxB).1)).differentiableAt (by simp)).hasFDerivAt

theorem contDiffOn_integral_nat {U : Set E} (hU : IsOpen U) (m : ℕ) :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (F : X → E → V),
      (∀ t, ContDiffOn ℝ ∞ (F t) U) →
      (∀ k : ℕ, ContinuousOn (fun p : X × E => iteratedFDeriv ℝ k (F p.1) p.2) (univ ×ˢ U)) →
      (∀ x₀ ∈ U, ∃ U' ∈ 𝓝 x₀, ∃ K : Set X, IsCompact K ∧ ∀ t ∉ K, ∀ x ∈ U', F t x = 0) →
      ContDiffOn ℝ m (fun x => ∫ t, F t x ∂ν) U := by
  have key : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
      (F : X → E → V), (∀ t, ContDiffOn ℝ ∞ (F t) U) →
      (∀ k : ℕ, ContinuousOn (fun p : X × E => iteratedFDeriv ℝ k (F p.1) p.2) (univ ×ˢ U)) →
      (∀ x₀ ∈ U, ∃ U' ∈ 𝓝 x₀, ∃ K : Set X, IsCompact K ∧ ∀ t ∉ K, ∀ x ∈ U', F t x = 0) →
      ∀ x₀ ∈ U, HasFDerivAt (fun x => ∫ t, F t x ∂ν) (∫ t, fderiv ℝ (F t) x₀ ∂ν) x₀ := by
    intro V _ _ _ F h1 h2 h3 x₀ hx
    exact hasFDerivAt_integral hU h1 (continuousOn_of_iteratedFDeriv_zero (h2 0))
      (continuousOn_of_iteratedFDeriv_zero (F := fun t => fderiv ℝ (F t))
        (continuousOn_iteratedFDeriv_fderiv 0 (h2 1))) h3 hx
  induction m with
  | zero =>
    intro V _ _ _ F h1 h2 h3
    have : ContinuousOn (fun x => ∫ t, F t x ∂ν) U := fun x hx =>
      (key V F h1 h2 h3 x hx).continuousAt.continuousWithinAt
    have h : ContDiffOn ℝ 0 (fun x => ∫ t, F t x ∂ν) U := contDiffOn_zero.2 this
    simpa using h
  | succ m ih =>
    intro V _ _ _ F h1 h2 h3
    have hG1 : ∀ t, ContDiffOn ℝ ∞ (fderiv ℝ (F t)) U := fun t =>
      (h1 t).fderiv_of_isOpen hU (by simp)
    have hG2 : ∀ k : ℕ, ContinuousOn
        (fun p : X × E => iteratedFDeriv ℝ k (fderiv ℝ (F p.1)) p.2) (univ ×ˢ U) := fun k =>
      continuousOn_iteratedFDeriv_fderiv k (h2 (k + 1))
    have hG3 : ∀ x₀ ∈ U, ∃ U' ∈ 𝓝 x₀, ∃ K : Set X, IsCompact K ∧
        ∀ t ∉ K, ∀ x ∈ U', fderiv ℝ (F t) x = 0 := by
      intro x₀ hx
      obtain ⟨U', hU', K, hK, hz⟩ := h3 x₀ hx
      refine ⟨interior U', interior_mem_nhds.2 hU', K, hK, fun t ht x hxU => ?_⟩
      have : F t =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [isOpen_interior.mem_nhds hxU] with y hy
        exact hz t ht y (interior_subset hy)
      rw [this.fderiv_eq]
      simp
    have hI := ih (E →L[ℝ] V) (fun t => fderiv ℝ (F t)) hG1 hG2 hG3
    have hcast : ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 := by norm_cast
    rw [hcast, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun x hx => (key V F h1 h2 h3 x hx).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    exact hI.congr fun x hx => (key V F h1 h2 h3 x hx).fderiv

theorem contDiffOn_integral {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {U : Set E} (hU : IsOpen U) (F : X → E → V)
    (h1 : ∀ t, ContDiffOn ℝ ∞ (F t) U)
    (h2 : ∀ k : ℕ, ContinuousOn (fun p : X × E => iteratedFDeriv ℝ k (F p.1) p.2) (univ ×ˢ U))
    (h3 : ∀ x₀ ∈ U, ∃ U' ∈ 𝓝 x₀, ∃ K : Set X, IsCompact K ∧ ∀ t ∉ K, ∀ x ∈ U', F t x = 0) :
    ContDiffOn ℝ ∞ (fun x => ∫ t, F t x ∂ν) U :=
  contDiffOn_infty.2 fun m => contDiffOn_integral_nat hU m V F h1 h2 h3

theorem intSmooth : PositivityTheory.RgBcC.VC.IntSmooth := by
  intro n X _ _ _ _ ν _ V _ _ _ F h1 h2 h3
  haveI : CompleteSpace V := FiniteDimensional.complete ℂ V
  have hU : IsOpen (PositivityTheory.RgBcC.GLs n) := by
    have h : Continuous fun g : PositivityTheory.RgTw.Mat n => g.det := Continuous.matrix_det continuous_id
    exact isOpen_ne_fun h continuous_const
  exact contDiffOn_integral hU F h1 h2 h3

end GlobalTheory.CompanionTheory.ParamInt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOneParamDifferentiable
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.OneParam

theorem hasDerivAt_zero_of_continuous_oneParam
    {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] (Φ : ℝ → 𝔸)
    (hc : Continuous Φ) (h0 : Φ 0 = 1) (hadd : ∀ s t, Φ (s + t) = Φ s * Φ t) :
    ∃ B, HasDerivAt Φ B 0 := by

  set F : ℝ → 𝔸 := fun x => ∫ s in (0 : ℝ)..x, Φ s with hF
  have hFd : ∀ x, HasDerivAt F (Φ x) x := fun x =>
    (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hF0 : F 0 = 0 := by simp [hF]

  have hsl : Filter.Tendsto (slope F 0) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (1 : 𝔸)) := by
    have := hasDerivAt_iff_tendsto_slope.1 (hFd 0)
    rwa [h0] at this
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ, ‖slope F 0 ε - 1‖ < 1 := by
    have := hsl.eventually (Metric.ball_mem_nhds (1 : 𝔸) one_pos)
    filter_upwards [this] with ε hε
    simpa [dist_eq_norm] using hε
  obtain ⟨ε, hε, hε0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hε0' : ε ≠ 0 := hε0

  set u : 𝔸 := slope F 0 ε with hu
  have huF : u = ε⁻¹ • F ε := by
    simp [hu, slope_def_module, hF0]
  have hone : ‖1 - u‖ < 1 := by rwa [norm_sub_rev]
  have huU : IsUnit u := by
    have := (Units.oneSub (1 - u) hone).isUnit
    simpa using this
  obtain ⟨U, hU⟩ := huU
  set v : 𝔸 := ((U⁻¹ : 𝔸ˣ) : 𝔸) with hv
  have huv : u * v = 1 := by rw [← hU, hv]; exact U.mul_inv

  have hmul : ∀ t, Φ t * F ε = F (t + ε) - F t := by
    intro t
    have h1 : Φ t * F ε = ∫ s in (0 : ℝ)..ε, Φ (t + s) := by
      have := (ContinuousLinearMap.mul ℝ 𝔸 (Φ t)).intervalIntegral_comp_comm
        (hc.intervalIntegrable (μ := volume) 0 ε)
      simp only [ContinuousLinearMap.mul_apply'] at this
      rw [hF]
      simp only [hadd]
      exact this.symm
    have h2 : (∫ s in (0 : ℝ)..ε, Φ (t + s)) = ∫ s in (t + 0)..(t + ε), Φ s :=
      intervalIntegral.integral_comp_add_left (a := 0) (b := ε) Φ t
    rw [h1, h2, add_zero]
    exact (intervalIntegral.integral_interval_sub_left
      (hc.intervalIntegrable 0 _) (hc.intervalIntegrable 0 _)).symm

  have hrec : ∀ t, Φ t = (ε⁻¹ • (F (t + ε) - F t)) * v := by
    intro t
    rw [← hmul, ← mul_smul_comm, ← huF, mul_assoc, huv, mul_one]

  have hshift : HasDerivAt (fun t => F (t + ε)) (Φ (0 + ε)) 0 :=
    (hFd (0 + ε)).comp_add_const 0 ε
  have hd : HasDerivAt (fun t => (ε⁻¹ • (F (t + ε) - F t)) * v)
      ((ε⁻¹ • (Φ (0 + ε) - Φ 0)) * v) 0 :=
    ((hshift.sub (hFd 0)).const_smul ε⁻¹).mul_const v
  have hfun : Φ = fun t => (ε⁻¹ • (F (t + ε) - F t)) * v := funext hrec
  exact ⟨(ε⁻¹ • (Φ (0 + ε) - Φ 0)) * v, by rw [show HasDerivAt Φ = HasDerivAt (fun t => (ε⁻¹ • (F (t + ε) - F t)) * v) from congrArg _ hfun]; exact hd⟩

end GlobalTheory.CompanionTheory.OneParam
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousTranslatedIntegrand
section
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.EpsteinThetaC

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem continuous_scalC : Continuous (scalC : IdeleGroup k → GL ι 𝔸[k]) := by
  have hinv : Continuous fun a : IdeleGroup k ↦ ((a⁻¹ : IdeleGroup k) : 𝔸[k]) :=
    Units.continuous_val.comp continuous_inv
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j ↦ ?_
    by_cases hij : i = j
    · subst hij
      simpa [Function.comp_def, scalC, Matrix.scalar_apply] using
        (Units.continuous_val : Continuous fun a : IdeleGroup k ↦ (a : 𝔸[k]))
    · simpa [Function.comp_def, scalC, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]
        using continuous_const
  · refine continuous_matrix fun i j ↦ ?_
    by_cases hij : i = j
    · subst hij
      simpa [Function.comp_def, scalC, Matrix.scalar_apply] using hinv
    · simpa [Function.comp_def, scalC, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]
        using continuous_const

theorem thetaC_ltr (A h : GL ι 𝔸[k]) (F : (ι → 𝔸[k]) → ℂ) :
    thetaC (ltr A F) h = thetaC F (A * h) := by
  simp only [thetaC, ltr, Units.val_mul, Matrix.mulVec_mulVec]

theorem continuous_thetaC {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι)) :
    Continuous (thetaC F : GL ι 𝔸[k] → ℂ) := by
  refine continuous_iff_continuousAt.2 fun h₀ ↦ ?_
  obtain ⟨C, hC, hh₀⟩ := exists_compact_mem_nhds h₀
  obtain ⟨u, hu, hFu⟩ := GlobalTheory.T.exists_summable_majorant_lattice_sum hF hC
  have hcont : ContinuousOn (thetaC F : GL ι 𝔸[k] → ℂ) C := by
    refine continuousOn_tsum (fun ξ ↦ Continuous.continuousOn ?_) hu fun ξ h hh ↦ hFu h hh ξ
    refine (continuous_of_mem_schwartzBruhatPi hF).comp ?_
    exact Units.continuous_val.matrix_mulVec continuous_const
  exact hcont.continuousAt hh₀

noncomputable def translatedIntegrand (w : InfinitePlace k) (Ψ : (ι → 𝔸[k]) → ℂ)
    (ω : HeckeCharacter k) (p : {r : ℝ // 0 < r} × GL ι 𝔸[k]) (u : normOneSubgroup k) : ℂ :=
  thetaC Ψ (p.2 * scalC (moduleSection w p.1 * (u : IdeleGroup k))) *
    (ω.toIdele (u : IdeleGroup k) : ℂ)

theorem continuous_translatedIntegrand (w : InfinitePlace k) {Ψ : (ι → 𝔸[k]) → ℂ}
    (hΨ : Ψ ∈ schwartzBruhatPi (K := k) (ι := ι)) (ω : HeckeCharacter k) :
    Continuous (Function.uncurry (translatedIntegrand w Ψ ω)) := by
  have hu : Continuous fun x : ({r : ℝ // 0 < r} × GL ι 𝔸[k]) × normOneSubgroup k ↦
      (x.2 : IdeleGroup k) := continuous_subtype_val.comp continuous_snd
  have hs : Continuous fun x : ({r : ℝ // 0 < r} × GL ι 𝔸[k]) × normOneSubgroup k ↦
      moduleSection w x.1.1 :=
    (continuous_moduleSection w).comp (continuous_fst.comp continuous_fst)
  have hg : Continuous fun x : ({r : ℝ // 0 < r} × GL ι 𝔸[k]) × normOneSubgroup k ↦
      x.1.2 := continuous_snd.comp continuous_fst
  exact ((continuous_thetaC hΨ).comp (hg.mul (continuous_scalC.comp (hs.mul hu)))).mul
    (continuous_subtype_val.comp (ω.continuous_toIdele.comp hu))

theorem continuous_thetaCInt_ltr {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι]
    [DecidableEq ι] (w : InfinitePlace k) {Ψ : (ι → 𝔸[k]) → ℂ}
    (hΨ : Ψ ∈ schwartzBruhatPi (K := k) (ι := ι)) (ω : HeckeCharacter k) :
    Continuous fun p : {r : ℝ // 0 < r} × GL ι 𝔸[k] ↦ thetaCInt w (ltr p.2 Ψ) ω p.1 := by
  have h := GlobalTheory.CompanionTheory.EisRk1Theta.continuous_setIntegral_of_continuous_uncurry (normOneMeasure k)
    (isCompact_closure_normOneFundamentalDomain k)
    (normOneMeasure_normOneFundamentalDomain_lt_top k) (continuous_translatedIntegrand w hΨ ω)
  refine h.congr fun p ↦ ?_
  simp only [thetaCInt, thetaC_ltr, translatedIntegrand]

end GlobalTheory.CompanionTheory.EpsteinThetaC
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoshTransformConvolution
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.CoshMul

theorem bump_hasCompactSupport {g : ℝ → ℝ} {T : ℝ} (h : IsBump g T) : HasCompactSupport g := by
  refine HasCompactSupport.intro (K := Set.Icc (-T) T) isCompact_Icc ?_
  intro t ht
  apply h.2.2
  by_contra hh
  exact ht (abs_le.mp (not_lt.mp hh))

theorem bump_mul_integrable {g : ℝ → ℝ} {T : ℝ} (h : IsBump g T) {f : ℝ → ℂ} (hf : Continuous f) :
    Integrable (fun t => (g t : ℂ) * f t) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (Complex.continuous_ofReal.comp h.1.continuous).mul hf
  · exact ((bump_hasCompactSupport h).comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)).mul_right

theorem continuous_cosh_mul (a : ℂ) : Continuous (fun s : ℝ => Complex.cosh ((s : ℂ) * a)) :=
  Complex.continuous_cosh.comp (Complex.continuous_ofReal.mul continuous_const)

theorem continuous_sinh_mul (a : ℂ) : Continuous (fun s : ℝ => Complex.sinh ((s : ℂ) * a)) :=
  Complex.continuous_sinh.comp (Complex.continuous_ofReal.mul continuous_const)

theorem bump_sinh_integral {g : ℝ → ℝ} {T : ℝ} (h : IsBump g T) (a : ℂ) :
    ∫ s : ℝ, (g s : ℂ) * Complex.sinh ((s : ℂ) * a) = 0 := by
  have h1 := integral_neg_eq_self (fun s : ℝ => (g s : ℂ) * Complex.sinh ((s : ℂ) * a)) volume
  have h2 : (fun s : ℝ => (g (-s) : ℂ) * Complex.sinh (((-s : ℝ) : ℂ) * a))
      = fun s : ℝ => -((g s : ℂ) * Complex.sinh ((s : ℂ) * a)) := by
    funext s
    rw [h.2.1]
    push_cast
    rw [neg_mul, Complex.sinh_neg]
    ring
  simp only [h2] at h1
  rw [integral_neg] at h1
  linear_combination (-1 / 2 : ℂ) * h1

theorem bump_cosh_shift {g : ℝ → ℝ} {T : ℝ} (h : IsBump g T) (a : ℂ) (t : ℝ) :
    ∫ s : ℝ, (g s : ℂ) * Complex.cosh (((s + t : ℝ) : ℂ) * a)
      = Complex.cosh ((t : ℂ) * a) * ∫ s : ℝ, (g s : ℂ) * Complex.cosh ((s : ℂ) * a) := by
  have h1 : ∀ s : ℝ, (g s : ℂ) * Complex.cosh (((s + t : ℝ) : ℂ) * a)
      = Complex.cosh ((t : ℂ) * a) * ((g s : ℂ) * Complex.cosh ((s : ℂ) * a))
        + Complex.sinh ((t : ℂ) * a) * ((g s : ℂ) * Complex.sinh ((s : ℂ) * a)) := by
    intro s
    push_cast
    rw [add_mul, Complex.cosh_add]
    ring
  simp_rw [h1]
  rw [integral_add ((bump_mul_integrable h (continuous_cosh_mul a)).const_mul _)
    ((bump_mul_integrable h (continuous_sinh_mul a)).const_mul _),
    integral_const_mul, integral_const_mul, bump_sinh_integral h a]
  simp

theorem conv_kernel_integrable {g g' : ℝ → ℝ} {T T' : ℝ} (h : IsBump g T) (h' : IsBump g' T')
    {f : ℝ → ℂ} (hf : Continuous f) :
    Integrable (Function.uncurry fun r t : ℝ => ((g t * g' (r - t) : ℝ) : ℂ) * f r)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · have c1 := h.1.continuous
    have c2 := h'.1.continuous
    simp only [Function.uncurry_def]
    fun_prop
  · refine HasCompactSupport.intro
      (K := Set.Icc (-T - T') (T + T') ×ˢ Set.Icc (-T) T) (isCompact_Icc.prod isCompact_Icc) ?_
    rintro ⟨r, t⟩ hx
    simp only [Function.uncurry_apply_pair]
    by_cases ht : t ∈ Set.Icc (-T) T
    · have hr : r ∉ Set.Icc (-T - T') (T + T') := fun hr => hx ⟨hr, ht⟩
      have : T' < |r - t| := by
        by_contra hh
        have := abs_le.mp (not_lt.mp hh)
        exact hr ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩
      rw [h'.2.2 _ this]
      simp
    · have : T < |t| := by
        by_contra hh
        exact ht (abs_le.mp (not_lt.mp hh))
      rw [h.2.2 _ this]
      simp

theorem coshT_mul_coshT (g g' : ℝ → ℝ) (T T' : ℝ) (c : ℂ) (h : IsBump g T) (h' : IsBump g' T') :
    coshT g c * coshT g' c = coshT (gconv g g') c := by
  unfold coshT gconv
  set a : ℂ := c ^ (1 / 2 : ℂ)
  have hc := continuous_cosh_mul a
  have e1 : ∀ r : ℝ, (((∫ t, g t * g' (r - t) : ℝ)) : ℂ) * Complex.cosh ((r : ℂ) * a)
      = ∫ t : ℝ, ((g t * g' (r - t) : ℝ) : ℂ) * Complex.cosh ((r : ℂ) * a) := by
    intro r
    rw [integral_mul_const, integral_complex_ofReal]
  simp_rw [e1]
  rw [integral_integral_swap (conv_kernel_integrable h h' hc)]
  have e2 : ∀ t : ℝ, ∫ r : ℝ, ((g t * g' (r - t) : ℝ) : ℂ) * Complex.cosh ((r : ℂ) * a)
      = ((g t : ℂ) * Complex.cosh ((t : ℂ) * a)) * ∫ s : ℝ, (g' s : ℂ) * Complex.cosh ((s : ℂ) * a) := by
    intro t
    have e3 := integral_add_right_eq_self
      (fun r : ℝ => ((g t * g' (r - t) : ℝ) : ℂ) * Complex.cosh ((r : ℂ) * a)) (μ := volume) t
    rw [← e3]
    have e4 : ∀ s : ℝ, ((g t * g' (s + t - t) : ℝ) : ℂ) * Complex.cosh (((s + t : ℝ) : ℂ) * a)
        = (g t : ℂ) * ((g' s : ℂ) * Complex.cosh (((s + t : ℝ) : ℂ) * a)) := by
      intro s
      rw [add_sub_cancel_right]
      push_cast
      ring
    simp_rw [e4]
    rw [integral_const_mul, bump_cosh_shift h' a t]
    ring
  simp_rw [e2]
  rw [integral_mul_const]

end GlobalTheory.CompanionTheory.WaveMult.CoshMul
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverSystemCechPullNaturalStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits GroundTheory.Arith.SchemeCoh GlobalTheory.SheafPull CrystallineSemistableComparison CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Cech
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_system_cech_pull_natural : ∀ {X Y : TopCat.{0}} (f : X ⟶ Y) {BY : Opens Y → Prop}
    {GoodY : ∀ {κ : Type}, Opens Y → (κ → Opens Y) → Prop} {BX : Opens X → Prop}
    {GoodX : ∀ {κ : Type}, Opens X → (κ → Opens X) → Prop} (hCY : IsCoverSystem BY GoodY) (hCX : IsCoverSystem BX GoodX)
    {κ ι : Type} (V : κ → Opens Y) (hV : iSup V = ⊤) (hVB : ∀ {n : ℕ} (i : Fin (n + 1) → κ), BY (inter V i))
    (U : ι → Opens X) (hU : iSup U = ⊤) (hUB : ∀ {n : ℕ} (i : Fin (n + 1) → ι), BX (inter U i)) (τ : ι → κ)
    (hτ : ∀ i, U i ≤ (Opens.map f).obj (V (τ i))) (n : ℕ) {G : AbSheaf Y} {G' : AbSheaf X}
    (hG : GoodAcyclic BY GoodY G) (hG' : GoodAcyclic BX GoodX G') (φ : G ⟶ (push f).obj G') (x : cechH G.obj V n),
    (cechHEquiv hCX U hU hUB n G' hG' : cechH G'.obj U n ≃+ Sheaf.H.{0} G' n) (cechPullH f φ.hom V U τ hτ n x) =
      hPull f φ n ((cechHEquiv hCY V hV hVB n G hG : cechH G.obj V n ≃+ Sheaf.H.{0} G n) x) := by
  first | exact @GlobalTheory.CompanionTheory.CechLerayPull.cechHEquiv_pull | exact GlobalTheory.CompanionTheory.CechLerayPull.cechHEquiv_pull | (intros; apply GlobalTheory.CompanionTheory.CechLerayPull.cechHEquiv_pull <;> assumption)
end

