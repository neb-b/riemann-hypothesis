module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0001
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0027
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0037

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgeFlat
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge

open ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter Set

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ} (R : AnRes P J e)

theorem brFib_finite' (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (y : Fin e → ℂ) :
    (brQ R Ψ ⁻¹' {y} ∩ {x | R.lift x x ∉ mcPts J ∧ Ψ (segre (R.lift x x)) 0 ≠ 0}).Finite := by
  refine Set.Finite.of_finite_image (f := brW R Ψ) ((fibreFinite K ι P e Ψ hP hΨ y).subset ?_)
    ((brW_injOn R Ψ).mono fun x hx => hx.2)
  rintro _ ⟨x, hx, rfl⟩
  have := brW_mem_fibre R Ψ hP.1 hP.2.1.2.1 hx.2.2
  rwa [show brQ R Ψ x = y from hx.1] at this

theorem lift_mem_iff {x z : R.X} (hz : z ∈ R.U x) :
    R.lift z z ∈ mcPts J ↔ R.lift x z ∈ mcPts J := by
  obtain ⟨c, hc, hzc⟩ := R.compat z x z ⟨R.mem_U z, hz⟩
  constructor
  · intro h
    refine mem_mcPts_of_sameOrbit R.homog ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩ h
    funext p
    rw [hzc]
    field_simp [hc p.1]
  · intro h
    exact mem_mcPts_of_sameOrbit R.homog ⟨c, hc, hzc⟩ h

theorem psi_lift_eq {x z : R.X} (hz : z ∈ R.U x)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    ∃ μ : ℂ, μ ≠ 0 ∧ Ψ (segre (R.lift z z)) = μ • Ψ (segre (R.lift x z)) := by
  obtain ⟨c, hc, hzc⟩ := R.compat z x z ⟨R.mem_U z, hz⟩
  exact ⟨∏ k, c k, Finset.prod_ne_zero_iff.mpr fun k _ => hc k, by rw [hzc, segre_smul, map_smul]⟩

theorem isOpen_chart_notB (j : Fin R.A.n) :
    IsOpen ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | R.lift x x ∉ mcPts J}) := by
  rw [isOpen_iff_mem_nhds]
  rintro u1 ⟨hu1, hB1⟩
  set x1 := (R.A.chart j).symm u1
  have hV : (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x1 ∈ 𝓝 u1 :=
    ((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x1)).mem_nhds ⟨hu1, R.mem_U x1⟩
  have hnot : ¬ ∀ f ∈ J, eval (R.lift x1 x1) (map (Int.castRingHom ℂ) f) = 0 := fun h =>
    hB1 ⟨(R.mem x1 x1 (R.mem_U x1)).1, h⟩
  push Not at hnot
  obtain ⟨f, hfJ, hf0⟩ := hnot
  have hcont : ContinuousAt (fun u => eval (R.lift x1 ((R.A.chart j).symm u))
      (map (Int.castRingHom ℂ) f)) u1 :=
    (MvPolynomial.continuous_eval _).continuousAt.comp
      (analyticAt_lift_chart R x1 j ⟨hu1, R.mem_U x1⟩).continuousAt
  filter_upwards [hV, hcont.eventually_ne hf0] with u hu hne
  refine ⟨hu.1, fun hB => ?_⟩
  exact hne (((lift_mem_iff R hu.2).mp hB).2 f hfJ)

theorem not_flat (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) {O : Set (Fin e → ℂ)}
    (hO : IsOpen O) (hOt : O ⊆ (R.A.chart j).target) (hne : O.Nonempty)
    (h0 : ∀ u ∈ O, Ψ (segre (R.lift ((R.A.chart j).symm u) ((R.A.chart j).symm u))) 0 ≠ 0)
    (han : AnalyticOnNhd ℂ (brQ R Ψ ∘ (R.A.chart j).symm) O)
    (hdet : ∀ u ∈ O, LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) u :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0) : False := by
  set O' := O ∩ ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | R.lift x x ∉ mcPts J})
    with hO'def
  have hO' : IsOpen O' := hO.inter (isOpen_chart_notB R j)
  have hne' : O'.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    obtain ⟨u, hu⟩ := hne
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO u hu
    have hsub : Metric.ball u r ⊆
        (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | R.lift x x ∈ mcPts J} := by
      intro v hv
      have hvO := hball hv
      refine ⟨hOt hvO, ?_⟩
      by_contra hB
      have : v ∈ O' := ⟨hvO, hOt hvO, hB⟩
      rw [h] at this
      exact this
    exact (Metric.measure_ball_pos volume u hr).ne' (measure_mono_null hsub (R.null j))
  obtain ⟨y, hy⟩ := exists_infinite_fibre hO' hne' (han.mono inter_subset_left)
    (fun u hu => hdet u hu.1)
  refine (brFib_finite' R Ψ hP hΨ y).not_infinite ((Set.Infinite.image
    (((R.A.chart j).symm.injOn.mono (show O' ⊆ (R.A.chart j).target from
      fun u hu => hOt hu.1)).mono inter_subset_left) hy).mono ?_)
  rintro _ ⟨u, ⟨huO, hqu⟩, rfl⟩
  exact ⟨hqu, huO.2.2, h0 u huO.1⟩

theorem det_brQ_chart (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {x : R.X}
    {j k : Fin R.A.n} (hj : x ∈ (R.A.chart j).source) (hk : x ∈ (R.A.chart k).source)
    (h0 : Ψ (segre (R.lift x x)) 0 ≠ 0) :
    LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) =
      LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) *
      LinearMap.det (fderiv ℂ (R.A.chart k ∘ (R.A.chart j).symm) (R.A.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) := by
  set u := R.A.chart j x
  have hsu : (R.A.chart j).symm u = x := (R.A.chart j).left_inv hj
  set T := R.A.chart k ∘ (R.A.chart j).symm with hTdef
  have huk : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' (R.A.chart k).source :=
    ⟨(R.A.chart j).map_source hj, by rw [mem_preimage, hsu]; exact hk⟩
  have hT : AnalyticAt ℂ T u := R.A.holo j k u huk
  have hTu : T u = R.A.chart k x := by simp only [hTdef, Function.comp_apply, hsu]
  have hQk := analyticAt_brQ R Ψ x k hk h0
  have heq : brQ R Ψ ∘ (R.A.chart j).symm =ᶠ[𝓝 u] (brQ R Ψ ∘ (R.A.chart k).symm) ∘ T := by
    filter_upwards [((R.A.chart j).isOpen_inter_preimage_symm (R.A.chart k).open_source).mem_nhds
      huk] with v hv
    simp only [hTdef, Function.comp_apply, (R.A.chart k).left_inv hv.2]
  rw [heq.fderiv_eq, fderiv_comp u (by rw [hTu]; exact hQk.differentiableAt) hT.differentiableAt,
    hTu]
  exact LinearMap.det_comp _ _

end GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgeIntegrable
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge

open ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter Set

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}

theorem brIntegrable_of (hLA : LogAbsLocIntStatement) (R : AnRes P J e)
    (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι) (hL : ∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm (L j))
    (hA : ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A) (hs : IsSectionOn P A s) :
    MIntegrable R.A (fun j => potOf R (L j)) (fun x => logNorm A s (R.lift x x)) := by
  intro j K hK hKc
  refine LocallyIntegrableOn.integrableOn_compact_subset ?_ hK hKc
  intro u0 hu0
  obtain ⟨a, ha, hsa, -⟩ := hs
  set x0 := (R.A.chart j).symm u0
  set V := (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x0 with hVdef
  have hV : IsOpen V := (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)
  have hu0V : u0 ∈ V := ⟨hu0, R.mem_U x0⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV u0 hu0V
  set B := Metric.closedBall u0 (r / 2) with hBdef
  have hBV : B ⊆ V := (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hBc : IsCompact B := isCompact_closedBall _ _
  have hBm : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  refine ⟨B, mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds _ (by linarith)), ?_⟩
  set γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun u => R.lift x0 ((R.A.chart j).symm u) with hγdef
  have hγ : ∀ u ∈ V, AnalyticAt ℂ γ u := fun u hu => analyticAt_lift_chart R x0 j hu
  set f : (Fin e → ℂ) → ℂ := fun u => eval (γ u) (map (Int.castRingHom ℂ) s) with hfdef
  have hf : AnalyticOnNhd ℂ f V := fun u hu =>
    analyticAt_eval_poly _ fun p => analyticAt_pi_iff.mp (hγ u hu) p
  set H : (Fin e → ℂ) → ℝ := fun u => A.h (γ u) with hHdef
  have hblk : ∀ u ∈ V, ∀ k, ∃ i, γ u ⟨k, i⟩ ≠ 0 := fun u hu => (R.mem x0 _ hu.2).1
  have hHc : ContinuousOn H V := fun u hu =>
    ((hA.continuousOn.continuousAt (isOpen_blockNonzero.mem_nhds (hblk u hu))).comp
      (hγ u hu).continuousAt).continuousWithinAt
  have hHpos : ∀ u ∈ V, 0 < H u := fun u hu => A.pos _ (hblk u hu)
  have hF : ∀ u ∈ V, logNorm A s (R.lift ((R.A.chart j).symm u) ((R.A.chart j).symm u)) =
      Real.log (‖f u‖ / H u) := by
    intro u hu
    obtain ⟨c, hc, hzc⟩ := R.compat _ x0 _ ⟨R.mem_U _, hu.2⟩
    rw [hzc]
    exact logNorm_bsmul A ha hsa hc (γ u)
  have hDc : ContinuousOn (locDens R.A (fun i => potOf R (L i)) j) B :=
    (locDensCont R.A _ (fun i => isPotential_potOf R (hL i)) j).mono
      (hBV.trans inter_subset_left)
  obtain ⟨M, hM⟩ := hBc.exists_bound_of_continuousOn hDc
  have hlogf : IntegrableOn (fun u => Real.log ‖f u‖) B :=
    (hLA e V f hV hf).integrableOn_compact_subset hBV hBc
  have hlogH : IntegrableOn (fun u => Real.log (H u)) B :=
    ((hHc.mono hBV).log fun u hu => (hHpos u (hBV hu)).ne').integrableOn_compact hBc
  have hfc : ContinuousOn f B := fun u hu => (hf u (hBV hu)).continuousAt.continuousWithinAt
  have hmeas : AEStronglyMeasurable (fun u => Real.log (‖f u‖ / H u) *
      locDens R.A (fun i => potOf R (L i)) j u) (volume.restrict B) := by
    have h1 : AEStronglyMeasurable (fun u => ‖f u‖ / H u) (volume.restrict B) :=
      (hfc.norm.div (hHc.mono hBV) fun u hu => (hHpos u (hBV hu)).ne').aestronglyMeasurable hBm
    exact (Real.measurable_log.comp_aemeasurable h1.aemeasurable).aestronglyMeasurable.mul
      (hDc.aestronglyMeasurable hBm)
  have hint : IntegrableOn (fun u => Real.log (‖f u‖ / H u) *
      locDens R.A (fun i => potOf R (L i)) j u) B := by
    refine Integrable.mono' ((hlogf.norm.add hlogH.norm).mul_const M) hmeas ?_
    refine ae_restrict_of_forall_mem hBm fun u hu => ?_
    rw [norm_mul]
    have hb := abs_log_div_le (norm_nonneg (f u)) (hHpos u (hBV hu))
    simp only [Real.norm_eq_abs] at hb ⊢
    exact mul_le_mul hb (hM u hu) (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
  refine hint.congr_fun (fun u hu => ?_) hBm
  simp only
  rw [hF u (hBV hu)]

end GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgeSheet
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge

open ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}
  (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

theorem exists_sheet_brW (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι)
    (hP : IsArithVar P (e + 1)) (hL : ∀ j, IsSmoothHerm (L j)) (hs : IsSectionOn P A s)
    (x : R.X) (hx : x ∉ brBad R Ψ) :
    ∃ γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ, IsSheet P Ψ (brQ R Ψ x) (brW R Ψ x) γ ∧
      logNorm A s (γ (brQ R Ψ x)) * maDensity (fun j y' => pot L j (γ y')) (brQ R Ψ x) =
        logNorm A s (R.lift x x) * pushDens R.A (fun j => potOf R (L j)) (brQ R Ψ) x := by
  classical
  obtain ⟨k0⟩ := hP.1
  have hPh : IsMultiHomogIdeal P := hP.2.1.2.1
  set j := chartIdx R.A x with hjdef
  have hj : x ∈ (R.A.chart j).source := Classical.choose_spec (R.A.cover x)
  set u := R.A.chart j x with hudef
  have hsu : (R.A.chart j).symm u = x := (R.A.chart j).left_inv hj
  have huU : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
    ⟨(R.A.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact R.mem_U x⟩
  obtain ⟨hQa, hQd⟩ := brGood R Ψ x hx j hj
  set Q := brQ R Ψ ∘ (R.A.chart j).symm with hQdef
  set Df := fderiv ℂ Q u with hDf
  have hdet : Df.det ≠ 0 := hQd
  set Ce := Df.toContinuousLinearEquivOfDetNeZero hdet with hCe
  have hCe' : (Ce : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) = Df :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero Df hdet
  have hstrict : HasStrictFDerivAt Q (Ce : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) u := by
    rw [hCe']; exact hQa.hasStrictFDerivAt
  set F := hstrict.toOpenPartialHomeomorph Q with hF
  have hFc : (F : (Fin e → ℂ) → (Fin e → ℂ)) = Q := hstrict.toOpenPartialHomeomorph_coe
  have hus : u ∈ F.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hyt : Q u ∈ F.target := hstrict.image_mem_toOpenPartialHomeomorph_target
  have hσu : F.symm (Q u) = u := by
    have := F.left_inv hus
    rwa [hFc] at this
  have hy0 : Q u = brQ R Ψ x := by simp only [hQdef, Function.comp_apply, hsu]
  have hσa : AnalyticAt ℂ F.symm (Q u) := by
    refine F.analyticAt_symm (i := Ce) hyt ?_ ?_
    · rw [hσu, hFc]; exact hQa
    · rw [hσu, hFc, hCe']
  have hσd : HasFDerivAt F.symm (Ce.symm : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) (Q u) := by
    refine F.hasFDerivAt_symm hyt ?_
    rw [hσu, hFc, hCe']
    exact hQa.differentiableAt.hasFDerivAt
  set γ₀ : (Fin e → ℂ) → (Σ k, ι k) → ℂ :=
    fun y' => R.lift x ((R.A.chart j).symm (F.symm y')) with hγ₀
  have hγ₀a : AnalyticAt ℂ γ₀ (Q u) := (analyticAt_lift_chart R x j huU).comp_of_eq hσa hσu
  have hγ₀u : γ₀ (Q u) = R.lift x x := by simp only [hγ₀, hσu, hsu]
  set ψ0 : (Fin e → ℂ) → ℂ := fun y' => Ψ (segre (γ₀ y')) 0 with hψ0
  have hψ0a : AnalyticAt ℂ ψ0 (Q u) :=
    analyticAt_pi_iff.mp ((analyticAt_segre_lift R Ψ x j huU).comp_of_eq hσa hσu) 0
  have hψ0u : ψ0 (Q u) ≠ 0 := by
    simp only [hψ0, hγ₀u]; exact projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx
  set c : (Fin e → ℂ) → K → ℂ := fun y' => Function.update (fun _ => (1 : ℂ)) k0 (ψ0 y')⁻¹
    with hcdef
  have hc_ne : ∀ y', ψ0 y' ≠ 0 → ∀ k, c y' k ≠ 0 := by
    intro y' h k
    by_cases hk : k = k0
    · subst hk; simp [hcdef, h]
    · simp [hcdef, Function.update_of_ne hk]
  have hca : ∀ k, AnalyticAt ℂ (fun y' => c y' k) (Q u) := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp only [hcdef, Function.update_self]; exact hψ0a.inv hψ0u
    · simp only [hcdef, Function.update_of_ne hk]; exact analyticAt_const
  set γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ := fun y' => bsmul (c y') (γ₀ y') with hγdef
  have hγa : AnalyticAt ℂ γ (Q u) :=
    analyticAt_pi_iff.mpr fun p => (hca p.1).mul (analyticAt_pi_iff.mp hγ₀a p)
  have hprod : ∀ y', ∏ k, c y' k = (ψ0 y')⁻¹ := fun y' => by
    simp [hcdef, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  have hseg : ∀ y', segre (γ y') = (ψ0 y')⁻¹ • segre (γ₀ y') := fun y' => by
    rw [← hprod y']; exact segre_smul (c y') (γ₀ y')
  refine ⟨γ, ⟨?_, ?_⟩, ?_⟩
  · rw [← hy0, hseg]
    simp only [hψ0, hγ₀u]
    rfl
  · rw [← hy0]
    have hU : ∀ᶠ y' in 𝓝 (Q u),
        F.symm y' ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
      hσa.continuousAt.preimage_mem_nhds (by
        rw [hσu]; exact ((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)).mem_nhds huU)
    filter_upwards [hγa.eventually_analyticAt, hU, F.open_target.mem_nhds hyt,
      hψ0a.continuousAt.eventually_ne hψ0u] with y' ha hUy ht h0
    refine ⟨ha.differentiableAt, mcPts_smul hPh (c y') (hc_ne y' h0) (R.mem x _ hUy.2), ?_⟩
    have hq : Q (F.symm y') = y' := by
      have := F.right_inv ht
      rwa [hFc] at this
    rw [hQdef, Function.comp_apply, brQ_eq_local R Ψ hUy.2] at hq
    rw [hseg, map_smul]
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_zero]
      exact inv_mul_cancel₀ h0
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
      rw [← congrFun hq i, div_eq_inv_mul]
  · rw [← hy0]
    obtain ⟨a, ha, hsa, -⟩ := hs
    have hlog : logNorm A s (γ (Q u)) = logNorm A s (R.lift x x) := by
      show logNorm A s (bsmul (c (Q u)) (γ₀ (Q u))) = _
      rw [logNorm_bsmul A ha hsa (hc_ne _ hψ0u), hγ₀u]
    rw [hlog]
    congr 1
    have hblk : ∀ k, ∃ i, γ₀ (Q u) ⟨k, i⟩ ≠ 0 := by
      rw [hγ₀u]; exact (R.mem x x (R.mem_U x)).1
    have hH : ∀ i, cxHessian (fun y' => pot L i (γ y')) (Q u) =
        cxHessian (fun y' => pot L i (γ₀ y')) (Q u) := by
      intro i
      set G : (Fin e → ℂ) → ℂ :=
        fun y' => ((-((L i).a k0 : ℝ) : ℝ) : ℂ) * Complex.log (ψ0 y' / ψ0 (Q u)) with hG
      set C : ℝ := -(((L i).a k0 : ℝ) * Real.log ‖ψ0 (Q u)‖) with hC
      have hGa : AnalyticAt ℂ G (Q u) := by
        refine analyticAt_const.mul ((hψ0a.div analyticAt_const hψ0u).clog ?_)
        show ψ0 (Q u) / ψ0 (Q u) ∈ Complex.slitPlane
        rw [div_self hψ0u]
        exact Complex.one_mem_slitPlane
      have heq : (fun y' => pot L i (γ y')) =ᶠ[𝓝 (Q u)]
          fun y' => pot L i (γ₀ y') + (G y').re + C := by
        filter_upwards [hψ0a.continuousAt.eventually_ne hψ0u,
          hγ₀a.continuousAt.eventually (isOpen_blockNonzero.mem_nhds hblk)] with y' h0 hb
        have hpos : 0 < (L i).h (γ₀ y') := (L i).pos _ hb
        have hn0 : ‖(ψ0 y')⁻¹‖ ^ (L i).a k0 ≠ 0 :=
          zpow_ne_zero _ (norm_ne_zero_iff.mpr (inv_ne_zero h0))
        simp only [pot, hγdef]
        rw [show bsmul (c y') (γ₀ y') = fun p => c y' p.1 * γ₀ y' p from rfl, (L i).smul _ _ (hc_ne y' h0), prod_norm_update_zpow, Real.log_mul hn0 hpos.ne',
          hG, hC, Complex.re_ofReal_mul, Complex.log_re, norm_div,
          Real.log_div (norm_ne_zero_iff.mpr h0) (norm_ne_zero_iff.mpr hψ0u), Real.log_zpow,
          norm_inv, Real.log_inv]
        ring
      rw [cxHessian_congr heq, cxHessian_add_re (φ := fun y' => pot L i (γ₀ y')) C
        (pot_contDiffAt (hL i) hγ₀a hblk) hGa]
    have hmd : maDensity (fun i y' => pot L i (γ y')) (Q u) =
        maDensity (fun i y' => pot L i (γ₀ y')) (Q u) := by
      simp only [maDensity, hH]
    rw [hmd, maDensity_eq_maDens]
    have hcd : ∀ i, ContDiffAt ℝ 2 (fun v => pot L i (R.lift x ((R.A.chart j).symm v)))
        (F.symm (Q u)) := by
      intro i
      rw [hσu]
      exact pot_contDiffAt (hL i) (analyticAt_lift_chart R x j huU)
        (by rw [hsu]; exact (R.mem x x (R.mem_U x)).1)
    have hcomp : ReciprocityTheory.AnForm.maDens (fun i y' => pot L i (γ₀ y')) (Q u) =
        ReciprocityTheory.AnForm.maDens (fun i v => pot L i (R.lift x ((R.A.chart j).symm v)))
          (F.symm (Q u)) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC F.symm (Q u)).det :=
      ReciprocityTheory.AnForm.A.maDens_comp (fun i v => pot L i (R.lift x ((R.A.chart j).symm v)))
        F.symm (Q u) hσa hcd
    have hdetinv : LinearMap.det ((Ce.symm : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = (LinearMap.det (Df : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)))⁻¹ := by
      have := ContinuousLinearEquiv.det_coe_symm Ce
      rw [hCe'] at this
      exact this
    have hloc : ReciprocityTheory.AnForm.maDens (fun i v => pot L i (R.lift x ((R.A.chart j).symm v))) u =
        locDens R.A (fun i => potOf R (L i)) j u := by
      unfold locDens
      rw [hsu]
      rfl
    rw [hcomp, hσu, ReciprocityTheory.AnForm.A.det_jacC, hσd.fderiv, hdetinv, hloc, Complex.normSq_inv,
      Complex.normSq_eq_norm_sq]
    unfold pushDens
    rw [div_eq_mul_inv]

end GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GeneratedModOfSubsingleton
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GeneratedMod (S : Type*) [CommRing S] {K : Type*} [Fintype K] [LinearOrder K] (ι : K → Type*)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] {M : Type*} [AddCommGroup M] [Module (MRingOver S ι) M]
    [Module S M] [IsScalarTower S (MRingOver S ι) M] (𝓜 : (K → ℤ) → Submodule S M) (d : K → ℤ) : Prop :=
  ∀ I : KH.Cell K ι 0, ∀ x ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) d,
    ∃ (t : MRingOver S ι) (a : K → ℕ) (r : ℕ) (p : Fin r → MRingOver S ι) (z : Fin r → KH.CechC S ι M 0),
      t ∈ KH.cellMon S I.1 ∧ IsMultiHomog t a ∧ (∀ j, IsMultiHomog (p j) a) ∧
      (∀ j, z j ∈ KH.cechZc ι 𝓜 d 0) ∧ t • x = ∑ j, p j • z j I

def H1GenAmple (S : Type) [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (N : K → ℤ) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M),
    Module.Finite (MRingOver S ι) M → KH.IsMGraded S ι 𝓜 → V ≤ Module.annihilator (MRingOver S ι) M →
    ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c →
      Subsingleton (KH.cechHc ι 𝓜 (e + c • N) 1) ∧ GeneratedMod S ι 𝓜 (e + c • N)

section Point

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type}
  [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] [∀ k, Subsingleton (ι k)]




omit [Fintype K] [∀ k, Subsingleton (ι k)] in
theorem isMultiHomog_one_zero : IsMultiHomog (1 : MRingOver S ι) 0 := by
  classical
  intro m hm k
  have : m = 0 := by
    rw [mem_support_iff, coeff_one] at hm
    split_ifs at hm with h
    · exact h.symm
    · exact absurd rfl hm
  simp [this]

end Point

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsBisAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter MeasureTheory

noncomputable section

def TensorPowerL2Degree.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsSmallGeneratedDatum P0 y D A → IsConjInvariantH A →
    ∃ (μ : Measure ((Σ k, ι k) → ℂ)) (m : ℕ),
      IsProbabilityMeasure μ ∧ μ (mcPts (mCoordIdeal y))ᶜ = 0 ∧ IsZariskiDenseMeasure (mCoordIdeal y) μ ∧
      1 ≤ m ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ q : ℕ in atTop,
        ∀ (r : ℕ) (ψ : chartLat y A.a (m * q) →+ EuclideanSpace ℝ (Fin r)), Function.Injective ψ →
          (∀ s : chartLat y A.a (m * q), ‖ψ s‖ = sectionL2Norm μ y A (m * q) (s : Ω)) →
          ∀ [DiscreteTopology (imageLattice ψ)] [IsZLattice ℝ (imageLattice ψ)],
            -Real.log (ZLattice.covolume (imageLattice ψ)) ≤
              (II K ι (mCoordIdeal y) (D + 1) (fun _ => A) + ε) *
                (((m * q : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

