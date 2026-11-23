module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0093
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0013

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PParamImageNull
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem ParamImageNull.segre_torusSmul {K : Type} [Fintype K] {ι : K → Type} (c : K → ℂ) (v : (Σ k, ι k) → ℂ) :
    segre (torusSmul c v) = (∏ k, c k) • segre v := by
  funext x
  simp [segre, torusSmul, Finset.prod_mul_distrib]

theorem ParamImageNull.differentiableAt_segre_comp {K : Type} [Fintype K] {ι : K → Type} {d : ℕ}
    {f : (Fin d → ℂ) → (Σ k, ι k) → ℂ} {w : Fin d → ℂ} (hf : DifferentiableAt ℂ f w) :
    DifferentiableAt ℂ (fun u => segre (f u)) w := by
  refine differentiableAt_pi.2 fun x => ?_
  simp only [segre]
  have hk : ∀ k, DifferentiableAt ℂ (fun u => f u ⟨k, x k⟩) w := fun k => differentiableAt_pi.1 hf ⟨k, x k⟩
  fun_prop

theorem ParamImageNull.proof : ParamImageNull.Statement := by
  intro K _ ι _ P d m V A γ N _hV hAV hA hγ hN Ψ _
  classical
  set G : Fin m → (Fin d → ℂ) → Fin (d + 1) → ℂ := fun i w => Ψ (segre (γ i w)) with hG
  set F : Fin m → (Fin d → ℂ) → Fin d → ℂ := fun i w l => G i w l.succ / G i w 0 with hF
  have hsub : {y : Fin d → ℂ | ∃ z ∈ mcPts P, z ∈ N ∧ Ψ (segre z) = Fin.cons 1 y} ⊆
      ⋃ i, F i '' (A i ∩ {w | G i w 0 ≠ 0}) := by
    rintro y ⟨z, hzP, hzN, hzy⟩
    obtain ⟨i, w, hw, c, hc, rfl⟩ := hN z ⟨hzN, hzP⟩
    rw [ParamImageNull.segre_torusSmul, map_smul] at hzy
    have h0 := congrFun hzy 0
    simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_zero] at h0
    have hG0 : G i w 0 ≠ 0 := by
      intro h
      rw [hG] at h
      simp only at h
      rw [h, mul_zero] at h0
      exact zero_ne_one h0
    refine Set.mem_iUnion.2 ⟨i, w, ⟨hw, hG0⟩, ?_⟩
    funext l
    have hl := congrFun hzy l.succ
    simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_succ] at hl
    simp only [hF]
    rw [div_eq_iff hG0, ← hl]
    have h0' : (∏ k, c k) * G i w 0 = 1 := h0
    calc G i w l.succ = G i w l.succ * ((∏ k, c k) * G i w 0) := by rw [h0', mul_one]
      _ = (∏ k, c k) * Ψ (segre (γ i w)) l.succ * G i w 0 := by simp only [hG]; ring
  refine measure_mono_null hsub (measure_iUnion_null fun i => ?_)
  refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
    (measure_mono_null Set.inter_subset_left (hA i))
  intro w ⟨hwA, hw0⟩
  have hγw : DifferentiableAt ℂ (γ i) w := (hγ i w (hAV i hwA)).differentiableAt
  have hGw : DifferentiableAt ℂ (G i) w :=
    (LinearMap.toContinuousLinearMap Ψ).differentiableAt.comp w (ParamImageNull.differentiableAt_segre_comp hγw)
  have hFw : DifferentiableAt ℂ (F i) w := by
    refine differentiableAt_pi.2 fun l => ?_
    show DifferentiableAt ℂ (fun u => G i u l.succ / G i u 0) w
    simp only [div_eq_mul_inv]
    exact (differentiableAt_pi.1 hGw l.succ).mul ((differentiableAt_pi.1 hGw 0).inv hw0)
  exact (hFw.restrictScalars ℝ).differentiableWithinAt

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PProjSmoothAlong
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open scoped ContDiff

theorem ProjSmoothAlong.proof (hO : HoloInjDerivInj.Statement) (hL : LocalOrbitChart.Statement) :
    ProjSmoothAlong.Statement := by
  intro II Ψ hΨ K hK ι hι Ω hΩ hQΩ E hE1 hE2 D M g hg z₀ hz₀
  set S := mcPts (mCoordIdeal D.y) with hS
  set x₀ := M.proj z₀ with hx₀
  obtain ⟨j, hj⟩ := M.atlas.cover x₀
  set e := M.atlas.chart j with he
  obtain ⟨W, hWo, hxW, s, hs, hsh⟩ := M.sections x₀
  obtain ⟨N, hNo, hzN, κ, hκa, hκt, hκi⟩ := hL K ι Ω D.y D.n D.arith D.smoothGeneric z₀ hz₀
  set σ : (Fin D.n → ℂ) → (Σ k, ι k) → ℂ := fun u => s (e.symm u) with hσ
  set f : (Fin D.n → ℂ) → (Fin D.n → ℂ) := fun u => κ (σ u) with hf
  set u₀ := e x₀ with hu₀
  set T := e.target ∩ e.symm ⁻¹' W with hT
  have hTo : IsOpen T := e.isOpen_inter_preimage_symm hWo
  have hσa : AnalyticOnNhd ℂ σ T := fun u hu => AnalyticAt.pi fun p => hsh p j u hu
  have hu₀t : u₀ ∈ e.target := e.map_source hj
  have hsymm₀ : e.symm u₀ = x₀ := e.left_inv hj
  have hu₀T : u₀ ∈ T := ⟨hu₀t, by simp only [Set.mem_preimage, hsymm₀]; exact hxW⟩

  have hσ₀ : σ u₀ = s x₀ := by simp only [hσ, hsymm₀]
  obtain ⟨hsx₀S, hsx₀p⟩ := hs x₀ hxW
  obtain ⟨c₀, hc₀, hc₀e⟩ := (M.fibre z₀ hz₀ (s x₀) hsx₀S).1 hsx₀p.symm
  have hsx₀N : s x₀ ∈ N := hc₀e ▸ (hκt z₀ hzN c₀ hc₀).1
  have hκs₀ : κ (s x₀) = κ z₀ := hc₀e ▸ (hκt z₀ hzN c₀ hc₀).2

  set T' := T ∩ σ ⁻¹' N with hT'
  have hT'o : IsOpen T' := hσa.continuousOn.isOpen_inter_preimage hTo hNo
  have hu₀T' : u₀ ∈ T' := ⟨hu₀T, by simp only [Set.mem_preimage, hσ₀]; exact hsx₀N⟩
  have hfa : AnalyticOnNhd ℂ f T' := fun u hu => (hκa (σ u) hu.2).comp (hσa u hu.1)
  have hinj : Set.InjOn f T' := by
    intro u hu u' hu' hfu
    obtain ⟨hmS, hmp⟩ := hs (e.symm u) hu.1.2
    obtain ⟨hmS', hmp'⟩ := hs (e.symm u') hu'.1.2
    obtain ⟨c, hc, hce⟩ := hκi (σ u) ⟨hu.2, hmS⟩ (σ u') ⟨hu'.2, hmS'⟩ hfu
    have hpe : M.proj (σ u) = M.proj (σ u') := (M.fibre (σ u) hmS (σ u') hmS').2 ⟨c, hc, hce⟩
    have h2 : e.symm u = e.symm u' := by
      simp only [hσ] at hpe
      rw [← hmp, ← hmp', hpe]
    rw [← e.right_inv hu.1.1, ← e.right_inv hu'.1.1, h2]

  have hDinj : Function.Injective (fderiv ℂ f u₀) := hO D.n f T' hT'o hfa hinj u₀ hu₀T'
  set Lc : (Fin D.n → ℂ) ≃L[ℂ] (Fin D.n → ℂ) :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℂ f u₀ : (Fin D.n → ℂ) →ₗ[ℂ] (Fin D.n → ℂ)) hDinj).toContinuousLinearEquiv
    with hLc
  have hFD : HasFDerivAt f (Lc : (Fin D.n → ℂ) →L[ℂ] (Fin D.n → ℂ)) u₀ := by
    have hcoe : (Lc : (Fin D.n → ℂ) →L[ℂ] (Fin D.n → ℂ)) = fderiv ℂ f u₀ := by
      ext v; rfl
    rw [hcoe]
    exact (hfa u₀ hu₀T').differentiableAt.hasFDerivAt
  have hcd : ContDiffAt ℂ ω f u₀ := (hfa u₀ hu₀T').contDiffAt
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  set linv := hcd.localInverse hFD hn with hlinv
  have hlinv_cd : ContDiffAt ℂ ω linv (f u₀) := hcd.to_localInverse hFD hn
  have hlinv₀ : linv (f u₀) = u₀ := hcd.localInverse_apply_image hFD hn
  have hleft : ∀ᶠ u in 𝓝 u₀, linv (f u) = u := (hcd.hasStrictFDerivAt' hFD hn).eventually_left_inverse
  have hfu₀ : f u₀ = κ z₀ := by simp only [hf, hσ₀, hκs₀]

  set Φ : ((Σ k, ι k) → ℂ) → (Fin D.n → ℂ) := fun z => linv (κ z) with hΦ
  have hΦcd : ContDiffAt ℂ ω Φ z₀ := by
    have h1 : ContDiffAt ℂ ω linv (κ z₀) := hfu₀ ▸ hlinv_cd
    exact h1.comp z₀ (hκa z₀ hzN).contDiffAt
  have hΦ₀ : Φ z₀ = u₀ := by simp only [hΦ, ← hfu₀, hlinv₀]
  obtain ⟨V₁, hV₁, hΦV₁⟩ := hΦcd.contDiffOn (m := ∞) le_top (fun _ => rfl)
  have hΦV₁R : ContDiffOn ℝ ∞ Φ V₁ := hΦV₁.restrict_scalars ℝ
  set V₂ := V₁ ∩ Φ ⁻¹' e.target with hV₂
  have hV₂n : V₂ ∈ 𝓝 z₀ :=
    inter_mem hV₁ (hΦcd.continuousAt.preimage_mem_nhds (e.open_target.mem_nhds (hΦ₀ ▸ hu₀t)))
  have hgs : ContDiffOn ℝ ∞ (g ∘ e.symm) e.target := by
    have := hg j
    simpa [ReciprocityTheory.AnForm.M.FinHolAtlas.Smooth, ReciprocityTheory.AnForm.M.FinHolAtlas.SmoothOn] using this
  have hGV₂ : ContDiffOn ℝ ∞ (fun z => g (e.symm (Φ z))) V₂ :=
    hgs.comp (hΦV₁R.mono Set.inter_subset_left) (fun z hz => hz.2)

  have hcont : ContinuousWithinAt M.proj S z₀ := M.cont z₀ hz₀
  have htend : Tendsto (fun w => e (M.proj w)) (𝓝[S] z₀) (𝓝 u₀) :=
    (e.continuousAt hj).tendsto.comp hcont.tendsto
  have hev1 : ∀ᶠ w in 𝓝[S] z₀, M.proj w ∈ e.source ∩ W :=
    hcont.tendsto ((e.open_source.inter hWo).mem_nhds ⟨hj, hxW⟩)
  have hev2 : ∀ᶠ w in 𝓝[S] z₀, linv (f (e (M.proj w))) = e (M.proj w) := htend.eventually hleft
  have hev3 : ∀ᶠ w in 𝓝[S] z₀, w ∈ N := nhdsWithin_le_nhds (hNo.mem_nhds hzN)
  have hev : ∀ᶠ w in 𝓝[S] z₀, (M.proj w ∈ e.source ∩ W ∧ linv (f (e (M.proj w))) = e (M.proj w)) ∧ w ∈ N :=
    (hev1.and hev2).and hev3
  rw [eventually_nhdsWithin_iff] at hev
  refine ⟨V₂ ∩ {w | w ∈ S → (M.proj w ∈ e.source ∩ W ∧ linv (f (e (M.proj w))) = e (M.proj w)) ∧ w ∈ N},
    inter_mem hV₂n hev, fun z => g (e.symm (Φ z)), hGV₂.mono Set.inter_subset_left, ?_⟩
  rintro w ⟨⟨-, hw⟩, hwS⟩
  obtain ⟨⟨⟨hxe, hxW'⟩, hli⟩, hwN⟩ := hw hwS
  obtain ⟨hsS, hsp⟩ := hs (M.proj w) hxW'
  obtain ⟨c, hc, hce⟩ := (M.fibre w hwS (s (M.proj w)) hsS).1 hsp.symm
  have hfe : f (e (M.proj w)) = κ w := by
    simp only [hf, hσ, e.left_inv hxe]
    rw [hce]
    exact (hκt w hwN c hc).2
  have hΦw : Φ w = e (M.proj w) := by
    simp only [hΦ]
    rw [← hfe, hli]
  simp only [hΦw, e.left_inv hxe]

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PPtsMonoSemipos
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem maDensity_logDiv_nonneg_of_sheet {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {L : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hsp : IsSemipositiveH P L) {r : ℝ} (hr : 0 < r) {e : ℕ}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ}
    {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} (h : IsSheet P Ψ y w γ) :
    0 ≤ maDensity (fun (_ : Fin e) y' => Real.log (L.h (γ y')) / r) y := by
  have hA : AnalyticAt ℂ γ y := sheet_analyticAt osgood h
  have hpts : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P := h.2.mono fun _ hy' => hy'.2.1
  have hy : γ y ∈ mcPts P := hpts.self_of_nhds
  have hh : ContDiffAt ℝ 2 L.h (γ y) :=
    (hsp.1.contDiffAt
      (HilbertSamuel.IntegralAgainstPositive.isOpen_blocksNonzero.mem_nhds hy.1)).of_le
      (WithTop.coe_le_coe.2 le_top)
  have hlog : ContDiffAt ℝ 2 (fun z => Real.log (L.h z)) (γ y) := hh.log (L.pos _ hy.1).ne'
  have h2 : ContDiffAt ℝ 2 (fun y' => Real.log (L.h (γ y'))) y :=
    hlog.comp y (hA.contDiffAt.restrict_scalars ℝ)
  have h2r : ContDiffAt ℝ 2 (fun y' => Real.log (L.h (γ y')) / r) y := h2.div_const r
  rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_maDensity_eq_maDens]
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun _ => ?_
  refine ReciprocityTheory.AnForm.A.hessC_posSemidef_of_levi _ _ h2r fun ξ => ?_
  have hfun : (fun y' => Real.log (L.h (γ y')) / r) =
      fun y' => (fun _ : Fin e → ℂ => (0 : ℝ)) y' + r⁻¹ * Real.log (L.h (γ y')) := by
    funext y'
    simp [div_eq_inv_mul]
  rw [hfun, ReciprocityTheory.AnForm.levi_add_smul r⁻¹ contDiffAt_const h2 ξ]
  have h0 : ReciprocityTheory.AnForm.levi (fun _ : Fin e → ℂ => (0 : ℝ)) y ξ = 0 := by
    simp [ReciprocityTheory.AnForm.levi]
  have hc : 0 ≤ ReciprocityTheory.AnForm.levi ((fun z => Real.log (L.h z)) ∘ γ) y ξ := by
    rw [ReciprocityTheory.AnForm.levi_comp (φ := fun z => Real.log (L.h z)) ξ hA hlog]
    exact hsp.2 _ hy _ (HilbertSamuel.IntegralAgainstPositive.isConeTangent_of_sheet le_rfl hA hpts ξ)
  rw [h0, zero_add]
  exact mul_nonneg (inv_nonneg.2 hr.le) hc

theorem PtsMonoSemipos.proof : PtsMonoSemipos.Statement := by
  intro K _ ι _ P e L r g₁ g₂ N hP hL hr hN hle h1 h2
  classical
  unfold ptsIntegral
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ
  swap
  · rw [dite_eq_right hΨ, dite_eq_right hΨ]
  rw [dite_eq_left hΨ, dite_eq_left hΨ]
  have hΨg : IsGoodProj P hΨ.choose := hΨ.choose_spec
  unfold ptsIntegralAt
  refine integral_mono_ae (h1 _ hΨg) (h2 _ hΨg) ?_
  rw [Filter.EventuallyLE, ae_iff]
  refine measure_mono_null (fun y hy => ?_) (hN _ hΨg)
  by_contra hyB
  apply hy
  have hfin := fibreFinite K ι P e hΨ.choose hP hΨg y
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine Finset.sum_le_sum fun w _ => ?_
  unfold sheetDensity
  by_cases hγ : ∃ γ, IsSheet P hΨ.choose y w γ
  · rw [dite_eq_left hγ, dite_eq_left hγ]
    obtain ⟨-, hev⟩ := hγ.choose_spec
    obtain ⟨-, hmem, hproj⟩ := hev.self_of_nhds
    have hnot : hγ.choose y ∉ N := fun hN' => hyB ⟨hγ.choose y, hmem, hN', hproj⟩
    exact mul_le_mul_of_nonneg_right (hle _ hmem hnot)
      (maDensity_logDiv_nonneg_of_sheet hL hr hγ.choose_spec)
  · rw [dite_eq_right hγ, dite_eq_right hγ]

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PRegAboveWeight
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem RegAboveWeight.proof (hBd : BdPtsNull.Statement) (hDiv : DivisorPreimageNull.Statement) :
    RegAboveWeight.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X
  obtain ⟨C, t₀, ht₀, hb⟩ := GroundTheory.Heights₂.Heights.Regular.ChartMollifiedBounds.proof
    GroundTheory.Heights₂.Heights.Regular.TruncPsh.proof X.M.Xc D.n X.M.atlas X.S.R X.S.ρ
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < t₀ ∧ 0 ≤ X.S.K t :=
    (eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds ht₀)).and
      (X.S_tied.K_tendsto.eventually_ge_atTop 0)
  obtain ⟨t₂, ht₂, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.1 hev
  refine ⟨t₂, ht₂, D.Bd ∪ {z | X.M.proj z ∉ X.S.R.Yo}, ?_, fun t ht htt z hz hzN => ?_⟩
  ·
    intro Ψ' hΨ'
    refine measure_mono_null (fun y hy => ?_)
      (measure_union_null (hBd II Ψ K ι Ω E D Ψ' hΨ') (hDiv K ι _ _ X.M X.S.R Ψ' hΨ'))
    obtain ⟨z, hz, hzN, hzy⟩ := hy
    rcases hzN with h | h
    · exact Or.inl ⟨z, hz, h, hzy⟩
    · exact Or.inr ⟨z, hz, h, hzy⟩
  obtain ⟨htt₀, hK⟩ : t < t₀ ∧ 0 ≤ X.S.K t := hsub ⟨ht, htt⟩
  have hBdz : z ∉ D.Bd := fun h => hzN (Or.inl h)
  have hY : X.M.proj z ∈ X.S.R.Yo := by
    by_contra h
    exact hzN (Or.inr h)
  have hXo : z ∈ D.Xo := Set.mem_sdiff_of_mem hz hBdz

  obtain ⟨k, hk⟩ := X.S.R.cover (X.M.proj z)
  have hkm := X.S.R.inner_subset_mid k hk
  have hε : 0 ≤ X.S.e1 t := ht.le.trans (X.S.e1_ge t ht)

  have h1 := ((hb t ht htt₀).2 (X.S.K t) hK k (X.M.proj z) hkm).2.2 hY

  have h2 := GroundTheory.Heights₂.Heights.Regular.LogLogRegularisation.le_glue X.S.R.toPotentialCharts
    (fun j x => X.S.R.phReg X.S.ρ (X.S.K t) t j x + 4 * X.S.e1 t * X.S.η j x) hε hkm
  have h3 : X.S.regWeight t (X.M.proj z) = X.S.R.glue
      (fun j x => X.S.R.phReg X.S.ρ (X.S.K t) t j x + 4 * X.S.e1 t * X.S.η j x) (X.S.e1 t) (X.M.proj z) := rfl
  have hη := X.S.cutoff.eq_zero k (X.M.proj z) hk
  simp only [hη, mul_zero, add_zero] at h2

  have h4 := X.S.ph_eq z ⟨hXo, hz⟩ hY
  have h5 : phMu X.H z = Real.log ((muLine X.H).h z) := rfl
  rw [h3, h5]
  linarith

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitTTop
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem ComponentSetting.mixN_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
    {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]
    (X : ComponentSetting D O Lt) (B : ℕ) (t : ℝ) : X.mixN B (D.n + 1) t = arLimFun X.H X.S B t := by
  unfold ComponentSetting.mixN arLimFun
  congr 1
  funext j
  simp [j.is_lt]

theorem StokesLimitTTop.proof (hE : TopNMixedExpand.Statement) (hM : TopNMixedLimit.Statement) :
    StokesLimitTTop.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q hII hAr hp hpq
  have hlim : ∀ k ∈ Finset.range (D.n + 2), ∃ L : ℝ, Tendsto (X.mixN B k) (𝓝[>] 0) (𝓝 L) := by
    intro k hk
    rcases Nat.lt_or_ge k (D.n + 1) with h | h
    · exact hM II Ψ K ι Ω E D O Lt X B hII hAr k (Nat.lt_succ_iff.1 h)
    · have hk' : k = D.n + 1 := le_antisymm (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) h
      subst hk'
      obtain ⟨L, hL⟩ := hAr
      exact ⟨L, hL.congr fun t => (X.mixN_top B t).symm⟩
  choose! L hL using hlim
  refine ⟨∑ k ∈ Finset.range (D.n + 2), ((D.n + 1).choose k : ℝ) * ((p : ℝ) / q) ^ (D.n + 1 - k) * L k, ?_⟩
  refine Tendsto.congr' ((hE II Ψ K ι Ω E D O Lt X B p q hII hp hpq).mono fun t ht => ht.symm) ?_
  exact tendsto_finsetSum _ fun k hk => (hL k hk).const_mul _

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PStokesLimitTp
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]

theorem ComponentSetting.wSt_torusSmul (X : ComponentSetting D O Lt) (B p q : ℕ) (t t' : ℝ) (c : K → ℂ) (hc : ∀ k, c k ≠ 0)
    (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts (mCoordIdeal D.y)) :
    X.wSt B p q t t' (torusSmul c z) = X.wSt B p q t t' z := by
  have ha : (X.MUq B p q t').a = (X.NbarQ B p q t).a := by
    simp only [ComponentSetting.MUq, MUc, ComponentSetting.NbarQ, smoothRepConj_a, smoothRep_a]
    rfl
  have hpos : 0 < ∏ k, ‖c k‖ ^ (X.NbarQ B p q t).a k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hc k)) _
  have e : torusSmul c z = fun x => c x.1 * z x := rfl
  have h1 := (X.MUq B p q t').smul c z hc
  have h2 := (X.NbarQ B p q t).smul c z hc
  rw [ha] at h1
  unfold ComponentSetting.wSt
  rw [e, h1, h2, Real.log_mul hpos.ne' ((X.MUq B p q t').pos z hz.1).ne',
    Real.log_mul hpos.ne' ((X.NbarQ B p q t).pos z hz.1).ne']
  ring

theorem StokesLimitTp.proof (hLim : TpIntegrandLimit.Statement) (hAbove : RegAboveWeight.Statement)
    (hU : TpCuspIntegrable.Statement) (hConv : PtsBddConv.Statement) (hMono : PtsMonoSemipos.Statement) :
    StokesLimitTp.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q hp hpq
  have hq : 1 ≤ q := hp.trans hpq
  have hr : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨t₁, ht₁, hL⟩ := hLim II Ψ K ι Ω E D O Lt X B p q hq
  obtain ⟨t₃, ht₃, N₂, hN₂, hA⟩ := hAbove II Ψ K ι Ω E D O Lt X
  refine ⟨min t₁ t₃, lt_min ht₁ ht₃, fun t ht0 ht hsp => ?_⟩
  obtain ⟨N₁, C, s₀, hs₀, hN₁, hbd, hpt⟩ := hL t ht0 (ht.trans (min_le_left _ _))
  obtain ⟨hint, hlim⟩ := hConv K ι (mCoordIdeal D.y) D.n (X.NbarQ B p q t) q (X.wSt B p q t)
    (fun z => cuspCorr X.H X.Cd z - (Real.log (X.S.ref.h z) + X.S.regWeight t (X.M.proj z))) N₁ C s₀
    D.arith hsp.1 hr hN₁ hs₀
    (fun s hs hs' => ⟨(hbd s hs hs').1, (hbd s hs hs').2, fun c hc z hz => X.wSt_torusSmul B p q t s c hc z hz⟩) hpt
  refine ⟨hlim, ?_⟩
  refine hMono K ι (mCoordIdeal D.y) D.n (X.NbarQ B p q t) q _ (fun z => X.Cd.cuspWeight z / 2) N₂ D.arith hsp hr
    hN₂ (fun z hz hzN => ?_) hint (hU II Ψ K ι Ω E D O Lt X B p q t hsp.1)
  have h := hA t ht0 (ht.trans (min_le_right _ _)) z hz hzN
  show phMu X.H z + X.Cd.cuspWeight z / 2 - (Real.log (X.S.ref.h z) + X.S.regWeight t (X.M.proj z)) ≤
    X.Cd.cuspWeight z / 2
  linarith

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StNbarLeviChart
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi)

def NbarLeviChart.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
    [Module O Lt] (X : ComponentSetting D O Lt) (B p q : ℕ) (t : ℝ),
    X.M.atlas.Smooth (X.S.regWeight t) →
    ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ w, IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal D.y) z w →
    ∀ k : Fin X.S.R.N, X.M.proj z ∈ X.S.R.mid k →
      ∃ v : Fin D.n → ℂ, IsChartVel X.M (X.S.R.chart k) z w v ∧
        levi (fun y => Real.log ((X.NbarQ B p q t).h y)) z w =
          q * levi (X.S.R.chartFun (X.S.regWeight t) k) (X.S.R.chart k (X.M.proj z)) v +
            p * levi (fun y => Real.log (D.A'.h y)) z w

section Inhabitants

namespace Line

open GroundTheory.Heights₂.Heights (CP)

end Line

end Inhabitants

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

