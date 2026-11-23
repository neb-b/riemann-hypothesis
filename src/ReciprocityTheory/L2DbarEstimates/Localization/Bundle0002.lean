module

public import ReciprocityTheory.L2DbarEstimates.Localization.UnweightBackStatement
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports

@[expose] public section

-- bundled from ReciprocityTheory.L2DbarEstimates.Localization.ChartA
section
namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set Function
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

section Tr

variable {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M]
  [BorelSpace M] {n : ℕ} {z : M → V n} {e : OpenPartialHomeomorph M (V n)}

theorem chT_aem_symm : AEMeasurable (e.symm : V n → M) (volume.restrict e.target) := e.continuousOn_symm.aemeasurable e.open_target.measurableSet

theorem chT_lint (hz : IsLocalHomeomorph z) (he : IsChart n z e) (f : M → ℝ≥0∞)
    (hf : AEMeasurable f (vol n z)) (hs : ∀ x, x ∉ e.source → f x = 0) :
    ∫⁻ x, f x ∂vol n z = ∫⁻ y in e.target, f (e.symm y) := by
  have hsub : Function.support f ⊆ e.source := fun x hx => by
    by_contra h; exact hx (hs x h)
  rw [← setLIntegral_eq_of_support_subset hsub, vol_restrict_source n z hz e he]
  have hf' : AEMeasurable f (Measure.map e.symm (volume.restrict e.target)) := by
    rw [← vol_restrict_source n z hz e he]; exact hf.restrict
  exact lintegral_map' hf' (chT_aem_symm (e := e))

theorem chT_int {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (hz : IsLocalHomeomorph z)
    (he : IsChart n z e) (f : M → E)
    (hf : AEStronglyMeasurable f (vol n z)) (hs : ∀ x, x ∉ e.source → f x = 0) :
    ∫ x, f x ∂vol n z = ∫ y in e.target, f (e.symm y) := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hs, vol_restrict_source n z hz e he]
  have hf' : AEStronglyMeasurable f (Measure.map e.symm (volume.restrict e.target)) := by
    rw [← vol_restrict_source n z hz e he]; exact hf.restrict
  exact integral_map (chT_aem_symm (e := e)) hf'

theorem chT_aesm {E : Type*} [NormedAddCommGroup E] (hz : IsLocalHomeomorph z)
    (he : IsChart n z e) (f : M → E) (hf : AEStronglyMeasurable f (vol n z)) :
    AEStronglyMeasurable (e.target.indicator (f ∘ e.symm)) volume := by
  have hf' : AEStronglyMeasurable f (Measure.map e.symm (volume.restrict e.target)) := by
    rw [← vol_restrict_source n z hz e he]; exact hf.restrict
  exact (aestronglyMeasurable_indicator_iff e.open_target.measurableSet).2
    (hf'.comp_aemeasurable (chT_aem_symm (e := e)))

theorem chartTransport_indicator_memLp_two {E : Type*} [NormedAddCommGroup E] [T2Space M] (hz : IsLocalHomeomorph z)
    (he : IsChart n z e) (f : M → E) (hf : LocalL2Isometry (vol n z) f) (hc : HasCompactSupport f)
    (hsub : tsupport f ⊆ e.source) :
    MemLp (e.target.indicator (f ∘ e.symm)) 2 volume := by
  have hae := chT_aesm hz he f hf.1
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    two_ne_zero ENNReal.ofNat_ne_top hae).2
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  have hz0 : ∀ x, x ∉ tsupport f → f x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hs : ∀ x, x ∉ e.source → ‖f x‖ₑ ^ 2 = 0 := by
    intro x hx
    simp [hz0 x (fun h => hx (hsub h))]
  have e1 : ∫⁻ y, ‖e.target.indicator (f ∘ e.symm) y‖ₑ ^ 2 =
      ∫⁻ y in e.target, ‖f (e.symm y)‖ₑ ^ 2 := by
    rw [← lintegral_indicator e.open_target.measurableSet]
    congr 1; funext y
    by_cases hy : y ∈ e.target <;> simp [hy]
  rw [e1, ← chT_lint hz he (fun x => ‖f x‖ₑ ^ 2) (hf.1.enorm.pow_const 2) hs]
  calc ∫⁻ x, ‖f x‖ₑ ^ 2 ∂vol n z = ∫⁻ x in tsupport f, ‖f x‖ₑ ^ 2 ∂vol n z := by
        rw [setLIntegral_eq_of_support_subset]
        intro x hx
        by_contra h
        exact hx (by simp [hz0 x h])
    _ < ⊤ := hf.2 _ hc

end Tr

theorem chT_plateau {n : ℕ} (K U : Set (V n)) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ ρ : V n → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ tsupport ρ ⊆ U ∧
      ∃ O : Set (V n), IsOpen O ∧ K ⊆ O ∧ ∀ y ∈ O, ρ y = 1 := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨t, htK, htf, hcov⟩ := hK.finite_cover_balls (e := δ / 3) (by positivity)
  let bx : ∀ x : V n, ContDiffBump x := fun x => ⟨δ / 3, 2 * δ / 3, by positivity, by linarith⟩
  let ψ : V n → ℝ := fun y => ∑ x ∈ htf.toFinset, bx x y
  let ρ : V n → ℝ := fun y => Real.smoothTransition (ψ y)
  have hψd : ContDiff ℝ ∞ ψ := ContDiff.sum fun x _ => (bx x).contDiff
  have hρd : ContDiff ℝ ∞ ρ := Real.smoothTransition.contDiff.comp hψd
  have hsuppψ : ∀ y, ψ y ≠ 0 → y ∈ Metric.cthickening (2 * δ / 3) K := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
    have hb : y ∈ Metric.ball x (bx x).rOut := by rw [← (bx x).support_eq]; exact hxy
    exact Metric.thickening_subset_cthickening _ _
      (Metric.ball_subset_thickening (htK (htf.mem_toFinset.1 hx)) _ hb)
  have hsuppρ : ∀ y, y ∉ Metric.cthickening (2 * δ / 3) K → ρ y = 0 := by
    intro y hy
    have : ψ y = 0 := by by_contra h; exact hy (hsuppψ y h)
    simp only [ρ, this, Real.smoothTransition.zero]
  have hts : tsupport ρ ⊆ Metric.cthickening (2 * δ / 3) K :=
    closure_minimal (fun y hy => by by_contra h; exact hy (hsuppρ y h)) Metric.isClosed_cthickening
  refine ⟨ρ, hρd, HasCompactSupport.intro hK.cthickening hsuppρ,
    hts.trans ((Metric.cthickening_mono (by linarith) K).trans hδU),
    ⋃ x ∈ t, Metric.ball x (δ / 3), isOpen_biUnion fun _ _ => Metric.isOpen_ball, hcov, ?_⟩
  intro y hy
  simp only [Set.mem_iUnion] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  have h1 : bx x y = 1 := (bx x).one_of_mem_closedBall (Metric.ball_subset_closedBall hxy)
  have h2 : 1 ≤ ψ y := by
    calc (1 : ℝ) = bx x y := h1.symm
      _ ≤ ψ y := Finset.single_le_sum (f := fun x' => bx x' y) (fun x' _ => (bx x').nonneg)
          (htf.mem_toFinset.2 hx)
  exact Real.smoothTransition.one_of_one_le h2

theorem chT_comp {n : ℕ} {M : Type*} [MeasurableSpace M] (μ : Measure M) (G : M → V n)
    (hG : AEStronglyMeasurable G μ) (j : Fin n) : AEStronglyMeasurable (fun x => G x j) μ := (EuclideanSpace.proj (𝕜 := ℂ) j).continuous.comp_aestronglyMeasurable hG

section Main

variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n} {e : OpenPartialHomeomorph M (V n)}

theorem chT_test (hExt : ExtendStatement n M) (hz : IsLocalHomeomorph z) (he : IsChart n z e)
    (ψ : V n → ℂ) (hψd : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψt : tsupport ψ ⊆ e.target) :
    IsTest n z (e.source.indicator (ψ ∘ e)) ∧
    (∀ y ∈ e.target, e.source.indicator (ψ ∘ e) (e.symm y) = ψ y) ∧
    (∀ j, ∀ y ∈ e.target, d n z j (e.source.indicator (ψ ∘ e)) (e.symm y) = wd n j ψ y ∧
        db n z j (e.source.indicator (ψ ∘ e)) (e.symm y) = wdb n j ψ y) := by
  obtain ⟨h1, h2, -, h4⟩ := hExt z hz e ψ he hψd hψc hψt
  refine ⟨⟨h1, h2⟩, fun y hy => ?_, fun j y hy => ?_⟩
  · rw [Set.indicator_of_mem (e.map_target hy), Function.comp_apply, e.right_inv hy]
  · have := h4 j (e.symm y) (e.map_target hy)
    rw [e.right_inv hy] at this
    exact this

theorem chT_mulρ (ρ : V n → ℝ) (hρd : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (U : Set (V n)) (hρt : tsupport ρ ⊆ U) (φ : V n → ℂ) (hφd : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ (fun y => (ρ y : ℂ) * φ y) ∧ HasCompactSupport (fun y => (ρ y : ℂ) * φ y) ∧
      tsupport (fun y => (ρ y : ℂ) * φ y) ⊆ U := by
  refine ⟨(Complex.ofRealCLM.contDiff.comp hρd).mul hφd, ?_, ?_⟩
  · exact (hρc.comp_left Complex.ofReal_zero).mul_right
  · exact tsupport_mul_subset_left.trans ((tsupport_comp_subset Complex.ofReal_zero ρ).trans hρt)

theorem chT_wd (ρ : V n → ℝ) (φ : V n → ℂ) (O : Set (V n)) (hOo : IsOpen O)
    (h1 : ∀ y ∈ O, ρ y = 1) (y : V n) (hy : y ∈ O) (j : Fin n) :
    wd n j (fun y => (ρ y : ℂ) * φ y) y = wd n j φ y ∧
      wdb n j (fun y => (ρ y : ℂ) * φ y) y = wdb n j φ y := by
  have hev : (fun y => (ρ y : ℂ) * φ y) =ᶠ[𝓝 y] φ := by
    filter_upwards [hOo.mem_nhds hy] with w hw
    rw [h1 w hw]; simp
  have := hev.fderiv_eq (𝕜 := ℝ)
  unfold wd wdb
  rw [this]
  exact ⟨rfl, rfl⟩

end Main

end

end ReciprocityTheory.L2DbarEstimates.F
end

-- bundled from ReciprocityTheory.L2DbarEstimates.Localization.Choice
section
namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem smoothReal_continuous {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (f : M → ℝ) (hf : SmoothR n z f) : Continuous f := by
  have hc : Continuous (fun x => (f x : ℂ)) := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    obtain ⟨e, hxe, rfl⟩ := hz x
    have hch : IsChart n (⇑e) e := fun _ _ => rfl
    have h1 := (hf e hch).continuousOn
    have h2 : ContinuousOn (fun y => (f y : ℂ)) e.source := by
      refine (h1.comp e.continuousOn (fun y hy => e.map_source hy)).congr fun y hy => ?_
      simp [Function.comp, e.left_inv hy]
    exact h2.continuousAt (e.open_source.mem_nhds hxe)
  exact (Complex.continuous_re.comp hc).congr fun x => by simp

theorem sSup_image_le_max {M : Type*} (g : M → ℝ) (s : Set M) (B : ℝ)
    (hB : ∀ x ∈ s, g x ≤ B) : sSup (g '' s) ≤ max B 0 := by
  refine Real.sSup_le ?_ (le_max_right _ _)
  rintro _ ⟨x, hx, rfl⟩
  exact (hB x hx).trans (le_max_left _ _)

theorem choice (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (hChi : ChiStatement) (hPsi : PsiStatement n M)
    (hShell : ShellStatement n M) (hLZ : LeviNormSqStatement n M) (hChain : ChainStatement n M) :
    ChoiceStatement n M := by
  intro X ph v C ε hph hv hC hε
  have hz := X.isLocalHomeomorph

  have hE : SmoothR n X.z (fun y => X.e y + ‖X.z y‖ ^ 2) :=
    SmoothR.add n X.z _ _ X.smooth_e (hLZ X.z hz).1
  have hEc : Continuous (fun y => X.e y + ‖X.z y‖ ^ 2) := smoothReal_continuous n X.z hz _ hE
  have hExh : ∀ b : ℝ, IsCompact {x | X.e x + ‖X.z x‖ ^ 2 ≤ b} := by
    intro b
    refine (X.isCompact_le b).of_isClosed_subset (isClosed_le hEc continuous_const) ?_
    intro x hx
    simp only [mem_ofPred_eq] at hx ⊢
    nlinarith [sq_nonneg ‖X.z x‖]
  have hLeviE : ∀ x ξ, (∑ j, ‖ξ j‖ ^ 2) ≤ (Levi n X.z (fun y => X.e y + ‖X.z y‖ ^ 2) x ξ).re := by
    intro x ξ
    rw [levi_add n X.z X.e (fun y => ‖X.z y‖ ^ 2) (SmoothR.ckR n X.z 2 _ X.smooth_e)
      (SmoothR.ckR n X.z 2 _ (hLZ X.z hz).1) x ξ, (hLZ X.z hz).2 x ξ, Complex.add_re,
      Complex.ofReal_re]
    linarith [X.levi_e x ξ]

  obtain ⟨b0, hb0⟩ := hC.bddAbove_image hEc.continuousOn
  set a : ℝ := b0 + 1 with ha
  have hCa : ∀ x ∈ C, X.e x + ‖X.z x‖ ^ 2 < a := by
    intro x hx
    have := hb0 ⟨x, hx, rfl⟩
    linarith

  obtain ⟨ψ, hψ, hψ0, hcut⟩ := hPsi X.z hz (fun y => X.e y + ‖X.z y‖ ^ 2) a hE hExh
  have hψc : Continuous ψ := smoothReal_continuous n X.z hz _ hψ
  have hdc : Continuous (fun x => dSqR n X.z ψ x) := by
    unfold dSqR
    refine continuous_finsetSum _ (fun j _ => ?_)
    exact ((Smooth.continuous n X.z hz _ (Smooth.d n X.z j _ hψ)).norm).pow 2

  obtain ⟨R1, hR1, hR1χ⟩ := hShell X.z hz (fun y => X.e y + ‖X.z y‖ ^ 2) ph ψ v a hEc hExh
    (smoothReal_continuous n X.z hz _ hph) hψc hv
  set g : M → ℝ := fun x => max (2 * ψ x) ((1 + 1 / ε) * dSqR n X.z ψ x) with hg
  have hgc : Continuous g := (continuous_const.mul hψc).max (continuous_const.mul hdc)
  set R : ℝ → ℝ := fun t => max (R1 t) (sSup (g '' {x | X.e x + ‖X.z x‖ ^ 2 ≤ t})) with hR
  have hRb : ∀ b : ℝ, BddAbove (R '' Iic b) := by
    intro b
    obtain ⟨B1, hB1⟩ := hR1 b
    obtain ⟨B, hB⟩ := (hExh b).bddAbove_image hgc.continuousOn
    refine ⟨max B1 (max B 0), ?_⟩
    rintro y ⟨t, ht, rfl⟩
    refine max_le_max (hB1 ⟨t, ht, rfl⟩) (sSup_image_le_max g _ B ?_)
    intro x hx
    exact hB ⟨x, (show X.e x + ‖X.z x‖ ^ 2 ≤ b from le_trans hx ht), rfl⟩
  have hgR : ∀ x, g x ≤ R (X.e x + ‖X.z x‖ ^ 2) := by
    intro x
    refine le_max_of_le_right (le_csSup ((hExh _).bddAbove_image hgc.continuousOn) ⟨x, ?_, rfl⟩)
    exact (le_refl (X.e x + ‖X.z x‖ ^ 2))

  obtain ⟨χ, hχ, hχa, hχ0, hχ1, hχ2, hχR⟩ := hChi a R hRb
  have hχs : SmoothR n X.z (fun y => χ (X.e y + ‖X.z y‖ ^ 2)) := SmoothR.comp n X.z χ hχ _ hE
  refine ⟨fun x => ph x + χ (X.e x + ‖X.z x‖ ^ 2), ψ, fun y => X.e y + ‖X.z y‖ ^ 2,
    {x | X.e x + ‖X.z x‖ ^ 2 < a}, SmoothR.add n X.z _ _ hph hχs, hψ, hEc, hcut,
    isOpen_lt hEc continuous_const, hCa, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp only [mem_ofPred_eq] at hx
    refine ⟨?_, (hψ0 x (by linarith)).1⟩
    show ph x + χ (X.e x + ‖X.z x‖ ^ 2) = ph x
    rw [hχa _ hx.le, add_zero]
  · intro x
    have : 2 * ψ x ≤ χ (X.e x + ‖X.z x‖ ^ 2) := by
      by_cases h : X.e x + ‖X.z x‖ ^ 2 ≤ a + 1
      · rw [(hψ0 x h).1, mul_zero]; exact hχ0 _
      · push Not at h
        exact ((le_max_left _ _).trans (hgR x)).trans (hχR _ h.le).1
    linarith
  · intro x ξ
    have hχ2' : ContDiff ℝ 2 χ := hχ.of_le (by norm_cast)
    rw [levi_add n X.z ph (fun y => χ (X.e y + ‖X.z y‖ ^ 2)) (SmoothR.ckR n X.z 2 _ hph)
      (SmoothR.ckR n X.z 2 _ hχs) x ξ, Complex.add_re,
      hChain X.z hz χ (fun y => X.e y + ‖X.z y‖ ^ 2) hχ2' hE x ξ, Complex.add_re,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.ofReal_re]
    have hs : 0 ≤ ∑ j, ‖ξ j‖ ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have h1 : (1 + 1 / ε) * dSqR n X.z ψ x * ∑ j, ‖ξ j‖ ^ 2 ≤
        deriv χ (X.e x + ‖X.z x‖ ^ 2) * ∑ j, ‖ξ j‖ ^ 2 := by
      by_cases h : X.e x + ‖X.z x‖ ^ 2 ≤ a + 1
      · rw [(hψ0 x h).2, mul_zero, zero_mul]
        exact mul_nonneg (hχ1 _) hs
      · push Not at h
        exact mul_le_mul_of_nonneg_right
          (((le_max_right _ _).trans (hgR x)).trans (hχR _ h.le).2) hs
    have h2 : deriv χ (X.e x + ‖X.z x‖ ^ 2) * ∑ j, ‖ξ j‖ ^ 2 ≤
        deriv χ (X.e x + ‖X.z x‖ ^ 2) *
          (Levi n X.z (fun y => X.e y + ‖X.z y‖ ^ 2) x ξ).re :=
      mul_le_mul_of_nonneg_left (hLeviE x ξ) (hχ1 _)
    have h3 : 0 ≤ deriv (deriv χ) (X.e x + ‖X.z x‖ ^ 2) *
        ‖dDot n X.z (fun y => ((X.e y + ‖X.z y‖ ^ 2 : ℝ) : ℂ)) x ξ‖ ^ 2 :=
      mul_nonneg (hχ2 _) (sq_nonneg _)
    linarith
  · refine ⟨hv.aestronglyMeasurable, ?_⟩
    exact hR1χ χ hχ0 (fun t ht => (hχR t ht).1.trans' (le_max_left _ _))

end

end ReciprocityTheory.L2DbarEstimates.F
end

-- bundled from ReciprocityTheory.L2DbarEstimates.Localization.Extend
section
namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem extend_support_subset {n : ℕ} {M : Type*} [TopologicalSpace M]
    (e : OpenPartialHomeomorph M (V n)) (G : V n → ℂ) (q : M)
    (hq : e.source.indicator (G ∘ e) q ≠ 0) : q ∈ e.symm '' tsupport G := by
  have hq' : q ∈ e.source := by
    by_contra h; exact hq (Set.indicator_of_notMem h _)
  rw [Set.indicator_of_mem hq'] at hq
  exact ⟨e q, subset_tsupport _ hq, e.left_inv hq'⟩

theorem extend_eventuallyEq {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (e e' : OpenPartialHomeomorph M (V n)) (G : V n → ℂ) (he : IsChart n z e)
    (he' : IsChart n z e') (y : V n) (hy : y ∈ e'.target) (hs : e'.symm y ∈ e.source) :
    (e.source.indicator (G ∘ e) ∘ e'.symm) =ᶠ[𝓝 y] G := by
  have hopen : IsOpen (e'.target ∩ e'.symm ⁻¹' e.source) :=
    e'.isOpen_inter_preimage_symm e.open_source
  filter_upwards [hopen.mem_nhds ⟨hy, hs⟩] with w hw
  obtain ⟨hw1, hw2⟩ := hw
  have hw3 : e'.symm w ∈ e'.source := e'.map_target hw1
  rw [Function.comp_apply, Set.indicator_of_mem (show e'.symm w ∈ e.source from hw2), Function.comp_apply, ← he hw2, he' hw3,
    e'.right_inv hw1]

theorem extend (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : ExtendStatement n M := by
  intro z _hz e G he hG hGc hGt
  have hK : IsCompact (e.symm '' tsupport G) :=
    hGc.image_of_continuousOn (e.continuousOn_symm.mono hGt)
  have hKs : e.symm '' tsupport G ⊆ e.source := by
    rintro _ ⟨y, hy, rfl⟩; exact e.map_target (hGt hy)
  have hts : tsupport (e.source.indicator (G ∘ e)) ⊆ e.symm '' tsupport G :=
    closure_minimal (fun q hq => extend_support_subset e G q hq) hK.isClosed
  have hw : ∀ e'' : OpenPartialHomeomorph M (V n), IsChart n z e'' → ∀ x ∈ e''.source, x ∈ e.source →
      (e.source.indicator (G ∘ e) ∘ e''.symm) =ᶠ[𝓝 (z x)] G ∧ z x = e x := by
    intro e'' h1 x h2 hx
    have hzx : z x = e'' x := h1 h2
    refine ⟨?_, he hx⟩
    rw [hzx]
    refine extend_eventuallyEq z e e'' G he h1 (e'' x) (e''.map_source h2) ?_
    rw [e''.left_inv h2]; exact hx
  refine ⟨?_, hK.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hKs, ?_⟩
  · intro e' he' y hy
    by_cases hs : e'.symm y ∈ e.source
    · exact (hG.contDiffAt.congr_of_eventuallyEq
        (extend_eventuallyEq z e e' G he he' y hy hs)).contDiffWithinAt
    · have hq : e'.symm y ∉ tsupport (e.source.indicator (G ∘ e)) := fun h => hs (hKs (hts h))
      have h0 := notMem_tsupport_iff_eventuallyEq.1 hq
      have h0' := h0.comp_tendsto (e'.continuousAt_symm hy).tendsto
      exact (contDiffAt_const.congr_of_eventuallyEq h0').contDiffWithinAt
  · intro j x hx
    have key : ∀ e'' : OpenPartialHomeomorph M (V n), IsChart n z e'' → x ∈ e''.source →
        wd n j (e.source.indicator (G ∘ e) ∘ e''.symm) (z x) = wd n j G (e x) ∧
        wdb n j (e.source.indicator (G ∘ e) ∘ e''.symm) (z x) = wdb n j G (e x) := by
      intro e'' h1 h2
      obtain ⟨hev, hzx⟩ := hw e'' h1 x h2 hx
      constructor
      · unfold wd; rw [hev.fderiv_eq, hzx]
      · unfold wdb; rw [hev.fderiv_eq, hzx]
    have hex : ∃ e'' : OpenPartialHomeomorph M (V n), IsChart n z e'' ∧ x ∈ e''.source := ⟨e, he, hx⟩
    constructor
    · simp only [d, dif_pos hex]
      exact (key _ (Classical.choose_spec hex).1 (Classical.choose_spec hex).2).1
    · simp only [db, dif_pos hex]
      exact (key _ (Classical.choose_spec hex).1 (Classical.choose_spec hex).2).2

end

end ReciprocityTheory.L2DbarEstimates.F
end

-- bundled from ReciprocityTheory.L2DbarEstimates.Localization.IntegrableOnCompactOfLocL2
section
namespace ReciprocityTheory.L2DbarEstimates.F

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff

noncomputable section

theorem multA_integrable_of_sq {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsFiniteMeasure ν]
    (F : α → ℂ) (hF : AEStronglyMeasurable F ν) (h : ∫⁻ x, ‖F x‖ₑ ^ 2 ∂ν < ⊤) :
    Integrable F ν := by
  have h2 : MemLp F 2 ν := by
    rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      two_ne_zero ENNReal.ofNat_ne_top hF]
    simpa using h
  exact h2.integrable one_le_two

theorem integrableOn_compact_of_locL2 {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    (μ : Measure M) [IsFiniteMeasureOnCompacts μ] (u : M → ℂ) (hu : LocalL2Isometry μ u)
    (K : Set M) (hK : IsCompact K) : IntegrableOn u K μ := by
  unfold LocalL2Isometry at hu
  have : IsFiniteMeasure (μ.restrict K) := ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  exact multA_integrable_of_sq (μ.restrict K) u hu.1.restrict (hu.2 K hK)

private lemma localL2Isometry_comp_of_norm_le {M E F : Type*} [TopologicalSpace M] [MeasurableSpace M]
    [NormedAddCommGroup E] [NormedAddCommGroup F] (μ : Measure M) (f : M → E) (g : E → F)
    (hg : Continuous g) (hb : ∀ e, ‖g e‖ ≤ ‖e‖) (hf : LocalL2Isometry μ f) :
    LocalL2Isometry μ (fun x => g (f x)) := by
  unfold LocalL2Isometry at hf ⊢
  refine ⟨hg.comp_aestronglyMeasurable hf.1, fun C hC => lt_of_le_of_lt ?_ (hf.2 C hC)⟩
  refine lintegral_mono fun x => ?_
  gcongr
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
  exact ENNReal.ofReal_le_ofReal (hb _)

theorem locL2_form_component {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    (μ : Measure M) (f : M → V n) (hf : LocalL2Isometry μ f) (j : Fin n) :
    LocalL2Isometry μ (fun x => f x j) := by
  refine localL2Isometry_comp_of_norm_le μ f (fun v : V n => v j) (EuclideanSpace.proj (𝕜 := ℂ) j).continuous ?_ hf
  intro v
  rw [EuclideanSpace.norm_eq]
  exact le_trans (le_abs_self _) (Real.abs_le_sqrt (Finset.single_le_sum
    (f := fun i => ‖v i‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ j)))

theorem locL2_two_form_component {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    (μ : Measure M) (σ : M → Fin n → Fin n → ℂ) (hσ : LocalL2Isometry μ σ) (j k : Fin n) :
    LocalL2Isometry μ (fun x => σ x j k) := by
  refine localL2Isometry_comp_of_norm_le μ σ (fun s : Fin n → Fin n → ℂ => s j k)
    ((continuous_apply k).comp (continuous_apply j)) ?_ hσ
  intro s
  exact (norm_le_pi_norm (s j) k).trans (norm_le_pi_norm s j)

theorem multA_intOn_w {M : Type*} [TopologicalSpace M] [T2Space M] [MeasurableSpace M]
    [OpensMeasurableSpace M] (μ : Measure M) [IsFiniteMeasureOnCompacts μ]
    (u : M → ℂ) (ph : M → ℝ) (hph : Continuous ph) (hu : AEStronglyMeasurable u μ)
    (h : ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-ph x)) ∂μ < ⊤)
    (K : Set M) (hK : IsCompact K) : IntegrableOn u K μ := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hph.continuousOn
  have : IsFiniteMeasure (μ.restrict K) := ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  refine multA_integrable_of_sq (μ.restrict K) u hu.restrict ?_
  have hpt : ∀ x ∈ K, ‖u x‖ₑ ^ 2 ≤
      ENNReal.ofReal (Real.exp C) * ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-ph x)) := by
    intro x hx
    have hx' : ph x ≤ C := le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hC x hx)
    have h1 : 1 ≤ Real.exp C * Real.exp (-ph x) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_mul (Real.exp_pos C).le]
    apply ENNReal.ofReal_le_ofReal
    calc ‖u x‖ ^ 2 = ‖u x‖ ^ 2 * 1 := by ring
      _ ≤ ‖u x‖ ^ 2 * (Real.exp C * Real.exp (-ph x)) := by gcongr
      _ = Real.exp C * (‖u x‖ ^ 2 * Real.exp (-ph x)) := by ring
  calc ∫⁻ x in K, ‖u x‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ x in K, ENNReal.ofReal (Real.exp C) *
          ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-ph x)) ∂μ :=
        setLIntegral_mono_ae' hK.measurableSet (Eventually.of_forall hpt)
    _ = ENNReal.ofReal (Real.exp C) *
          ∫⁻ x in K, ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-ph x)) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp C) *
          ∫⁻ x, ENNReal.ofReal (‖u x‖ ^ 2 * Real.exp (-ph x)) ∂μ := by
        gcongr; exact Measure.restrict_le_self
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top h

theorem multA_int_mul {M : Type*} [TopologicalSpace M] [T2Space M] [MeasurableSpace M]
    [OpensMeasurableSpace M] (μ : Measure M) (u c : M → ℂ)
    (hu : ∀ K, IsCompact K → IntegrableOn u K μ) (hc : Continuous c) (hcs : HasCompactSupport c) :
    Integrable (fun x => u x * c x) μ := by
  have h1 : IntegrableOn (fun x => u x * c x) (tsupport c) μ :=
    (hu _ hcs).mul_continuousOn hc.continuousOn hcs
  exact (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right _ _).trans (subset_tsupport c))).mp h1

theorem multA_contR {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (hz : IsLocalHomeomorph z) (ph : M → ℝ) (hph : SmoothR n z ph) : Continuous ph := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨e, hx, hze⟩ := hz x
  have hc : IsChart n z e := fun y _ => by rw [hze]
  have hg := (hph e hc).continuousOn
  have h1 : ContinuousAt (((fun y => (ph y : ℂ)) ∘ e.symm) ∘ e) x :=
    (hg.continuousAt (e.open_target.mem_nhds (e.map_source hx))).comp (e.continuousAt hx)
  have h2 : ((fun y => (ph y : ℂ)) ∘ e.symm) ∘ e =ᶠ[𝓝 x] fun y => (ph y : ℂ) := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    simp [e.left_inv hy]
  have h3 := Complex.continuous_re.continuousAt.comp (h1.congr h2)
  simpa [Function.comp_def] using h3

end

end ReciprocityTheory.L2DbarEstimates.F
end

