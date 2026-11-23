module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OneStepOf

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.AeZero
section
open MeasureTheory
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

noncomputable section

namespace PositivityTheory.Rg.BcB.E2.P.Spec

theorem ae_zero {S : Type} [TopologicalSpace S] [CompactSpace S] [T2Space S] [MeasurableSpace S] [BorelSpace S]
    (ν : Measure S) [IsFiniteMeasure ν] [ν.Regular] (u : S → ℝ) (hu : Continuous u) (h0 : ∀ s, 0 ≤ u s)
    (hi : ∫ s, (u s : ℂ) ∂ν = 0) : ∀ᵐ s ∂ν, u s = 0 := by
  rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at hi
  have hint : Integrable u ν := integrableOn_univ.1 (hu.continuousOn.integrableOn_compact isCompact_univ)
  exact (integral_eq_zero_iff_of_nonneg (fun s => h0 s) hint).1 hi

end PositivityTheory.Rg.BcB.E2.P.Spec

namespace PositivityTheory.Rg.BcB.E2.P

open PositivityTheory.Rg.BcB.E2.P.Spec in
theorem spec : Gelf → Point → SpecMeas → SpecIso → Spec := by
  classical
  intro hG hP hM hI K _ _ _ B _ _ _ _ R p C₀ ε hp hε
  obtain ⟨S, _, _, _, π, e, hπ, he⟩ := hG K B R
  have hne : ∀ b, ‖e b‖ = ‖R b‖ := fun b => by rw [← hπ, he]
  obtain ⟨s₀, hs₀⟩ := hP B S e p fun b => (hp b).trans (hne b).ge
  let _ : MeasurableSpace S := borel S
  have : BorelSpace S := ⟨rfl⟩

  let gr : S → ℝ := fun s => max 0 (1 - (2 / ε) * ∑ c ∈ C₀, ‖e c s - p c‖)
  have hgr : Continuous gr := by
    refine continuous_const.max (continuous_const.sub (continuous_const.mul ?_))
    exact continuous_finsetSum _ fun c _ => continuous_norm.comp ((e c).continuous.sub continuous_const)
  let g : C(S, ℂ) := ⟨fun s => (gr s : ℂ), Complex.continuous_ofReal.comp hgr⟩
  have hg0 : g s₀ = 1 := by
    simp [g, gr, hs₀]
  have hgne : π g ≠ 0 := by
    intro h
    have h1 : ‖g‖ = 0 := by rw [← hπ, h, norm_zero]
    have h2 := ContinuousMap.norm_coe_le_norm g s₀
    rw [hg0, h1] at h2
    norm_num at h2
  obtain ⟨v, hv⟩ : ∃ v, π g v ≠ 0 := by
    by_contra h
    push Not at h
    exact hgne (ContinuousLinearMap.ext h)
  set w := π g v with hw
  obtain ⟨ν, hνf, hνr, hν⟩ := hM K S π w
  obtain ⟨V, hViso, hVmul⟩ := hI K S π w ν hν
  let χ : S → (B →⋆ₐ[ℂ] ℂ) := fun s => (ContinuousMap.evalStarAlgHom ℂ ℂ s).comp e
  have hχ : ∀ s b, χ s b = e b s := fun s b => rfl
  refine ⟨S, borel S, ν, hνf, χ, V, ⟨?_, ?_, ?_, hViso, ?_⟩, ?_⟩
  · intro h0
    have h1 := hν 1
    rw [h0, integral_zero_measure, map_one, ContinuousLinearMap.one_apply] at h1
    exact hv (inner_self_eq_zero.1 h1.symm)
  · intro b
    simp only [hχ]
    exact (e b).continuous.measurable
  · intro b s
    rw [hχ, ← hne]
    exact ContinuousMap.norm_coe_le_norm _ _
  · intro b h h' hh
    rw [← he]
    exact hVmul (e b) h h' (by simpa only [hχ] using hh)
  · rw [Filter.eventually_all_finset]
    intro c hc
    let tr : S → ℝ := fun s => max 0 (‖e c s - p c‖ - ε)
    have htr : Continuous tr :=
      continuous_const.max ((continuous_norm.comp ((e c).continuous.sub continuous_const)).sub continuous_const)
    let t : C(S, ℂ) := ⟨fun s => (tr s : ℂ), Complex.continuous_ofReal.comp htr⟩
    have htg : t * g = 0 := by
      ext s
      simp only [ContinuousMap.mul_apply, ContinuousMap.zero_apply, t, g, ContinuousMap.coe_mk]
      rcases le_or_gt (‖e c s - p c‖) ε with h | h
      · have : tr s = 0 := max_eq_left (by linarith)
        simp [this]
      · have hs : ‖e c s - p c‖ ≤ ∑ c ∈ C₀, ‖e c s - p c‖ :=
          Finset.single_le_sum (f := fun c => ‖e c s - p c‖) (fun _ _ => norm_nonneg _) hc
        have h2 : 2 < (2 / ε) * ∑ c ∈ C₀, ‖e c s - p c‖ := by
          rw [div_mul_eq_mul_div, lt_div_iff₀ hε]
          nlinarith
        have : gr s = 0 := max_eq_left (by linarith)
        simp [this]
    have hint : ∫ s, (tr s : ℂ) ∂ν = 0 := by
      have h1 := hν t
      have h2 : π t w = 0 := by
        rw [hw, ← ContinuousLinearMap.mul_apply, ← map_mul, htg, map_zero, ContinuousLinearMap.zero_apply]
      rw [h2, inner_zero_right] at h1
      exact h1
    filter_upwards [ae_zero ν tr htr (fun s => le_max_left _ _) hint] with s hs
    rw [hχ]
    have : ‖e c s - p c‖ - ε ≤ 0 := max_eq_left_iff.1 hs
    linarith

end PositivityTheory.Rg.BcB.E2.P

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Aeeq
section
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
namespace PositivityTheory.Rg.BcB.E2.P

open MeasureTheory
open scoped Pointwise

theorem aeeq : AeEq := by
  intro X u u' hu hu' hi hi' hae
  have : MeasurableConstSMul X.Γ X.G := ⟨fun γ => measurable_const_mul (γ : X.G)⟩
  have : SMulInvariantMeasure X.Γ X.G X.μ := ⟨fun γ s _ => measure_preimage_mul _ γ.1 s⟩
  set A : Set X.G := {x | u x ≠ u' x} with hA
  have hAo : IsOpen A := isOpen_ne_fun hu hu'
  have hAF : X.μ (A ∩ X.F) = 0 := by
    have h1 : X.ν A = 0 := ae_iff.1 hae
    rw [Ctx.ν, Measure.restrict_apply hAo.measurableSet] at h1
    exact h1
  have hinv : ∀ γ : X.Γ, γ • A = A := by
    intro γ
    ext x
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    show u (((γ⁻¹ : X.Γ) : X.G) * x) ≠ u' (((γ⁻¹ : X.Γ) : X.G) * x) ↔ u x ≠ u' x
    rw [hi _ (γ⁻¹).2, hi' _ (γ⁻¹).2]
  have hμA : X.μ A = 0 := X.fd.measure_zero_of_invariant A hinv hAF
  have hAe : A = ∅ := (hAo.measure_eq_zero_iff X.μ).1 hμA
  funext x
  by_contra h
  have hx : x ∈ A := h
  rw [hAe] at hx
  exact hx

end PositivityTheory.Rg.BcB.E2.P
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Convcont
section
open MeasureTheory Topology
open scoped Pointwise
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P

namespace Convcont

theorem shift (X : Ctx) (φ u : X.G → ℂ) (x : X.G) :
    ∫ y, φ y * u (x * y) ∂X.μ = ∫ z, φ (x⁻¹ * z) * u z ∂X.μ := by
  have := integral_mul_left_eq_self (μ := X.μ) (fun z => φ (x⁻¹ * z) * u z) x
  simp only [inv_mul_cancel_left] at this
  exact this

end Convcont

open Convcont in
theorem convcont : ConvCont := by
  intro X φ u hφ hu
  have hfun : (fun x => ∫ y, φ y * u (x * y) ∂X.μ) = fun x => ∫ z, φ (x⁻¹ * z) * u z ∂X.μ :=
    funext fun x => shift X φ u x
  rw [hfun]
  obtain ⟨B, hB⟩ := hφ.1.bounded_above_of_compact_support hφ.2
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds x₀
  have hK : IsCompact (N * tsupport φ) := hNc.mul hφ.2
  have hcx : ∀ z : X.G, Continuous fun x : X.G => φ (x⁻¹ * z) :=
    fun z => hφ.1.comp (continuous_inv.mul continuous_const)
  refine continuousAt_of_dominated (bound := (N * tsupport φ).indicator fun z => B * ‖u z‖) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x =>
      ((hφ.1.comp (continuous_const.mul continuous_id)).aestronglyMeasurable).mul hu.aestronglyMeasurable
  · filter_upwards [hN] with x hx
    refine Filter.Eventually.of_forall fun z => ?_
    by_cases hz : z ∈ N * tsupport φ
    · rw [Set.indicator_of_mem hz, norm_mul]
      exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
    · rw [Set.indicator_of_notMem hz]
      have h0 : φ (x⁻¹ * z) = 0 := by
        by_contra h
        apply hz
        refine ⟨x, hx, x⁻¹ * z, subset_tsupport _ h, ?_⟩
        simp
      simp [h0]
  · rw [integrable_indicator_iff hK.measurableSet]
    exact ((hu.integrableOn_isCompact hK).norm.const_mul B)
  · exact Filter.Eventually.of_forall fun z => ((hcx z).mul continuous_const).continuousAt

end PositivityTheory.Rg.BcB.E2.P
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Desint
section
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate

namespace PositivityTheory.Rg.BcB.E2.P

theorem desint : JointRep → Tonelli → WeakAE → EigAE → LocInt → NonZero → Smooth → Desint := by
  intro hJR hTon hWk hEig hLoc hNZ hSm
  intro X ι κ S _ _ _ ν _ _ F W Φ σ g c₀ P hd hW hΦ hσ hc₀ hP
  let _ : MeasurableSpace (Lp ℂ 2 ν) := borel _
  have : BorelSpace (Lp ℂ 2 ν) := ⟨rfl⟩
  obtain ⟨Ψ, hΨm, hΨ⟩ := hJR S ν
  obtain ⟨f, hrep, hinv⟩ : ∃ f : ι → X.G → S → ℂ, (∀ i, IsRep (F i) (f i)) ∧
      ∀ i, ∀ γ ∈ X.Γ, ∀ x s, f i (γ * x) s = f i x s :=
    ⟨fun i x s => Ψ (F i x) s, fun i =>
      ⟨hΨm.comp (((hd.cont i).measurable.comp measurable_fst).prodMk measurable_snd), fun x => hΨ (F i x)⟩,
      fun i γ hγ x s => by simp only [hd.inv i γ hγ x]⟩
  have : SFinite X.ν := by unfold Ctx.ν; infer_instance
  have hT : ∀ᵐ s ∂ν, ∀ i, ∫⁻ x, W x * ‖f i x s‖ₑ ^ 2 ∂X.ν < ⊤ :=
    ae_all_iff.2 fun i => hTon X.G S X.ν ν (F i) (f i) W (hrep i) hW (hd.wt i)
  have hE : ∀ᵐ s ∂ν, ∀ c i, ∀ᵐ x ∂X.μ,
      ∑ j, ∫ y, Φ c i j y * conj (f j (x * y) s) ∂X.μ = σ c s * conj (f i x s) :=
    ae_all_iff.2 fun c => hEig X ι S ν F f (Φ c) (σ c) (hσ c).2.choose hd.cont hrep (hΦ c) (hσ c).1
      (hσ c).2.choose_spec (hd.eig c)
  have hL : ∀ᵐ s ∂ν, ∀ i, LocallyIntegrable (fun x => f i x s) X.μ :=
    ae_all_iff.2 fun i => hLoc X S ν (F i) (f i) (hd.cont i) (hrep i)
  have hO : ∀ᵐ s ∂ν, ∀ n, ∑ i, ∫ x, g n i x * conj (f i x s) ∂X.ν = 0 :=
    ae_all_iff.2 fun n => hWk X.G S ι X.ν ν F f (g n) 0 hrep (fun i => (hd.gint n i).1)
      (fun i => (hd.gint n i).2) MemLp.zero (fun h => by rw [hd.orth n h]; simp)
  have hN : ¬ ∀ᵐ s ∂ν, ∀ i, ∀ᵐ x ∂X.μ, f i x s = 0 := by
    intro h
    apply hd.ne
    funext i
    exact hNZ X S ν (F i) (f i) (hd.cont i) (hrep i) (h.mono fun s hs => hs i)
  obtain ⟨s, hsN, hsP, hs0, hsT, hsE, hsL, hsO⟩ :=
    ((not_eventually.1 hN).and_eventually (hP.and (hc₀.and (hT.and (hE.and (hL.and hO)))))).exists
  have huL : ∀ i, LocallyIntegrable (fun x => conj (f i x s)) X.μ := fun i =>
    (hsL i).mono (Complex.continuous_conj.comp_aestronglyMeasurable (hsL i).aestronglyMeasurable)
      (Eventually.of_forall fun x => by simp)
  obtain ⟨f', hf', heig⟩ := hSm X ι κ (fun i x => conj (f i x s)) Φ (fun c => σ c s) c₀ huL
    (fun i γ hγ x => by simp only [hinv i γ hγ x s]) hΦ hs0 hsE
  have hae : ∀ i, f' i =ᵐ[X.ν] fun x => conj (f i x s) := fun i => by
    unfold Ctx.ν; exact ae_restrict_of_ae (hf' i).2.1
  refine ⟨s, hsP, f', ⟨fun i => (hf' i).1, ?_, fun i => (hf' i).2.2, fun i => ?_, heig, fun n => ?_⟩⟩
  · intro h0
    apply hsN
    intro i
    filter_upwards [(hf' i).2.1] with x hx
    simp only [h0, Pi.zero_apply] at hx
    simpa using hx.symm
  · rw [lintegral_congr_ae (g := fun x => W x * ‖f i x s‖ₑ ^ 2)
      ((hae i).mono fun x hx => by simp only [hx, RCLike.enorm_conj])]
    exact hsT i
  · rw [← hsO n]
    refine Finset.sum_congr rfl fun i _ => integral_congr_ae ?_
    filter_upwards [hae i] with x hx
    rw [hx]

end PositivityTheory.Rg.BcB.E2.P
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Eigae
section
open MeasureTheory
open scoped ENNReal ComplexConjugate
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P

theorem eigae : WeakAE → EigAE := by
  intro hW X ι S _ _ ν _ F f Φ σ A hFc hrep hΦ hσ hσA hE
  have hfm : ∀ j, Measurable (Function.uncurry (f j)) := fun j => (hrep j).1
  have hfx : ∀ j x, Measurable (f j x) := fun j x => (hfm j).comp measurable_prodMk_left
  have key : ∀ i x, ∀ᵐ s ∂ν, ∑ j, ∫ y, Φ i j y * conj (f j (x * y) s) ∂X.μ = σ s * conj (f i x s) := by
    intro i x
    refine hW X.G S ι X.μ ν (fun j y => F j (x * y)) (fun j y => f j (x * y)) (fun j => Φ i j)
      (fun s => σ s * conj (f i x s)) (fun j => ⟨?_, fun y => (hrep j).2 (x * y)⟩)
      (fun j => (hΦ i j).1.aestronglyMeasurable) (fun j => ?_) ?_ (fun h => ?_)
    · exact (hfm j).comp ((measurable_const_mul x).prodMap measurable_id)
    · have hc : Continuous fun y => Φ i j y • F j (x * y) :=
        (hΦ i j).1.smul ((hFc j).comp (continuous_const.mul continuous_id))
      have hi := (hc.integrable_of_hasCompactSupport (μ := X.μ) ((hΦ i j).2.smul_right)).2
      refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) hi)
      refine lintegral_congr fun y => ?_
      simp [enorm_smul]
    · have hm : MemLp (f i x) 2 ν := (Lp.memLp (F i x)).ae_eq ((hrep i).2 x).symm
      refine MemLp.of_le_mul (c := A) hm ?_ (ae_of_all _ fun s => ?_)
      · exact (hσ.mul (Complex.continuous_conj.measurable.comp (hfx i x))).aestronglyMeasurable
      · simp only [norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_right (hσA s) (norm_nonneg _)
    · rw [hE x i h]
      refine integral_congr_ae ?_
      filter_upwards [(hrep i).2 x] with s hs
      simp [hs]
  refine ae_all_iff.2 fun i => ?_
  have hmeas : MeasurableSet {p : X.G × S |
      ∑ j, ∫ y, Φ i j y * conj (f j (p.1 * y) p.2) ∂X.μ = σ p.2 * conj (f i p.1 p.2)} := by
    refine measurableSet_eq_fun ?_ ?_
    · refine Finset.measurable_sum _ fun j _ => ?_
      have : StronglyMeasurable fun q : (X.G × S) × X.G => Φ i j q.2 * conj (f j (q.1.1 * q.2) q.1.2) := by
        refine Measurable.stronglyMeasurable ?_
        refine ((hΦ i j).1.measurable.comp measurable_snd).mul (Complex.continuous_conj.measurable.comp ?_)
        exact (hfm j).comp ((measurable_fst.fst.mul measurable_snd).prodMk measurable_fst.snd)
      exact (this.integral_prod_right' (ν := X.μ)).measurable
    · exact (hσ.comp measurable_snd).mul (Complex.continuous_conj.measurable.comp (hfm i))
  exact (Measure.ae_ae_comm hmeas).1 (ae_of_all _ fun x => key i x)

end PositivityTheory.Rg.BcB.E2.P
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Gelf
section
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
namespace PositivityTheory.Rg.BcB.E2.P

theorem gelf : Gelf := by
  intro K _ _ _ B _ _ _ _ R
  let A0 : StarSubalgebra ℂ (K →L[ℂ] K) := R.range
  have hc : ∀ x y : A0, x * y = y * x := by
    rintro ⟨x, b, rfl⟩ ⟨y, c, rfl⟩
    apply Subtype.ext
    change R b * R c = R c * R b
    rw [← map_mul, ← map_mul, mul_comm]
  let A : StarSubalgebra ℂ (K →L[ℂ] K) := A0.topologicalClosure
  have : IsClosed (A : Set (K →L[ℂ] K)) := A0.isClosed_topologicalClosure
  let cr : CommRing A := A0.commRingTopologicalClosure hc
  let _ : CommCStarAlgebra A :=
    { (inferInstance : CStarAlgebra A) with mul_comm := cr.mul_comm }
  let G := gelfandStarTransform A
  have hmem : ∀ b, R b ∈ A := fun b => A0.le_topologicalClosure ⟨b, rfl⟩
  refine ⟨WeakDual.characterSpace ℂ A, inferInstance, inferInstance, inferInstance,
    A.subtype.comp G.symm.toStarAlgHom, G.toStarAlgHom.comp (R.codRestrict A hmem), ?_, ?_⟩
  · intro f
    have h1 : ‖G (G.symm f)‖ = ‖G.symm f‖ := (gelfandTransform_isometry A).norm_map_of_map_zero (map_zero _) _
    rw [G.apply_symm_apply] at h1
    rw [h1]
    rfl
  · intro b
    change ((G.symm (G ⟨R b, hmem b⟩) : A) : K →L[ℂ] K) = R b
    rw [G.symm_apply_apply]

end PositivityTheory.Rg.BcB.E2.P
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Hssep
section
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
namespace PositivityTheory.Rg.BcB.E2.P

open MeasureTheory

theorem hssep : HsSep := by
  intro X ι _
  haveI : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  haveI : SFinite X.ν := by unfold Ctx.ν; infer_instance
  haveI : IsSeparable X.ν := inferInstance
  haveI : SecondCountableTopology (Lp ℂ 2 X.ν) := inferInstance
  infer_instance

end PositivityTheory.Rg.BcB.E2.P
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Imports
section
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
namespace PositivityTheory.Rg.BcB.E2.P

theorem point : Point := by
  unfold PositivityTheory.Rg.BcB.E2.Point
  intro B _ _ _ _ S _ _ e p hp
  by_contra hne
  push Not at hne
  choose b hb using hne
  let c : S → B := fun s => b s - algebraMap ℂ B (p (b s))
  have hpc : ∀ s, p (c s) = 0 := fun s => by
    simp only [c, map_sub]
    rw [AlgHomClass.commutes]
    simp
  have hec : ∀ s, e (c s) s ≠ 0 := fun s => by
    have h1 : e (c s) s = e (b s) s - p (b s) := by
      simp only [c, map_sub, ContinuousMap.sub_apply]
      rw [AlgHomClass.commutes, Algebra.algebraMap_eq_smul_one, ContinuousMap.smul_apply,
        ContinuousMap.one_apply, smul_eq_mul, mul_one]
    rw [h1]
    exact sub_ne_zero.2 (hb s)
  let g : S → B := fun s => star (c s) * c s
  have hpg : ∀ s, p (g s) = 0 := fun s => by simp [g, hpc]
  have heg : ∀ s t, e (g s) t = ((‖e (c s) t‖ ^ 2 : ℝ) : ℂ) := fun s t => by
    simp only [g, map_mul, map_star, ContinuousMap.mul_apply, ContinuousMap.star_apply]
    rw [Complex.ofReal_pow]
    exact Complex.conj_mul' _
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun s => {t : S | e (c s) t ≠ 0})
    (fun s => isOpen_compl_singleton.preimage (e (c s)).continuous)
    (fun t _ => Set.mem_iUnion.2 ⟨t, hec t⟩)
  let G : B := ∑ s ∈ F, g s
  let v : S → ℝ := fun t => ∑ s ∈ F, ‖e (c s) t‖ ^ 2
  have hpG : p G = 0 := by simp [G, hpg]
  have heG : ∀ t, e G t = (v t : ℂ) := fun t => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [G, v, map_sum, ContinuousMap.sum_apply, heg]
    push_cast
    rfl
  have hv : ∀ t, 0 < v t := fun t => by
    obtain ⟨s, hsF, hs⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ t))
    have hs' : e (c s) t ≠ 0 := hs
    exact Finset.sum_pos' (fun i _ => by positivity) ⟨s, hsF, pow_pos (norm_pos_iff.2 hs') 2⟩
  have hvM : ∀ t, v t ≤ ‖e G‖ := fun t => by
    have h1 := ContinuousMap.norm_coe_le_norm (e G) t
    rw [heG, Complex.norm_real, Real.norm_of_nonneg (hv t).le] at h1
    exact h1
  have hM : 0 ≤ ‖e G‖ := norm_nonneg _
  have key := hp (1 - ((1 / (‖e G‖ + 1) : ℝ) : ℂ) • G)
  have hp1 : p (1 - ((1 / (‖e G‖ + 1) : ℝ) : ℂ) • G) = 1 := by simp [hpG]
  rw [hp1, norm_one] at key
  have hlt : ‖e (1 - ((1 / (‖e G‖ + 1) : ℝ) : ℂ) • G)‖ < 1 := by
    rw [ContinuousMap.norm_lt_iff _ one_pos]
    intro t
    have ht : e (1 - ((1 / (‖e G‖ + 1) : ℝ) : ℂ) • G) t = ((1 - v t / (‖e G‖ + 1) : ℝ) : ℂ) := by
      simp only [map_sub, map_one, map_smul, ContinuousMap.sub_apply, ContinuousMap.one_apply,
        ContinuousMap.smul_apply, heG, smul_eq_mul]
      push_cast
      ring
    rw [ht, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    have h2 : v t / (‖e G‖ + 1) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith [hvM t]
    have h3 : 0 < v t / (‖e G‖ + 1) := div_pos (hv t) (by linarith)
    constructor <;> linarith
  linarith

end PositivityTheory.Rg.BcB.E2.P
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Nonzero
section
open MeasureTheory
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P

theorem nonzero : NonZero := by
  intro X S _ ν _ F f hF hf h0
  have hmeas : MeasurableSet {p : X.G × S | f p.1 p.2 = 0} :=
    (measurableSet_singleton (0 : ℂ)).preimage hf.1
  have h1 : ∀ᵐ x ∂X.μ, ∀ᵐ s ∂ν, f x s = 0 :=
    (Measure.ae_ae_comm (μ := X.μ) (ν := ν) (p := fun x s => f x s = 0) hmeas).2 h0
  have h2 : F =ᵐ[X.μ] (0 : X.G → Lp ℂ 2 ν) := by
    filter_upwards [h1] with x hx
    have : (F x : S → ℂ) =ᵐ[ν] 0 := by
      filter_upwards [(hf.2 x).symm, hx, Lp.coeFn_zero ℂ 2 ν] with s h1 h2 h3
      rw [h1, h2]; rfl
    simpa using (Lp.eq_zero_iff_ae_eq_zero).2 this
  exact (Continuous.ae_eq_iff_eq X.μ hF continuous_const).1 h2

end PositivityTheory.Rg.BcB.E2.P
end

