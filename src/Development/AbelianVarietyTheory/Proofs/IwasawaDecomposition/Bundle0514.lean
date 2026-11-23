module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0497
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FjCauchyBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.M3bNormHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver
public import Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP
public import Formalism.LocalToGlobal.LatticeGeometry.Bundle0003
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
public import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
public import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.SharpRestriction.Divisibility.Bundle0001
public import Formalism.SharpRestriction.Divisibility.Bundle0002
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
public import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
public import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.SubsingletonRankIndicatorIff
public import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.WeightFamilies
public import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive
public import Formalism.LocalRingCardinality.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0206
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
public import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0499
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MaximumPrincipleIsotropicFlowRescaledBound
section
open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom

namespace GlobalTheory.CuspStep

theorem half_plane_bound {g : ℂ → ℂ} {M C : ℝ} (hd : DifferentiableOn ℂ g {z | 0 ≤ z.re})
    (hM : ∀ z : ℂ, 0 ≤ z.re → ‖g z‖ ≤ M) (hC : ∀ y : ℝ, ‖g (y * I)‖ ≤ C) : ‖g 1‖ ≤ C := by
  refine PhragmenLindelof.right_half_plane_of_bounded_on_real (f := g) ?_ ⟨0, by norm_num, 0, ?_⟩ ?_ hC (by simp)
  · refine DifferentiableOn.diffContOnCl ?_
    rw [Complex.closure_setOf_lt_re]
    exact hd
  · refine Asymptotics.IsBigO.of_bound M ?_
    refine Filter.Eventually.filter_mono inf_le_right ?_
    rw [Filter.eventually_principal]
    intro z hz
    simpa using hM z (le_of_lt hz)
  · refine ⟨M, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with y hy
    exact hM y (by simpa using hy)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem differentiable_flow (ξ : Fin r → E) (a : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    Differentiable ℂ (fun z : ℂ => X.flow ξ (fun τ => z * a τ) x) := by
  refine differentiable_pi.mpr fun τ => differentiable_pi.mpr fun i => differentiable_pi.mpr fun j => ?_
  simp only [Data.flow, Data.flowMat, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

theorem nfac_flow_real (la : Wt X.Ψ r) {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (s : X.Ψ → ℂ) (hs : ∀ τ, (s τ).im = 0) : X.nfac la (X.flow ξ s x) = X.nfac la x := by
  have hd : X.flow ξ s x ∈ X.dom :=
    FjCauchy.flow_mem_dom X hξ hx s fun τ => by rw [hs, add_zero]; exact FjCauchy.tt_pos X hξ hx τ
  have h := m3bNorm_holds r X _ (FjCauchy.isIsoV_embV X hξ) la x hx s hd
  simp only [hs, zero_div, add_zero, inv_one, min_self, max_self, Real.one_rpow, Finset.prod_const_one] at h
  have h1 : X.nfac la x / X.nfac la (X.flow ξ s x) = 1 := le_antisymm h.2 h.1
  have hn := FlowCoefficientBounds.nfac_pos X hd la
  rw [div_eq_one_iff_eq hn.ne'] at h1
  exact h1.symm

theorem norm_flow_le {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P) (hF : FreqNonneg X la P)
    {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (hs : ∀ τ, 0 ≤ (s τ).im) :
    ‖P (X.flow ξ s x)‖ ≤ ∑' ν : X.Ψ → ℝ, ‖X.fj la ξ ν P x‖ := by
  have hd : X.flow ξ s x ∈ X.dom :=
    FjCauchy.flow_mem_dom X hξ hx s fun τ => add_pos_of_pos_of_nonneg (FjCauchy.tt_pos X hξ hx τ) (hs τ)
  have h0 := m3bExp_holds r X la P hP ξ hξ x hx 0 (by rw [EmbeddingHermitianPairs.flow_zero]; exact hx)
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, Complex.exp_zero, mul_one] at h0
  have hsum : Summable fun ν : X.Ψ → ℝ => ‖X.fj la ξ ν P x‖ := summable_norm_iff.mpr h0.summable
  have h1 := m3bExp_holds r X la P hP ξ hξ x hx s hd
  refine h1.norm_le_of_bounded hsum.hasSum fun ν => ?_
  by_cases hz : X.fj la ξ ν P x = 0
  · simp [hz]
  · have hν := hF ξ hξ ν x hx hz
    rw [norm_mul]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    have hsn : 0 ≤ ∑ τ, ν τ * (s τ).im := Finset.sum_nonneg fun τ _ => mul_nonneg (hν τ) (hs τ)
    have : (4 * Real.pi * I * ∑ τ, (ν τ : ℂ) * s τ).re = -(4 * Real.pi * ∑ τ, ν τ * (s τ).im) := by
      simp [Complex.mul_re, Complex.mul_im, Complex.im_sum]
    rw [this]
    have := Real.pi_pos
    have : 0 ≤ 4 * Real.pi * ∑ τ, ν τ * (s τ).im := by positivity
    linarith

theorem stepBound (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r)
    (P : Frame X.Ψ r → ℂ) (w : ℝ) (hP : X.IsSec la P) (hF : FreqNonneg X la P)
    (hw : ∀ τ, X.spread la τ / 2 ≤ w) : StepBound X w (X.pnorm la P) := by
  intro ξ hξ x hx q hq B hB
  have ht := FjCauchy.tt_pos X hξ hx
  set b : X.Ψ → ℂ := fun τ => I * (((q τ - 1) * X.tt ξ x τ : ℝ) : ℂ) with hb
  have hbim : ∀ τ, (b τ).im = (q τ - 1) * X.tt ξ x τ := fun τ => by
    simp only [hb, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  have hbre : ∀ τ, (b τ).re = 0 := fun τ => by
    simp only [hb, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  have hbn : ∀ τ, (b τ).im ≤ 0 := fun τ => by
    rw [hbim]; exact mul_nonpos_of_nonpos_of_nonneg (by linarith [(hq τ).2]) (ht τ).le
  have hx' : X.flow ξ b x ∈ X.dom := FjCauchy.flow_mem_dom X hξ hx b fun τ => by
    rw [hbim]; nlinarith [mul_pos (hq τ).1 (ht τ)]
  set x' := X.flow ξ b x with hx'def
  have hn' := FlowCoefficientBounds.nfac_pos X hx' la
  have hn := FlowCoefficientBounds.nfac_pos X hx la
  have him : ∀ z : ℂ, 0 ≤ z.re → ∀ τ, 0 ≤ (z * -b τ).im := fun z hz τ => by
    simp only [Complex.mul_im, Complex.neg_im, Complex.neg_re, hbre, neg_zero, mul_zero, add_zero]
    exact mul_nonneg hz (by linarith [hbn τ])
  have hreal : ∀ y : ℝ, ‖P (X.flow ξ (fun τ => (y * I) * -b τ) x')‖ ≤ B / X.nfac la x' := fun y => by
    have hs : ∀ τ, ((y * I : ℂ) * -b τ).im = 0 := fun τ => by simp [hbre]
    rw [le_div_iff₀ hn', ← nfac_flow_real X la hξ hx' _ hs]
    have h := hB fun τ => ((y * I : ℂ) * -b τ).re
    have he : X.flow ξ (fun τ => (y * I) * -b τ) x' =
        X.flow ξ (fun τ => (((y * I : ℂ) * -b τ).re : ℂ) + b τ) x := by
      rw [hx'def, EmbeddingHermitianPairs.flow_flow X hξ.2.1]
      congr 1
      congr 1
      funext τ
      exact Complex.ext (by simp) (by rw [hs]; simp)
    rw [he]
    exact h
  have key := half_plane_bound (g := fun z => P (X.flow ξ (fun τ => z * -b τ) x'))
    (hP.1.comp (differentiable_flow X ξ (fun τ => -b τ) x').differentiableOn fun z hz =>
      FjCauchy.flow_mem_dom X hξ hx' _ fun τ =>
        add_pos_of_pos_of_nonneg (FjCauchy.tt_pos X hξ hx' τ) (him z hz τ))
    (fun z hz => norm_flow_le X hP hF hξ hx' _ (him z hz)) hreal
  have he : X.flow ξ (fun τ => 1 * -b τ) x' = x := by
    rw [hx'def, EmbeddingHermitianPairs.flow_flow X hξ.2.1]
    have : ((fun τ => 1 * -b τ) + b) = 0 := by funext τ; simp
    rw [this, EmbeddingHermitianPairs.flow_zero]
  simp only [he] at key
  have hB0 : 0 ≤ B := by
    have := (norm_nonneg _).trans key
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hn'))
  have hr := (m3bNorm_holds r X _ (FjCauchy.isIsoV_embV X hξ) la x hx b hx').2
  have hr2 : X.nfac la x / X.nfac la x' ≤ ∏ τ, q τ ^ (-w) := by
    refine le_trans hr (Finset.prod_le_prod₀ (fun τ _ => ?_) fun τ _ => ?_)
    all_goals
      have hqq : 1 + (b τ).im / X.ttV (X.embV ξ) x τ = q τ := by
        change 1 + (b τ).im / X.tt ξ x τ = q τ
        rw [hbim, mul_div_assoc, div_self (ht τ).ne']; ring
      have h1 : 1 ≤ (q τ)⁻¹ := (one_le_inv₀ (hq τ).1).mpr (hq τ).2
      simp only [hqq, max_eq_right ((hq τ).2.trans h1)]
    · positivity
    · rw [Real.rpow_neg (hq τ).1.le, ← Real.inv_rpow (hq τ).1.le]
      exact Real.rpow_le_rpow_of_exponent_le h1 (hw τ)
  calc X.pnorm la P x = ‖P x‖ * X.nfac la x := rfl
    _ ≤ B / X.nfac la x' * X.nfac la x := mul_le_mul_of_nonneg_right key hn.le
    _ = B * (X.nfac la x / X.nfac la x') := by ring
    _ ≤ B * ∏ τ, q τ ^ (-w) := mul_le_mul_of_nonneg_left hr2 hB0

end GlobalTheory.CuspStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeromorphicGermVanishesOfPeriodicExpModulus
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.ShFam.BdArc

theorem not_eventually_re_pos_of_periodic {f : ℂ → ℂ} {M : ℝ} (hM : 0 < M) (hper : Function.Periodic f M)
    (hd : ∀ᶠ z in imTop, DifferentiableAt ℂ f z) (h0 : Tendsto f imTop (𝓝 0)) :
    ¬ ∀ᶠ z in imTop, 0 < (f z).re := by
  intro hpos
  set F := Function.Periodic.cuspFunction M f with hF
  have hF0 : F 0 = 0 := Function.Periodic.cuspFunction_zero_of_zero_at_inf hM h0
  have hd0 : DifferentiableAt ℂ F 0 :=
    Function.Periodic.differentiableAt_cuspFunction_zero hM hper hd
      (Filter.ZeroAtFilter.boundedAtFilter (l := comap Complex.im atTop) (f := f) h0)
  have hd1 : ∀ᶠ q in 𝓝[≠] 0, DifferentiableAt ℂ F q :=
    Function.Periodic.eventually_differentiableAt_cuspFunction_nhds_ne_zero hM hper hd
  have hp1 : ∀ᶠ q in 𝓝[≠] (0 : ℂ), 0 < (F q).re := by
    filter_upwards [(Function.Periodic.invQParam_tendsto hM).eventually hpos, self_mem_nhdsWithin] with q hq hq0
    rwa [hF, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq0]
  have hd2 : ∀ᶠ q in 𝓝 (0 : ℂ), DifferentiableAt ℂ (fun z => Complex.exp (-F z)) q := by
    filter_upwards [eventually_nhdsWithin_iff.mp hd1] with q hq
    by_cases hq0 : q = 0
    · subst hq0; exact hd0.neg.cexp
    · exact (hq hq0).neg.cexp
  have hmax : IsLocalMax (norm ∘ fun z => Complex.exp (-F z)) 0 := by
    filter_upwards [eventually_nhdsWithin_iff.mp hp1] with q hq
    by_cases hq0 : q = 0
    · subst hq0; exact le_rfl
    · have := hq hq0
      simp only [Function.comp, Complex.norm_exp, hF0, Complex.neg_re, Real.exp_le_exp]
      simpa using this.le
  have hc := Complex.eventually_eq_of_isLocalMax_norm hd2 hmax
  obtain ⟨q, hq1, hq2⟩ := (hp1.and (hc.filter_mono nhdsWithin_le_nhds)).exists
  have := congrArg norm hq2
  simp only [Complex.norm_exp, hF0, Complex.neg_re, Real.exp_eq_exp] at this
  simp at this
  exact hq1.ne' this

theorem not_tendsto_re_atTop_of_periodic {L : ℂ → ℂ} {T M : ℝ} (hM : 0 < M)
    (hd : DifferentiableOn ℂ L {w | T < w.im}) (hper : ∀ w : ℂ, T < w.im → L (w + M) = L w) :
    ¬ Tendsto (fun w => (L w).re) imTop atTop := by
  intro ht
  have hT : ∀ᶠ w in imTop, T < w.im := (tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_gt_atTop T)
  have hopen : IsOpen {w : ℂ | T < w.im} := isOpen_lt continuous_const Complex.continuous_im
  have hpos : ∀ᶠ w in imTop, 0 < (L w).re := ht.eventually (eventually_gt_atTop 0)
  classical
  set f : ℂ → ℂ := fun w => if T < w.im then (L w)⁻¹ else 0 with hf
  have hfe : ∀ w : ℂ, T < w.im → f w = (L w)⁻¹ := fun w hw => if_pos hw
  refine not_eventually_re_pos_of_periodic (f := f) hM ?_ ?_ ?_ ?_
  · intro w
    by_cases hw : T < w.im
    · have hw' : T < (w + M).im := by simpa using hw
      rw [hfe _ hw, hfe _ hw', hper w hw]
    · have hw' : ¬ T < (w + M).im := by simpa using hw
      simp only [hf, if_neg hw, if_neg hw']
  · filter_upwards [hT, hpos] with w hw hw0
    have hne : L w ≠ 0 := fun h => by simp [h] at hw0
    refine ((hd.differentiableAt (hopen.mem_nhds hw)).inv hne).congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hw] with z hz using hfe z hz
  · have h1 : Tendsto (fun w => ‖L w‖) imTop atTop :=
      tendsto_atTop_mono (fun w => Complex.re_le_norm (L w)) ht
    have h2 : Tendsto (fun w => (L w)⁻¹) imTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      simp only [norm_inv]
      exact h1.inv_tendsto_atTop
    refine h2.congr' ?_
    filter_upwards [hT] with w hw using (hfe w hw).symm
  · filter_upwards [hT, hpos] with w hw hw0
    have hne : L w ≠ 0 := fun h => by simp [h] at hw0
    rw [hfe w hw, Complex.inv_re]
    exact div_pos hw0 (Complex.normSq_pos.mpr hne)

theorem tendsto_zero_of_norm_eq_mul_exp_periodic :
    ∀ (p L h a b : ℂ → ℂ) (T r : ℝ) (M n : ℕ) (ζ : ℂ), 0 < M → 0 < n → ζ ^ n = 1 → 0 < r → DifferentiableOn ℂ p {w | T < w.im} → DifferentiableOn ℂ L {w | T < w.im} → (∀ w : ℂ, T < w.im → p (w + M) = ζ * p w ∧ L (w + M) = L w ∧ ‖h (eTwoPi w)‖ = ‖p w‖ * ‖Complex.exp (L w)‖) → Tendsto p imTop (𝓝 0) → DifferentiableOn ℂ a (Metric.ball (0 : ℂ) r) → DifferentiableOn ℂ b (Metric.ball (0 : ℂ) r) → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → b u ≠ 0 ∧ h u * b u = a u) → Tendsto h (𝓝[≠] 0) (𝓝 0) := by
  intro p L h a b T r M n ζ hM _ _ hr _ hL hw hp ha hb hab
  have hball : Metric.ball (0 : ℂ) r ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds _ hr
  have hmer : MeromorphicAt h 0 := by
    refine ((ha.analyticAt hball).meromorphicAt.div (hb.analyticAt hball).meromorphicAt).congr ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds hball, self_mem_nhdsWithin] with u hu hu0
    obtain ⟨h1, h2⟩ := hab u hu hu0
    simp only [Pi.div_apply]
    rw [← h2, mul_div_cancel_right₀ _ h1]
  rw [tendsto_zero_iff_meromorphicOrderAt_pos hmer]
  by_contra hord
  rw [not_lt] at hord
  have hne : ∀ᶠ u in 𝓝[≠] (0 : ℂ), h u ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hmer).mp (fun ht => by simp [ht] at hord)
  obtain ⟨c, hc⟩ : ∃ c, Tendsto h⁻¹ (𝓝[≠] 0) (𝓝 c) := by
    rw [tendsto_nhds_iff_meromorphicOrderAt_nonneg hmer.inv, meromorphicOrderAt_inv]
    induction hk : meromorphicOrderAt h 0 with
    | top => simp
    | coe k =>
      rw [hk] at hord
      have hk0 : k ≤ 0 := by exact_mod_cast hord
      have : (0 : ℤ) ≤ -k := by omega
      exact_mod_cast this
  have he : Tendsto eTwoPi imTop (𝓝[≠] 0) := by
    refine (Function.Periodic.qParam_tendsto (h := 1) one_pos).congr fun w => ?_
    simp [Function.Periodic.qParam, eTwoPi]
  have hT : ∀ᶠ w in imTop, T < w.im := (tendsto_comap (f := Complex.im) (x := atTop)).eventually (eventually_gt_atTop T)
  refine not_tendsto_re_atTop_of_periodic (M := (M : ℝ)) (by exact_mod_cast hM) hL
    (fun w hw' => by simpa using (hw w hw').2.1) ?_
  rw [← tendsto_neg_atBot_iff, ← Real.tendsto_exp_comp_nhds_zero]
  have h1 := hp.norm.mul (hc.comp he).norm
  simp only [norm_zero, zero_mul] at h1
  refine h1.congr' ?_
  filter_upwards [hT, he.eventually hne] with w hw' hw0
  have h2 := (hw w hw').2.2
  have h3 : ‖h (eTwoPi w)‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
  simp only [Function.comp, Pi.inv_apply, norm_inv]
  rw [Complex.norm_exp] at h2
  rw [Real.exp_neg, ← div_eq_mul_inv, div_eq_iff h3, h2]
  field_simp

end GlobalTheory.ShFam.BdArc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyEquivClassSet
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.TrueGeo GlobalTheory.ShFam Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Member
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.LevPin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Comp

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {V : HSp D} {r : ℕ}

end Comp

section Abstract

end Abstract

section Classes

open GlobalTheory.Mass Formalism.IndefR.Lev Formalism.L2.DIV

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ} {V : HSp D} {r : ℕ}

end Classes

section Local

open Formalism.UG GlobalTheory.LatticeStabLocal Formalism.L2.Herm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
  (Λ : Submodule (𝓞 E) (Fin n → E))

theorem mem_hatL_iff [Module.Finite (𝓞 E) Λ] (z : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    z ∈ hatL (F := F) Λ ↔ ∀ v : HeightOneSpectrum (𝓞 F), (fun i => prV (E := E) v (z i)) ∈ locL v Λ :=
  mem_latS_adele_iff Λ z

end Local

section LocalLevel

open Formalism.UG GlobalTheory.LatticeStabLocal Formalism.L2.Herm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : CMData F E) (S : HSpace E) (gp : Fin 2 → ℕ) (Λ : Submodule (𝓞 E) (Fin S.rank → E))

variable {hc S gp Λ}

end LocalLevel

section Level

open Formalism.L2.Geo.Def Formalism.IndefR.Lev Formalism.L2.DIV
open Formalism.UG (levelVL levelAfL prV bc stabGL)

variable (D)

variable {D}

end Level

end GlobalTheory.LevPin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyOfModToModIso
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM

namespace GlobalTheory.ModelPresentation

theorem exists_epi_twist_free {R : Type} [CommRing R] {N : ℕ} {X : Scheme.{0}} (ι : X ⟶ PSpace R N)
    [IsClosedImmersion ι] (F : X.Modules) [GlobalTheory.QCoh.IsFiniteQC F] :
    ∃ (a m : ℕ) (φ : GlobalTheory.twist (GlobalTheory.QCoh.freeModule X (Fin m)) ((GlobalTheory.ProjSpace.On R N (-(a : ℤ))).pull ι) ⟶ F),
      Epi φ := by
  have hA := (GlobalTheory.isAmple_projective_O_one R N).pull_of_isClosedImmersion ι
  have hL := hA.isLB
  obtain ⟨a, ha⟩ := (tendsto_natCast_atTop_atTop.eventually (hA.eventually_isGloballyGenerated_twistZ F)).exists
  obtain ⟨k, s, hs⟩ := GlobalTheory.QCoh.isGloballyGenerated_iff_spanStalks.1 ha
  have h₁ := (GlobalTheory.QCoh.epi_sectionsHom_iff s).2 hs
  have h₂ := (GlobalTheory.Twist.epi_map_iff (GlobalTheory.Twist.isLB_lbZPow hL (-(a : ℤ))) (GlobalTheory.QCoh.sectionsHom s)).2 h₁
  exact ⟨a, k, (GlobalTheory.Twist.twistZPullIso ι (GlobalTheory.ProjSpace.O1_isLB R N) _ (-(a : ℤ))).inv ≫
    GlobalTheory.Twist.map _ (GlobalTheory.QCoh.sectionsHom s) ≫ (GlobalTheory.Twist.twistZAddIso F hL (add_neg_cancel (a : ℤ))).hom ≫
    (GlobalTheory.Twist.twistZZeroIso F hL).inv, inferInstance⟩

theorem nonempty_cokernel_iso {C : Type*} [Category C] [Abelian C] {A B F : C} (φ : B ⟶ F) [Epi φ]
    (ψ : A ⟶ kernel φ) [Epi ψ] : Nonempty (cokernel (ψ ≫ kernel.ι φ) ≅ F) :=
  ⟨cokernelEpiComp ψ (kernel.ι φ) ≪≫ (cokernelIsCokernel (kernel.ι φ)).coconePointUniqueUpToIso
    (Abelian.epiIsCokernelOfKernel (KernelFork.ofι (kernel.ι φ) (kernel.condition φ)) (kernelIsKernel φ))⟩

theorem isNoetherianRing_place {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) {p : ℕ} (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) :
    IsNoetherianRing (c.V W) := by
  have := c.fin
  have : NumberField c.F := {}
  have : IsDiscreteValuationRing (c.V W) := by
    refine (isDiscreteValuationRing_and_finite_residueField_of_numberField (c.V W) hp ?_).1
    rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
    rcases hW with h | h
    · exact absurd (by exact_mod_cast h) hp
    · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')
  infer_instance

theorem nonempty_ofMod_toMod_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (Y : LocalSystem Xo p W) (i₀ : Idx H p), ∀ (Z : Mdl Y i₀) (F : Z.X.Modules) [GlobalTheory.QCoh.IsFiniteQC F], Nonempty ((Z.ofMod F).toMod ≅ F) := by
  intro E _ _ _ H Dw Xo p W hp hW Y i₀ Z F _
  have := isNoetherianRing_place Z.i.c W hp.ne_zero hW
  have : IsProper (PSpace.str (Z.i.c.V W) Z.n) := isProper_str _ _
  have : IsLocallyNoetherian Z.X :=
    LocallyOfFiniteType.isLocallyNoetherian (Z.I.subschemeι ≫ PSpace.str (Z.i.c.V W) Z.n)
  obtain ⟨a, m, φ, hφ⟩ := exists_epi_twist_free Z.I.subschemeι F
  have := GlobalTheory.Twist.isFiniteQC_twist (F := GlobalTheory.QCoh.freeModule Z.X (Fin m))
    (LB.isLB_pull (GlobalTheory.ProjSpace.On_isLB (Z.i.c.V W) Z.n (-(a : ℤ))) Z.I.subschemeι)
  obtain ⟨a', m', ψ, hψ⟩ := exists_epi_twist_free Z.I.subschemeι (kernel φ)
  have h : ∃ S : Z.Sh, Nonempty (S.toMod ≅ F) :=
    ⟨⟨a, m, a', m', ψ ≫ kernel.ι φ⟩, nonempty_cokernel_iso φ ψ⟩
  rw [Mdl.ofMod, dite_eq_left h]
  exact h.choose_spec

end GlobalTheory.ModelPresentation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowsPassToMovedDivisionLatticesHeightsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rows_pass_to_moved_divisionLatticesHeights :
    ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt)
      (Wt : Set B.places.Pl) (O : Obj2 (w.D Z)) (t : RowsT K w Z Wt O.p0)
      (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ)
      (O' : Obj2 (w.D (Db.setDivZ Z N h))),
    O' = DivMv.objMv (w := w) (Z := Z) N h O →
    ∃ t' : RowsT K w (Db.setDivZ Z N h) Wt O'.p0, RowsSame t t' ∧
      HEq t'.r.z.geo (GlobalTheory.Mem.R3.Tr.geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩)
        (SRe.upL Z Z.S N h) (iK := t.r.z.alg) t.r.z.geo) ∧
      HEq (SRe.pkOf t') ((SRe.pkOf t).up Z Z.S N h) ∧
      (ObjT O t → ObjT O' t') ∧ (Nonempty (RXs t) → Nonempty (RXs t')) :=
  GlobalTheory.Mem.R3.Rw.DivMv.rows_move_geo
end

