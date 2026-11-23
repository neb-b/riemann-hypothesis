module

public import Mathlib
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.TailBoundStatementHolds
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceStatementHolds
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedMeasureConvergenceSnc
public import ReciprocityTheory.AnalyticForms.LeviForms.UnifInt
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.WeakConvergenceOffZeroSet
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0083
public import ReciprocityTheory.AnalyticForms.LeviForms.ConvExpandStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSet

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.UniformIntegrabilityStatementHolds
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem maMeasure_bdry_null_any {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ)
    (W : Fin n → Set X) (hS : IsSection A L s) (hSNC : IsSNC A L s m W) (Φ : Fin e → LocPot X) :
    maMeasure A Φ (bdry s) = 0 := by
  have hB := LeviFormBoundaryTopology.isClosed_bdry hS
  have hAn : A.IsAnalyticSubset (bdry s) := by
    intro x
    refine ⟨L.U x, L.isOpen_U x, L.mem_U x, 1, fun _ => s x, fun _ => hS.1 x, ?_⟩
    ext z
    constructor
    · rintro ⟨hz, hzU⟩
      exact ⟨hzU, fun _ => (LeviFormBoundaryTopology.bdry_iff hS hzU).1 hz⟩
    · rintro ⟨hzU, hz⟩
      exact ⟨(LeviFormBoundaryTopology.bdry_iff hS hzU).2 (hz 0), hzU⟩
  have hInt : interior (bdry s) = ∅ := LeviFormBoundaryTopology.interior_bdry_eq_empty hS hSNC
  unfold maMeasure
  split_ifs with h
  · simp only [Measure.coe_finsetSum, Finset.sum_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hT := (A.chart j).open_target.measurableSet
    rw [Measure.map_apply_of_aemeasurable (((A.chart j).continuousOn_symm.aemeasurable hT).mono_ac
      (withDensity_absolutelyContinuous _ _)) hB.measurableSet]
    refine withDensity_absolutelyContinuous _ _ ?_
    rw [Measure.restrict_apply' hT]
    have := analyticNull A (bdry s) hAn hInt j
    rw [Set.inter_comm, (A.chart j).image_source_inter_eq'] at this
    rwa [Set.inter_comm]
  · simp

theorem unifInt_holds : UnifIntStatement := by
  intro e X _ _ _ _ _ A Θ L s n m W hΘ hΘpos hL hs hsnc hsle L' v Dg hL' hv hvsnc hsvsnc hvle
    th ph phT C₅ C t₀ hsing hreg hC2
  dsimp only
  have hconv := _root_.GlobalTheory.CompanionTheory.Ar.Giv.convergence_holds A Θ L s m W hΘ hΘpos hL hs hsnc hsle th ph phT C₅ C t₀ hsing hreg hC2
  have hlog1 : ∀ y, 1 ≤ Real.log (rW L s y) := by
    intro y
    have h := rW_ge L s hsle y
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (rW L s y) := Real.log_le_log (Real.exp_pos 1) h
  have hunif : ∀ g : X → ℝ,
      TendstoLocallyUniformlyOn (fun (_ : ℝ) => g) g (𝓝[>] (0 : ℝ)) (bdry s)ᶜ := by
    intro g u hu x _
    exact ⟨Set.univ, Filter.univ_mem,
      Filter.Eventually.of_forall fun _ y _ => refl_mem_uniformity hu⟩
  have hweak : ∀ (g : X → ℝ) (B : ℝ), Continuous g → (∀ y, |g y| ≤ B) →
      Tendsto (fun t => ∫ y, g y ∂maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ))
        (𝓝[>] 0) (𝓝 (∫ y, g y ∂maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ))) := by
    intro g B hg hB
    have hb : ∀ (t : ℝ) (y : X), y ∉ bdry s →
        |(fun (_ : ℝ) => g) t y| ≤ B * Real.log (rW L s y) := by
      intro t y _
      have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB y)
      calc |g y| ≤ B := hB y
        _ = B * 1 := (mul_one B).symm
        _ ≤ B * Real.log (rW L s y) := mul_le_mul_of_nonneg_left (hlog1 y) hB0
    have h := hconv g (fun _ => g) B (fun _ => hg.continuousOn) hb (hunif g)
    dsimp only at h
    exact h.2.2.2.2
  have hone : ∀ (t : ℝ) (y : X), y ∉ bdry s →
      |(fun (_ : ℝ) (_ : X) => (1 : ℝ)) t y| ≤ 1 * Real.log (rW L s y) := by
    intro t y _
    simpa using hlog1 y
  have h1 := hconv (fun _ => 1) (fun _ _ => 1) 1 (fun _ => continuousOn_const) hone (hunif _)
  dsimp only at h1
  have hμfin : IsFiniteMeasure (maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ)) := h1.1
  have hμTfin : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      IsFiniteMeasure (maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ)) := by
    filter_upwards [h1.2.2.2.1] with t ht
    exact (integrable_const_iff.1 ht).resolve_left one_ne_zero
  have hzero : {y | GroundTheory.Heights₂.Heights.AnalyticLimit.secNorm L' v y = 0} = bdry v := by
    ext y
    simp [GroundTheory.Heights₂.Heights.AnalyticLimit.secNorm, bdry, Real.exp_ne_zero]
  have hnull : ∀ Φ : Fin e → LocPot X,
      maMeasure A Φ {y | GroundTheory.Heights₂.Heights.AnalyticLimit.secNorm L' v y = 0} = 0 := by
    intro Φ
    rw [hzero]
    exact maMeasure_bdry_null_any A L' v ![1] ![Dg] hv hvsnc Φ
  have hbd : ∀ y, 0 ≤ GroundTheory.Heights₂.Heights.AnalyticLimit.secNorm L' v y ∧
      GroundTheory.Heights₂.Heights.AnalyticLimit.secNorm L' v y ≤ 1 := by
    intro y
    have h0 : 0 ≤ GroundTheory.Heights₂.Heights.AnalyticLimit.secNorm L' v y :=
      mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
    refine ⟨h0, ?_⟩
    by_contra hlt
    have hpos := Real.log_pos (not_le.1 hlt)
    have h2 : logNormSec L' v y = Real.log (GroundTheory.Heights₂.Heights.AnalyticLimit.secNorm L' v y) := rfl
    linarith [hvle y]
  cases e with
  | zero =>
    have hfin : Finite X := by
      have hsub : ∀ j, (A.chart j).source.Subsingleton := fun j x hx y hy =>
        (A.chart j).injOn hx hy (Subsingleton.elim _ _)
      have hU : (⋃ j, (A.chart j).source).Finite := Set.finite_iUnion fun j => (hsub j).finite
      have hcov : (Set.univ : Set X) ⊆ ⋃ j, (A.chart j).source := fun x _ =>
        Set.mem_iUnion.2 (A.cover x)
      exact Set.finite_univ_iff.1 (hU.subset hcov)
    have hμeq : ∀ t, maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ) =
        maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ) := fun t =>
      congrArg _ (Subsingleton.elim _ _)
    have hint : Integrable (fun y => -logNormSec L' v y)
        (maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ)) := Integrable.of_finite
    simp only [hμeq]
    exact ⟨hint, Filter.Eventually.of_forall fun _ => hint, tendsto_const_nhds⟩
  | succ e =>
    have hsmall := _root_.GlobalTheory.CompanionTheory.Ar.Giv.green_small_uniform GroundTheory.Heights₂.Heights.AnalyticLimit.UniformIntegrability.full
      GlobalTheory.CompanionTheory.Ar.Giv.tailBound_holds A Θ L s m W hΘ hΘpos hL hs hsnc hsle L' v Dg hL' hv hvsnc
      hsvsnc th ph phT C₅ C t₀ hsing hreg
    exact _root_.GlobalTheory.CompanionTheory.Ar.Giv.tendsto_integral_neg_log_of_green_small (maMeasure A (fun i => th i + LocPot.ofFun (ph i) + Θ))
      (fun t => maMeasure A (fun i => th i + LocPot.ofFun (phT i t) + Θ))
      (GroundTheory.Heights₂.Heights.AnalyticLimit.secNorm L' v) hμfin hμTfin
      (GroundTheory.Heights₂.Heights.AnalyticLimit.continuous_secNorm A L' v hL' hv) hbd (hnull _)
      (Filter.Eventually.of_forall fun t => hnull _) hweak hsmall

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ZeroWeightRegularFamily
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem levi_const_zero {D : ℕ} (y w : Fin D → ℂ) : levi (fun _ : Fin D → ℂ => (0 : ℝ)) y w = 0 := by
  simp [levi]

theorem zeroMember_isRegFamily : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) (C₅ C t₁ : ℝ), IsPotential A Θ → IsPosPot A Θ → (∀ y, logNormSec L s y ≤ 0) → 0 ≤ C₅ → 0 ≤ C → 0 < t₁ → t₁ ≤ Real.exp (-Real.exp 1) → IsSingWeight A L s (LocPot.ofFun 0) 0 C₅ ∧ IsRegFamily A Θ L s (LocPot.ofFun 0) 0 (fun _ => 0) C t₁ ∧ IsRegFamilyC2 A s 0 (fun _ => 0) := by
  intro e X _ A Θ L s C₅ C t₁ hΘ hpos hL hC₅ hC ht₁ hte
  have hr : ∀ y, Real.exp 1 ≤ rW L s y := fun y => by
    have := hL y; unfold rW; linarith
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hlogr : ∀ y, 0 ≤ Real.log (rW L s y) := fun y => Real.log_nonneg (he1.trans (hr y))
  have hε : ∀ t, 0 < t → t ≤ t₁ → 0 ≤ epsT C t := by
    intro t ht htt
    rw [epsT_eq_mul]
    exact mul_nonneg hC (loglog_quot_nonneg ht (htt.trans hte))
  have hll : ∀ t, 0 < t → t ≤ t₁ → 1 ≤ Real.log (Real.log (1 / t)) :=
    fun t ht htt => (log_inv_bounds ht (htt.trans hte)).2
  have h0 : A.Smooth (0 : X → ℝ) := fun j => contDiffOn_const
  have ht1 : t₁ < 1 := by
    exact hte.trans_lt (Real.exp_lt_one_iff.2 (neg_lt_zero.2 (Real.exp_pos 1)))
  refine ⟨⟨isPotential_ofFun A 0 h0, fun j => contDiffOn_const, ?_, fun y _ => ⟨?_, hC₅⟩⟩,
    ⟨ht₁, ht1, fun t ht htt => ?_⟩, fun j K _ _ => ⟨fun u hu => Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu,
      fun u hu => Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu,
      fun u hu => Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu⟩⟩
  · intro x j y _ w
    show 0 ≤ levi (fun z => (0 : X → ℝ) ((A.chart j).symm z) + (0 : X → ℝ) ((A.chart j).symm z)) y w
    simp only [Pi.zero_apply, add_zero]
    rw [levi_const_zero]
  · have := mul_nonneg hC₅ (hlogr y)
    show -C₅ * Real.log (rW L s y) ≤ 0
    linarith
  · have hεt := hε t ht htt
    have hr3 : 0 ≤ t ^ ((1 : ℝ) / 3) := Real.rpow_nonneg ht.le _
    refine ⟨h0, fun _ => hC, fun _ _ => le_refl _, fun _ => ?_, ?_, fun _ _ _ => ?_, fun y _ => ?_,
      fun t' htt' ht' _ => ?_⟩
    · have := mul_nonneg hC (le_trans zero_le_one (hll t ht htt))
      show -C * Real.log (Real.log (1 / t)) ≤ 0
      linarith
    · intro x j y hy w
      obtain ⟨hyt, hyU⟩ := hy
      have hU : (A.chart j).symm y ∈ (Set.univ ∩ Set.univ) ∩ Θ.U x := hyU
      have hO2 : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U x) :=
        (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target (Θ.isOpen_U x)
      have hΘ2 : ContDiffAt ℝ 2 (Θ.φ x ∘ (A.chart j).symm) y :=
        ((hΘ.1 x j).contDiffAt (hO2.mem_nhds ⟨hyt, hU.2⟩)).of_le (by norm_cast)
      have hΘl : 0 ≤ levi (Θ.φ x ∘ (A.chart j).symm) y w := by
        by_cases hw : w = 0
        · rw [hw, levi_zero]
        · exact (hpos x j y ⟨hyt, hU.2⟩ w hw).le
      have hfun : (LocPot.ofFun 0 + LocPot.ofFun 0 + Θ.rsmul (epsT C t)).φ x ∘ (A.chart j).symm =
          fun z => (fun _ : Fin e → ℂ => (0 : ℝ)) z + epsT C t * (Θ.φ x ∘ (A.chart j).symm) z := by
        funext z
        show (0 : X → ℝ) _ + (0 : X → ℝ) _ + epsT C t * Θ.φ x _ = 0 + epsT C t * Θ.φ x _
        simp
      rw [hfun, levi_add_smul (epsT C t) contDiffAt_const hΘ2 w, levi_const_zero]
      exact add_nonneg le_rfl (mul_nonneg hεt hΘl)
    · show (0 : ℝ) ≤ 0 + t ^ ((1 : ℝ) / 3) + epsT C t
      linarith
    · have := mul_nonneg hεt (le_trans (Real.exp_pos 1).le (hr y))
      show (0 : ℝ) ≤ 0 + t ^ ((1 : ℝ) / 3) + epsT C t * rW L s y
      linarith
    · have := mul_nonneg hC (hε t' (ht.trans_le htt') ht')
      show (0 : ℝ) ≤ 0 + C * epsT C t'
      linarith

end GlobalTheory.CompanionTheory.Ar.Giv
end

