module

public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Exch
section
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace PositivityTheory.SiegelWeilFormula.Act

theorem exch {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β] [Countable ι] {μ : Measure α} {m : Measure β}
    [SFinite μ] [SFinite m] (g : ι → α × β → ℂ) (hi : ∀ i, Integrable (g i) (μ.prod m))
    (hs : Summable fun i => ∫ p, ‖g i p‖ ∂(μ.prod m)) :
    Summable (fun i => ∫ u, ∫ v, g i (u, v) ∂m ∂μ) ∧
      ∫ u, ∫ v, (∑' i, g i (u, v)) ∂m ∂μ = ∑' i, ∫ u, ∫ v, g i (u, v) ∂m ∂μ := by
  have hsum : HasSum (fun i => ∫ u, ∫ v, g i (u, v) ∂m ∂μ) (∫ p, ∑' i, g i p ∂(μ.prod m)) := by
    have h := hasSum_integral_of_summable_integral_norm hi hs
    rw [show (fun i => ∫ p, g i p ∂(μ.prod m)) = fun i => ∫ u, ∫ v, g i (u, v) ∂m ∂μ from
      funext fun i => integral_prod (g i) (hi i)] at h
    exact h
  have hint : Integrable (fun p => ∑' i, g i p) (μ.prod m) := by
    refine ⟨AEStronglyMeasurable.tsum fun i => (hi i).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    calc ∫⁻ p, ‖∑' i, g i p‖ₑ ∂(μ.prod m) ≤ ∫⁻ p, ∑' i, ‖g i p‖ₑ ∂(μ.prod m) :=
          lintegral_mono fun p => enorm_tsum_le_tsum_enorm
      _ = ∑' i, ∫⁻ p, ‖g i p‖ₑ ∂(μ.prod m) :=
          lintegral_tsum fun i => (hi i).aestronglyMeasurable.enorm
      _ = ∑' i, ENNReal.ofReal (∫ p, ‖g i p‖ ∂(μ.prod m)) := by
          congr 1
          funext i
          rw [ofReal_integral_norm_eq_lintegral_enorm (hi i)]
      _ = ENNReal.ofReal (∑' i, ∫ p, ‖g i p‖ ∂(μ.prod m)) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg fun p => norm_nonneg _) hs).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  refine ⟨hsum.summable, ?_⟩
  rw [hsum.tsum_eq, integral_prod _ hint]

end PositivityTheory.SiegelWeilFormula.Act

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.IsFirstChernFamily
section
noncomputable section

open MeasureTheory

namespace PositivityTheory.SiegelWeilFormula.Act

def LatHaar : Prop :=
  ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (Γ : AddSubgroup V) [Countable Γ] (φ : V ≃ₜ+ V), (∀ x, φ x ∈ Γ ↔ x ∈ Γ) →
    ∀ s : Set V, IsAddFundamentalDomain Γ s μ → μ s ≠ 0 → μ s ≠ ⊤ → μ.map φ = μ

theorem latHaar : LatHaar := by
  unfold LatHaar
  intro V _ _ _ _ _ _ _ _ μ _ Γ _ φ hΓ s hs hs0 hstop
  have hmeas : Measurable φ := φ.continuous.measurable
  have : (μ.map φ).IsAddHaarMeasure := inferInstance
  have hc := Measure.isAddLeftInvariant_eq_smul (μ.map φ) μ
  have hqmp : Measure.QuasiMeasurePreserving φ μ μ := by
    refine ⟨hmeas.aemeasurable, fun t ht => ?_⟩
    rw [hc, Measure.smul_apply, ht, smul_zero]
  let e : Γ → Γ := fun g => ⟨φ.symm g, (hΓ _).1 (by simp)⟩
  have he : Function.Bijective e := by
    constructor
    · intro g g' h
      have h2 : φ (φ.symm (g : V)) = φ (φ.symm (g' : V)) := congrArg (fun x : Γ => φ (x : V)) h
      exact Subtype.ext (by simpa using h2)
    · intro g
      exact ⟨⟨φ g, (hΓ g).2 g.2⟩, Subtype.ext (by simp [e])⟩
  have hef : ∀ g : Γ, Function.Semiconj φ (e g +ᵥ ·) (g +ᵥ ·) := by
    intro g x
    show φ ((e g : V) + x) = (g : V) + φ x
    rw [map_add (f := _)]
    simp [e]
  have hs' : IsAddFundamentalDomain Γ (φ ⁻¹' s) μ := hs.preimage_of_equiv hqmp he hef
  have heq : μ (φ ⁻¹' s) = μ s := hs'.measure_eq hs
  have hνs : (μ.map φ) s = μ s := by
    rw [← heq]
    exact (φ.toHomeomorph.toMeasurableEquiv).map_apply s
  rw [hc, Measure.coe_nnreal_smul_apply] at hνs
  have h1 : ((Measure.addHaarScalarFactor (μ.map φ) μ : NNReal) : ENNReal) = 1 := by
    have h3 : ((Measure.addHaarScalarFactor (μ.map φ) μ : NNReal) : ENNReal) * μ s = 1 * μ s := by
      rw [one_mul]
      exact hνs
    exact (ENNReal.mul_left_inj hs0 hstop).1 h3
  have h2 : Measure.addHaarScalarFactor (μ.map φ) μ = 1 := by exact_mod_cast h1
  rw [hc, h2, one_smul]

end PositivityTheory.SiegelWeilFormula.Act

end
end

