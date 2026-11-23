module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfH
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.SumNormSqWPos
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0033

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Up.DivCorePf

open ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section

variable {r : ℕ} (X : Data E r)

theorem chi_ne_zero (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) : X.χ la γ ≠ 0 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin la
  intro h0
  have := h γ hγ
  rw [h0, zero_pow hn.ne'] at this
  exact zero_ne_one this

theorem isSec_one : X.IsSec 0 (fun _ => (1 : ℂ)) := by
  refine ⟨differentiableOn_const _, fun x _ b _ => by simp [bchar], fun γ hγ x _ => ?_⟩
  have h := X.χ_add 0 0 γ hγ
  rw [add_zero] at h
  rw [mul_one]
  exact mul_left_cancel₀ (chi_ne_zero X 0 hγ) (by rw [mul_one]; exact h)

variable {X}

theorem isSec_mul {la la' : Wt X.Ψ r} {P Q : Frame X.Ψ r → ℂ} (hP : X.IsSec la P)
    (hQ : X.IsSec la' Q) : X.IsSec (la + la') (fun x => P x * Q x) := by
  refine ⟨hP.1.mul hQ.1, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩
  · simp only [hP.2.1 x hx b hb, hQ.2.1 x hx b hb, bchar_add X hb]
    ring
  · simp only [hP.2.2 γ hγ x hx, hQ.2.2 γ hγ x hx, X.χ_add la la' γ hγ]
    ring

theorem isSec_pow {L : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec L P) (m : ℕ) :
    X.IsSec (m • L) (fun x => P x ^ m) := by
  induction m with
  | zero => simpa using isSec_one X
  | succ m ih => simpa only [succ_nsmul, pow_succ] using isSec_mul ih hP

theorem exists_extension (hExt : ExtFStatement (E := E)) {x0 : Frame X.Ψ r} (ho : IsOrth X x0)
    {la : Wt X.Ψ r} {W : Frame X.Ψ r → ℝ≥0∞} (hWL : WLower X la W) {bb : ℝ} (hbb : 0 ≤ bb)
    {F : V (nd X) → ℂ} (hF : DifferentiableOn ℂ F (OmF X x0)) (hI : InAt X x0 W bb F) :
    ∃ P : Frame X.Ψ r → ℂ, IsBEq X la P ∧ ∀ z ∈ OmF X x0, P (cpt X x0 z) = F z := by
  obtain ⟨c, hc, hWL'⟩ := hWL
  have hka1 : ∀ z ∈ OmF X x0, kaF X x0 bb z ≤ 1 := fun z hz => by
    unfold kaF
    rw [Real.exp_le_one_iff]
    have := mul_nonneg hbb (ExF.rhF_nonneg X x0 ho hz)
    linarith
  refine hExt r X x0 ho la F hF fun Cs _ _ => ?_
  have hpt : ∀ᵐ z ∂muF X x0, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z))) ≤
      ENNReal.ofReal (1 / c) * (ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z)) := by
    refine (OntoH.ae_mem_Om X x0).mono fun z hz => ?_
    have hk : 0 < kaF X x0 bb z := Real.exp_pos _
    have e : ‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z)) =
        1 / c * (‖F z‖ ^ 2 * (c * Real.exp (-phla X la (cpt X x0 z)))) := by field_simp
    rw [e, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
    gcongr
    · exact le_div_self (by positivity) hk (hka1 z hz)
    · exact hWL' _ hz
  refine ((setLIntegral_le_lintegral _ _).trans (lintegral_mono_ae hpt)).trans_lt ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI

theorem poin_sum_mul {ι : Type*} (S : Finset ι) {la la' : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ}
    {g Q : ι → Frame X.Ψ r → ℂ} (hg : ∀ i ∈ S, X.IsSec la' (g i))
    (hP : ∀ y ∈ X.dom, P y = ∑ i ∈ S, g i y * Q i y) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hQ : ∀ i ∈ S, Summable fun γ : X.Γ => ‖(X.χ la γ.1)⁻¹ * Q i (lact γ.1 x)‖) :
    poin X (la + la') P x = ∑ i ∈ S, g i x * poin X la (Q i) x := by
  unfold poin
  have e : ∀ γ : X.Γ, (X.χ (la + la') γ.1)⁻¹ * P (lact γ.1 x) =
      ∑ i ∈ S, g i x * ((X.χ la γ.1)⁻¹ * Q i (lact γ.1 x)) := by
    intro γ
    rw [hP _ (OntoS.dom_lact X γ.2 hx), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have h1 := chi_ne_zero X la γ.2
    have h2 := chi_ne_zero X la' γ.2
    rw [(hg i hi).2.2 γ.1 γ.2 x hx, X.χ_add la la' γ.1 γ.2]
    field_simp
  rw [tsum_congr e, Summable.tsum_finsetSum fun i hi => ((hQ i hi).of_norm).mul_left (g i x)]
  exact Finset.sum_congr rfl fun i _ => tsum_mul_left

end

end GlobalTheory.Up.DivCorePf
