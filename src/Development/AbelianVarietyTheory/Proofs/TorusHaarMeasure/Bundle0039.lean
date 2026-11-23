module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.UpperBounds.SumNormSqWPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0002
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0033
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0020
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OmFConnPf
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableSetSatFrames

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContDiffAtCompCpt
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Up

namespace DivLeviPf

section Euclid

variable {n p : ℕ} {g : Fin p → V n → ℂ} {y : V n}

theorem logSum_contDiffAt (hg : ∀ k, ContDiffAt ℂ ∞ (g k) y) (hne : ∃ k, g k y ≠ 0) :
    ContDiffAt ℝ ∞ (fun w => Real.log (∑ k, ‖g k w‖ ^ 2)) y := by
  have h1 : ContDiffAt ℝ ∞ (fun w => ∑ k, ‖g k w‖ ^ 2) y := by
    simp only [← Complex.normSq_eq_norm_sq]
    exact ContDiffAt.sum fun k _ => HE.normSq_contDiffAt (hg k)
  exact h1.log (sum_normSq_pos hne).ne'

theorem logSum_levi_nonneg (hg : ∀ k, ContDiffAt ℂ ∞ (g k) y) (hne : ∃ k, g k y ≠ 0)
    (ξ : Fin n → ℂ) :
    0 ≤ (leviV n (fun w => ((Real.log (∑ k, ‖g k w‖ ^ 2) : ℝ) : ℂ)) y ξ).re := by
  obtain ⟨k0, hk0⟩ := hne
  have h := leviLogNormSq n p g y ξ (fun k => (hg k).of_le HE.two_le_inf)
    (fun h => hk0 (congrFun h k0))
  have e : (fun w => ((Real.log (∑ k, ‖g k w‖ ^ 2) : ℝ) : ℂ)) =
      fun w => ((Real.log (sqNorm (fun i => g i w)) : ℝ) : ℂ) := by
    funext w
    simp only [← Complex.normSq_eq_norm_sq]
    rfl
  rw [e, h, Complex.ofReal_re]
  exact div_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
    (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)

end Euclid

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem contDiffAt_comp_cpt {P : Frame X.Ψ r → ℂ} (hP : DifferentiableOn ℂ P X.dom)
    (x0 : Frame X.Ψ r) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    ContDiffAt ℂ ∞ (fun w => P (cpt X x0 w)) z := by
  have hc : Differentiable ℂ (cpt X x0) :=
    differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b =>
      (IW.cpt_entry_cd X x0 τ a b).differentiable (by simp)
  exact HE.contDiffAt_of_punct (ExF.isOpen_OmF X x0)
    (hP.comp hc.differentiableOn fun w hw => hw) hz

theorem exists_s_ne_zero {Xa : ArchInM X} (Fl : FlatM X Xa) {x0 : Frame X.Ψ r} (hx0 : x0 ∈ X.dom) :
    ∃ k, ∃ x ∈ X.dom, Fl.s k x ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨j, -⟩ := (Fl.S_eq x0 hx0).1 fun k => h k x0 hx0
  have h0 : (0 : V (nd X)) ∈ OmF X (Fl.xs j) := by
    show cpt X (Fl.xs j) 0 ∈ X.dom
    rw [IW.cpt_zero]
    exact Fl.xs_mem j
  have hev : (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      Fl.s k (cpt X (Fl.xs j) z) / Fl.w0 (cpt X (Fl.xs j) z) : V (nd X))) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [(ExF.isOpen_OmF X (Fl.xs j)).mem_nhds h0] with w hw
    ext k
    simp [h k _ hw]
  apply Fl.coord j
  rw [hev.fderiv_eq, fderiv_fun_const]
  have h2 := Xa.n_ge
  have : Nonempty (Fin (nd X)) := ⟨⟨0, by omega⟩⟩
  show LinearMap.det (0 : V (nd X) →ₗ[ℂ] V (nd X)) = 0
  exact LinearMap.det_zero' (EuclideanSpace.basisFun (Fin (nd X)) ℂ).toBasis

end DivLeviPf


end GlobalTheory.Up
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.UnfoldPoincareOnto
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory.PoincareClosed

theorem unfold_poincare_onto :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ ψ : Frame X.Ψ r → ℝ≥0∞, Measurable ψ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x) → ∫⁻ z, ψ (cpt X x0 z) ∂muF X x0 = ∫⁻ z in FF, ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0) ∧ (KaUnfoldStatement (E := E)) ∧ (PairUnfoldStatement (E := E)) ∧ (PoinStatement (E := E)) ∧ (OntoStatement (E := E)) := by
  obtain ⟨-, hMeas, -, hExt⟩ := GlobalTheory.FrameMeasureClosed.measure_statements (E := E)
  have hUnf := GlobalTheory.Unfold.lintegral_unfold (E := E) hMeas
  have hκ := GlobalTheory.kaFrame (E := E) GlobalTheory.FramePotential.frame_potential_basic
    GlobalTheory.MinorRatioNear.minorRatio_near (GlobalTheory.FrameSumBound.frame_sum_bound GlobalTheory.grpSep)
  have hKa : KaUnfoldStatement (E := E) := GlobalTheory.kaUnfold_of_unfold_of_kappa hUnf hκ
  have hPair : PairUnfoldStatement (E := E) :=
    GlobalTheory.PairUnfold.pairUnfold_of_unfold (GlobalTheory.UnfoldComplex.unfold_integral hUnf) hKa
  have hN := GlobalTheory.NormFactor.nfac_transform (E := E)
  have hPoin : PoinStatement (E := E) :=
    GlobalTheory.PoincareAssembly.poinStatement_of hκ
      (GlobalTheory.PointSup.pointSup hMeas GlobalTheory.OrthNear.orthNear hN)
      (GlobalTheory.norm_le_sqrt_weight_near_orthonormal hMeas GlobalTheory.OrthNear.orthNear hN)
      (GlobalTheory.PoinHol.poin_summable_isBddSec GlobalTheory.differentiableOn_tsum_of_norm_le hN)
      (GlobalTheory.poincare_sqIntegrable_fundSet hUnf)
  exact ⟨hUnf, hKa, hPair, hPoin,
    onto_of hPoin hExt RhGradFStatement_holds exhaustG_holds hKa hPair bigCellStatement_holds
      OmFConnStatement_holds⟩

end GlobalTheory.PoincareClosed
end

