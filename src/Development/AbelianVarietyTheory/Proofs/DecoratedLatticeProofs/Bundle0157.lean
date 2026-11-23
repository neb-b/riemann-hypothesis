module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergTranslateThetaContinuousDifferentiable
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0141
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0131
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0829
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SchurOrthogonalitySquareIntegrable
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.SharpRestriction.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0001
public import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.CarriesOfKilled
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SobolevBoundedThetaFormMatrixCoeffSmooth
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff Topology

namespace GlobalTheory.Unf.MatCoef

theorem contDiff_of_partials {k : ℕ} (P : ((Fin k → ℝ) → ℂ) → Prop) (hc : ∀ F, P F → Continuous F)
    (hd : ∀ F, P F → ∀ i : Fin k, ∃ (m : ℕ) (a H : Fin m → (Fin k → ℝ) → ℂ), (∀ j, ContDiff ℝ ∞ (a j)) ∧
      (∀ j, P (H j)) ∧ ∀ t, HasDerivAt (fun s : ℝ => F (t + s • Pi.single i 1)) (∑ j, a j t * H j t) 0) :
    ∀ F, P F → ContDiff ℝ ∞ F := by
  have key : ∀ n : ℕ, ∀ F, P F → ContDiff ℝ n F := by
    intro n
    induction n with
    | zero => intro F hF; exact contDiff_zero.2 (hc F hF)
    | succ n ih =>
      intro F hF
      choose m a H ha hH hD using hd F hF
      have hGc : ∀ i, Continuous fun t => ∑ j, a i j t * H i j t := fun i =>
        continuous_finsetSum _ fun j _ => ((ha i j).continuous).mul (hc _ (hH i j))
      have hfd := _root_.GlobalTheory.hasFDerivAt_of_continuous_coordinate_line_derivs k F (fun i t => ∑ j, a i j t * H i j t) hGc hD
      have hfe : fderiv ℝ F = fun t => ∑ i, (∑ j, a i j t * H i j t) •
          (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (1 : ℂ) := by
        funext t
        rw [(hfd t).fderiv]
        refine Finset.sum_congr rfl fun i _ => ?_
        ext x
        simp [mul_comm]
      rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl, contDiff_succ_iff_fderiv]
      refine ⟨fun t => (hfd t).differentiableAt, by simp, ?_⟩
      rw [hfe]
      refine ContDiff.sum fun i _ => ?_
      have hs : ContDiff ℝ n fun t => ∑ j, a i j t * H i j t :=
        ContDiff.sum fun j _ => ((ha i j).of_le (mod_cast le_top)).mul (ih _ (hH i j))
      exact hs.smul contDiff_const
  intro F hF
  exact contDiff_infty.2 fun n => key n F hF

end GlobalTheory.Unf.MatCoef

namespace GlobalTheory.Unf.MatCoef

open GlobalTheory.OrientedHeis GlobalTheory.FockCompare

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} {S T : HSp D}

theorem form_sub {ℓ : (WO S T → ℂ) → ℂ} (hℓ : IsSobForm ψ θ S T ℓ) {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hg : IsThetaFunO ψ S T g) : ℓ (f - g) = ℓ f - ℓ g := by
  have e : f - g = f + (-1 : ℂ) • g := by rw [neg_one_smul, sub_eq_add_neg]
  rw [e, hℓ.add f _ hf (theta_smul (-1) hg), hℓ.smul (-1) g hg]
  ring

theorem symplOH_zero_left (u : WO S T) : symplOH S T 0 u = 0 := by
  have := symplOH_add_left (S := S) (T := T) 0 0 u
  rw [add_zero] at this
  linear_combination -this

theorem decomp (h : Chart θ σ) (a : WO S T) : (iotaW σ T S (piW θ T S a)).map (finPart D) = 0 ∧
    (a - iotaW σ T S (piW θ T S a)).map (infPart D) = 0 := by
  refine ⟨h.real_iota T S _, ?_⟩
  have hp : piW θ T S (a - iotaW σ T S (piW θ T S a)) = 0 := by rw [AddMonoidHom.map_sub, h.pi_iota, sub_self]
  ext i j
  exact ThetaCont.infPart_eq_zero h _ fun τ => congrFun (congrFun (congrFun hp τ) i) j

theorem theta_heisO_any (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (u : WO S T) : IsThetaFunO ψ S T (heisO ψ S T u f) := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨hr, hn⟩ := decomp h u
  have e : heisO ψ S T u f = heisO ψ S T (iotaW σ T S (piW θ T S u)) (heisO ψ S T (u - iotaW σ T S (piW θ T S u)) f) := by
    rw [heisO_heisO, (symplOH_fin_real hn hr).2, AddChar.map_zero_eq_one, one_smul, add_sub_cancel]
  rw [e]
  exact theta_heisO_real hθ hψ hr (GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hf hn)

theorem continuous_form (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {ℓ : (WO S T → ℂ) → ℂ}
    (hℓ : IsSobForm ψ θ S T ℓ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    Continuous fun u => ℓ (heisO ψ S T u f) := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  haveI : IsTopologicalAddGroup (Formalism.L2.Theta.AE D) := IsTopologicalRing.to_topologicalAddGroup
  haveI : IsTopologicalAddGroup (WO S T) := Pi.topologicalAddGroup
  haveI : ContinuousSub (WO S T) := IsTopologicalAddGroup.to_continuousSub
  haveI : ContinuousAdd (WO S T) := inferInstance
  refine continuous_iff_continuousAt.2 fun u₀ => ?_
  have hg : IsThetaFunO ψ S T (heisO ψ S T u₀ f) := theta_heisO_any hψ hθ hf u₀
  obtain ⟨U, hU, hl⟩ := hg.level
  obtain ⟨d, C, hC⟩ := hℓ.bound U hU
  have hgU : heisO ψ S T u₀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U := ⟨hg, hl⟩
  let r : WO S T → WO S T := fun a => iotaW σ T S (piW θ T S a)
  have hrc : Continuous r := (h.continuous_iota T S).comp (continuous_pi' hθ T S)
  have hr0 : r 0 = 0 := by simp [r]
  have hnc : Continuous fun a => a - r a := continuous_id.sub hrc
  have hev : ∀ᶠ a in 𝓝 (0 : WO S T), a - r a ∈ U :=
    hnc.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simp [hr0]))
  have hform : ∀ a, a - r a ∈ U → ℓ (heisO ψ S T (u₀ + a) f) =
      ψ (-(symplOH S T a u₀)) * ℓ (heisO ψ S T (r a) (heisO ψ S T u₀ f)) := by
    intro a ha
    obtain ⟨hr, hn⟩ := decomp h a
    have e1 : heisO ψ S T (r a) (heisO ψ S T u₀ f) = heisO ψ S T a (heisO ψ S T u₀ f) := by
      have e2 : heisO ψ S T (a - r a) (heisO ψ S T (r a) (heisO ψ S T u₀ f)) = heisO ψ S T (r a) (heisO ψ S T u₀ f) :=
        heisO_comm_fin_real hn hr (hl _ ha hn)
      rw [← e2, heisO_heisO, (symplOH_fin_real hn hr).1, AddChar.map_zero_eq_one, one_smul, sub_add_cancel]
    have e3 : heisO ψ S T a (heisO ψ S T u₀ f) = ψ (symplOH S T a u₀) • heisO ψ S T (u₀ + a) f := by
      rw [heisO_heisO, add_comm]
    rw [e1, e3, hℓ.smul _ _ (theta_heisO_any hψ hθ hf _), ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel,
      AddChar.map_zero_eq_one, one_mul]
  have hphase : Filter.Tendsto (fun a => ψ (-(symplOH S T a u₀))) (𝓝 0) (𝓝 1) := by
    have hc : Continuous fun a : WO S T => ψ (-(symplOH S T a u₀)) :=
      hψ.1.1.comp (continuous_symplOH continuous_id continuous_const).neg
    simpa only [symplOH_zero_left, neg_zero, AddChar.map_zero_eq_one] using hc.tendsto 0
  have hmain : Filter.Tendsto (fun a => ℓ (heisO ψ S T (r a) (heisO ψ S T u₀ f))) (𝓝 0)
      (𝓝 (ℓ (heisO ψ S T u₀ f))) := by
    have ht := ((_root_.GlobalTheory.HeisTaylor.heisO_taylor D ψ hψ θ hθ S T d _ hg).1).comp (hrc.tendsto' 0 0 hr0)
    have ht2 : Filter.Tendsto (fun a => (C : ℝ≥0∞) * supSob ψ θ d (heisO ψ S T (r a) (heisO ψ S T u₀ f) - heisO ψ S T u₀ f))
        (𝓝 0) (𝓝 0) := by
      simpa only [mul_zero, Function.comp_def] using ENNReal.Tendsto.const_mul ht (Or.inr ENNReal.coe_ne_top)
    rw [tendsto_iff_edist_tendsto_0]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht2 (fun _ => zero_le) fun a => ?_
    have hm : heisO ψ S T (r a) (heisO ψ S T u₀ f) ∈ GlobalTheory.Size.thetaLevel ψ S T U :=
      ⟨theta_heisO_real hθ hψ (h.real_iota T S _) hg, fun u hu h0 => heisO_comm_fin_real h0 (h.real_iota T S _) (hl u hu h0)⟩
    show edist _ _ ≤ _
    rw [edist_eq_enorm_sub, ← form_sub hℓ hm.1 hg]
    exact hC _ (sub_mem hm hgU)
  have hlim : Filter.Tendsto (fun a => ℓ (heisO ψ S T (u₀ + a) f)) (𝓝 0) (𝓝 (ℓ (heisO ψ S T u₀ f))) := by
    have := hphase.mul hmain
    rw [one_mul] at this
    exact this.congr' (hev.mono fun a ha => (hform a ha).symm)
  have hc2 : Filter.Tendsto (fun u => u - u₀) (𝓝 u₀) (𝓝 0) := tendsto_sub_nhds_zero_iff.2 Filter.tendsto_id
  exact (hlim.comp hc2).congr fun u => by simp only [Function.comp_apply, add_sub_cancel]

theorem deriv_phase (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {M : ℝ →+ WO S T} (hM : Continuous M)
    (hMf : ∀ s, (M s).map (finPart D) = 0) (w : WO S T) :
    deriv (fun s : ℝ => ψ (symplOH S T w (M s))) 0 =
      -(Real.pi * Complex.I) * (omO S T (piW θ T S w) (piW θ T S (M 1)) : ℂ) := by
  have hlin : ∀ s : ℝ, piW θ T S (M s) = s • piW θ T S (M 1) := fun s => by
    have := map_real_smul ((piW θ T S).comp M) ((continuous_pi' h.inf T S).comp hM) s 1
    simpa using this
  have e : (fun s : ℝ => ψ (symplOH S T w (M s))) = fun s : ℝ =>
      Complex.exp (-(Real.pi * Complex.I) * ((s * omO S T (piW θ T S w) (piW θ T S (M 1)) : ℝ) : ℂ)) := by
    funext s
    rw [← h.iota_pi (hMf s), psi_symplOH h hψ, hlin, LinearMap.map_smul, smul_eq_mul]
  rw [e]
  have hd : HasDerivAt (fun s : ℝ =>
      Complex.exp (-(Real.pi * Complex.I) * ((s * omO S T (piW θ T S w) (piW θ T S (M 1)) : ℝ) : ℂ)))
      (Complex.exp (-(Real.pi * Complex.I) * (((0 : ℝ) * omO S T (piW θ T S w) (piW θ T S (M 1)) : ℝ) : ℂ)) *
        (-(Real.pi * Complex.I) * ((1 * omO S T (piW θ T S w) (piW θ T S (M 1)) : ℝ) : ℂ))) 0 :=
    ((((hasDerivAt_id (0 : ℝ)).mul_const (omO S T (piW θ T S w) (piW θ T S (M 1)))).ofReal_comp).const_mul
      (-(Real.pi * Complex.I))).cexp
  rw [hd.deriv]
  simp

theorem contDiff_phase (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {k : ℕ} {L : (Fin k → ℝ) →+ WO S T}
    (hL : Continuous L) {M : ℝ →+ WO S T} (hM : Continuous M) (hMf : ∀ s, (M s).map (finPart D) = 0) (u : WO S T) :
    ContDiff ℝ ∞ fun t => -deriv (fun s : ℝ => ψ (symplOH S T (u + L t) (M s))) 0 := by
  let A : (Fin k → ℝ) →L[ℝ] RW T S := AddMonoidHom.toRealLinearMap ((piW θ T S).comp L) ((continuous_pi' h.inf T S).comp hL)
  let B : RW T S →L[ℝ] ℝ := LinearMap.toContinuousLinearMap ((omO S T).flip (piW θ T S (M 1)))
  have hB : ∀ t, B (A t) = omO S T (piW θ T S (L t)) (piW θ T S (M 1)) := fun t => rfl
  have e : (fun t => -deriv (fun s : ℝ => ψ (symplOH S T (u + L t) (M s))) 0) = fun t =>
      (Real.pi * Complex.I) * Complex.ofRealCLM (omO S T (piW θ T S u) (piW θ T S (M 1)) + B (A t)) := by
    funext t
    rw [deriv_phase h hψ hM hMf, hB, AddMonoidHom.map_add (f := _), LinearMap.map_add₂, Complex.ofRealCLM_apply]
    ring
  rw [e]
  have hc : ContDiff ℝ ∞ fun t => omO S T (piW θ T S u) (piW θ T S (M 1)) + B (A t) :=
    contDiff_const.add (B.contDiff.comp A.contDiff)
  exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hc)

end GlobalTheory.Unf.MatCoef

namespace GlobalTheory.Unf.MatCoef

open GlobalTheory.OrientedHeis GlobalTheory.FockCompare

theorem matCoef_smooth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (S T : HSp D) (ℓ : (WO S T → ℂ) → ℂ), IsSobForm ψ θ S T ℓ → ∀ f, IsThetaFunO ψ S T f →
    Continuous (fun u => ℓ (heisO ψ S T u f)) ∧ ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WO S T), Continuous L →
      (∀ t, (L t).map (finPart D) = 0) → ∀ u, ContDiff ℝ ∞ fun t => ℓ (heisO ψ S T (u + L t) f) := by
  intro D ψ hψ θ hθ S T ℓ hℓ f hf
  refine ⟨continuous_form hψ hθ hℓ hf, fun k L hL hLf u => ?_⟩
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  let P : ((Fin k → ℝ) → ℂ) → Prop := fun F =>
    ∃ (u : WO S T) (f : WO S T → ℂ), IsThetaFunO ψ S T f ∧ F = fun t => ℓ (heisO ψ S T (u + L t) f)
  refine contDiff_of_partials P ?_ ?_ _ ⟨u, f, hf, rfl⟩
  · rintro _ ⟨u, f, hf, rfl⟩
    exact (continuous_form hψ hθ hℓ hf).comp (continuous_const.add hL)
  · rintro _ ⟨u, f, hf, rfl⟩ i
    let E : ℝ →ₗ[ℝ] (Fin k → ℝ) := LinearMap.toSpanSingleton ℝ (Fin k → ℝ) (Pi.single i 1)
    let M : ℝ →+ WO S T := L.comp E.toAddMonoidHom
    have hM : Continuous M := hL.comp E.continuous_of_finiteDimensional
    have hMf : ∀ s, (M s).map (finPart D) = 0 := fun s => hLf _
    have hf' : IsThetaFunO ψ S T (fun p => deriv (fun s : ℝ => heisO ψ S T (M s) f p) 0) :=
      ((_root_.GlobalTheory.HeisTaylor.heisO_taylor D ψ hψ θ hθ S T 0 f hf).2 M hM hMf).1
    refine ⟨2, ![fun _ => 1, fun t => -deriv (fun s : ℝ => ψ (symplOH S T (u + L t) (M s))) 0],
      ![fun t => ℓ (heisO ψ S T (u + L t) (fun p => deriv (fun s : ℝ => heisO ψ S T (M s) f p) 0)),
        fun t => ℓ (heisO ψ S T (u + L t) f)], fun j => ?_, fun j => ?_, fun t => ?_⟩
    · fin_cases j
      · exact contDiff_const
      · exact contDiff_phase h hψ hL hM hMf u
    · fin_cases j
      · exact ⟨u, _, hf', rfl⟩
      · exact ⟨u, f, hf, rfl⟩
    · have e : (fun s : ℝ => ℓ (heisO ψ S T (u + L (t + s • Pi.single i 1)) f)) =
          fun s => ℓ (heisO ψ S T ((u + L t) + M s) f) := by
        funext s
        have : E s = s • Pi.single i 1 := rfl
        rw [map_add (f := _), add_assoc, ← this]
        rfl
      rw [e]
      convert _root_.GlobalTheory.MatCoeffDeriv.hasDerivAt_form_heisO_line D ψ hψ θ hθ S T ℓ hℓ f hf M hM hMf (u + L t) using 1
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_mul]
      ring

end GlobalTheory.Unf.MatCoef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalOperatorEigenvaluesDeterminedByParams
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ParamEigen

variable {D : D7} {V : HSp D}

theorem heckeLin_eq_of_rep {K : Subgroup (GA D V)} {α α' : GA D V} {R R' : Finset (GA D V)}
    (hR : IsCosetRep V (K : Set (GA D V)) α R) (hR' : IsCosetRep V (K : Set (GA D V)) α' R')
    {a b : GA D V} (ha : a ∈ K) (hb : b ∈ K) (hα : α' = a * α * b) {f : GA D V → ℂ}
    (hf : ∀ k ∈ K, ∀ g, f (g * k) = f g) : heckeLin V R f = heckeLin V R' f := by
  classical
  have m1 : ∀ γ ∈ R, ∃ k₁ ∈ (K : Set (GA D V)), ∃ k₂ ∈ (K : Set (GA D V)), γ = k₁ * α' * k₂ := fun γ hγ => by
    obtain ⟨-, k₁, h₁, k₂, h₂, rfl⟩ := hR.1 γ hγ
    exact ⟨k₁ * a⁻¹, K.mul_mem h₁ (K.inv_mem ha), b⁻¹ * k₂, K.mul_mem (K.inv_mem hb) h₂, by rw [hα]; group⟩
  have m2 : ∀ γ ∈ R', ∃ k₁ ∈ (K : Set (GA D V)), ∃ k₂ ∈ (K : Set (GA D V)), γ = k₁ * α * k₂ := fun γ hγ => by
    obtain ⟨-, k₁, h₁, k₂, h₂, rfl⟩ := hR'.1 γ hγ
    exact ⟨k₁ * a, K.mul_mem h₁ ha, b * k₂, K.mul_mem hb h₂, by rw [hα]; group⟩
  have inv : ∀ x y : GA D V, x⁻¹ * y ∈ K → y⁻¹ * x ∈ K := fun x y h => by
    simpa using K.inv_mem h
  funext g
  simp only [heckeLin, LinearMap.coe_mk, AddHom.coe_mk]
  refine Finset.sum_bij' (fun γ hγ => (hR'.2 γ (m1 γ hγ)).exists.choose)
    (fun γ hγ => (hR.2 γ (m2 γ hγ)).exists.choose)
    (fun γ hγ => (hR'.2 γ (m1 γ hγ)).exists.choose_spec.1)
    (fun γ hγ => (hR.2 γ (m2 γ hγ)).exists.choose_spec.1) ?_ ?_ ?_
  · intro γ hγ
    have s1 := (hR'.2 γ (m1 γ hγ)).exists.choose_spec
    set γ' := (hR'.2 γ (m1 γ hγ)).exists.choose
    have s2 := (hR.2 γ' (m2 γ' s1.1)).exists.choose_spec
    exact (hR.2 γ' (m2 γ' s1.1)).unique s2 ⟨hγ, inv _ _ s1.2⟩
  · intro γ hγ
    have s1 := (hR.2 γ (m2 γ hγ)).exists.choose_spec
    set γ' := (hR.2 γ (m2 γ hγ)).exists.choose
    have s2 := (hR'.2 γ' (m1 γ' s1.1)).exists.choose_spec
    exact (hR'.2 γ' (m1 γ' s1.1)).unique s2 ⟨hγ, inv _ _ s1.2⟩
  · intro γ hγ
    have s1 := (hR'.2 γ (m1 γ hγ)).exists.choose_spec
    set γ' := (hR'.2 γ (m1 γ hγ)).exists.choose
    have e : g * γ = g * γ' * (γ'⁻¹ * γ) := by group
    rw [e, hf _ s1.2]

end GlobalTheory.ParamEigen

namespace GlobalTheory.ParamEigen

variable {D : D7} {V : HSp D}


open GlobalTheory.AdelicU GlobalTheory.PRep in
theorem heckeLin_eq_heckeVec {v : HeightOneSpectrum (𝓞 D.host.F)} {K : Set (GA D V)}
    (hK : ∀ x, x ∈ K ↔ ∃ k ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) v, emb D.sp.cm.sig V.gram v k = x)
    (g : GLoc D.sp.cm.sig V.gram v) {R : Finset (GA D V)} (hR : IsCosetRep V K (emb D.sp.cm.sig V.gram v g) R)
    {φ : GA D V → ℂ}
    (hφ : φ ∈ fixed ((rightReg ℂ _ ℂ).comp (emb D.sp.cm.sig V.gram v)) (stabLoc D.sp.cm.sig V.gram (frameLat V) v)) :
    heckeLin V R φ = GlobalTheory.LFun.heckeVec ((rightReg ℂ _ ℂ).comp (emb D.sp.cm.sig V.gram v))
      (stabLoc D.sp.cm.sig V.gram (frameLat V) v)
      (Formalism.UG.dosetInd ℂ (stabLoc D.sp.cm.sig V.gram (frameLat V) v) g) φ := by
  classical
  let H : Subgroup (GA D V) := (stabLoc D.sp.cm.sig V.gram (frameLat V) v).map (emb D.sp.cm.sig V.gram v)
  have hKH : K = (H : Set (GA D V)) := Set.ext fun x => (hK x).trans (by simp [H])
  subst hKH
  have := GlobalTheory.HeckeDual.isLattice_frameLat V
  obtain ⟨R₀, r1, r2⟩ := GlobalTheory.HeckeDual.exists_rep _ (isOpen_stabLoc D.sp.cm.sig V.gram (frameLat V) v)
    (isCompact_stabLoc D.sp.cm.sig V.gram (frameLat V) v) g
  obtain ⟨s1, s2⟩ := GlobalTheory.LFun.rep_image (emb D.sp.cm.sig V.gram v) (emb_injective _ _ v) hK r1 r2
  have hR₀ : IsCosetRep V (H : Set (GA D V)) (emb D.sp.cm.sig V.gram v g) (R₀.image (emb D.sp.cm.sig V.gram v)) :=
    ⟨fun γ hγ => ⟨by
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hγ
      exact mem_finPts.2 (projInf_emb _ _ v y), s1 γ hγ⟩, s2⟩
  have hinv : ∀ k ∈ H, ∀ x, φ (x * k) = φ x := by
    rintro _ ⟨k, hk, rfl⟩ x
    exact congrFun (GlobalTheory.LGrp.mem_fixed.1 hφ k hk) x
  rw [heckeLin_eq_of_rep hR hR₀ (one_mem H) (one_mem H) (by group) hinv,
    GlobalTheory.LFun.heckeVec_dosetInd hφ (R := R₀) (fun γ hγ => DoubleCoset.mem_doubleCoset.2 (r1 γ hγ))
      fun x hx => r2 x (DoubleCoset.mem_doubleCoset.1 hx)]
  funext x
  rw [heckeLin_apply, Finset.sum_image (emb_injective _ _ v).injOn, Finset.sum_apply]
  rfl

theorem doubleCoset_of_divAt {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} (hP : IsPrimeIdem P e f)
    {ϖ ϖ' : 𝓞 D.host.E} (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2) (h1' : ϖ' ∈ P.asIdeal)
    (h2' : ϖ' ∉ P.asIdeal ^ 2) {d : List ℤ} (hd : d.Pairwise (fun a b => b ≤ a)) {α α' : GA D V}
    (hα : SuppF V f α) (hα' : SuppF V f α') (hD : DivAt V e (ϖ : D.host.E) d α)
    (hD' : DivAt V e (ϖ' : D.host.E) d α') :
    ∃ a b, a ∈ KsphC V ∅ ∧ SuppF V f a ∧ b ∈ KsphC V ∅ ∧ SuppF V f b ∧ α' = a * α * b := by
  rcases id hP with ⟨hi, rfl⟩ | ⟨rfl, -, -⟩
  · obtain ⟨a, ⟨ha, ha'⟩, b, ⟨hb, hb'⟩, hab⟩ :=
      GlobalTheory.SplitLabel.split_label V P e ϖ ϖ' d α α' hi h1 h2 h1' h2' hα hα' hD hD'
    exact ⟨a, b, ha, ha', hb, hb', hab⟩
  · exact (GlobalTheory.InertDoubleCoset.inert_double_cosets V P _ hP (GlobalTheory.SphLabelOps.exists_real_unif D P) α hα).2.2
      ϖ ϖ' d α' h1 h2 h1' h2' hd hα' hD hD'

end GlobalTheory.ParamEigen

namespace GlobalTheory.ParamEigen

variable {D : D7} {V : HSp D}


open GlobalTheory.AdelicU GlobalTheory.PRep in
theorem exists_eig {J : Set (GA D V)} {χ : GA D V → ℂ} {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    (hJ : SphOff J χ Sb) (B : GlobalTheory.LFun.Fam D.host.E) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) :
    ∃ z : ℂ, ∀ f : GA D V → ℂ, GlobalTheory.LFun.IsParamFunV V Sb f B → ∀ R, Hecke₂ V J χ Sb P d R →
      heckeLin V R f = z • f := by
  classical
  by_cases h : ∃ R, Hecke₂ V J χ Sb P d R
  swap
  · exact ⟨0, fun f _ R hR => absurd ⟨R, hR⟩ h⟩
  obtain ⟨R₀, e₀, f₀, ϖ₀, α₀, hS, hP₀, p1, p2, hd, hJ1, -, hα₀, hD₀, -, hR₀⟩ := h
  have hv : P.under (𝓞 D.host.F) ∉ Sb := GlobalTheory.LFun.offS_iff.1 hS
  have hs := Supp.suppF_iff_of_isPrimeIdem V hP₀ rfl
  have hK : ∀ x, x ∈ {k | k ∈ J ∧ SuppF V f₀ k} ↔
      ∃ k ∈ stabLoc D.sp.cm.sig V.gram (frameLat V) (P.under (𝓞 D.host.F)), emb D.sp.cm.sig V.gram _ k = x :=
    fun x => by
      constructor
      · rintro ⟨m1, m2⟩
        obtain ⟨k, rfl⟩ := (hs x).1 m2
        exact ⟨k, (Supp.emb_mem_KsphC V k).1 ((hJ1 _ m2).1 m1), rfl⟩
      · rintro ⟨k, hk, rfl⟩
        have := (hs _).2 ⟨k, rfl⟩
        exact ⟨(hJ1 _ this).2 ((Supp.emb_mem_KsphC V k).2 hk), this⟩
  let H : Subgroup (GA D V) :=
    (stabLoc D.sp.cm.sig V.gram (frameLat V) (P.under (𝓞 D.host.F))).map (emb D.sp.cm.sig V.gram _)
  have hKH : {k | k ∈ J ∧ SuppF V f₀ k} = (H : Set (GA D V)) := Set.ext fun x => (hK x).trans (by simp [H])
  obtain ⟨g₀, rfl⟩ := (hs α₀).1 hα₀
  obtain ⟨z, hz⟩ := _root_.GlobalTheory.LFun.EigLoc.heckeVec_eq_smul_of_isParamVec _ _ D.sp.cm.sig V.rank V.gram (frameLat V) _ P rfl (B P) _
    (Formalism.UG.Final.DosetIndMem _ (stabLoc D.sp.cm.sig V.gram (frameLat V) (P.under (𝓞 D.host.F))) ℂ g₀)
  refine ⟨z, fun f hf R hR => ?_⟩
  obtain ⟨e, f', ϖ, α, -, hP', q1, q2, -, -, -, hα, hD, -, hRc⟩ := hR
  obtain ⟨rfl, rfl⟩ :=
    ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e₀ f₀ hP₀).2.2.2.1 e f' hP'
  have hpv := hf _ hv P rfl
  have hfix := hpv.mem_fixed
  obtain ⟨a, b, ha, ha', hb, hb', hab⟩ := doubleCoset_of_divAt hP₀ p1 p2 q1 q2 hd hα₀ hα hD₀ hD
  have hmem : ∀ k, k ∈ KsphC V ∅ → SuppF V f' k → k ∈ H := fun k hk hk' => by
    rw [← SetLike.mem_coe, ← hKH]
    exact ⟨(hJ1 k hk').2 hk, hk'⟩
  have hinv : ∀ k ∈ H, ∀ x, f (x * k) = f x := by
    rintro _ ⟨k, hk, rfl⟩ x
    exact congrFun (GlobalTheory.LGrp.mem_fixed.1 hfix k hk) x
  rw [hKH] at hRc hR₀
  rw [heckeLin_eq_of_rep hRc hR₀ (H.inv_mem (hmem a ha ha')) (H.inv_mem (hmem b hb hb')) (by rw [hab]; group) hinv,
    heckeLin_eq_heckeVec hK g₀ (hKH ▸ hR₀) hfix, hz _ _ f hpv]

end GlobalTheory.ParamEigen

namespace GlobalTheory.ParamEigen

theorem eig_of_param : ∀ (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), SphOff J χ Sb → ∀ B : GlobalTheory.LFun.Fam D.host.E,
    ∃ a : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, ∀ f : GA D V → ℂ, GlobalTheory.LFun.IsParamFunV V Sb f B →
      ∀ P d R, Hecke₂ V J χ Sb P d R → heckeLin V R f = a P d • f := by
  intro D V J χ Sb hJ B
  choose a ha using exists_eig (V := V) hJ B
  exact ⟨a, fun f hf P d R hR => ha P d f hf R hR⟩

end GlobalTheory.ParamEigen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaAdjointScalarTheoremOfScalarFormula
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.ThmAFromAForm

theorem pThmA_of_aForm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → AForm R.toRealDat R.SF → (∀ p c c', R.Carries p c → R.Carries p c' → R.EEc c = R.EEc c' ∧ ∀ i, R.Wc' i c = R.Wc' i c') → R.PThmA := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s _ hC _ hA h1
  exact GlobalTheory.LiftScalarTest.of_aForm R hA hC.scal.lam0 (fun i p c c' hc hc' => (h1 p c c' hc hc').2 i)

end GlobalTheory.ThmAFromAForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainCuspSpaceFiniteDimOfHarishChandra
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finDim_of_levFacts : GlobalTheory.Published.HarishChandraFinite → ∀ D : D7, LevFacts D → FinDim D := by
  intro hP D hL c hc j hj s hs
  have h1 := (hL c hc j hj s hs).1
  have : FiniteDimensional ℂ (Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L)) :=
    GlobalTheory.MultFinite.hcFinite hP hc.inf h1
  exact Module.Finite.map _ _

end GlobalTheory.ChainOnto

end
end

