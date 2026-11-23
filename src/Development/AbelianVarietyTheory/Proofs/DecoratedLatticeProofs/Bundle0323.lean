module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0303
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergWordsWeilOperatorSupNormPolynomialGrow
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergFixesLatticeVacuumPeriodLattice
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0436
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateAbsSumWeilTranslateModerateGrowth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

open scoped ENNReal NNReal

namespace GlobalTheory.MixedAbsGrowth

theorem map_infPart_nsmul {D : D7} {m r : ℕ} (n : ℕ) (u : Mx D m r) (hu : u.map (infPart D) = 0) :
    (n • u).map (infPart D) = 0 := by
  ext i j
  have h := congrFun (congrFun hu i) j
  simp only [Matrix.map_apply, Matrix.zero_apply] at h ⊢
  rw [Matrix.smul_apply, nsmul_eq_mul, (infPart D).map_mul, h, mul_zero]

theorem map_infPart_actO {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (u : WO S T)
    (hu : u.map (infPart D) = 0) : (actO S T g h u).map (infPart D) = 0 := by
  unfold actO
  rw [Matrix.map_mul, Matrix.map_mul, hu, Matrix.mul_zero, Matrix.zero_mul]

theorem actO_actO_inv {D : D7} {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h (actO S T g⁻¹ h⁻¹ x) = x := by
  have := GlobalTheory.WeilVacMove.actO_inv_actO g⁻¹ h⁻¹ x
  rwa [inv_inv, inv_inv] at this

theorem mixed_abs_growth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∃ (C : ℝ) (A : ℕ), ∀ g h (w : WO S₀ T), (∑' x : ratMx D T.rank ρ, ‖d.mixS T ψ v.μ v.𝓕 (om (g, h) f) x w‖ₑ) ≤ ENNReal.ofReal (C * (height S g * height T h) ^ A) := by
  intro D ψ S T χS χT om hW S₀ ρ d v f hf
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  obtain ⟨U, hUo, hU⟩ := hf.level
  obtain ⟨K₀, hK₀, -, m, hm⟩ := GlobalTheory.KernelSeminorm.exists_level_multiple hUo
  obtain ⟨k, hk⟩ := _root_.GlobalTheory.MixSumBound.mixS_tsum_le D ψ hW.std θ hθ S S₀ T ρ d v
  obtain ⟨C, hC⟩ := hk K₀ hK₀
  obtain ⟨A, hA⟩ := GlobalTheory.WeilWordGrowth.sup_words_growth D ψ S T χS χT om hW θ hθ k
  obtain ⟨c, hc⟩ := hA f hf
  refine ⟨(C : ℝ) * (m : ℝ) ^ k * max c 0, A + k, fun g h w => ?_⟩
  obtain ⟨n, hn0, hnm, hnU⟩ := hm g h
  have hF := hW.om_pres (g, h) f hf
  have hlev : ∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ S T (n • u) (om (g, h) f) = om (g, h) f := by
    intro u hu hinf
    have h1 := hU _ (hnU u hu hinf) (map_infPart_actO _ _ _ (map_infPart_nsmul n u hinf))
    have h2 := hW.om_heis g h (actO S T g⁻¹ h⁻¹ (n • u)) f hf
    rw [h1, actO_actO_inv] at h2
    exact h2.symm
  have h1 := hC n hn0 (om (g, h) f) hF hlev w
  have h2 : supSob ψ θ k (om (g, h) f) ≤ ENNReal.ofReal (c * (height S g * height T h) ^ A) := hc g h
  set H : ℝ := height S g * height T h with hH
  have H0 : 0 ≤ H := mul_nonneg (height_pos S g).le (height_pos T h).le
  refine h1.trans ?_
  have e1 : ((C : ℝ≥0∞) * (n : ℝ≥0∞) ^ k) = ENNReal.ofReal ((C : ℝ) * (n : ℝ) ^ k) := by
    rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_pow (Nat.cast_nonneg n),
      ENNReal.ofReal_natCast]
  rw [e1]
  refine (mul_le_mul' le_rfl (h2.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (le_max_left c 0) (pow_nonneg H0 A))))).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hn : (n : ℝ) ^ k ≤ ((m : ℝ) * H) ^ k := pow_le_pow_left₀ (Nat.cast_nonneg n) hnm k
  have hc0 : 0 ≤ max c 0 := le_max_right c 0
  calc (C : ℝ) * (n : ℝ) ^ k * (max c 0 * H ^ A) ≤ (C : ℝ) * ((m : ℝ) * H) ^ k * (max c 0 * H ^ A) := by
        gcongr
    _ = (C : ℝ) * (m : ℝ) ^ k * max c 0 * H ^ (A + k) := by rw [mul_pow, pow_add]; ring

end GlobalTheory.MixedAbsGrowth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedWeilVacuumEqVacuumOfMovedLattices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MovedVac

theorem halfBack : ∀ (D : D7) (S T : HSp D) (g : GA D S) (h : GA D T) (e : AE D) (u : WO S T),
    IsHalf e (actO S T g h u) → IsHalf e u := by
  intro D S T g h e u hu
  have hA : Formalism.L2.Theta.mt T h⁻¹ * Formalism.L2.Theta.mt T h = 1 := by
    simp only [Formalism.L2.Theta.mt, map_inv]
    exact congrArg Units.val (inv_mul_cancel (matHom T h))
  have hB : Formalism.L2.Theta.mt S g⁻¹ * Formalism.L2.Theta.mt S g = 1 := by
    simp only [Formalism.L2.Theta.mt, map_inv]
    exact congrArg Units.val (inv_mul_cancel (matHom S g))
  have cancel : ∀ X : Matrix (Fin T.rank) (Fin S.rank) (AE D),
      HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h⁻¹) (HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h) X)
        (Formalism.L2.Theta.mt S g⁻¹))) (Formalism.L2.Theta.mt S g) = X := by
    intro X
    simp only [Matrix.mul_assoc, hB, Matrix.mul_one]
    rw [← Matrix.mul_assoc, hA, Matrix.one_mul]
  have key : e • actO S T g h u = actO S T g h u := by
    ext i j; exact hu i j
  have key2 : e • u = u := by
    have h1 := congrArg (fun M : Matrix (Fin T.rank) (Fin S.rank) (AE D) =>
      HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h⁻¹) M) (Formalism.L2.Theta.mt S g)) key
    simp only [actO] at h1
    rw [cancel u] at h1
    simp only [Matrix.mul_smul, Matrix.smul_mul] at h1
    rw [cancel u] at h1
    exact h1
  intro i j
  have := congrFun (congrFun key2 i) j
  rw [Matrix.smul_apply, smul_eq_mul] at this
  exact this

theorem norm_weilRepresentation_thetaFunction_preserved : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (μ : (AE D)ˣ →* Circle) (om : Om S T),
    IsWeilDatumO ψ S T μ μ om → ∀ f, IsThetaFunO ψ S T f → ∀ p (m : Measure (WO S T)) (𝓕 : Set (WO S T)),
    IsCovolOne (ratL T S) m 𝓕 → nrm2 m 𝓕 (om p f) = nrm2 m 𝓕 f := by
  intro D ψ S T μ om hW f hf p m 𝓕 hm
  have hU := hW.om_unit m 𝓕 hm.1 hm.2.1 p f hf
  have hf' := hW.om_pres p f hf
  haveI : OpensMeasurableSpace (WO S T) := ⟨le_rfl⟩
  have key : ∀ F : WO S T → ℂ, Continuous F → nrm2 m 𝓕 F = (∫⁻ w in 𝓕, ‖F w‖ₑ ^ 2 ∂m).toReal := by
    intro F hF
    unfold nrm2
    have hc : Continuous fun w => ‖F w‖ ^ 2 := by fun_prop
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun w => ‖F w‖ ^ 2)
      (Filter.Eventually.of_forall fun w => sq_nonneg ‖F w‖) hc.aestronglyMeasurable]
    congr 1
    refine lintegral_congr fun w => ?_
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [key _ hf'.cont, key _ hf.cont, hU]

theorem latMove : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b), S.gram = 1 → T.gram = 1 →
    ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)),
    Moves S hS g N → Moves T hT h N' →
    ∀ u' ∈ latO S T (latFr S hS N) (latFr T hT N') (fun _ => True),
      ∃ u ∈ latO S T (intVec D _) (intVec D _) (fun _ => True), actO S T g h u = u' := _root_.GlobalTheory.LatMoveStd.latO_moved_onto

theorem latSign : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a)
    (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ g ∈ GfC S, ∀ h ∈ GfC T,
    ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)),
    Moves S hS g N → Moves T hT h N' → ∀ f, IsThetaFunO ψ S T f →
    IsLatVac (heisO ψ S T) (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) f →
    ∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
    toHom S T hS hT γ ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → ∀ v, GlobalTheory.AdTh.IsFinOf S T γ v →
    ∀ w, alV D.host.d sc (embH (tauE D) δ (toHom S T hS hT γ)) * heisO ψ S T v f w = f w := _root_.GlobalTheory.LatSign.latSign

theorem lamPre : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ)
    (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)),
    ∀ x ∈ LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N',
    ∃ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      toHom S T hS hT γ ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' ∧
      embH (tauE D) δ (toHom S T hS hT γ) = x ∧ ∃ v, GlobalTheory.AdTh.IsFinOf S T γ v := _root_.GlobalTheory.AdForm.LamPre.exists_mat_of_mem_lamC

theorem fixedLine : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a)
    (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ g ∈ GfC S, ∀ h ∈ GfC T,
    ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)),
    Moves S hS g N → Moves T hT h N' → ∀ f, IsThetaFunO ψ S T f →
    IsLatVac (heisO ψ S T) (latO S T (latFr S hS N) (latFr T hT N') fun _ => True) f →
    xiN θ S T hS hT δ sc f ∈ Formalism.L2.Th1.H.fixedBy (HV sc) (alV D.host.d sc)
      (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
  intro D ψ θ S T a b hS hT δ sc hP g hg h hh N N' hN hN' f hf hl x hx z
  obtain ⟨γ, hγ, rfl, v, hv⟩ := lamPre D S T a b hS hT δ N N' x hx
  have hs := latSign D ψ θ S T a b hS hT δ sc hP g hg h hh N N' hN hN' f hf hl γ hγ v hv
  have hu := _root_.GlobalTheory.AdForm.HeisRead.xiN_heisO_finOf D ψ θ S T a b hS hT δ sc hP f hf γ v hv
  rw [← hu]
  simp only [xiN]
  rw [← hs]
  ring

theorem vac_moved : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ f, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (intVec D _) (intVec D _) f → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ N N', Moves S hS g N → Moves T hT h N' → IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (latFr S hS N) (latFr T hT N') (om (g, h) f) ∧ xiN θ S T hS hT δ sc (om (g, h) f) ∈ Formalism.L2.Th1.H.Th (HV sc) (alV D.host.d sc) (LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') ∧ xiN θ S T hS hT δ sc (om (g, h) f) ≠ 0 := by
  intro D ψ θ S T a b hS hT δ sc hP μ om hW f hf g hg h hh N N' hN hN'
  obtain ⟨hstd, hv⟩ := hf
  have hhol : IsHol θ S T ψ f := ⟨hv.theta, hv.fock⟩
  have hI := _root_.GlobalTheory.AdForm.FinComm.finite_comm_creation D ψ θ S T a b hS hT δ sc hP μ om hW g hg h hh f hhol
  have hth' : IsThetaFunO ψ S T (om (g, h) f) := hW.om_pres _ f hv.theta
  have hvac : IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (latFr S hS N) (latFr T hT N') (om (g, h) f) := by
    refine ⟨hstd, { inf := hv.inf, theta := hth', lat := ?_, fock := hI.1.2, norm := ?_ }⟩
    · refine ⟨fun u' hu' => ?_, fun e he u' hu' hhalf => ?_⟩
      · obtain ⟨u, hu, rfl⟩ := latMove D S T a b hS hT hP.gS hP.gT g hg h hh N N' hN hN' u' hu'
        have h2 : actO S T g h u + actO S T g h u = actO S T g h (u + u) := by
          simp only [actO, Matrix.mul_add, Matrix.add_mul]
        have h3 := hv.lat.1 u hu
        rw [two_nsmul] at h3 ⊢
        rw [h2, ← hW.om_heis g h _ f hv.theta, h3]
      · obtain ⟨u, hu, rfl⟩ := latMove D S T a b hS hT hP.gS hP.gT g hg h hh N N' hN hN' u' hu'
        rw [← hW.om_heis g h u f hv.theta, hv.lat.2 e he u hu (halfBack D S T g h e u hhalf)]
    · refine ⟨hv.norm.1, fun p hp => ?_⟩
      show nrm2 p.1 p.2 (om (g, h) f) = 1
      rw [norm_weilRepresentation_thetaFunction_preserved D ψ S T μ om hW f hv.theta (g, h) p.1 p.2 hp]
      exact hv.norm.2 p hp
  have hne : om (g, h) f ≠ 0 := by
    intro h0
    obtain ⟨p, hp⟩ := hvac.2.norm.1
    have h1 := hvac.2.norm.2 p hp
    rw [h0] at h1
    simp [nrm2] at h1
  have hII := _root_.GlobalTheory.AdForm.VacRead.xiN_entire_and_injective D ψ θ S T a b hS hT δ sc hP
  refine ⟨hvac, ⟨GlobalTheory.SCV.analyticOnNhd_of_differentiable (hII.1 _ hI.1) _,
    fixedLine D ψ θ S T a b hS hT δ sc hP g hg h hh N N' hN hN' _ hth' hvac.2.lat⟩, fun h0 => hne (hII.2 _ hth' h0)⟩

end GlobalTheory.MovedVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NatCastNotMemUnderSq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open NumberField IsDedekindDomain Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SplitDegOneChar

theorem absNorm_under {E F : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Algebra (𝓞 F) (𝓞 E)] [Algebra.IsIntegral (𝓞 F) (𝓞 E)]
    (PP : HeightOneSpectrum (𝓞 E)) (p : ℕ) (hp : p.Prime) (hPP : Ideal.absNorm PP.asIdeal = p) :
    Ideal.absNorm (PP.under (𝓞 F)).asIdeal = p := by
  set v := PP.under (𝓞 F) with hvdef
  have hle : v.asIdeal ≤ PP.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) := le_rfl
  haveI := v.isMaximal
  haveI := PP.isMaximal
  letI := Ideal.Quotient.field v.asIdeal
  letI : Algebra (𝓞 F ⧸ v.asIdeal) (𝓞 E ⧸ PP.asIdeal) := Ideal.Quotient.algebraQuotientOfLEComap hle
  have hE : Nat.card (𝓞 E ⧸ PP.asIdeal) = p := by rw [← hPP, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 E ⧸ PP.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hE]; exact hp.ne_zero)
  haveI : Module.Finite (𝓞 F ⧸ v.asIdeal) (𝓞 E ⧸ PP.asIdeal) := Module.Finite.of_finite
  have h := Module.natCard_eq_pow_finrank (K := 𝓞 F ⧸ v.asIdeal) (V := 𝓞 E ⧸ PP.asIdeal)
  rw [hE] at h
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact ((hp.pow_eq_iff).1 h.symm).1

theorem natCast_not_mem_under_sq {E F : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra (𝓞 F) (𝓞 E)] [Algebra.IsIntegral (𝓞 F) (𝓞 E)]
    (PP : HeightOneSpectrum (𝓞 E)) (p : ℕ) (hsq : (p : 𝓞 E) ∉ PP.asIdeal ^ 2) :
    (p : 𝓞 F) ∉ (PP.under (𝓞 F)).asIdeal ^ 2 := by
  intro h
  apply hsq
  have h1 := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) h
  rw [Ideal.map_pow, map_natCast] at h1
  exact Ideal.pow_right_mono (Ideal.map_comap_le) 2 h1

end GlobalTheory.SplitDegOneChar

namespace GlobalTheory.SplitDegOneChar

theorem psiE_sec_pr_eq_exp : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E) (p : ℕ), p.Prime → Ideal.absNorm PP.asIdeal = p → ((p : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ^ 2 → q.v = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → (∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt PP x) → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (x : D.host.E) (b : ℤ), Formalism.L2.Col.IntAt PP (x - (b : D.host.E) / (p : D.host.E)) → psiE ψ (q.sec ((ofSplit q).pr x)) = Complex.exp (2 * Real.pi * Complex.I * b / (p : ℂ)) := by
  intro D k _ _ _ _ q PP p hp hPP hsq hv hint ψ hψ x b hx
  have hpr : ∀ y : D.host.E, (ofSplit q).pr y = q.pr (incA D y) := fun _ => rfl
  set c : D.host.F := (b : D.host.F) / (p : D.host.F) with hcdef
  have hc : algebraMap D.host.F D.host.E c = (b : D.host.E) / (p : D.host.E) := by
    rw [hcdef, map_div₀, map_intCast, map_natCast]
  have hxs : x = (x - (b : D.host.E) / (p : D.host.E)) + algebraMap D.host.F D.host.E c := by
    rw [hc]; ring
  have hadd : ∀ u w : AE D, psiE ψ (u + w) = psiE ψ u * psiE ψ w := by
    intro u w; simp only [GlobalTheory.MixPer.psiE, map_add (f := _), AddChar.map_add_eq_mul]
  rw [hxs, hpr, map_add (f := _), map_add (f := _), map_add (f := _), hadd]

  have hy : q.pr (incA D (x - (b : D.host.E) / (p : D.host.E))) ∈ 𝒪[k] := by
    rw [← hpr]; exact (hint _).2 hx
  have h1 : psiE ψ (q.sec (q.pr (incA D (x - (b : D.host.E) / (p : D.host.E))))) = 1 := by
    rw [GlobalTheory.MixPer.psiE, GlobalTheory.SplitCharCond.trace_sec q, GlobalTheory.SplitCharCond.snd_trace,
      GlobalTheory.SplitCharCond.char_int hψ (GlobalTheory.SplitCharCond.trace_int ((q.int_iff _).1 hy))]
  rw [h1, one_mul]

  obtain ⟨ε, hε, he⟩ := q.above
  have htr : Algebra.trace (AF D.host.F) (AE D) q.e = ε := by
    refine Algebra.TensorProduct.includeLeft_injective (S := AF D.host.F) (algebraMap D.host.F D.host.E).injective ?_
    change algebraMap (AF D.host.F) (AE D) _ = algebraMap (AF D.host.F) (AE D) _
    rw [GlobalTheory.FockCompare.SymplVal.trace_AE, he]
  have hinc : incA D (algebraMap D.host.F D.host.E c) =
      algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) c) := GlobalTheory.SplitCharCond.one_tmul_eq c
  rw [q.sec_pr, hinc, mul_comm, ← Algebra.smul_def, GlobalTheory.MixPer.psiE, map_smul, smul_eq_mul, htr, mul_comm]
  have hnorm : Ideal.absNorm q.v.asIdeal = p := by rw [hv]; exact absNorm_under PP p hp hPP
  have hsqv : (p : 𝓞 D.host.F) ∉ q.v.asIdeal ^ 2 := by rw [hv]; exact natCast_not_mem_under_sq PP p hsq
  have key := GlobalTheory.StdCharDegOne.stdChar_placeIdem_div D ψ hψ p hp q.v hnorm hsqv ε hε (b : 𝓞 D.host.F) b
    (by rw [sub_self]; exact zero_mem _)
  rw [← key, hcdef]
  push_cast
  rfl

end GlobalTheory.SplitDegOneChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OffIdempotentMemIdealTwoIntegers
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OffIdemTwo
open GlobalTheory.IdemSupport GlobalTheory.OffIdemDen

theorem exists_split {K : Type} [Field K] [NumberField K] (c d : 𝓞 K) (hc0 : c ≠ 0) (hd : d ≠ 0) :
    ∃ x y : 𝓞 K, (x : K) / c * c + (y : K) / d * d = 1 ∧
      (∀ Q : HeightOneSpectrum (𝓞 K), ¬ (c ∈ Q.asIdeal ∧ d ∈ Q.asIdeal) →
        ∃ g t : 𝓞 K, g ≠ 0 ∧ g ∉ Q.asIdeal ∧ (x : K) / c = t * (g : K)⁻¹) ∧
      (∀ Q : HeightOneSpectrum (𝓞 K), ¬ (c ∈ Q.asIdeal ∧ d ∈ Q.asIdeal) →
        ∃ g t : 𝓞 K, g ≠ 0 ∧ g ∉ Q.asIdeal ∧ (y : K) / d = t * (g : K)⁻¹) := by
  obtain ⟨G, hG⟩ : ∃ G : Ideal (𝓞 K), G = Ideal.span {c} ⊔ Ideal.span {d} := ⟨_, rfl⟩
  obtain ⟨I', hI'⟩ : G ∣ Ideal.span {c} := Ideal.dvd_iff_le.2 (hG ▸ le_sup_left)
  obtain ⟨D', hD'⟩ : G ∣ Ideal.span {d} := Ideal.dvd_iff_le.2 (hG ▸ le_sup_right)
  have hG0 : G ≠ 0 := by
    intro h
    have : c ∈ G := hG ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
    rw [h, Ideal.zero_eq_bot, Ideal.mem_bot] at this
    exact hc0 this
  have hcop : I' ⊔ D' = ⊤ := by
    apply mul_left_cancel₀ hG0
    rw [Ideal.mul_sup, ← hI', ← hD', Ideal.mul_top, hG]
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 (hcop.symm ▸ Submodule.mem_top : (1 : 𝓞 K) ∈ I' ⊔ D')
  have coe0 : ∀ w : 𝓞 K, w ≠ 0 → (w : K) ≠ 0 := fun w hw => RingOfIntegers.coe_ne_zero_iff.2 hw
  have hint : ∀ (w z : 𝓞 K), w ≠ 0 → (∀ g ∈ G, g * z ∈ Ideal.span {w}) →
      ∀ Q : HeightOneSpectrum (𝓞 K), ¬ (c ∈ Q.asIdeal ∧ d ∈ Q.asIdeal) →
      ∃ g t : 𝓞 K, g ≠ 0 ∧ g ∉ Q.asIdeal ∧ (z : K) / w = t * (g : K)⁻¹ := by
    intro w z hw hz Q hQ
    have hGQ : ¬ G ≤ Q.asIdeal := fun h => hQ
      ⟨h (hG ▸ Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)),
       h (hG ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))⟩
    obtain ⟨g, hg, hgQ⟩ := Set.not_subset.1 hGQ
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (hz g hg)
    have hg0 : g ≠ 0 := fun h => hgQ (h ▸ Q.asIdeal.zero_mem)
    have hgE := coe0 g hg0
    have hwE := coe0 w hw
    have htE : (t : K) * w = g * z := by
      have := congrArg (algebraMap (𝓞 K) K) ht
      rwa [map_mul, map_mul] at this
    refine ⟨g, t, hg0, hgQ, ?_⟩
    field_simp
    linear_combination -htE
  refine ⟨x, y, ?_, hint c x hc0 fun g hg => hI' ▸ Ideal.mul_mem_mul hg hx,
    hint d y hd fun g hg => hD' ▸ Ideal.mul_mem_mul hg hy⟩
  rw [div_mul_cancel₀ _ (coe0 c hc0), div_mul_cancel₀ _ (coe0 d hd)]
  have := congrArg (algebraMap (𝓞 K) K) hxy
  rwa [map_add, map_one] at this

theorem off_comp {D : D7} {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : Comp D Φ) {e : AE D}
    {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e SS) :
    (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS) → Φ (1 - e - cA D e) Q = 0) ∧
    ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Φ (1 - e - cA D e) Q ∈ Q.adicCompletionIntegers D.host.E := by
  obtain ⟨⟨es, hes, rfl⟩, horth⟩ := he
  have hdl : ∀ P ∈ SS, IsDelta Φ P (es P) := fun P hP => delta_of_isIdemAt hΦ (hes P hP)
  have hdc : ∀ P ∈ SS, IsDelta Φ (cP P) (cA D (es P)) := fun P hP => delta_conj hΦ (hdl P hP)
  have hE : ∀ Q, Φ (∑ P ∈ SS, es P) Q = ∑ P ∈ SS, Φ (es P) Q := fun Q => map_sum (evQ Φ Q) _ _
  have hC : ∀ Q, Φ (cA D (∑ P ∈ SS, es P)) Q = ∑ P ∈ SS, Φ (cA D (es P)) Q := fun Q => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; exact map_sum (evQ Φ Q) _ _
  have hO : ∀ Q, Φ (1 - ∑ P ∈ SS, es P - cA D (∑ P ∈ SS, es P)) Q =
      1 - Φ (∑ P ∈ SS, es P) Q - Φ (cA D (∑ P ∈ SS, es P)) Q := fun Q => by
    change evQ Φ Q _ = _
    rw [map_sub, map_sub, map_one]; rfl
  have hprod : ∀ Q, Φ (∑ P ∈ SS, es P) Q * Φ (cA D (∑ P ∈ SS, es P)) Q = 0 := fun Q => by
    rw [← ev_mul, horth, ev_zero]

  have hzero : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), (Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS) →
      Φ (1 - ∑ P ∈ SS, es P - cA D (∑ P ∈ SS, es P)) Q = 0 := by
    intro Q hQQ
    rw [hO]
    rcases hQQ with hQ | hQ
    · have h1 : Φ (∑ P ∈ SS, es P) Q = 1 := by
        rw [hE, Finset.sum_eq_single Q (fun P hP hne => (hdl P hP).2.2 Q (Ne.symm hne))
          (fun h => absurd hQ h), (hdl Q hQ).2.1]
      have h2 := hprod Q
      rw [h1, one_mul] at h2
      rw [h1, h2, sub_self, sub_zero]
    · rw [conjP_eq_cP] at hQ
      have h1 : Φ (cA D (∑ P ∈ SS, es P)) Q = 1 := by
        rw [hC, Finset.sum_eq_single (cP Q) (fun P hP hne => (hdc P hP).2.2 Q (fun h => hne (by
            rw [h, cP_cP])))
          (fun h => absurd hQ h)]
        have := (hdc (cP Q) hQ).2.1
        rwa [cP_cP] at this
      have h2 := hprod Q
      rw [h1, mul_one] at h2
      rw [h1, h2, sub_zero, sub_self]

  have hoint : ∀ Q : HeightOneSpectrum (𝓞 D.host.E),
      Φ (1 - ∑ P ∈ SS, es P - cA D (∑ P ∈ SS, es P)) Q ∈ Q.adicCompletionIntegers D.host.E := by
    intro Q
    rw [hO, hE, hC]
    exact sub_mem (sub_mem (Q.adicCompletionIntegers D.host.E).one_mem
      (sum_mem fun P hP => delta_mem (hdl P hP) Q)) (sum_mem fun P hP => delta_mem (hdc P hP) Q)
  exact ⟨hzero, hoint⟩

theorem term_int {D : D7} {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : Comp D Φ) (o : AE D)
    (hoint : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Φ o Q ∈ Q.adicCompletionIntegers D.host.E) (u : D.host.E)
    (hu : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Φ o Q = 0 ∨ ∃ g t : 𝓞 D.host.E, g ≠ 0 ∧ g ∉ Q.asIdeal ∧
      u = t * (g : D.host.E)⁻¹) : finPart D (o * incA D u) ∈ intAE D := by
  rw [hΦ.int]
  intro Q
  rw [ev_mul, hΦ.inc]
  rcases hu Q with h0 | ⟨g, t, hg0, hgQ, heq⟩
  · rw [h0, zero_mul]
    exact (Q.adicCompletionIntegers D.host.E).zero_mem
  · refine mul_mem (hoint Q) ?_
    have : algebraMap D.host.E (Q.adicCompletion D.host.E) u ∈ Q.adicCompletionIntegers D.host.E := by
      rw [heq, map_mul]
      exact mul_mem (Q.coe_mem_adicCompletionIntegers t) ((inv_mem_iff Q hg0).2 hgQ)
    exact this

theorem off_two : ∀ (D : D7) (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ c : ℕ, 0 < c → ∀ d : 𝓞 D.host.E, d ≠ 0 → (∀ Q : HeightOneSpectrum (𝓞 D.host.E), (c : 𝓞 D.host.E) ∈ Q.asIdeal → d ∈ Q.asIdeal → Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS) → ∃ a₁ a₂ : AE D, finPart D a₁ ∈ intAE D ∧ finPart D a₂ ∈ intAE D ∧ 1 - e - cA D e = a₁ * incA D (c : D.host.E) + a₂ * incA D (d : D.host.E) := by
  intro D e SS he c hc d hd hcd
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨hzero, hoint⟩ := off_comp hΦ he
  generalize 1 - e - cA D e = o at hzero hoint ⊢
  have hc0 : (c : 𝓞 D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  obtain ⟨x, y, hxy, hx, hy⟩ := exists_split (c : 𝓞 D.host.E) d hc0 hd
  have hcast : ((c : 𝓞 D.host.E) : D.host.E) = (c : D.host.E) := map_natCast _ c
  rw [hcast] at hxy hx
  refine ⟨o * incA D ((x : D.host.E) / c), o * incA D ((y : D.host.E) / d),
    term_int hΦ o hoint _ fun Q => ?_, term_int hΦ o hoint _ fun Q => ?_, ?_⟩
  · by_cases h : (c : 𝓞 D.host.E) ∈ Q.asIdeal ∧ d ∈ Q.asIdeal
    · exact Or.inl (hzero Q (hcd Q h.1 h.2))
    · exact Or.inr (hx Q h)
  · by_cases h : (c : 𝓞 D.host.E) ∈ Q.asIdeal ∧ d ∈ Q.asIdeal
    · exact Or.inl (hzero Q (hcd Q h.1 h.2))
    · exact Or.inr (hy Q h)
  · have h1 := congrArg (incA D) hxy
    rw [map_add (f := _), map_mul, map_mul, map_one] at h1
    rw [mul_assoc, mul_assoc, ← mul_add, h1, mul_one]

end GlobalTheory.OffIdemTwo
end
end

