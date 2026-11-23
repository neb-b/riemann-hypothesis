module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0401
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0400
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0076
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0012
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0005
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UniformBesselConstant
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselSettingUniformConstantStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.HaarEqSmul
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0062
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0037
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselTorusElementProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0336
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusNormaliserBessel
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0395
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRoot
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0118
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0050
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentEqLatticeUnipotentCoords
section
noncomputable section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom GlobalTheory.CovDomGrp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovDomGrp

theorem nO_eq_nLam_coords : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (u : D.what₂.Word), (∀ γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E, (GlobalTheory.SgAlg.InN (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) γ ∧ GlobalTheory.SgGlob.latMap γ (Lc X) = Lc X) → ∃ s ∈ NOinf X u, ∀ w, Ac X C w * γ.map w.embedding * (Ac X C w)⁻¹ = Matrix.of (Gm D (trX X C s) w)) ∧ (∀ s ∈ NOinf X u, ∃ γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E, (GlobalTheory.SgAlg.InN (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) γ ∧ GlobalTheory.SgGlob.latMap γ (Lc X) = Lc X) ∧ ∀ w, Ac X C w * γ.map w.embedding * (Ac X C w)⁻¹ = Matrix.of (Gm D (trX X C s) w)) := by
  intro D X θ C u
  have key : ∀ (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (γ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) D.host.E), (∀ y, crdH X (n y) = γ *ᵥ crdH X y) →
      ((GlobalTheory.SgAlg.InN (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) γ ∧ GlobalTheory.SgGlob.latMap γ (Lc X) = Lc X) ↔
        n ∈ Formalism.MainNotions.S.Lat.NLam (VS D).L0 (lf D (X.Fu u))) := by
    intro n γ hγ
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨⟨(GlobalTheory.T.isHermitianIsometryMatrix_iff_mem_isometries X n γ hγ).1 h1, (_root_.GlobalTheory.CovDomGrp.latMap_Lc_iff X n γ hγ).1 h4⟩, (_root_.GlobalTheory.CovDomGrp.flag_iff X u n γ hγ).1 h2,
        (_root_.GlobalTheory.CovDomGrp.orth_cond_iff_coord X u n γ hγ).1 h3⟩
    · rintro ⟨⟨h1, h4⟩, h2, h3⟩
      exact ⟨⟨(GlobalTheory.T.isHermitianIsometryMatrix_iff_mem_isometries X n γ hγ).2 h1, (_root_.GlobalTheory.CovDomGrp.flag_iff X u n γ hγ).2 h2, (_root_.GlobalTheory.CovDomGrp.orth_cond_iff_coord X u n γ hγ).2 h3⟩,
        (_root_.GlobalTheory.CovDomGrp.latMap_Lc_iff X n γ hγ).2 h4⟩
  refine ⟨fun γ hγ => ?_, fun s hs => ?_⟩
  · obtain ⟨n, hn⟩ := exists_equiv X γ hγ.1.1
    have hnL := (key n γ hn).1 hγ
    obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X n hnL.1.1
    exact ⟨x.1, (Formalism.L2.SG.Pf.NcReal.JX.NOf.noratC_holds X u x.1).2 ⟨x, n, hx, rfl, hnL⟩,
      _root_.GlobalTheory.CovDomGrp.Transp.transp X C x.1 γ (_root_.GlobalTheory.CovDomGrp.coordMat_place X n γ hx hn)⟩
  · obtain ⟨x, n, hx, rfl, hnL⟩ := (Formalism.L2.SG.Pf.NcReal.JX.NOf.noratC_holds X u s).1 hs
    obtain ⟨γ, hγ⟩ := exists_mat X n
    exact ⟨γ, (key n γ hγ).2 hnL, _root_.GlobalTheory.CovDomGrp.Transp.transp X C x.1 γ (_root_.GlobalTheory.CovDomGrp.coordMat_place X n γ hx hγ)⟩

end GlobalTheory.CovDomGrp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.KFiniteCoefAndTorusTranslateIsBesselCoefLargeGap
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

noncomputable section

namespace GlobalTheory.AmpTKGap

theorem isCoef_kfin_and_torus_translate : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq) (κ τ : ℝ), 0 < κ → 0 < τ → ∀ f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp), Formalism.MainNotions.S.IsKFinCoefH L.σ f → (∃ s : ℂ, BranchingSupport.IsCoef (GlobalTheory.AmpTK.rep L) l l' f s) ∧ ∃ s : ℂ, BranchingSupport.IsCoef (GlobalTheory.AmpTK.rep L) l l' (fun x => f (Formalism.MainNotions.FrameBoundFromBesselTorus.cj k r κ τ x)) s := by
  intro H k r L l l' κ τ hκ hτ f hf
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  have hDS : (GlobalTheory.AmpTK.rep L).IsDS L.ε L.lam := ⟨L.hlam, hσ⟩
  have hmain := (GlobalTheory.isCoef_of_translate_smul_exists H.1.1.2.2.1 k r L.ε L.lam (GlobalTheory.AmpTK.rep L) L.Wp L.Wq l l' hDS).1
  have hd := Formalism.MainNotions.FrameBoundFromBesselTorus.dM_mem_UH (k := k) (r := r) hκ hτ
  have hdi := Formalism.MainNotions.FrameBoundFromBesselTorus.dMi_mem_UH (k := k) (r := r) hκ hτ
  have h1 : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) ∈ BranchingSupport.GG k r := by
    have := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hd hdi
    rwa [Formalism.MainNotions.FrameBoundFromBesselTorus.dM_mul_dMi hκ hτ] at this
  obtain ⟨P, Q, hQ, hP, h⟩ := hf
  refine ⟨hmain f ⟨1, h1, 1, h1, P, Q, hQ, hP, fun g => ?_⟩, hmain _ ⟨_, hd, _, hdi, P, Q, hQ, hP, fun g => ?_⟩⟩
  · exact (congrArg f (by simp : (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) * g * 1 = g)).trans (h g)
  · exact (congrArg f (Formalism.MainNotions.FrameBoundFromBesselTorus.cj_cjI hκ hτ g)).trans (h g)

end GlobalTheory.AmpTKGap

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralAmplitudeNormSqBigCellGap
section
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.AmpNormGap

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P GlobalTheory.AmpNorm

theorem lintegral_hsNormSq_amp_gap : GlobalTheory.GapIn.Hyp → GlobalTheory.GapIn.AmpKF0 → CellConv → ∀ (k r : ℕ) (L : LocBessel k r) (μG : Measure (Mt k r)) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), 2 ≤ k → L.c ≠ 0 → L.κN ≠ 0 → L.κN ≠ ⊤ → IsHaarOn (UH (Hpk k r)) μG → IsSection k r L.z L.z' μsec → ∃ c : ℝ, 0 < c ∧ ∀ (R : Rep k r) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (l : R.H → L.Wp) (l' : R.H → L.Wq) (w : R.H), haveI := FiniteDimensional.complete ℂ L.Wp; haveI := FiniteDimensional.complete ℂ L.Wq; R.IsDS L.ε mu → GapAtLeast L.ε mu h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h → GapCell k r h → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π R.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' R.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∃ v, R.KFin v ∧ l v ≠ 0) → (∃ v, R.KFin v ∧ l' v ≠ 0) → PI.UpqRep.IsLowUnitH k r L.ε mu R.σ w → ∫⁻ q : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r (Tz k r L.z) (Tz k r L.z') q * hsNormSq (amp R l l' w μG (bigCell k r q.1 (μsec q.2)))) = ENNReal.ofReal (c / PI.BesselPeriodGGP.fdegH μG R.σ w ^ 3) := by
  intro hH hAmp hConv k r L μG μsec hk hc hκ0 hκt hG hsec
  have := FiniteDimensional.complete ℂ L.Wp
  have := FiniteDimensional.complete ℂ L.Wq
  have hK : PI.KFinSmooth := hH.1.1.2.2.1
  have hk1 : 1 ≤ k := by omega
  have hstd : cStd ≠ 0 := by simp [cStd]
  have hα : cStd / L.c ≠ 0 := div_ne_zero hstd hc
  have hcα : L.c * (cStd / L.c) = cStd := mul_div_cancel₀ _ hc
  set α := cStd / L.c
  obtain ⟨ha, hT, -, hcell⟩ := ThA.TorusElt.torusElt k r α hα
  have hn : 0 < ‖α‖ := norm_pos_iff.2 hα
  have hGB := (HaarNotions.isHaarOn_iff_groups k r μG).1.1 hG
  have hNB : B.IsHaarOn (Nset k r) L.μN := (HaarNotions.isHaarOn_iff_groups k r L.μN).2.1.1
    (_root_.GlobalTheory.haarLie_isHaarOn_Nset k r L.κN (pos_iff_ne_zero.2 hκ0) hκt.lt_top)
  have hW := ((HaarNotions.isHaarOn_iff_groups k r L.μW).2.2 L.z L.hz.1 L.hz.2 hk1).1 L.hμW.1
  have hW' := ((HaarNotions.isHaarOn_iff_groups k r L.μW').2.2 L.z' L.hz'.1 L.hz'.2 hk1).1 L.hμW'.1
  have hδ : 0 < ‖α‖ ^ B.kap k r := by positivity
  have hN₁ : B.IsHaarOn (Nset k r) (ENNReal.ofReal (‖α‖ ^ B.kap k r) • L.μN) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [Measure.smul_apply, hNB.conc, smul_zero]
    · intro a ha; rw [Measure.map_smul, hNB.left a ha]
      exact (show Continuous (lmulM a) from by unfold lmulM; exact continuous_const.matrix_mul continuous_id).measurable.aemeasurable
    · intro a ha; rw [Measure.map_smul, hNB.right a ha]
      exact (show Continuous (B.rmulF a) from by unfold B.rmulF; exact continuous_id.matrix_mul continuous_const).measurable.aemeasurable
    · intro K hK
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hNB.finite_compact K hK)
    · intro h0
      apply hNB.ne_zero
      have h1 := Measure.measure_univ_eq_zero.2 h0
      rw [Measure.smul_apply, smul_eq_mul] at h1
      exact Measure.measure_univ_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left (ENNReal.ofReal_pos.2 hδ).ne')
  set μ₁ := ENNReal.ofReal (‖α‖ ^ B.kap k r) • L.μN with hμ₁
  have hmap : μ₁.map (conjM (ThA.aT k r α)) = L.μN := by
    rw [ThA.TorusJac.haar_map_conj _ hN₁ α hα, hμ₁, smul_smul, ← ENNReal.ofReal_mul (by positivity),
      inv_mul_cancel₀ hδ.ne', ENNReal.ofReal_one, one_smul]
  set a := ThA.aT k r α
  have hu := WeylGroupFacts.isUnit_of_uh ha
  have hai := WeylGroupFacts.uh_inv ha
  have hp : ∀ z, inWb k r z → ∀ n ∈ Nset k r, psi k r z L.c (a * n * a⁻¹) = psi k r z cStd n := by
    intro z hz n hn
    unfold psi
    rw [((hT z hz).2 n hn).2.2, ← mul_assoc L.c, hcα]
  obtain ⟨u, hw⟩ := CapelliOfHC.exists_isType k r L.Wp L.z L.π L.u L.hz.1 L.hz.2 L.hπ
  obtain ⟨u', hw'⟩ := CapelliOfHC.exists_isType k r L.Wq L.z' L.π' L.u' L.hz'.1 L.hz'.2 L.hπ'
  obtain ⟨χ, hχ1, hχ2, hχ3⟩ := character_exists_alt
  let D : B.RealPlaceData k r L.Wp L.Wq :=
    ⟨L.z, L.z', L.π, L.π', μG, L.μW, μ₁, L.μW', μsec, χ, hk1, L.hz.1, L.hz'.1, L.hz.2, L.hz'.2,
      hw.2.1, hw'.2.1, hw.2.2.2.1, hw'.2.2.2.1, hw.2.2.1, hw'.2.2.1, hGB, hW, hN₁, hW', hsec, hχ1, hχ2, hχ3⟩
  obtain ⟨ν₁, ν₁', hS, hS'⟩ := exists_sideG_both_of_isType k r L.Wp L.Wq D u u' hw hw'
  obtain ⟨c₀, hc₀, hP⟩ := Gp91.GlobalTheory.T.bessel_setting_uniform_constant hH.1 k r L.Wp L.Wq D
  obtain ⟨c₁, -, hdeg⟩ := Gp91.GlobalTheory.BesselDegree.schur_fdeg hH.1 k r L.ε μG hG
  refine ⟨((‖α‖ ^ 2) ^ B.kap k r)⁻¹ * c₀, by positivity, ?_⟩
  intro R mu h l l' w hR hgap hok hgc hl hl' ⟨v, hv, hv0⟩ ⟨v', hv', hv0'⟩ hlow
  have hRG : R.IsDG L.ε mu := ⟨hR.1, hR.2, ⟨h, hgap, hok⟩⟩
  obtain ⟨hmul, h1, hun, hsm, hTK, hTT, hKT, -⟩ := GlobalTheory.rep_basic_of_isDS hK k r L.ε mu R hR
  have hwK : R.KFin w := PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hlow
  have hw0 : w ≠ 0 := by
    obtain ⟨P, -, hn1, -⟩ := hlow
    intro h0
    simp [h0] at hn1
  have hDD : ∀ x ∈ ThreeDimData.DDsp R.σ w, x ∈ R.TK := fun x hx =>
    (Submodule.span_le.2 (by rintro _ ⟨g, hg, rfl⟩; exact hTT g hg w (hKT w hwK)) : ThreeDimData.DDsp R.σ w ≤ R.TK) hx
  set d := PI.BesselPeriodGGP.fdegH μG R.σ w with hd
  have hdd : ∀ x, x ≠ 0 → PI.BesselPeriodGGP.fdegH μG R.σ x = d := fun x hx => by
    rw [hd, (hdeg mu R hRG).1 x hx, (hdeg mu R hRG).1 w hw0]
  have hd0 : 0 ≤ d := div_nonneg (by positivity) (integral_nonneg fun _ => by positivity)
  obtain ⟨l₁, hl₁⟩ := Gp91.CompanionTheory.FamilyDerivativeExpansion.BeL.exists_normalised_bessel_map hH.1 k r L.ε mu h R L.Wp _ _ _ _ _ _ _ hRG hgap hok hS
  obtain ⟨l₁', hl₁'⟩ := Gp91.CompanionTheory.FamilyDerivativeExpansion.BeL.exists_normalised_bessel_map hH.1 k r L.ε mu h R L.Wq _ _ _ _ _ _ _ hRG hgap hok hS'
  have hy := hTT _ hai _ (hKT v hv)
  have hy' := hTT _ hai _ (hKT v' hv')
  have e₁ : ‖⟪l₁ (R.σ a⁻¹ v), l v⟫_ℂ‖ = ‖⟪l v, l v⟫_ℂ‖ := by
    refine norm_inner_of_rankOne ?_
    rw [← (hl₁.2 _ (hTK _ hy) _ hy).2, ← hl v (hTK _ (hKT v hv)) v (hKT v hv), ← hmap]
    exact (be_conj R hmul h1 hun L.π hW hN₁ ha (hT _ L.hz.1).1 (hp _ L.hz.1) v v).symm
  have e₂ : ‖⟪l₁' (R.σ a⁻¹ v'), l' v'⟫_ℂ‖ = ‖⟪l' v', l' v'⟫_ℂ‖ := by
    refine norm_inner_of_rankOne ?_
    rw [← (hl₁'.2 _ (hTK _ hy') _ hy').2, ← hl' v' (hTK _ (hKT v' hv')) v' (hKT v' hv'), ← hmap]
    exact (be_conj R hmul h1 hun L.π' hW' hN₁ ha (hT _ L.hz'.1).1 (hp _ L.hz'.1) v' v').symm
  let LR : LocBessel k r :=
    { L with lam := mu, hlam := hR.1, Hs := R.H, hsN := R.nacg, hsI := R.ips, hsC := R.cs, σ := R.σ, hσ := hR.2 }
  have hone : OnePlaceKF LR h μG w l l' :=
    ⟨⟨hgap, hok, hc, hlow, hG, fun x hx y hy => hl x (hTK _ (hDD x hx)) y (hDD y hy),
      fun x hx y hy => hl' x (hTK _ (hDD x hx)) y (hDD y hy)⟩,
      fun x hx y hy => hl x (hTK _ (hDD x hx)) y (hKT y hy), fun x hx y hy => hl' x (hTK _ (hDD x hx)) y (hKT y hy)⟩
  let F : B.Mat k r → (L.Wq →L[ℂ] L.Wp) := fun x => coefF LR v v' (l v) (l' v') (a * x * a⁻¹)
  have hF : IsCoef R l₁ l₁' F (⟪l' v', l₁' (R.σ a⁻¹ v')⟫_ℂ * ⟪l₁ (R.σ a⁻¹ v), l v⟫_ℂ) := by
    refine ⟨1, fun _ => R.σ a⁻¹ v, fun _ => R.σ a⁻¹ v', fun _ => (innerSL ℂ (l' v')).smulRight (l v),
      fun _ => ⟨hy, hy'⟩, fun g hg => ?_, ?_⟩
    · rw [Fin.sum_univ_one, ← hun a ha (R.σ a⁻¹ v), ← hmul _ ha _ hai, Matrix.mul_nonsing_inv _ hu, h1,
        ← hmul _ hg _ hai, ← hmul _ ha _ (WeylGroupFacts.uh_mul hg hai), ← Matrix.mul_assoc]
      ext x
      show ⟪l' v', x⟫_ℂ • ⟪v, R.σ (a * g * a⁻¹) v'⟫_ℂ • l v = ⟪v, R.σ (a * g * a⁻¹) v'⟫_ℂ • ⟪l' v', x⟫_ℂ • l v
      exact smul_comm _ _ _
    · rw [Fin.sum_univ_one, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_right]
  have hnorm := hP L.ε mu h R l₁ l₁' d hRG hgap hok hl₁ hl₁' hdd F _ hF
  set S : ℂ := ⟪l v, l v⟫_ℂ * ⟪l' v', l' v'⟫_ℂ with hSdef
  have hS0 : 0 < ‖S‖ := norm_pos_iff.2 (mul_ne_zero (inner_self_ne_zero.2 hv0) (inner_self_ne_zero.2 hv0'))
  rw [norm_mul, norm_inner_symm, e₁, e₂, mul_comm ‖_‖, ← norm_mul, ← hSdef] at hnorm
  have := B7.sf hW
  have := B7.sf hW'
  have := B7.sf hN₁
  have hpt : ∀ q ∈ B7.Q0 D, hsNormSq (amp R l l' w μG (bigCell k r q.1 (μsec q.2))) =
      (d⁻¹ / ‖S‖) ^ 2 * ‖B.hsVec (B.JF D F (B.gq D (B7.d_S r (‖α‖ ^ 2) q)))‖ ^ 2 := by
    intro q hq
    have hcd := cellData_bigCell LR μG D rfl rfl hq
    obtain ⟨b, hb0, hb1, hb2⟩ := hConv k r LR h μG _ _ _ _ hκt hok hgc hcd hcd.2.2.1
    have hA : S • amp R l l' w μG (bigCell k r q.1 (μsec q.2)) = (d : ℂ)⁻¹ •
        besselJ k r L.z L.z' L.c L.π L.π' L.μW L.μN L.μW' (coefF LR v v' (l v) (l' v'))
          (bigCell k r q.1 (μsec q.2)) :=
      hAmp k r LR h μG w l l' hone _ _ _ _ hcd b hb0 hb1 hb2 v v' hv hv' (l v) (l' v')
    rw [← hmap, ThA.besselJ_conj k r L.z L.z' L.c cStd L.π L.π' L.μW μ₁ L.μW' hW.conc hN₁.conc hW'.conc a hu
      (hT _ L.hz.1).1 (hT _ L.hz'.1).1 (hp _ L.hz.1) (hp _ L.hz'.1), hcell] at hA
    have h2 := congrArg hsNormSq hA
    rw [GlobalTheory.AmpNorm.hsNormSq_smul, GlobalTheory.AmpNorm.hsNormSq_smul, GlobalTheory.AmpNorm.hsNormSq_eq (besselJ _ _ _ _ _ _ _ _ _ _ _ _), norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hd0] at h2
    have e : B.gq D (B7.d_S r (‖α‖ ^ 2) q) =
        bigCell k r (fun i => ((‖α‖ ^ (2 * (r - i.val)) : ℝ) : ℂ) * q.1 i) (μsec q.2) := by
      simp only [pow_mul]
      rfl
    rw [e, div_pow, div_mul_eq_mul_div, eq_div_iff (by positivity), mul_comm]
    exact h2
  rw [lintegral_congr_ae (g := fun q : (Fin r → ℂ) × ℂ => ENNReal.ofReal ((d⁻¹ / ‖S‖) ^ 2) *
      ENNReal.ofReal (bcWeight k r (Tz k r L.z) (Tz k r L.z') q *
        (fun q => ‖B.hsVec (B.JF D F (B.gq D q))‖ ^ 2) (B7.d_S r (‖α‖ ^ 2) q))),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_weight_scale (Tz k r L.z) (Tz k r L.z') (‖α‖ ^ 2) (by positivity)
      (fun q => ‖B.hsVec (B.JF D F (B.gq D q))‖ ^ 2)]
  · refine (congrArg (fun t => _ * (_ * t)) hnorm).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rcases hd0.eq_or_lt with h0 | h0
    · simp [← h0]
    · field_simp
  · filter_upwards [B7.ae_mem_good_set_or_weight_zero D] with q hQ
    rw [← ENNReal.ofReal_mul (by positivity)]
    rcases hQ with hQ | hQ
    · rw [hpt q hQ, mul_left_comm]
    · have hQ' : bcWeight k r (Tz k r L.z) (Tz k r L.z') q = 0 := hQ
      simp only [hQ', zero_mul, mul_zero]

end GlobalTheory.AmpNormGap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedBesselMapsAnyScalePieriConstants
section
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselMoveGap

open GlobalTheory.BesselMove

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem bessel_move_gap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (c : ℂ) (μW μN μG νq : Measure (Mt k r)) (t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), t ∈ GG k r → (∀ n, n ∈ Nset k r ↔ t * n * t⁻¹ ∈ Nset k r) → (∀ h ∈ UWset k r z, t * h = h * t) → (∀ n ∈ Nset k r, psi k r z cStd n = psi k r z c (t * n * t⁻¹)) → SideG k r z π u μW μN μG νq → SideG k r z π u μW (μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) μG (νq.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) ∧ ∀ (R : Rep k r), Formalism.MainNotions.S.IsURepOn (GG k r) R.σ → (∀ B : R.H → Wp, PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π B ↔ IsBes R z π (fun v => B (R.σ t v))) ∧ ∀ l₁ : R.H → Wp, IsBeL R z π μW (μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) l₁ → ∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be z c π R.σ μW μN x v = (innerSL ℂ (l₁ (R.σ t⁻¹ v))).smulRight (l₁ (R.σ t⁻¹ x)) := by
  intro _ k r Wp _ _ _ _ z π u c μW μN μG νq t ht hN hc hψ hS
  obtain ⟨s1, s2, s3, s4, hW, hμN, hG, hq⟩ := hS
  have hti : t⁻¹⁻¹ = t := Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (unit_of ht))
  have hcan : ∀ n : MM k r, t * (t⁻¹ * n * t) * t⁻¹ = n := fun n => by
    simp only [Matrix.mul_assoc, mul_inv' ht, Matrix.mul_one, mic ht]
  have hN' : ∀ n ∈ Nset k r, t⁻¹ * n * t ∈ Nset k r := fun n hn => by
    rw [hN, hcan]; exact hn
  have hc' : ∀ h ∈ UWset k r z, t⁻¹ * h = h * t⁻¹ := fun h hh => by
    calc t⁻¹ * h = t⁻¹ * (h * t) * t⁻¹ := by simp only [Matrix.mul_assoc, mul_inv' ht, Matrix.mul_one]
      _ = h * t⁻¹ := by rw [← hc h hh, imc ht]
  refine ⟨⟨s1, s2, s3, s4, hW, haar_conj ht hN hμN, hG, ?_⟩, fun R hR => ⟨fun B => ⟨fun hB => ?_, fun hB => ?_⟩, ?_⟩⟩
  · have := quot_conj ht hG hq
    rw [← muS_conj ht hW hμN hc] at this
    exact this
  · exact bessel_transport hR ht (fun n hn => (hN n).mp hn) hc hψ hB
  · have h := bessel_transport (ψ' := psi k r z c) hR (inv_mem ht) (fun n hn => by rw [hti]; exact hN' n hn) hc'
      (fun n hn => by rw [hti, hψ _ (hN' n hn), hcan]) hB
    have e : (fun v => B (R.σ t (R.σ t⁻¹ v))) = B := by
      funext v
      rw [← sig_mul hR ht (inv_mem ht), mul_inv' ht, sig_one hR]
    rw [e] at h
    exact h
  · intro l₁ hl x hx v hv
    haveI := hW.1
    haveI := hμN.1
    rw [← (hl.2 _ (sig_sm hR (inv_mem ht) hx) _ (sig_TK hR (inv_mem ht) hv)).2]
    show _ = Formalism.FourierDecayAlt.ThreeDimData.be z cStd π R.σ μW (μN.map (conjE ht)) _ _
    unfold Formalism.FourierDecayAlt.ThreeDimData.be
    rw [prod_conj ht, integral_map_equiv]
    refine integral_congr_ae ?_
    filter_upwards [ae_prod hW hμN] with p hp
    show (⟪v, R.σ (Matrix.of p.1 * Matrix.of p.2) x⟫_ℂ * star (psi k r z c (Matrix.of p.2))) • π (Matrix.of p.1)⁻¹ =
      (⟪R.σ t⁻¹ v, R.σ (Matrix.of p.1 * (t⁻¹ * Matrix.of p.2 * t)) (R.σ t⁻¹ x)⟫_ℂ *
        star (psi k r z cStd (t⁻¹ * Matrix.of p.2 * t))) • π (Matrix.of p.1)⁻¹
    rw [hψ _ (hN' _ hp.2), hcan, ← sig_inner hR (inv_mem ht) v,
      ← sig_mul hR (inv_mem ht) (mul_mem' hp.1.1 hp.2.1),
      ← sig_mul hR (mul_mem' hp.1.1 (hN' _ hp.2).1) (inv_mem ht)]
    have e : Matrix.of p.1 * (t⁻¹ * Matrix.of p.2 * t) * t⁻¹ = t⁻¹ * (Matrix.of p.1 * Matrix.of p.2) := by
      simp only [Matrix.mul_assoc, mul_inv' ht, Matrix.mul_one]
      rw [← Matrix.mul_assoc, ← hc' _ hp.1, Matrix.mul_assoc]
    rw [e]

end GlobalTheory.BesselMoveGap

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalBesselFrameRealPlaceLinearIndependent
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

namespace GlobalTheory.RationalFrame

open NumberField Formalism.L2.SG.PoincareInHH

theorem hJ_lin {n : ℕ} (ε : Fin n → Bool) {ι : Type*} [Fintype ι] (x : Fin n → ℂ) (g : ι → ℂ)
    (y : ι → Fin n → ℂ) (c : ℂ) (w : Fin n → ℂ) :
    hJ ε x (∑ i, g i • y i + c • w) = ∑ i, g i * hJ ε x (y i) + c * hJ ε x w := by
  unfold hJ
  simp only [mulVec_add, mulVec_sum, mulVec_smul, dotProduct_add, dotProduct_sum, dotProduct_smul, smul_eq_mul]

theorem frame_linearIndependent (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    LinearIndependent ℂ (Formalism.L2.SG.RealObj.frm X u 1 v) := by
  have hfr : Formalism.L2.SG.RealObj.frm X u 1 v = Formalism.L2.SG.RealObj.fam (fun a => rv X.B.I v (X.eR a))
      (rv X.B.I v (X.zR u)) := by
    funext a
    simp [Formalism.L2.SG.RealObj.frm, Formalism.L2.SG.RealObj.famSc]
  have hze : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.eR a)) = 0 := by
    intro a
    refine (Cut.hJ_crd X v _ _).trans ?_
    have h := (VS D).herm.eq (X.eX a) (X.zu u)
    rw [(X.zu_orth u a).1] at h
    rw [← h]
    simp
  have hzz : hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u)) ≠ 0 := by
    rw [HidaSetting.zR, Cut.hJ_crd X v, X.zu_norm]
    simp only [map_neg, map_natCast, neg_ne_zero, Nat.cast_ne_zero]
    exact ((D.mem u).A.T_prime).ne_zero
  have hfe : ∀ j a, hJ (X.B.I.ε v) (rv X.B.I v (X.fR j)) (rv X.B.I v (X.eR a)) = if a = j then 1 else 0 := by
    intro j a
    refine (Cut.hJ_crd X v _ _).trans ?_
    rw [Cut.hT_f_e X]
    split_ifs <;> simp
  have hfz : ∀ j, hJ (X.B.I.ε v) (rv X.B.I v (X.fR j)) (rv X.B.I v (X.zR u)) = 0 := by
    intro j
    refine (Cut.hJ_crd X v _ _).trans ?_
    rw [(X.zu_orth u j).2]
    simp
  rw [hfr, Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_castSucc] at hg
  simp only [Formalism.L2.SG.RealObj.fam, Fin.snoc_castSucc, Fin.snoc_last] at hg
  have hlast : g (Fin.last _) = 0 := by
    have h := congrArg (hJ (X.B.I.ε v) (rv X.B.I v (X.zR u))) hg
    rw [hJ_lin] at h
    simp only [hze, mul_zero, Finset.sum_const_zero, zero_add] at h
    unfold hJ at h
    simp only [mulVec_zero, dotProduct_zero] at h
    exact (mul_eq_zero.1 h).resolve_right hzz
  intro i
  refine Fin.lastCases hlast (fun j => ?_) i
  have h := congrArg (hJ (X.B.I.ε v) (rv X.B.I v (X.fR j))) hg
  rw [hJ_lin, hfz] at h
  simp only [hfe, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, add_zero] at h
  unfold hJ at h
  simp only [mulVec_zero, dotProduct_zero] at h
  exact h

end GlobalTheory.RationalFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalFrameGramEmbedEqRealFrameGram
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

namespace GlobalTheory.ZhatRat

theorem mapFlag_fvec {D : D7} {r : ℕ} {T : D.host.E} (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (h : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (F : FlagG (VS D) r T) (b : Fin (r + 1)) :
    (Formalism.L2.SG.TermOp.mapFlag γ h F).fvec b = γ (F.fvec b) := by
  refine Fin.lastCases ?_ (fun b' => ?_) b
  · simp only [FlagG.fvec, Fin.snoc_last, Formalism.L2.SG.TermOp.mapFlag]
  · simp only [FlagG.fvec, Fin.snoc_castSucc, Formalism.L2.SG.TermOp.mapFlag]

theorem frm_one {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (v : NumberField.InfinitePlace X.B.I.F)
    (a : Fin (D.R.rS + 1)) :
    Formalism.L2.SG.RealObj.frm X u 1 v a = rv X.B.I v (X.crd ((X.Fu u).fvec a)) := by
  unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc Formalism.L2.SG.RealObj.fam
  rw [Complex.ofReal_one, one_pow, inv_one, one_smul]
  refine Fin.lastCases ?_ (fun a' => ?_) a
  · rw [Fin.snoc_last, FlagG.fvec, Fin.snoc_last, X.flagZVector u]
    rfl
  · rw [Fin.snoc_castSucc, FlagG.fvec, Fin.snoc_castSucc, X.Fu_e u]
    rfl

end GlobalTheory.ZhatRat


open GlobalTheory.ZhatRat in
theorem GlobalTheory.zhatRat_embed : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (W : WittDat X) (u u' : D.what₂.Word) (s : TT Y u u') (τ : D.what₂.Tau), (ZhatL (lf D (FlagOfWord W u)) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame)).map (embS D τ) = Formalism.L2.SG.RealObj.ZX X u u' 1 s.pt.1 (X.pl.symm τ) := by
  intro D X Y W u u' s τ
  obtain ⟨M, _, hM1, _, hM3⟩ := s.rep.2.1
  have hiso : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1
  rw [← mapL_lf W u]
  refine (congrArg (fun Z => Matrix.map Z (embS D τ)) (zhatL_mapL (W.δ u) (W.isom u) (lf D (X.Fu u)) s.frame)).trans ?_
  ext a b
  simp only [Matrix.map_apply]
  have hM1' : ∀ v, uMat (s.pt.1 v) = (X.B.I.P v)⁻¹ * (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map ⇑(X.B.I.φ v) * X.B.I.P v := hM1
  have hM3' : ∀ y, X.crd (s.lin y) = (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y := hM3
  have hL : (s.frame).fl.fvec b = s.lin ((X.Fu u').fvec b) := by
    unfold Formalism.L2.SG.TermOp.GTerm.frame Formalism.L2.SG.TermOp.mapLF
    rw [dite_eq_left hiso]
    exact mapFlag_fvec _ hiso _ _
  change embS D τ (brS (VS D) (s.frame.fl.fvec b) ((X.Fu u).fvec a)) = _
  rw [hL]
  unfold brS Formalism.L2.SG.RealObj.ZX Formalism.L2.SG.RealObj.Zhat
  rw [frm_one, frm_one, hM1', Formalism.L2.SG.Pf.Level.rv_mulVec, ← hM3', Formalism.L2.SG.Pf.Level.hJ_rv, X.φ_eq,
    X.pl.apply_symm_apply, Formalism.L2.SG.PoincareInHH.Cut.hform_crd]
end

