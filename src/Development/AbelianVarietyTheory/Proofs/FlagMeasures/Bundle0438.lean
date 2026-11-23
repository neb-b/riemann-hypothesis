module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Mathlib
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
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantLengthMomentsAmplitudesLargeGap
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0437
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0043
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsAllAlongFamilyGap
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

noncomputable section
open GlobalTheory.Amp

namespace GlobalTheory.GapUAmp

theorem abs_all_along_family_gap : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 A C1 : ℝ, ∃ C thr : ℝ, 0 ≤ C ∧ ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → (∀ Cn : ℝ, OwnEv Fm fun C' Cl x i => Formalism.MainNotions.BridgeLemma.AbsAllParameters (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1 Cn C) ∧ (OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.PrimeSumLogBound (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1) := by
  intro _ hH _ Cg cb Cu cT CT C0 A C1
  obtain ⟨CMo, hMo⟩ := _root_.GlobalTheory.AmpMomentsGap.amplitude_moments_gap hH Cg cb Cu cT CT C0 C1 25
  obtain ⟨C₀, hAbs⟩ := GlobalTheory.Amp.AbsRange.abs_range Cg cb Cu cT CT C0 C1 CMo
  obtain ⟨m₁, hAbs'⟩ := hAbs (max C₀ 0) (le_max_left _ _)
  refine ⟨max C₀ 0, 1000, le_max_right _ _, ?_⟩
  intro eps Fm _ hCl _
  have key : ∀ Cn : ℝ, OwnEv Fm fun C' Cl x i =>
      ABSr (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 (max C₀ 0) := by
    intro Cn
    obtain ⟨m₂, hM⟩ := hMo Cn
    obtain ⟨x0, hx0⟩ := GlobalTheory.family_sizes_eventually_large eps Fm (max (max m₁ m₂) 1)
    refine ⟨x0, fun x hx i => ?_⟩
    obtain ⟨-, hm, -, -, hrd, -⟩ := hx0 x hx i
    have hm1 : (1 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) := le_trans (le_max_right _ _) hm
    have hB : ∀ m₀, m₀ ≤ max (max m₁ m₂) 1 → Big (Fm.D x i) (Fm.L x i) (sCl Fm) m₀ :=
      fun m₀ h => ⟨hrd, by nlinarith, le_trans h hm⟩
    exact hAbs' Cn _ _ _ _ (hB _ (le_trans (le_max_left _ _) (le_max_left _ _)))
      (hM _ _ _ _ hCl (hB _ (le_trans (le_max_right _ _) (le_max_left _ _))))
  refine ⟨fun Cn => (key Cn).mono ?_, (key 0).mono ?_⟩
  · intro C' Cl x i h τ w w' hTT θ hθ W hW lam' hl S hS γ p hp θ' hθ' νR hR hHyp hD
    have h0 : HypZ (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 := by
      unfold Formalism.MainNotions.S.Cnt.Hyp at hHyp; exact hHyp.1
    exact (h h0 τ w w' hTT θ hθ W hW lam' hl S hS γ p hp θ' hθ' νR hR hD).2
  · intro C' Cl x i h τ w w' hTT θ hθ W hW S hS _ γ p hp θ' hθ' νR hR hHyp hD
    have h0 : HypZ (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 := by
      unfold Formalism.MainNotions.S.Cnt.Hyp at hHyp; exact hHyp.1
    exact (h h0 τ w w' hTT θ hθ W hW (lamD _ τ) (by simp [l1dist]) S hS γ p hp θ' hθ' νR hR hD).1

end GlobalTheory.GapUAmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyGenericMassPositiveBoundedProofStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familyGenericMassPositiveBounded_proof : PI.VolStabS.MassDataS.SWXS → GlobalTheory.SnFam.WeightsFam := by
  first | exact @GlobalTheory.WeightsFamPf.weightsFam_of | exact GlobalTheory.WeightsFamPf.weightsFam_of | (intros; apply GlobalTheory.WeightsFamPf.weightsFam_of <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalAmplitudeWittLiftEqQuotientIntegralStatement
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localAmplitude_wittLift_eq_quotientIntegral : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (C : Choice X 1) (hB : WuBessel C) (u u' : D.what₂.Word) (t : D.s.Term u u') (s : TT Y u u'), s.toTerm = tc hI t → D.s.Gterm t ≠ 0 → D.s.relevant t → Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (τ : D.what₂.Tau) (μ ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))), SFinite μ → Formalism.L2.SG.RealObj.IsQuotLoc μ ν → (∃ p, IsRootMeasR D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) p (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) (μ.map (fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) ((s.pt.1 (vOf X τ))⁻¹ * y * (s.pt.1 (vOf X τ))))))) → hsNormSq ((locS hB u u' τ).J (nu1 hI C t τ) (gamR hI C t τ)) = Complex.normSq ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) * hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ)); Formalism.L2.SG.RealObj.Jv ν (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) (s.pt.1 (vOf X τ))) := by
  first | exact @GlobalTheory.AmpLoc.hsNormSq_amp_loc | exact GlobalTheory.AmpLoc.hsNormSq_amp_loc | (intros; apply GlobalTheory.AmpLoc.hsNormSq_amp_loc <;> assumption)
end

