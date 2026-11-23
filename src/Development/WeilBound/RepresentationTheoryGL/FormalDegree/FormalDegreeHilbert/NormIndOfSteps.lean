module

public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.MomentRecursion.MomStep
public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.PositiveDefiniteConjugates.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.PositiveDefiniteConjugates.PhiCont
public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.OperatorNormSigns.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.DegreeGapNorms.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.DegreeGapNorms.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.KTypeRanges.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.KTypeRanges.KmapZero
public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.FormalDegreeFormula.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.InConeRefl
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0016
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle0005
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KTypesAboveOfDsClass
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DiscreteSeriesSU.GapInv
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0177
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0281
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.HcFormalDegreeOfDiscreteSeriesFormalDegree
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0279
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0276
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0424

@[expose] public section

noncomputable section

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS PositivityTheory.RgDs

theorem hsInt : HsInt := GlobalTheory.CompanionTheory.RgFd.hsInt GlobalTheory.CompanionTheory.HsPsProof.hsPs hsPol phiMul phiCont

theorem psiNorm_of (hI : NormInd) : PsiNorm := by
  intro n ε lam hl
  by_cases h : S7.q0 ε = 0
  · exact normDef n ε h lam hl
  · have h1 : 1 ≤ min (pOf ε) (qOf ε) := Nat.one_le_iff_ne_zero.2 h
    exact hI n ε (h1.trans (min_le_left _ _)) (h1.trans (min_le_right _ _)) lam hl

theorem modelDS_of (hL : ExplicitFunctionSquareIntegrable) (hK : Key) (hH : Hilb) : ModelDS := by
  intro n ε lam T μ hl hμ
  have hP : IsPsiFor ε lam T (S7.PsiM T μ) :=
    ⟨fun k₁ k₂ g hg => S7.psiM_equiv T μ k₁ k₂ hg, S7.psiM_one T μ, S7.psiM_smooth T μ hμ,
      fun g hg => S7.psiM_casimir T μ hμ hg, hL n ε lam T μ hl hμ⟩
  exact ⟨hP, (hH n ε lam T _ hl hP (hK n ε lam T μ hl hμ hP)).1⟩

theorem realMetaplectic_of_forall (h : FdAll) : GlobalTheory.Published.FormalDegreeCompactDual := by
  intro cd sc hc N ε lam hl H _ _ σ w hσ hw
  have h1 := h N ε lam hl H σ hσ
  rw [GlobalTheory.FdegGap.muCD_eq_scaled cd sc hc ε] at h1
  exact fdegOf_of_isFdeg' h1 hw

theorem fdAll_of_norm (hN : PsiNorm) (hK : Key) (hH : Hilb) : FdAll :=
  have hM := modelDS_of (square_integrable_of_norm hN) hK hH
  fdAll_of hM (fdModel_of degPsi hlamStable (formF_of hlamStable (kmapZero_of hlamStable)) hN hM)

theorem normInd_of_steps (hP : CoefPow)
    (h : MomW → CoefPow → KNull → HsPol → PhiMul → PhiLe → PhiCont → HsInt → GapNorm → NormInd) : NormInd :=
  h momW hP (kNull_of momW hP) hsPol phiMul phiLe phiCont hsInt (gapNorm_of degPsi)

end PositivityTheory.RgFd
