module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermsAbsTsumLeHeightPoly
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0163
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.SectionTrace.SecOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0763
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0760
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0761
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.EisensteinChartSplitting.PositiveSumGrowth.AbsAPos

@[expose] public section

namespace PositivityTheory.RgEis.Sp

open ResidueKilled.Tr

theorem siegelEisensteinContinuation_of (hD : Dict) (hI : DictInf) (hL : SecLaw) (hW : WallLaw) (hG : CMGood)
    (hT : GrpTop) (hB : BdetLaw) (hE : ExtLaw) (hP : ParLaw) (hS : SgAll) : GlobalTheory.Published.SiegelEisensteinContinuation :=
  ResidueKilled.Tr.tTop hG hT hB hE hP hS (_root_.GlobalTheory.CompanionTheory.TChartProof.tChart hD hI _root_.GlobalTheory.CompanionTheory.StdChart.tStd) (_root_.GlobalTheory.CompanionTheory.ScalWall.tScal hL hW) _root_.GlobalTheory.CompanionTheory.DivMult.div_multiplier

end PositivityTheory.RgEis.Sp
