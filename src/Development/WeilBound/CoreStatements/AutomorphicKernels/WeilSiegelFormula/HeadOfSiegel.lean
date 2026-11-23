module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.WeilSiegelSchwartz.EcHeisSch
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0724
public import Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.WeilSiegelSchwartz.HermitianIntegrability.SiegelND
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0700
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2737
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0475
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0589
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableOfTsumEnormLtTop
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0460
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0461
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0673
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0495
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0513
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0464
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0656
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0651

@[expose] public section

namespace PositivityTheory.PfWsf.Top

theorem pull : PositivityTheory.GramSchwartzFunctions.PullSchLI := GlobalTheory.CompanionTheory.PullSch.pullSchLI
theorem orb : PositivityTheory.GramSchwartzFunctions.ThetaOrbits := GlobalTheory.CompanionTheory.ThetaOrbit.thetaOrbits

theorem head_of_two (hE : PositivityTheory.GramSchwartzFunctions.EisCells) (hB : PositivityTheory.GramSchwartzFunctions.BigCell) : GlobalTheory.Published.WeilSiegelFormula :=
  GlobalTheory.CompanionTheory.SiegelAssemblyLI.weilSiegelFormula_of_chapters_LI
    (GlobalTheory.CompanionTheory.WeilTheta.weilThetaConvergence_of_siegelSet GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary)
    GlobalTheory.WeilEisConv.weilEisensteinSiegelConvergence pull hE orb hB

theorem big_of_three (h1 : PositivityTheory.GramSchwartzFunctions.BC.PoissonHerm) (h2 : PositivityTheory.GramSchwartzFunctions.BC.SiegelND) (h3 : PositivityTheory.GramSchwartzFunctions.BC.SiegelDeg) :
    PositivityTheory.GramSchwartzFunctions.BigCell :=
  GlobalTheory.CompanionTheory.WeilSiegel.bigCell_of_poisson_siegel GlobalTheory.CompanionTheory.HermVol.exists_isCovolOneH h1 GlobalTheory.CompanionTheory.SplitGram.hasSum_IfrB h2 h3

end PositivityTheory.PfWsf.Top

namespace PositivityTheory.PfWsf.Top

end PositivityTheory.PfWsf.Top

namespace PositivityTheory.PfWsf.Top

theorem head_of_three (h4 : PositivityTheory.GramSchwartzFunctions.BC.PoissonHerm) (h5 : PositivityTheory.GramSchwartzFunctions.BC.SiegelND)
    (h6 : PositivityTheory.GramSchwartzFunctions.BC.SiegelDeg) : GlobalTheory.Published.WeilSiegelFormula :=
  head_of_two GlobalTheory.CompanionTheory.EisCellsChapter.eisCells (big_of_three h4 h5 h6)
end PositivityTheory.PfWsf.Top

namespace PositivityTheory.PfWsf.Top

theorem head_of_siegel (h5 : PositivityTheory.GramSchwartzFunctions.BC.SiegelND) (h6 : PositivityTheory.GramSchwartzFunctions.BC.SiegelDeg) : GlobalTheory.Published.WeilSiegelFormula :=
  head_of_three GlobalTheory.CompanionTheory.HermPoisson.poissonHerm_main h5 h6
end PositivityTheory.PfWsf.Top

namespace PositivityTheory.PfWsf.Top

theorem head_of_deg (h6 : PositivityTheory.GramSchwartzFunctions.BC.SiegelDeg) : GlobalTheory.Published.WeilSiegelFormula :=
  head_of_siegel PositivityTheory.PfWsf.Hand.Merge.siegelND h6
end PositivityTheory.PfWsf.Top
