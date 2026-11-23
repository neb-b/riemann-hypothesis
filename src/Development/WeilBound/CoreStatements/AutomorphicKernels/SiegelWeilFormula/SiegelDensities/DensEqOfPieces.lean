module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.Bundle0002
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.Bundle0003

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Densx

theorem densEq_of_pieces (hE1 : PositivityTheory.PfSWUS.HMass.OneVecBinary) (hE2 : PositivityTheory.PfSWUS.HMass.OneVecBinaryMass)
    (hB : PositivityTheory.PfSWUS.HMass.SchwartzDensInf) (hBase : BaseOne) (hO : MassOne) : PositivityTheory.SiegelWeilFormula.Gen.DensEq :=
  densEq_of_C hB (swMeasCAll_of hBase isomC scaleC (stepC_of hE1 (massCAll_of hE2 hO))
    (notRepC_of hE1 (massCAll_of hE2 hO)))

end PositivityTheory.SiegelWeilFormula.Densx

end
