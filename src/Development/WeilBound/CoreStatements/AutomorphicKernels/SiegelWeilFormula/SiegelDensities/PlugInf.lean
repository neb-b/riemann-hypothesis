module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.DensEqOfBase
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchTop

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Densx

theorem densEq_of_one (hBase : BaseOne) (hO : MassOne) : PositivityTheory.SiegelWeilFormula.Gen.DensEq :=
  densEq_of_base PositivityTheory.PfSWUS.SchInf.schwartzDensInf hBase hO

end PositivityTheory.SiegelWeilFormula.Densx

end
