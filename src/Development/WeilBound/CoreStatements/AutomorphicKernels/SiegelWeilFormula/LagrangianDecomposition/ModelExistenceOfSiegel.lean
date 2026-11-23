module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ModelExistenceOfSiegelSmall
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SmallSTop

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Ald

theorem model_existence_of_siegel (hG : SiegelSmall) : ModelEx := model_existence_of_siegel_small hG (smallS_of' chartFacts sliceFacts)

end PositivityTheory.SiegelWeilFormula.Ald

end
