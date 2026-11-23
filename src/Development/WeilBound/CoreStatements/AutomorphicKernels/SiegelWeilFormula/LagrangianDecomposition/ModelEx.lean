module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.ModelExistenceOfSiegel
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.Bundle0012

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Ald

theorem modelEx : ModelEx := model_existence_of_siegel (siegelSmall_of_slice sliceFacts)

end PositivityTheory.SiegelWeilFormula.Ald

end
