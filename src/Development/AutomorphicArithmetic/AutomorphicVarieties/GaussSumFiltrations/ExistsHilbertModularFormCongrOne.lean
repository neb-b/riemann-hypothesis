module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HasQOfSmallSubOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.OneUseOf

@[expose] public section

namespace UpperTheory.V

theorem Published.exists_hilbertModularForm_congr_one : Published.HilbertOne := GlobalTheory.HilbertThetaSeries.hilbertOne

theorem Lit.oneUse : Lit.OneUse := Lit.oneUse_of Published.exists_hilbertModularForm_congr_one

end UpperTheory.V
