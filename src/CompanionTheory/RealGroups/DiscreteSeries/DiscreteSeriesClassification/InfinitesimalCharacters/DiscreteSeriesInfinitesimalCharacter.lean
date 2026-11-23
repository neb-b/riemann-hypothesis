module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.InfinitesimalCharacters.DsInfCharOf
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0427
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0188
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0397
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0760

@[expose] public section

namespace CompanionTheory.RgDsInf

theorem dsInfChar' : GlobalTheory.Dec.DSInfChar :=
  dsInfChar_of
    (fun V _ _ => GlobalTheory.CompanionTheory.CapelliGelfand.etr_eq_gelfVal_of_capelli V)
    GlobalTheory.CompanionTheory.SmoothVecGl.unitAct_glRel
    GlobalTheory.CompanionTheory.CapelliMap.map_qdet_etr
    GlobalTheory.CompanionTheory.CoefWord.eword_coef
    GlobalTheory.CompanionTheory.CycWordTrace.sum_cycWord_eq_etr
    GlobalTheory.CompanionTheory.KFinSmoothBoth.kFin_smooth_both
    GlobalTheory.CompanionTheory.DiscreteSeries.isDS_sk_imp_upqRep
    GlobalTheory.CompanionTheory.CoefSmooth.coef_smooth
    CompanionTheory.D.DSIC.discrete_series_infinitesimal_character

end CompanionTheory.RgDsInf
