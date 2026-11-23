module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.CoverExistsOf
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.Development
public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.ExplicitFunctionSquareIntegrable
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.EquivariantSections.KeyIdentityHolds
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.HilbertSpaceModels.HilbertSpaceRealisationHolds
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.InfinitesimalCharacters.DiscreteSeriesInfinitesimalCharacter

@[expose] public section

namespace CompanionTheory.RgDs.B

theorem dsExists : GlobalTheory.Dec.DSExists := dsExists_of CompanionTheory.RgFd.explicit_function_square_integrable K.key_identity_holds Hilb.hilbert_space_realisation_holds

theorem kTypesAbove : GlobalTheory.Dec.KTypesAbove := kTypesAbove_of CompanionTheory.RgFd.explicit_function_square_integrable K.key_identity_holds Hilb.hilbert_space_realisation_holds

theorem dsInfChar : GlobalTheory.Dec.DSInfChar := CompanionTheory.RgDsInf.dsInfChar'

theorem discreteSeriesUpqExists : GlobalTheory.Published.DiscreteSeriesUpqExists := upqExists_of dsExists

theorem discreteSeriesExists : GlobalTheory.Published.DiscreteSeriesExists := exists_of dsExists

theorem discreteSeriesCoverExists : GlobalTheory.Published.DiscreteSeriesCoverExists := coverExists_of dsExists

theorem classUsed : ClassUsed := classUsed_of dsExists kTypesAbove dsInfChar

end CompanionTheory.RgDs.B
