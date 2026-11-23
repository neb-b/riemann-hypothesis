module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.RelOpCurve
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.DerivK
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.FromHC

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.DS.HW

theorem kRepPiece : KRepPieceStatement := kRepPiece_of kRepRel kRepStable

theorem compRed : CompRedStatement := compRed_of kRepRel kRepStable kRepPiece

theorem derivExists : DerivExistsStatement := derivExists_of derivExists_allPos

theorem uRepCompRed : URepCompRedStatement := uRepCompRed_of uRepHom derivExists kRepRel compRed

end ReciprocityTheory.ChartRestriction.DS.HW
