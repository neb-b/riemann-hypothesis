module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BaseChangeDescent.Strong
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeak
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.SplitRigidity.SplitRigid
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.Thin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.Bundle0001
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.SaturatedBaseChange.SpehSingleFactorEquiv
public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.JacquetShalikaBound
public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.CuspidalMultiplicityOne

@[expose] public section

open UpperTheory.V.Z.Tf PositivityTheory.AutomorphicGaloisHodgeTate.SaturatedBaseChange

namespace UpperTheory.Gal.Desc

theorem speh : GlobalTheory.BcSpeh.BcSpeh := UpperTheory.BaseChangeIdentities.speh UpperTheory.BaseChangeIdentities.baseChangeNB

theorem weakAll : WeakAll := weakAll_of SR.splitRigid (GaloisFromTraceFormula.partNorm GaloisFromTraceFormula.absInf) GOne.unitOf GaloisFromTraceFormula.runTh

theorem desc : GlobalTheory.Cong.Desc :=
  desc_of speh compUnique oneFactor PositivityTheory.JacquetShalikaLocal.jacquetShalikaBound PositivityTheory.jumpWindows.cuspidalMultiplicityOne SR.splitRigid GOne.thin GOne.unitOf weakAll

theorem descOffT : GlobalTheory.Cong.DescOffT := GlobalTheory.Cong.descOffT_of_desc desc

end UpperTheory.Gal.Desc
