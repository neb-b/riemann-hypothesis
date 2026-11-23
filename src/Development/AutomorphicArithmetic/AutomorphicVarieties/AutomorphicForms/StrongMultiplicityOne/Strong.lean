module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.Bundle0003

@[expose] public section

namespace UpperTheory.V.Af

theorem StrongMultiplicityOne.smoCentral : StrongMultiplicityOne.SmoCentral := by
  have hPft := Smo.pftSch_of Smo.schOfClosed Smo.pftDeriv Smo.pftMul
  have hStep := StrongMultiplicityOne.archStep StrongMultiplicityOne.trDual (Smo.schTw (Smo.schTensor Smo.schOfClosed)) hPft (Smo.betaSch hPft) Smo.betaInt
  have hArch := StrongMultiplicityOne.archKir Smo.colConj Smo.rowStep hStep StrongMultiplicityOne.linChange
  have hLoc := Smo.locKir Smo.colConj Smo.rowStep (Smo.locStep Smo.avgChar Smo.locDual)
  have hKill := StrongMultiplicityOne.killP hArch (StrongMultiplicityOne.finKir hLoc Smo.psiLoc StrongMultiplicityOne.embY) StrongMultiplicityOne.embY StrongMultiplicityOne.psiInf StrongMultiplicityOne.chartCont
  have hZero := Smo.sphZero Smo.sphDict (Smo.tjSet Smo.sphDict) Smo.centLoc
  have hMap := StrongMultiplicityOne.eigMap StrongMultiplicityOne.chartCont
  have hVan := StrongMultiplicityOne.vanish (StrongMultiplicityOne.sphAll Smo.awayInd hZero StrongMultiplicityOne.embY) Smo.injP Smo.denseAway Smo.whBasic hMap
  have hCont := StrongMultiplicityOne.convCont StrongMultiplicityOne.chartCont
  have hSet := StrongMultiplicityOne.setUp Smo.psiLoc Smo.levelS StrongMultiplicityOne.niceOf
  have hPair := StrongMultiplicityOne.pair (StrongMultiplicityOne.seed Smo.whBasic (StrongMultiplicityOne.seedConv StrongMultiplicityOne.chartCont) StrongMultiplicityOne.niceOf) hSet hKill hVan Smo.whBasic
    Smo.whLin (StrongMultiplicityOne.convNice hCont (StrongMultiplicityOne.convFub StrongMultiplicityOne.chartCont)) StrongMultiplicityOne.niceOf hMap
  exact StrongMultiplicityOne.smoCentral_of (StrongMultiplicityOne.cenSame (Smo.centEq Smo.centLoc Smo.awayInd Smo.denseAway) hSet) hPair StrongMultiplicityOne.compl
    (StrongMultiplicityOne.proj hMap) Smo.orthTr (StrongMultiplicityOne.orthConv (StrongMultiplicityOne.orthStep StrongMultiplicityOne.chartCont) hCont)

theorem strongMultOneC : StrongMultiplicityOne.StrongMultOneC :=
  StrongMultiplicityOne.strong_of StrongMultiplicityOne.smoCentral StrongMultiplicityOne.carrier StrongMultiplicityOne.eigOfSat StrongMultiplicityOne.normTwist

end UpperTheory.V.Af
