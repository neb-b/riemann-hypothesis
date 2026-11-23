module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.SphBound
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.HasLevel
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0006
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0009
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0010
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0013
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0018
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0015
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0027
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.FixW
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LRowTotal
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.MuCellTop
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.LFibEx
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.LPartFT
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0762
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0023
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.EisMeasTop
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0652
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEqSmulOfInvariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongrOverOfFrame
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0764
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0014
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ProjKComm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0763
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0025
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.FromColsSmulApply
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtendByZeroHermitianVal
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0017
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0005
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.JPosOfIdemEx
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCfRel
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0022
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0020

@[expose] public section

theorem PositivityTheory.Rg.Rsw.resCore : PositivityTheory.Rg.Rsw.ResCore :=
  open PositivityTheory.Rg.Rsw in
  have i := PositivityTheory.Rg.Rsw.L.idemEx
  have ge := PositivityTheory.Rg.Rsw.L.goodEv i
  have be := PositivityTheory.Rg.Rsw.L.bumpEx i
  have wm := PositivityTheory.Rg.Rsw.L.wMaj
  have tp := PositivityTheory.Rg.Rsw.L.thProd wm
  have rt := PositivityTheory.Rg.Rsw.L.rowTotal i be
  have fw := PositivityTheory.Rg.Rsw.L.fixW i PositivityTheory.Rg.Rsw.L.genK wm
  have ns := PositivityTheory.Rg.Rsw.L.nullSing i
  have t2 := GlobalTheory.CompanionTheory.ColumnSplitting.main i PositivityTheory.Rg.Rsw.L.latBound GlobalTheory.CompanionTheory.QKAvg.qk PositivityTheory.Rg.Rsw.L.ikSch
  have em := PositivityTheory.Rg.Rsw.Em.eisMeas i be (PositivityTheory.Rg.Rsw.L.major i ge be) fw (PositivityTheory.Rg.Rsw.L.fixTh i PositivityTheory.Rg.Rsw.L.geng PositivityTheory.Rg.Rsw.L.genK) tp (PositivityTheory.Rg.Rsw.Cell.muCell htExist i)
    PositivityTheory.Rg.Rsw.L.fibEx (GlobalTheory.CompanionTheory.RCellP.rcell wm PositivityTheory.Rg.Rsw.L.partFT) PositivityTheory.Rg.Rsw.L.posExt (PositivityTheory.Rg.Rsw.L.approxId i)
  have mi := PositivityTheory.Rg.Rsw.L.muId i ge be tp em ns (GlobalTheory.CompanionTheory.OrbUniq.uniq_of_trans i ns (GlobalTheory.CompanionTheory.RgTrans.idemEx_trans i)) (GlobalTheory.CompanionTheory.RswNoFrame.noFrame i) t2 (PositivityTheory.Rg.Rsw.L.toS i)
  have ci := GlobalTheory.CompanionTheory.RkCoef.target polar resMu mapsExist cfFJ pcBound pcFc rSec htExist tp rt wm PositivityTheory.Rg.Rsw.L.ikSch t2 mi
  have tb := PositivityTheory.Rg.Rsw.L.thBdd wm PositivityTheory.Rg.Rsw.L.latBound PositivityTheory.Rg.Rsw.L.wa1
  have cl := PositivityTheory.Rg.Rsw.L.cutLow PositivityTheory.Rg.Rsw.L.fourierPt PositivityTheory.Rg.Rsw.L.wa1
  have ie := (fun _ _ _ => PositivityTheory.Rg.Rsw.L.ikEq2 : PositivityTheory.Rg.Rsw.L.GenG → PositivityTheory.Rg.Rsw.L.WMaj → PositivityTheory.Rg.Rsw.L.IkSch → PositivityTheory.Rg.Rsw.L.IkEq) PositivityTheory.Rg.Rsw.L.geng wm PositivityTheory.Rg.Rsw.L.ikSch
  have tc := PositivityTheory.Rg.Rsw.L.thCoef PositivityTheory.Rg.Rsw.L.latBound
  PositivityTheory.Rg.Rsw.L.resCore polar cfFJ i ge fw wm (GlobalTheory.CompanionTheory.Jp.jPos_of_idemEx i) (PositivityTheory.Rg.Rsw.L.cfRel htExist) PositivityTheory.Rg.Rsw.L.cfInv cl
    (PositivityTheory.Rg.Rsw.L.cutId polar cfFJ ci tc PositivityTheory.Rg.Rsw.L.fourierPt PositivityTheory.Rg.Rsw.L.wa1 PositivityTheory.Rg.Rsw.L.cfInv tb cl PositivityTheory.Rg.Rsw.L.ikSch ie wm) tb tc PositivityTheory.Rg.Rsw.L.ikSch ie
