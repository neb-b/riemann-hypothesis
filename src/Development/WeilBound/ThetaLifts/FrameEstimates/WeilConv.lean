module

public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0009
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0011
public import Development.WeilBound.ThetaLifts.FrameEstimates.ThickFrames
public import Development.WeilBound.ThetaLifts.FrameEstimates.IContOf
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0003
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0002
public import Development.WeilBound.ThetaLifts.FrameEstimates.SiegelAll
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0008
public import Development.WeilBound.ThetaLifts.FrameEstimates.ThetaSumNeg
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0006
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0005
public import Development.WeilBound.ThetaLifts.FrameEstimates.CoefSum
public import Development.WeilBound.ThetaLifts.FrameEstimates.CoefEq
public import Development.WeilBound.ThetaLifts.FrameEstimates.CoefBd
public import Development.WeilBound.ThetaLifts.FrameEstimates.FourierInj
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0004
public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0010
public import Development.WeilBound.ThetaLifts.FrameEstimates.InitialPairs.TriplePairHolds

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sqAll : SqAll := sqAll_of' coefSum coefEq_of (coefBd_of coefReal_of)

theorem sqSo : SqSo :=
  sqSo_of' soFin_of soCut_of (parity_of coefEq_of fourierInj_of) coefSum coefEq_of (coefBd_of coefReal_of)

theorem latTor : LatTor := latTor_of frameBasis_of oneVar_of

theorem latFull : LatFull := latFull_of latTor (minor_of frameBasis_of)

theorem domWeilU (h : GlobalTheory.Published.SiegelSetUnitary) : DomWeilU :=
  domWeilU_of grpTop_of epsOf_of (siegelAll_of h) sqAll latInv_of latMeas latCpt_of (latArch_of frameBasis_of) latTor
    Sq.posWt' Sq.square_integrable_integral_holds

theorem soSemiU (h : GlobalTheory.Published.SiegelSetUnitary) : SoSemiU :=
  soSemiU_of grpTop_of epsOf_of (siegelAll_of h) sqSo latInv_of latCpt_of latFull Sq.posWt'

theorem domSoU (h : GlobalTheory.Published.SiegelSetUnitary) : DomSoU := domSoU_of epsOf_of finVolU (soSemiU h)

theorem weilConv (h : GlobalTheory.Published.SiegelSetUnitary) (hB : ThetaBasic) : WeilConv :=
  weilConv_of hB (domWeil_of_U (domWeilU h)) soFin_of

theorem soDecay (h : GlobalTheory.Published.SiegelSetUnitary) : SoDecay := soDecay_of (soSemi_of_U (soSemiU h)) soFin_of

theorem soCont (h : GlobalTheory.Published.SiegelSetUnitary) (hB : ThetaBasic) : SoCont := soCont_of hB (domSoU h) soFin_of

theorem kDecay (h : GlobalTheory.Published.SiegelSetUnitary) (hB : ThetaBasic) : KDecay :=
  kDecay_of hB Sq.triplePair_holds (weilConv h hB) (soDecay h) (domSoU h) soFin_of

theorem iCont (h : GlobalTheory.Published.SiegelSetUnitary) (hB : ThetaBasic) : PositivityTheory.ThKF.ICont :=
  iCont_of hB grpTop_of epsOf_of (domWeil_of_U (domWeilU h)) (domSoU h) soFin_of

end PositivityTheory.ThKEst

end
