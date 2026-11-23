module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PTranslF
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PProdOp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PGenLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PSphOp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PAbsCore
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Isotypic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.GlobalHaarAverageTraceIdentity
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bridge
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL1SpectralBounds.Bundle0002

@[expose] public section

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

theorem slotFacts : SlotBasic := slotFacts_pf places
theorem levTop : LevTop := levTop_pf slotFacts
theorem levFix : LevFix := levFix_pf places slotFacts (jointFix_pf slotFacts)
theorem toYd : ToYd := toYd_pf slotFacts levTop translF_pf heckeSum_pf lvShift_pf
theorem pfHecke : PfHecke := pfHecke_pf slotFacts levTop
theorem prodOp : ProdOp := prodOp_pf slotFacts levTop absStep_pf pfHecke
theorem locComm : LocComm := locComm_pf slotFacts levTop
theorem yLoc : YLoc := yLoc_pf pfHecke prodOp
theorem zSimple : ZSimple := zSimple_pf (genLoc_pf slotFacts levTop pfHecke prodOp) locComm (sphOp_pf cvOp) yLoc
theorem zTr : ZTr := zTr_pf adm pfHecke prodOp locComm yLoc zSimple (ySwap_pf slotFacts pfHecke prodOp) (isot_pf slotFacts)
  (simpleFix_pf cvOp) (absCore_pf traceForm_pf)
theorem tTr : TTr := tTr_pf places pfHecke prodOp locComm yLoc (ex2Act_pf exAct) satAll_pf
theorem levelTr : LevelTr := levelTr_pf adm zTr (seenTr_pf trLevel adm cvOp) tTr

theorem piTerm_eq_traceSum_of_degreeFourTest (h : ThetaFixedGlobalWeights) : PiTerm := piTerm_of_weights_levels h wtEx_pf levTop levFix lcLevel_pf toYd levelTr twUniq_pf

theorem piTerm_of (h : ThetaFixOf) : PiTerm := piTerm_eq_traceSum_of_degreeFourTest (aux_statement_11 UpperTheory.V.Z.GSp4Splitting.global_haarAverage_trace_identity h)

theorem piTerm_holds : PiTerm := piTerm_of UpperTheory.V.Z.Tf.GOne.thetaFixOf

theorem cvIn : CvIn := cvIn_pf basic_pf (aeEq_pf basic_pf)
theorem wtInd : WtInd := wtInd_pf basic_pf
theorem typeIn : TypeIn := typeIn_pf piAdm_pf detZero_pf evalBasis_pf cvIn (formEx_pf basic_pf (aeEq_pf basic_pf) wtInd)
  (orthZero_pf basic_pf (aeEq_pf basic_pf) wtInd) absType_pf

theorem piFin_holds : PiFin := piFinOf_pf piAdm_pf tensType_pf (cvType_pf detZero_pf evalBasis_pf) cvIn typeIn

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi
