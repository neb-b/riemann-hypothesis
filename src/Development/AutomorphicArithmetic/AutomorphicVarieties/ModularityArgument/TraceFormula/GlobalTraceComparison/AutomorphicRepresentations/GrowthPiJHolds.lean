module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.ZeroPf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle0016
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle0013
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle0014
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.EllFormula2J

@[expose] public section

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

theorem aeEq : AeEq := aeEq_pf basic_pf
theorem zero : Zero := zero_pf aeEq
theorem pointRep : PointRep := pointRep_pf aeEq kInv_pf
theorem ker : Ker := ker_pf weak_pf pointRep pComm_pf pDiag_pf
theorem supp : Supp := supp_pf basic_pf zero kInv_pf pSupp_pf ker
theorem gBound : GBound := gBound_pf basic_pf
theorem gFac : GFac := gFac_pf (finFac_pf basic_pf evalBasis_pf (finGen_pf basic_pf))
  (dropP_pf zero kInv_pf basic_pf weak_pf pointRep pComm_pf)
theorem rep : Rep := rep_pf basic_pf (thetaInt_pf basic_pf) kInv_pf pDiag_pf ker
theorem sizes : Sizes := by first | exact sizes_of_basic basic_pf | exact sizes_of_basic
theorem domInt : DomInt := domInt_pf basic_pf sizes
theorem halfTerm : HalfTerm := halfTerm_pf basic_pf gBound supp rep flip_pf domInt
theorem uncutHalf : DiscreteGroups.T1.G.UncutHalf := uncutOf_pf basic_pf gFac halfTerm (rangeW_pf rep) trFin_pf
theorem cutTail : DiscreteGroups.T1.G.CutTail2 :=
  tailOf_pf basic_pf sizes inCut_pf (tailInt_of_bounds gFac gBound supp domInt) (diagInt_pf gFac halfTerm)

theorem growthPiJ_holds : PositivityTheory.Rg.BcB.Desc.GrowthPiJ :=
  DiscreteGroups.T1.G.rGrowthPiJ_of (fun _ _ => uncutHalf) (fun _ _ => cutTail) PositivityTheory.Rg.BcB.CV.ellFormula2J
    PositivityTheory.Rg.BcB.E1.sFun_holds DiscreteGroups.T1.G.Dcy.piVecEx_holds DiscreteGroups.T1.G.piInv

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi
