module

public import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.Development
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0048
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsProperSpreadsOut
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0751
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0737
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0123
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0126
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0130
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HtpyStOfCxSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0131
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeExOfAcyclic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExactOfSpan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteCover
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0165
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0162
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0138
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UOfIsBaseChange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0197
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleHomCompSquareZeroSection
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0151
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0734
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0747
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectFirstCohomologyBaseChange
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCohomologyComparisonSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0155
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransferSumProjectionsDegreeZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0127
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeFunctionalTwoFormNaturality
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0124
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExteriorPairingIotaTwo
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOfRTensor
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormComponentOfWedgeClassZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechTripleRestrictCompositeInjectiveCohomologyFo
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BilinearStatementWithDescentHypotheses
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0618
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0240
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0739
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cup1BoundaryOfBoundary
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0741
public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianWedgeProducts.EqZeroOfExteriorPowerMapAdd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemOfSmulEqZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0754
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0244
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0748
public import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.ClosedPoints.IsClosedPoint
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0738

@[expose] public section

namespace MainStatements.Hodge.Free

theorem abelianHodgeDeRham' : Chapters := by
  exact {
    dict := GlobalTheory.CompanionTheory.Dict.dictSt
    cx := GlobalTheory.CompanionTheory.HodgeCx.cxSt
    low := GlobalTheory.CompanionTheory.HodgeLow.lowSt_of_dictSt
    htpy := GlobalTheory.CompanionTheory.Hodge.htpySt_of_cxSt
    qcalc := GlobalTheory.CompanionTheory.QCalc.qCalcSt
    fubini := GlobalTheory.CompanionTheory.NerveCoh.fubiniSt
    affacyc := GlobalTheory.CompanionTheory.AffAcyc.main
    descent := GlobalTheory.CompanionTheory.Descent.descentSt
    sysbc := GlobalTheory.CompanionTheory.SysBC.sysBCSt
    stein := GlobalTheory.CompanionTheory.Hodge.stein_holds
    cot := GlobalTheory.CompanionTheory.Cot.cotSt
    par := GlobalTheory.CompanionTheory.AbForms.parSt
    axo := GlobalTheory.CompanionTheory.Axis.axOSt
    axform := GlobalTheory.CompanionTheory.AxForm.axFormSt
    cmp := GlobalTheory.CompanionTheory.Hodge.Nerve.cmpSt_of_cxSt
    fincoh := GlobalTheory.CompanionTheory.Hodge.finCohSt_of_cmpSt
    van := GlobalTheory.CompanionTheory.Hodge.vanSt
    perfnoeth := GlobalTheory.CompanionTheory.PerfN.perfNoeth
    perfbase := GlobalTheory.CompanionTheory.PerfExt.main
    perfh1 := GlobalTheory.CompanionTheory.PerfectFirstCohomology.perfect_first_cohomology_base_change
    perfh2 := GlobalTheory.CompanionTheory.PerfectSecondCohomology.perfect_second_cohomology_from_fibres
    wedgeof := GlobalTheory.CompanionTheory.WedgeOf.wedgeOf_of_low
    hopffield := GlobalTheory.CompanionTheory.HopfC.hopfFieldSt
    oneform := GlobalTheory.CompanionTheory.OneFormCoh.oneFormCohSt
    twoform := GlobalTheory.CompanionTheory.HodgeTwoForm.twoFormCohSt
    closed := GlobalTheory.CompanionTheory.HodgeClosed.closedSt_of_twoFormCohSt
    lift := GlobalTheory.CompanionTheory.Hodge.LiftO.lift_of_forms
    alt := GlobalTheory.CompanionTheory.HodgeAlt.altSt
    hyp2 := GlobalTheory.CompanionTheory.HypWedge.hyp2St
    hopf := GlobalTheory.CompanionTheory.HopfSys.hopfSt
    bi := GlobalTheory.CompanionTheory.GroupLaw.bilinear_statement_with_descent_hypotheses
    formbc := GlobalTheory.CompanionTheory.Hodge.FormBC.formBC
    oside := GlobalTheory.CompanionTheory.HodgeO.oBC_wedge
    perf := GlobalTheory.CompanionTheory.PerfModels.perfSt_of_spreads
    final := GlobalTheory.CompanionTheory.HodgeAssembly.abelianHodgeDeRham_of_statements
    hopfle := GlobalTheory.CompanionTheory.HopfLe.hopfLeSt
    h1le := GlobalTheory.CompanionTheory.Hodge.FirstCohomologyUpperBounds.h1Le
    wedgefield2 := GlobalTheory.CompanionTheory.Hodge.WedgeFieldGeo.wedgeField_of_field
    noprim := MainStatements.Hodge.Pf.noprim
    smalllift := GlobalTheory.CompanionTheory.SmallLift.main
    perfvb := GlobalTheory.CompanionTheory.PerfVB.perfVB
    h1all := GlobalTheory.CompanionTheory.Hodge.FirstCohomologyVectorBundle.first_cohomology_vector_bundle_rank
    flatbc := GlobalTheory.CompanionTheory.Hodge.FlatBase.flatBC
    feweqn := GlobalTheory.CompanionTheory.FewEq.fewEq
    stalkdim := MainStatements.Hodge.Pf.stalkdim
    h1ge := GlobalTheory.CompanionTheory.FirstCohomologyLowerBound.first_cohomology_dimension_lower_bound
    h1field := GlobalTheory.CompanionTheory.AbelianFirstCohomologyOverField.first_cohomology_rank_over_field
  }

theorem abelianHodgeDeRham : GlobalTheory.Published.AbelianHodgeDeRham :=
  abelianHodgeDeRham'.print GlobalTheory.CompanionTheory.NoethApprox.schemeModels GlobalTheory.CompanionTheory.SmoothSpread.smooth_spreads GlobalTheory.CompanionTheory.SpreadingModels.properSpreads
    GlobalTheory.CompanionTheory.TrivLoc.trivLocus GlobalTheory.CompanionTheory.KLFinite.kFinite

end MainStatements.Hodge.Free
