module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.DualityDiagonalClassOfAffineProperBaseChange
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.PositiveMeasureNorms.Bundle0002

@[expose] public section

namespace PositivityTheory.Rg.BcB.E2

open E1

theorem spec_holds : Spec := P.spec P.gelf P.point P.specmeas P.speciso

theorem desint_holds : Desint :=
  P.desint P.jointrep P.tonelli P.weakae (P.eigae P.weakae) (P.locint P.tonelli) P.nonzero (P.smooth P.convcont)

theorem fData_holds : FData :=
  P.fdata (P.rowsex kerBasic vecEx vecNorm vecInner) (P.rowseig P.aeeq (P.unfold kerBasic P.convcont))

theorem oneStep_holds : OneStep := oneStep_of spec_holds fData_holds desint_holds P.hssep

theorem orthogonal_keeping_holds : E.OrthogonalKeepingOperator := orthogonal_keeping_of_estimate oneStep_holds

theorem proper_base_change : E.E2 := duality_diagonalClass_of_affineProperBaseChange orthogonal_keeping_holds

end PositivityTheory.Rg.BcB.E2
