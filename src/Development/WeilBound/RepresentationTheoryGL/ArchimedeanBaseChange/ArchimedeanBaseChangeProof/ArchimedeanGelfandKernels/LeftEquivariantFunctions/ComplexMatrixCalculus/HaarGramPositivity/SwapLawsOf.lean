module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.HaarGramPositivity.Bundle0002
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.HaarGramPositivity.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.HaarGramPositivity.GramStrictPos
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.HaarGramPositivity.AdjointInv

@[expose] public section

namespace PositivityTheory.RgBcC

theorem fr0Laws_of (hR : RmLaws) (hG : GamMul) (hM : MtLaws) (hD : GamDer) : MatrixFrechetDerivativeAtZeroLaws := Cxe.fr0Laws_of hR hG hM hD

theorem swapLaws_of (hR : RmLaws) : SwapLaws := Cxe.swapLaws_of hR

end PositivityTheory.RgBcC
