module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.CxDataOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InverseLineDerivatives.RmAnti
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.AdjugateDifferentiability.DifferentiableMt
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.KroneckerSmoothness.SumKronLeft
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.KroneckerSmoothness.FrameInvMulSymZero

@[expose] public section

namespace PositivityTheory.RgBcC

theorem cxData_model {n : ℕ} (lam : Fin n → ℤ) (hlam : Antitone lam) :
    CxData lam (lefE n lam) (lefFr n lam) (lefε n lam) (lefι n lam) (lefS n lam) (lefΓ n lam) (lefT n lam) := by
  have hsw : SwapLaws := swapLaws_of rmLaws
  have hfd : MatrixFrechetDerivativeAtZero := fr0Der_of gamDer gamMul mtLaws rmLaws
  exact cxData_of cfPair mtLaws gamMul car gamCre gamScal number rmLaws rmChar avg fr0Laws hsw
    (tdOf avg hbOrtho hsw hfd (wedgeDer_of gamDer))
    (eigOf avg gamMul rmLaws rmHol rmAnti eigProd eigLocal) lam hlam

theorem cxEx_model : CxEx := fun n lam hlam =>
  ⟨lefE n lam, lefFr n lam, lefε n lam, lefι n lam, lefS n lam, lefΓ n lam, lefT n lam, cxData_model lam hlam⟩

end PositivityTheory.RgBcC
