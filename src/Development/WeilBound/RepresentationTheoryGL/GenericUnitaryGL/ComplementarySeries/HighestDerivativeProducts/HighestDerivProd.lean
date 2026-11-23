module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.PhiPG0
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueSequenceHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PsiGpCommutationHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiGpCommutationHolds
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.HighestDerivativeProducts.IsSmoothCharDpowM
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0646
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0479
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeibnizOrderOfExactSequences
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0392
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0656
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIrreducibleTensorDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0336
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0371
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0593

@[expose] public section

namespace GlobalTheory.RgGu.Leib.Hand

theorem leibnizOrd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    LeibnizOrd k :=
  _root_.GlobalTheory.CompanionTheory.LeibOrd.Main.leibnizOrd_of_parts k (_root_.GlobalTheory.CompanionTheory.BZRes.resSeq k) (_root_.GlobalTheory.CompanionTheory.RgGu.PsiGP.psiGP k) (_root_.GlobalTheory.CompanionTheory.LeibPhi.phiGP k) (GlobalTheory.CompanionTheory.BZPsiPG.Hand.psiPG k) (GlobalTheory.CompanionTheory.BZPhiPG.phiPG k)
    (GlobalTheory.T.phi_pg_rank_zero_holds k)

end GlobalTheory.RgGu.Leib.Hand
