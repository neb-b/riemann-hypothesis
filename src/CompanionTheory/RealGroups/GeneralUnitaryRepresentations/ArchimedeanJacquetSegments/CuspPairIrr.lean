module

public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.ComapTwKer
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.DerFin
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.Bundle0002
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.Bundle0003
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.CuspPair
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580

@[expose] public section

namespace CompanionTheory.RgGu.NR

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nuPair : GlobalTheory.BZSeg.NuPair k :=
  nuPair_of k (GlobalTheory.T.derivative_jacquet_holds k GlobalTheory.CompanionTheory.BZCuspPair.irrAdm) (jmTheta k) (derFin_of k (derEquiv k))

theorem cuspPairIrr : GlobalTheory.BZSeg.CuspPairIrr k := cuspPairIrr_of k (nuPair k)

end CompanionTheory.RgGu.NR
