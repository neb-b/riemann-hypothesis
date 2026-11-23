module

public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.CuspPairIrr
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.PosMkIff
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.Bundle0001
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.Compact
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.BoundB
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.ConjProd
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.Bundle0003
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.Bundle0002
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.Bundle0003

@[expose] public section

namespace CompanionTheory.RgGu.NR

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem redClC : RedCl k :=
  redCl_ofC k (someRed_of k (complementary_of signature) (compact k) (boundB k) (herm_ofB k (conjProd k) (conjDual k))
    (prodModel k)) (cuspUnit k) (cuspPairIrr k)

theorem rhoNuRhoReducibleC : CompanionTheory.Pf1.SegRepC.SegTwo.RhoNuRhoReducible := rhoNuRho_ofC fun k _ _ _ _ => redClC k

end CompanionTheory.RgGu.NR
