module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.VanishingOnXAndXPlusGlobal

export Formalism.MainNotions.S.UnitaryVolumeMass (DefiniteComplementRank Lem1 Lem2 LatticeSpanEquality ThmA HyperplaneEquality ThmB)

open NumberField Formalism.BasicNotions Formalism.MainNotions.S.Lat Module

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def adm1 (D : D7) : Prop :=
  S.UnitaryVolumeMass.stGlue D

section Fam
variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

end Fam

end Formalism.MainNotions.VanishingOnXAndXPlusGlobal

end
