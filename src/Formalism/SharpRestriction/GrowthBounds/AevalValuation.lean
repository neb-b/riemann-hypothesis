module

public import Formalism.SharpRestriction.GrowthBounds.AevalValuation.MemSupportedOf
public import Formalism.SharpRestriction.GrowthBounds.AevalValuation.ValGen
public import Formalism.SharpRestriction.GrowthBounds.MonomialSupport.PhMonomialMul
public import Formalism.SharpRestriction.GrowthBounds.MonomialSupport.GeZSum
public import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients

@[expose] public section

namespace Formalism.MainNotions.TraceSpectra

theorem restChain : Formalism.MainNotions.PairMembershipBlocks.RestChain :=
  restChain_of valAeval valFilt Formalism.MainNotions.LetterSubstitution.valNN Formalism.MainNotions.LetterSubstitution.phMon Formalism.MainNotions.LetterSubstitution.compPh Formalism.MainNotions.LetterSubstitution.fdigPh
    Formalism.MainNotions.LetterSubstitution.fdigSum

theorem stmtE (D : Formalism.BasicNotions.D7) : tableLineDegreeFive.ClosedFormOfAdmitted D := Formalism.MainNotions.PairMembershipBlocks.stmtE_of_chain D restChain

end Formalism.MainNotions.TraceSpectra
