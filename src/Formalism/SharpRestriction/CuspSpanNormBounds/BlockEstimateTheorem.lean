module

public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0003
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0002
public import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyBlockLiftEstimate
public import Formalism.SharpRestriction.CuspSpanNormBounds.PSDKOnOfPSDK
public import Formalism.SharpRestriction.ParConsts

@[expose] public section

open Matrix MeasureTheory NumberField Filter Topology Polynomial
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.BlockEstimateTheorem

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR

export Formalism.MainNotions.S.UnitaryLevelOperators (lenI mid3 wnormSq Msq IsKFinCoefT)

export Formalism.MainNotions.S.LocalFrameAxioms (LocMatch FrameAx PsiAx k_le_nS Nlet)

def vmOf (D : D7) {k0 : ℕ} (hk : k0 + 1 = D.R.k) (G : GramWordSpace.GramMap k0 D.R.rS) : ValMap D.R.k D.R.rS :=
  hk ▸ G.toValMap

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

end Family

end Formalism.MainNotions.BlockEstimateTheorem

end
