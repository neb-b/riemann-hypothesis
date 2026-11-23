module

public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembershipOfThreeParts
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembVB
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembDd
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Bundle0011

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.Proposition5Numerics

theorem restMemb (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : RestMemb D CLa Ck Crk Cdeg :=
  membership_of_three_parts restValBdG restXXG_b restDdG_holds D CLa Ck Crk Cdeg

end Formalism.MainNotions.Proposition5Numerics
