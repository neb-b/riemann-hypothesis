module

public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Bundle0009
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.ProjectionMemPartialSpan
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Bundle0006
public import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Bundle0011

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.Proposition5Numerics

theorem decomposition_of_three_parts (hVB : RestValBdG) (hXX : RestXXG) (hDd : RestDdG) : RestDecG :=
  restDecG_of atl valSlice valComp hVB hXX hDd

theorem membership_of_three_parts (hVB : RestValBdG) (hXX : RestXXG) (hDd : RestDdG) (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) :
    RestMemb D CLa Ck Crk Cdeg :=
  membership_of_four_parts (decomposition_of_three_parts hVB hXX hDd) restAlgG restDegG restLabG D CLa Ck Crk Cdeg

end Formalism.MainNotions.Proposition5Numerics
