module

public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0005
public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0004
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw

@[expose] public section

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLl
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.WeilJacquetShalikaLaw Formalism.MainNotions.WeightDegreeSizes

variable {D : D7} {L : SizeData₂ D}

theorem sizeData_at_level_primes_of_defs {X : ErrX D} {K : Formalism.MainNotions.G.Consts} {c : ErrC} (P : ParameterChoice' D L) (hF : L.FDef) (hE : L.EDef X K c)
    (hTg : LevelPrimeNotTypePrime D) : LevelPrimeSizes D L := ETDef_of P hF hE hTg

end Formalism.MainNotions.J

end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.GandSy
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions.WeilJacquetShalikaLaw

variable {D : D7} {L : SizeData₂ D}

theorem servedModel_of_params (P : ParameterChoice' D L) (X : Inst D L) (K : Consts) (h3 : 3 ≤ L.sc.x ^ (L.sc.ez / 5)) :
    Formalism.MainNotions.WeightDegreeSizes.ServedHasModel X K := by
  unfold Formalism.MainNotions.WeightDegreeSizes.ServedHasModel
  intro u w hw hV
  refine Formalism.BasicNotions.gIdx_of_cand P K h3 u _ ?_ hw
  unfold VV at hV
  by_contra hc
  exact hV (if_neg (fun h => hc h.1))

end Formalism.MainNotions.J
end
end

