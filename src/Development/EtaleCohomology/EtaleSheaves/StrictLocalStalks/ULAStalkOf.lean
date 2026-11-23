module

public import Development.EtaleCohomology.EtaleSheaves.StrictLocalStalks.Bundle0001

@[expose] public section

open LateralTheory.E.t_E3Cut

namespace LateralTheory.E.ULAStalkPf

theorem ULAStalk_of' (hI : IntClos) (hT : SHTensor) (hA : AICSH) (hE : SHEqv) (hC3 : EtaleBaseChangeFractionFieldIndEtaleOverPolynomial)
    (p2 : IECob) (p3 : FracAIC) : ULAStalk :=
  ULAStalk_of hI hT hA hE hC3 polyPO p2 p3 fracOf

end LateralTheory.E.ULAStalkPf
