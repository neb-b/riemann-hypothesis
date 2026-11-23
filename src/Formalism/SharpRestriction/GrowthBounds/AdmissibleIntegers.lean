module

public import Formalism.SharpRestriction.GrowthBounds.AdmissibleIntegers.StatementsOfRemainingBound
public import Formalism.SharpRestriction.GrowthBounds.AdmissibleIntegers.Bundle0001

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions.G Formalism.MainNotions Formalism.MainNotions.WeilJacquetShalikaLaw

namespace Formalism.MainNotions.WeilJacquetShalikaLaw.Proof

theorem restComp_proved : RestComp := fun _ _ _ _ hI hD => remaining_primes_of_admitted hI hD

theorem stmt_proved (D : D7) (L : SizeData₂ D) (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D) (Dx : DivX D) :
    Stmt D L X Y K c Dx := stmt_of_rest restComp_proved D L X Y K c Dx

end Formalism.MainNotions.WeilJacquetShalikaLaw.Proof

end
