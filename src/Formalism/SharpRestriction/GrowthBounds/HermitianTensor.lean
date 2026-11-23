module

public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.ModelIdentificationHolds
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.Bundle0006
public import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.TauP

@[expose] public section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem qPh_proved : QPh :=
  qPh_of_rest tauP smithP

theorem theorem_I_closed_form_holds (D : Formalism.BasicNotions.D7) : SecondPartClosed D :=
  theorem_I_of_pairing_GL D qPh_proved

end Formalism.MainNotions.flipOneThree.Pf
