module

public import Mathlib
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne

@[expose] public section

namespace GlobalTheory.HCXi

def BesselXiIntegrable : Prop := Formalism.FourierDecayAlt.B.XiExists

end GlobalTheory.HCXi
