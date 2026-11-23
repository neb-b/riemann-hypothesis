module

public import Mathlib
public import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0009
public import Development.DiscreteGroups.GlobalIrreducibility.LConvUnitOf
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0003
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0005
public import Development.DiscreteGroups.GlobalIrreducibility.LConvComm
public import Development.DiscreteGroups.GlobalIrreducibility.LConvUnif
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0008
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0013
public import Development.DiscreteGroups.GlobalIrreducibility.LConvGen
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0012

@[expose] public section

namespace DiscreteGroups.sglob.LConv

theorem localConverseGL : GlobalTheory.Published.LocalConverseGL :=
  localConverseGL_of_leaves cuspGen kirBump bigCell extremeExists extremeIrred sepOfExtreme commBound unifOfComm
    altIdentity finiteOfAlt unitOfUnif glue

end DiscreteGroups.sglob.LConv
