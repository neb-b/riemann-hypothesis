module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.EsTotHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PSpSpecIf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.Bundle0006
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleDualityTraceIsomorphism

@[expose] public section

namespace UpperTheory.Gal.Mod

theorem specGood : GlobalTheory.EtC.SpecGood := spSpecIf UpperTheory.Et.proper_base_change UpperTheory.Et.etale_base_change_of_duality

theorem esGen_all : ESGen := esGen_holds specGood

end UpperTheory.Gal.Mod
