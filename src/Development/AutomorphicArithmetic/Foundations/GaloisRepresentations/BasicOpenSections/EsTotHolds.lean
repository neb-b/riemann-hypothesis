module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PEsGen
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.CycAllHolds

@[expose] public section

namespace UpperTheory.Gal.Mod

theorem esGen_holds (h : GlobalTheory.EtC.SpecGood) : ESGen :=
  esGen h esPt_holds nwtOne (frobQ frobTors) baseFacts denseGen frEx @corrPull @corrComm

end UpperTheory.Gal.Mod
