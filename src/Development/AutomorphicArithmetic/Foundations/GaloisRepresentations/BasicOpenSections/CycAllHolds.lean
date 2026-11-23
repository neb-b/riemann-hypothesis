module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PFibExt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.Bundle0007
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.Bundle0005

@[expose] public section

namespace UpperTheory.Gal.Mod

theorem wtVal_holds : WtVal := by
  exact wtVal fibExt secGen (clopenAt resClosed hensSplit)

theorem cycAll_holds : CycAll := by
  exact cycAll resClosed valLiftB (cycRes wtVal_holds) (cycExt fibExt)

theorem esPt_holds : ESPt := esPt cycAll_holds

end UpperTheory.Gal.Mod
