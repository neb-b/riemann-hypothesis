module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.GLFacts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.ExistsStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.LocDescOf

@[expose] public section

namespace UpperTheory.Gal.LocD

theorem funInv_holds : FunInv := by
  have dist := distInv (distZero (cellStep stabSub))
  exact funInv (biInv dist) prMem prLeft prAuto prSurj etaEx

theorem scalar_holds : Scalar := by
  have fi := funInv_holds
  exact scalar_of (eig eigZero) toBorel jacSemi (core fi gLCells gLFacts)

theorem locDesc_holds : LocDesc := locDesc_of scalar_holds tracePow

theorem ofSupport_holds : OfSupport := ofSupport

end UpperTheory.Gal.LocD
