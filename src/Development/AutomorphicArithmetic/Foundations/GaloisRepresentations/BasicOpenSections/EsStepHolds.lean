module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PHopOp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PTowES
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.EsGenAll

@[expose] public section

namespace UpperTheory.Gal.Mod

theorem hopOp_holds : HopOp := hopOp @galEx @corrOpEq

theorem towES_holds : TowES := towES esGen_all bcEx (liesOp hopOp_holds @opCover) (fixDesc hopOp_holds)

theorem esStep_holds : UpperTheory.Gal.Int.Geo.ESStep := esStep towES_holds placeData grPass

end UpperTheory.Gal.Mod
