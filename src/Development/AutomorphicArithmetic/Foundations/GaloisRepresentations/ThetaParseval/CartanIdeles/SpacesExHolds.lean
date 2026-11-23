module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.IdeleStep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.BaseEx

@[expose] public section

namespace UpperTheory.Gal.TP.Skew

theorem lineEx_holds : LineEx := lineEx ordAut (ordLine conjAut (ideleStep conjAut) ordEmb invFun ordAut) memOrd memDual

theorem spacesEx_holds : SpacesEx := spacesEx_of lineEx_holds posEx stdHerm lineSkew

theorem baseEx_holds : BaseEx := baseEx

theorem skewLine_holds : SkewLine := skewLine_of spacesEx_holds baseEx_holds

end UpperTheory.Gal.TP.Skew
