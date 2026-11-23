module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.ConjDivNorm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.TypVal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.ChrPairsPf

@[expose] public section

namespace UpperTheory.Gal.TP.Chr

theorem chrEx_holds : ChrEx := chrEx muEmb readEx readLoc readRes readExp absFacts (typProd typVal) expInj

theorem chrPairs_holds : UpperTheory.Gal.TP.Sub.ChrPairs := chrPairs chrEx_holds typVal

end UpperTheory.Gal.TP.Chr
