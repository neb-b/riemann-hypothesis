module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.SameKTrans
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PFrameEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.Bundle0009

@[expose] public section

namespace UpperTheory.Gal.Int.Geo.Pl

theorem tjOK_holds : TjOK := tjOK_of sides_holds dict_holds levBasic_holds

theorem tjIdx_holds : TjIdx := tjIdx_of sides_holds dict_holds levBasic_holds

theorem memEx_holds : MemEx := memEx_of sides_holds dict_holds levBasic_holds

theorem siteTriv_holds : SiteTriv := siteTriv_of sides_holds levBasic_holds

theorem siteEx_holds : SiteEx :=
  siteEx_of sides_holds dict_holds levBasic_holds (stabOf_of nearNbhd_holds primeProj_holds dict_holds)

theorem goodOf_holds : GoodOf :=
  goodOf_of levBasic_holds tjOK_holds (projLev_of dict_holds primeProj_holds levBasic_holds inIdUnit_holds)

theorem congOf_holds : CongOf := congOf_of levBasic_holds tjOK_holds tjIdx_holds

theorem exists_unitaryGroupDatum_of_vector_exponent_spectral (h1 : VecEx) (h2 : ExpOf) (h3 : SpecTop) : PlanEx :=
  planEx_of ⟨frameEx_holds, h1, h3, h2, sides_holds, levBasic_holds, memEx_holds, siteTriv_holds, siteEx_holds, goodOf_holds,
    congOf_holds, datEx_holds, CertificateRingHomMap.rootsAlg_holds, satCard, intCof_holds⟩

end UpperTheory.Gal.Int.Geo.Pl
