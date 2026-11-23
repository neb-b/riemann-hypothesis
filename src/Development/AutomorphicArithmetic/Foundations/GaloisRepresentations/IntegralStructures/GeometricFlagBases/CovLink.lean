module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.CovMain
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.QuotObjLink
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3142
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PFinCover
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PRepMul
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.Bundle0012

@[expose] public section

namespace UpperTheory.Gal.Int.Geo.CovMain

open UpperTheory.Gal.FiniteEtaleModels in
theorem mIn : MIn :=
  { ex := @GlobalTheory.T.harrisTaylorIntegralModel_nonempty,
    proj := @GlobalTheory.UPel.HT.Model.isProjOver_of_compactB,
    cmp := @GlobalTheory.T.exists_open_closed_immersion_genModel_to_fibre,
    finModel := finModel_holds (finCover_holds
      (repAll_holds idealInd_holds (repMul_holds crtMul_holds crtProj_holds))
      (ptAll_holds idealInd_holds crtMul_holds) grpFin_holds),
    placeOf := placeOf_holds,
    cong := crystallineComparison.Mod.congKS_link,
    corr := crystallineComparison.Mod.corrBC_holds crystallineComparison.Mod.quotObj_link }

theorem ksCong_holds : KSCong := kSCong_of mIn
theorem stdEx_holds : StdEx := stdEx_of mIn
theorem ksCover_holds : KSCover := kSCover_of mIn

end UpperTheory.Gal.Int.Geo.CovMain
