module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CIn
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.Bundle0006
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.PhiStepOf
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmooth2

@[expose] public section

namespace UpperTheory.Ru.crystallineComparison

theorem finAll : UpperTheory.Gal.crystallineComparison.Br.FinAll := finAll_of fun l _ K _ r f hf => cIn l K r f hf

theorem smoothModel_crystalline : CrystallineSemistableComparison.SmoothModelCrystalline := (CrystallineSemistableComparison.cstSmooth_of_side fun l _ K _ => UpperTheory.Gal.KunnethLefschetz.Top.etSide_sm_holds l K).1

theorem phiStep : UpperTheory.Gal.Int.Geo.PhiStep := phiStep_of (UpperTheory.Gal.Int.Geo.geoSide_of finAll smoothModel_crystalline)

end UpperTheory.Ru.crystallineComparison
