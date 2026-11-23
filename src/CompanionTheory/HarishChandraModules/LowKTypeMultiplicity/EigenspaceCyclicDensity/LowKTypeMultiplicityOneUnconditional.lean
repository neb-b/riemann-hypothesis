module

public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.WtProj
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsPowEqZero
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InNOfMem
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.Bundle0001
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0022
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.FilterAll
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.Bundle0002
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.KoszulDifferentialAnticommutator
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.GeneralizedVermaModulePolynomial
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.CycDense
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter

@[expose] public section

namespace CompanionTheory.D.LK

theorem hGenCO : GenCO := genCO_of koszul_differential_sq_zero (cover2_of (acycAbs_of koszul_differential_sq_zero))

theorem hInj : Inj :=
  inj_of (vanK_of (cok_of hGenCO) GlobalTheory.CompanionTheory.LKWtProj.wtProj (GlobalTheory.CompanionTheory.KWeightMajor.wtMajor_of DSIC.hLowSpan)) GlobalTheory.CompanionTheory.LKWtProj.wtProj koszul_differential_sq_zero

theorem hMultAlg : MultAlg :=
  multAlg_of DSIC.hLowSpan DSIC.hHWMap GlobalTheory.CompanionTheory.LKDens.dens GlobalTheory.CompanionTheory.LKInvLift.invLift GlobalTheory.CompanionTheory.HCdecomp.hcdec hGenCO top_degree_cycle hInj

theorem hKModExists : KModExists :=
  GlobalTheory.CompanionTheory.KModExists.kModExists DSIC.hSmMod CompanionTheory.D.gk.admitted.kFin_mem_smoothVecs DSIC.hKFinStab DSIC.hStabLink DSIC.hHWofType
    DSIC.hTypeOfHW

theorem hOrthCyc : OrthCyc := GlobalTheory.CompanionTheory.LowKType.orthCyc

theorem low_K_type_multiplicity_one_unconditional : LowKMultOneP := lowKMultOneP_of hMultAlg hKModExists cyclic_vectors_dense hOrthCyc

end CompanionTheory.D.LK
