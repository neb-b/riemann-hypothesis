module

public import Mathlib
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
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.Bridge
public import Development.AutomorphicSpectrum.Proofs.SemilocalMultiplicity.DsInfCharCap

@[expose] public section

namespace GlobalTheory.CompanionTheory.TypeCount.LowK

open CompanionTheory.D.LK

theorem hGenCO : GenCO := genCO_of koszul_differential_sq_zero (cover2_of (acycAbs_of koszul_differential_sq_zero))

theorem hInj : Inj :=
  inj_of (vanK_of (cok_of hGenCO) GlobalTheory.CompanionTheory.LKWtProj.wtProj
    (GlobalTheory.CompanionTheory.KWeightMajor.wtMajor_of GlobalTheory.CompanionTheory.TransS.InfChar.hLowSpan)) GlobalTheory.CompanionTheory.LKWtProj.wtProj koszul_differential_sq_zero

theorem hMultAlg : MultAlg :=
  multAlg_of GlobalTheory.CompanionTheory.TransS.InfChar.hLowSpan GlobalTheory.CompanionTheory.TransS.InfChar.hHWMap GlobalTheory.CompanionTheory.LKDens.dens
    GlobalTheory.CompanionTheory.LKInvLift.invLift GlobalTheory.CompanionTheory.HCdecomp.hcdec hGenCO top_degree_cycle hInj

theorem hKModExists : KModExists :=
  GlobalTheory.CompanionTheory.KModExists.kModExists GlobalTheory.CompanionTheory.TransS.InfChar.hSmMod CompanionTheory.D.gk.admitted.kFin_mem_smoothVecs
    GlobalTheory.CompanionTheory.TransS.InfChar.hKFinStab GlobalTheory.CompanionTheory.TransS.InfChar.hStabLink GlobalTheory.CompanionTheory.TransS.InfChar.hHWofType
    GlobalTheory.CompanionTheory.TransS.InfChar.hTypeOfHW

theorem hOrthCyc : OrthCyc := GlobalTheory.CompanionTheory.LowKType.orthCyc

theorem lowKMultOneP : LowKMultOneP := lowKMultOneP_of hMultAlg hKModExists cyclic_vectors_dense hOrthCyc

theorem lowKMultOne : Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOne := low_K_type_multiplicity_one_of lowKMultOneP

end GlobalTheory.CompanionTheory.TypeCount.LowK
