module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalGaloisCompatibility.ToralDeRham.GaloisCompatUnlinkedSupportOfSpherical
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineInputs.InputsOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.MixedUnlinkedExponents.CharLiftPrimeHolds

@[expose] public section

namespace UpperTheory.Gal.ToralGalois

theorem inq_holds : Inq := ⟨UpperTheory.Gal.Int.Inp.inp_holds, UpperTheory.Gal.GamX.charLiftPrime_holds⟩

theorem galoisCompat_unlinkedSupport_of_spherical : GlobalTheory.RoadU.CoreAll → GlobalTheory.DeRhamOfPlainTorus.R1 := GalTw.GlobalTheory.DeRhamOfPlainTorus.galoisCompat_unlinkedSupport_of_spherical inq_holds

end UpperTheory.Gal.ToralGalois
