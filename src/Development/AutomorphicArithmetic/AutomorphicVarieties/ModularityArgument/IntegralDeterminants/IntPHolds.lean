module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.IntegralDeterminants.IntPOfDesc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BaseChangeDescent.BcBackOffT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt

@[expose] public section

namespace UpperTheory.V.Z.Int

theorem intP_holds : UpperTheory.V.Br.IntP := intP_of_desc UpperTheory.Gal.Desc.descOffT

theorem intK_holds : UpperTheory.V.Af.IntK := intK_of_desc UpperTheory.Gal.Desc.descOffT

theorem intP' : UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Br.IntP := fun _ => intP_holds

theorem intK' : UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.IntK := fun _ => intK_holds

end UpperTheory.V.Z.Int
