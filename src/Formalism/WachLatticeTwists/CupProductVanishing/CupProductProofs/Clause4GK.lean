module

public import Formalism.WachLatticeTwists.CupProductVanishing.Bundle0001
public import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
public import Formalism.WachLatticeTwists.CharacterSplitJumps.CharacterJumpProofs.MemAnnih
public import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.Bundle0001
public import Formalism.WachLatticeTwists.LatticeDualFibres.Statement
public import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient
public import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.ExistsPowSmulIntegral
public import Formalism.WachLatticeTwists.LatticeDualFibres.StatDualFibreLattice
public import Formalism.WachLatticeTwists.CupProductVanishing.CupProductProofs.Bundle0001
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.Bundle0001

@[expose] public section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG (KO annih)
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsFGTop NatInv)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.T2

theorem clause4GK : CupClauseGK := by
  intro p _ K O _ _ _ _ A T' G _ _ _ _ _ _ _ _ r χ E Dw _ ε hK hO e hε hA
  obtain ⟨F⟩ := ReciprocityTheory.ChartRestriction.T2.natInv_all_iso hK hO e (ε := ε.comp Dw.subtype) hε
  exact clause4 O A T' G r χ E Dw ε hA ⟨F⟩

end Formalism.RepresentationBoundsCohomology.T2
