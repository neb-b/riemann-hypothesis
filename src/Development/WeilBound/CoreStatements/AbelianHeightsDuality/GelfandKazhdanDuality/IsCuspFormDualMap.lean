module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008

@[expose] public section

noncomputable section

open NumberField Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace PositivityTheory.PRW.GKD

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


variable (E a) in
abbrev invA : GA E a →* GA E a := invT a (Ad E)

theorem invA_invA (g : GA E a) : invA E a (invA E a g) = g := by
  apply Units.ext
  exact Matrix.transpose_transpose g.val

end PositivityTheory.PRW.GKD

end
