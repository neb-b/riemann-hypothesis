module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne

@[expose] public section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.Published

def GelfandKazhdanDual : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (n : ℕ) (π : CuspSub E n), Paired π π invTOp

end GlobalTheory.Published

end
