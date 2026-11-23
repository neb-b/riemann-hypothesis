module

public import Mathlib
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Formalism.SatakeDualWeyl.Statement

@[expose] public section

noncomputable section

namespace Formalism.MJ

open Matrix
open scoped ComplexOrder

def moeb {p q : ℕ} (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    (z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin p) (Fin q) ℂ :=
  (g.toBlocks₁₁ * z + g.toBlocks₁₂) * (g.toBlocks₂₁ * z + g.toBlocks₂₂)⁻¹

def hcDom (p q : ℕ) : Set (Matrix (Fin p) (Fin q) ℂ) :=
  {z | (1 - zᴴ * z).PosDef}

def vecOf {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) : Fin p × Fin q → ℂ := fun x => z x.1 x.2

end Formalism.MJ
