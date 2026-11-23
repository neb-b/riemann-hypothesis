module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0236

@[expose] public section

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.LinRed

namespace GlobalTheory.CompanionTheory.Hypotheses₂

namespace HCSS

variable {n : ℕ}

def lieOf (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {X | ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G}

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

end HCSS

namespace HCSS

variable {n : ℕ}

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {G : Set (Matrix (Fin n) (Fin n) ℂ)}
  {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

end HCSS

end GlobalTheory.CompanionTheory.Hypotheses₂

end
