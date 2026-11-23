module

public import Formalism.PeriodIntegrals.Bundle0016

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.DSIC

open PI.DSInfCharCap
open scoped InnerProductSpace Matrix

def QdetConjInv : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A), Formalism.REAL.GlRel E →
    ∀ g : Matrix (Fin n) (Fin n) ℂ, IsUnit g → ∀ u : ℂ,
      Formalism.REAL.qdet (fun a b => ∑ c, ∑ d, (g c a * g⁻¹ b d) • E c d) u = Formalism.REAL.qdet E u

end PI.UnitaryGroupMassFormula.DSIC
