module

public import Formalism.SharpRestriction.Bundle0001
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationCocycleLiftCriterion
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ExplicitFormulaErrorOfHostConditions
public import Formalism.ZetaNonvanishing.ZetaLandau

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.HC

def EAt (Λ : Level) (D : D7) (x eps C : ℝ) : Prop := EAtH Λ D.host.toHostRaw D.host.TT x eps C

def EFamC (Λ : Level) {eps : ℝ} (Fm : FamCore eps) : Prop :=
  ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, EAt Λ (Fm.D x i) x eps C

section

variable {Fam : ℝ → Type 1} (core : ∀ {eps : ℝ}, Fam eps → FamCore eps)
  (Tied : ∀ {eps : ℝ}, Fam eps → (eD eL K cHH eK CL x : ℝ) → Prop)

variable {core Tied}

end

end Formalism.HC

end
