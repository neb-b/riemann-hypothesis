module

public import Formalism.ThetaLogCoordinates.TraceIsometryWeights.StatementC
public import Formalism.MahlerMeasure.Bundle0007

@[expose] public section

namespace Formalism.InvariantFactorPaths.PW

open MvPolynomial Finset Formalism.GM.M Formalism.GM

def DischargeP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (ρ : Fin r) (e1 : ℕ), kapC p r LL.total ≤ e1 → HypP p LL ρ e1

def DischargeW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (e1 : ℕ), kapC p r LL.total ≤ e1 → HypW p (r := r) LL e1

def DischargeE : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (ρ : Fin r) (e1 : ℕ), kapC p r LL.total ≤ e1 → HypE p LL ρ e1

end Formalism.InvariantFactorPaths.PW
