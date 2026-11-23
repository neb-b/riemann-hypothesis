module

public import Mathlib
public import Formalism.PairingDivisors.StatementH

@[expose] public section

-- bundled from Formalism.PairingDivisors.StatementA
section
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw conjPl)

noncomputable section

namespace Formalism.PairingDivisionLocalBalance

def eq {k : Type} [Field k] (q : ℕ) (s : ℕ) (Y : k) : k :=
  (1 - Y * ((q : k) ^ s)⁻¹) * (1 - Y⁻¹ * ((q : k) ^ s)⁻¹) + ((q : k) - 1) * (((q : k) ^ s)⁻¹) ^ 2

end Formalism.PairingDivisionLocalBalance
end
end

-- bundled from Formalism.PairingDivisors.StatementX
section
open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw lw conjPl)

noncomputable section

namespace Formalism.PairingDivisionLocalBalance

def HtLe {K : Type} [Field K] [NumberField K] [StarRing K] (g : Pl K → ℤ) (z : K) (B : ℝ) : Prop :=
  (Function.support fun w : Pl K => lw w * |((vw w z + g w : ℤ) : ℝ)|).Finite ∧
  ∑ᶠ w : Pl K, lw w * |((vw w z + g w : ℤ) : ℝ)| ≤ B

end Formalism.PairingDivisionLocalBalance
end
end

