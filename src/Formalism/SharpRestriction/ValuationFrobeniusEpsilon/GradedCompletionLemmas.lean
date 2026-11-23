module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.InstLocalRingSymplecticCoefficients

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.UnusedSlot38

open MvPowerSeries
open scoped Classical

variable {O : Type} [CommRing O] {a rk : ℕ} (wt : Fin a → (Fin rk → ℤ))

def monoWt (m : Fin a →₀ ℕ) : Fin rk → ℤ := m.sum fun i e => (e : ℤ) • wt i

def comp (j : Fin rk → ℤ) (f : MvPowerSeries (Fin a) O) : MvPowerSeries (Fin a) O :=
  fun m => if monoWt wt m = j then coeff m f else 0

end Formalism.MainNotions.UnusedSlot38
