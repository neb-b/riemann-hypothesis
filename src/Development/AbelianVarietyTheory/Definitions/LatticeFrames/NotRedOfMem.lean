module

public import Mathlib
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002

@[expose] public section

noncomputable section

namespace GlobalTheory.Klein

open Formalism.L2.Th1.F
open scoped ComplexConjugate

variable {p : ℕ} [Fact p.Prime]

def Good (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r : ℂ) : Prop :=
  p ≠ 2 ∧ ‖ι (12 * r)‖ ≤ 1 ∧ ‖ι (12 * r ^ 2 - L.g₂)‖ ≤ 1 ∧ ‖ι (4 * r ^ 3 - L.g₂ * r - L.g₃)‖ ≤ 1 ∧
    ‖ι (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)‖ = 1

def Red (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r z : ℂ) : Prop :=
  z ∉ L.lattice ∧ ‖ι (L.weierstrassP z - r)‖ ≤ 1

theorem not_red_of_mem (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r : ℂ) {z : ℂ} (h : z ∈ L.lattice) : ¬ Red ι L r z :=
  fun h' => h'.1 h

end GlobalTheory.Klein
