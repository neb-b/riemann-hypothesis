module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008

@[expose] public section

noncomputable section

open GlobalTheory.DiscSpec

namespace GlobalTheory.Rigid

def strings {X ι : Type} [Fintype ι] (p : ι → X) (d : ι → ℕ) : Multiset (X × ℝ) :=
  ∑ i, (Finset.univ : Finset (Fin (d i))).val.map fun k => (p i, spehExp (d i) k)

end GlobalTheory.Rigid
