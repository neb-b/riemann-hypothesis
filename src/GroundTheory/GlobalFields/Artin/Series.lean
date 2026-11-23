module

public import Mathlib
public import GroundTheory.GlobalFields.Artin.LogCharpoly
public import GroundTheory.GlobalFields.TateThesis.HeckeLFunction
public import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

open IsDedekindDomain NumberField Filter Topology ComplexConjugate

namespace GroundTheory.Global

section Average

variable {G : Type*} [Group G]

end Average

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

section LocalAverage

variable (v : HeightOneSpectrum (𝓞 K))

end LocalAverage





section Convergence

omit [IsGalois K L] in
theorem exists_norm_le (f : Gal(L/K) → ℂ) : ∃ C, ∀ g, ‖f g‖ ≤ C := by
  classical
  have := Fintype.ofFinite Gal(L/K)
  exact ⟨∑ g, ‖f g‖, fun g => Finset.single_le_sum (fun x _ => norm_nonneg (f x))
    (Finset.mem_univ g)⟩

end Convergence

section Holomorphy

end Holomorphy

section Additivity

end Additivity

section Conjugation

end Conjugation

end GroundTheory.Global
