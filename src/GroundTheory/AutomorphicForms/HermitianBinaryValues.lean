module

public import Mathlib
public import GroundTheory.AutomorphicForms.HermitianLocalSplit
public import GroundTheory.GlobalFields.Adele.Bundle0001
public import GroundTheory.GlobalFields.Adele.BaseChange.FiniteMap
public import GroundTheory.GlobalFields.LocalFieldAtPlace

@[expose] public section

noncomputable section

namespace GroundTheory.Automorphic

open NumberField IsDedekindDomain GroundTheory.Global Filter

section Algebra

variable {K : Type*} [Field K]

end Algebra

section Archimedean

open NumberField.InfinitePlace.Completion

variable {K : Type*} [Field K] {v : InfinitePlace K}

theorem continuous_ringEquivRealOfIsReal (hv : v.IsReal) :
    Continuous (ringEquivRealOfIsReal hv) := by
  have : (ringEquivRealOfIsReal hv : v.Completion → ℝ) = extensionEmbeddingOfIsReal hv := by
    ext x
    simp
  rw [this]
  exact (isometry_extensionEmbeddingOfIsReal hv).continuous

end Archimedean

section Main

open NumberField.InfinitePlace.Completion

universe u

variable {K : Type u} [Field K] [NumberField K]

section AtL

open scoped NumberField.LiesOver
open GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange

variable {γ t : K} [Fact (∀ r : K, r ^ 2 ≠ -γ + t * r)]

end AtL

end Main

end GroundTheory.Automorphic
