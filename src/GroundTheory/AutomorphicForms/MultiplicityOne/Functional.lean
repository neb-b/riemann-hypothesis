module

public import Mathlib
public import GroundTheory.AutomorphicForms.MultiplicityOne.Equivariance

@[expose] public section

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace MultiplicityOne

open Reduction AutomorphicForm RightCosetSpace CuspidalSpectrum FourierWhittaker

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem continuous_adelicChar_neg_supSum :
    Continuous fun X : Pos n → 𝔸[K] => (GroundTheory.Global.adelicChar K (-supSum 0 X) : ℂ) :=
  continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (continuous_supSum 0).neg)

variable (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]

variable {μ}


variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]



end MultiplicityOne

end

end GroundTheory.Automorphic
