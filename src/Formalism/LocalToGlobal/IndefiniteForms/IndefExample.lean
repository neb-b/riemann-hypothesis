module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ConjugateWeightLatticeOfGeneral
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.KappaNormalise
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic

@[expose] public section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.L2.Indef.Examples₂

open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K]

variable {K}

end Std

section Amb

variable {K : Type} [Field K] [NumberField K] [StarRing K]

end Amb

namespace one

variable (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K)

end one

namespace two

open scoped Classical

variable (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K)
  (S : Finset (HeightOneSpectrum (𝓞 K))) (a : K) (kap l : InfinitePlace K → ℝ)

variable {K v0 S a kap l}

variable (K v0 S a kap l)

variable {K v0 S a kap l}

end two

section Pair

variable {K : Type} [Field K] [NumberField K] [StarRing K]


end Pair

section Concrete

open NumberField.IsCMField

abbrev K3 := CyclotomicField 3 ℚ

end Concrete

end Formalism.L2.Indef.Examples₂
