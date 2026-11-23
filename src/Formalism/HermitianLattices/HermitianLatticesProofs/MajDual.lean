module

public import Mathlib
public import Formalism.HermitianLattices.Bundle0002
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0004

@[expose] public section

open NumberField
open scoped nonZeroDivisors

noncomputable section

namespace Formalism.HermitianLatticesTheory

section
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

end

section
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

end

section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]

lemma majDual_star_int (r : RingOfIntegers K) : IsIntegral ℤ (star (r : K)) := by
  exact (NumberField.RingOfIntegers.isIntegral_coe r).map (starRingEnd K).toIntAlgHom

end

section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]

end

section
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

variable [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]

end

end Formalism.HermitianLatticesTheory
