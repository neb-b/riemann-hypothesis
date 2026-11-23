module

public import Mathlib
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0001

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open CategoryTheory AlgebraicGeometry IsDedekindDomain TopologicalSpace Topology

universe u

class IsLocallyFactorial (X : Scheme.{u}) : Prop where
  ufm_stalk : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)

variable {X : Scheme.{u}}

instance (priority := 100) IsLocallyFactorial.isNormalScheme [IsIntegral X]
    [IsLocallyFactorial X] : IsNormalScheme X where
  isDomain_stalk _ := inferInstance
  isIntegrallyClosed_stalk x := by
    have := IsLocallyFactorial.ufm_stalk (X := X) x
    infer_instance

namespace PrimeDivisor

variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]


omit [IsLocallyNoetherian X] [IsNormalScheme X] in
lemma heightOneSpectrum_eq (x : PrimeDivisor X)
    (w : HeightOneSpectrum (X.presheaf.stalk x.point)) : w = x.heightOneSpectrum := by
  have := x.dimensionLEOne_stalk
  have hmax : w.asIdeal.IsMaximal := Ring.DimensionLEOne.maximalOfPrime w.ne_bot w.isPrime
  ext1
  exact IsLocalRing.eq_maximalIdeal hmax

lemma ord_nonneg_iff (x : PrimeDivisor X) {f : X.functionField} (hf : f ≠ 0) :
    0 ≤ x.ord f ↔ f ∈ (algebraMap (X.presheaf.stalk x.point) X.functionField).range := by
  have := x.isDedekindDomain_stalk
  have hv0 : x.valuation f ≠ 0 := (Valuation.ne_zero_iff _).mpr hf
  have key : 0 ≤ x.ord f ↔ x.valuation f ≤ 1 := by
    simp only [ord, Left.nonneg_neg_iff]
    rw [WithZero.log_le_iff_le_exp hv0]
    simp
  rw [key]
  constructor
  · intro h
    apply HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro w
    rw [x.heightOneSpectrum_eq w]
    exact h
  · rintro ⟨a, rfl⟩
    simp only [valuation]
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_le_one _ _

end PrimeDivisor

section Algebra

variable {A : Type*} [CommRing A] [IsDomain A] (p : Ideal A) [p.IsPrime]

end Algebra

section Hartogs

end Hartogs

section Affine

variable {U : X.Opens} (hU : IsAffineOpen U)


variable [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]

end Affine

section Uniformizer

variable [IsIntegral X] [IsLocallyNoetherian X] [IsLocallyFactorial X]

end Uniformizer

section LocallyPrincipal

variable [IsIntegral X] [IsNoetherian X] [IsLocallyFactorial X]

end LocallyPrincipal

section Regular

variable [IsIntegral X] [IsLocallyNoetherian X] [IsLocallyFactorial X]

end Regular

section Regular

variable [IsIntegral X] [IsLocallyNoetherian X] [IsLocallyFactorial X]

end Regular

end GroundTheory.Arith.SchemeCoh
