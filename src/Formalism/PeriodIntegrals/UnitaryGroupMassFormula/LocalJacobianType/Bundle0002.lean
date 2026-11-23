module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0013
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.BoxMulAlt
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain PI.LocJacTyp
open scoped TensorProduct Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def OTop : Prop :=
  IsCompact (OEv (E := E) v) ∧ IsOpen (OEv (E := E) v) ∧
  (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v ∧
  (∀ x ∈ OEv (E := E) v, ∀ y ∈ OEv (E := E) v, x * y ∈ OEv (E := E) v) ∧
  (∀ x ∈ OEv (E := E) v, ∀ y ∈ OEv (E := E) v, x + y ∈ OEv (E := E) v) ∧
  (∀ x ∈ OEv (E := E) v, -x ∈ OEv (E := E) v) ∧
  (∀ t ∈ v.adicCompletionIntegers F, ∀ x ∈ OEv (E := E) v, sc (E := E) v t * x ∈ OEv (E := E) v) ∧
  (∀ σ : E →ₐ[F] E, ∀ x ∈ OEv (E := E) v, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ x ∈ OEv (E := E) v)

def BoxMul : Prop :=
  ∀ (ι : Type) [Fintype ι] (μ : Measure (ι → Fv F v ⊗[F] E)) [μ.IsAddHaarMeasure]
    (y : ι → Fv F v ⊗[F] E), (∀ i, IsUnit (y i)) →
    (μ (Set.univ.pi fun i => {c | y i * c ∈ OEv (E := E) v})).toReal =
      (μ (Obox (E := E) v ι)).toReal * ∏ i, (absV v (Algebra.norm (Fv F v) (y i)))⁻¹

end PI.UnitaryGroupMassFormula.LocJacTyp
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ExpProductSquareInv
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain PI.LocJacTyp
open scoped Classical

section Count

end Count

section Real

open Real

variable (r : ℕ)

end Real

section Final

open Real

end Final

section AbsProd

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

def absVHom : Fv F v →* ℝ where
  toFun := absV v
  map_one' := absV_one v
  map_mul' := absV_mul v

theorem absV_prod {ι : Type} (s : Finset ι) (f : ι → Fv F v) :
    absV v (∏ i ∈ s, f i) = ∏ i ∈ s, absV v (f i) :=
  map_prod (absVHom v) f s

end AbsProd

end PI.UnitaryGroupMassFormula.LocJacTyp
end
end

