module

public import Mathlib
public import Formalism.SatakeDualWeyl.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelProductIndex.ZeroMemLatSet
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelProductIndex.Development
public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.Bundle0004

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.G

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem finite_setOf_mem_asIdeal {x : 𝓞 F} (hx : x ≠ 0) : {v : HeightOneSpectrum (𝓞 F) | x ∈ v.asIdeal}.Finite := by
  have hI : (Ideal.span {x} : Ideal (𝓞 F)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hx
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  exact Ideal.dvd_span_singleton.mpr hv

end Formalism.L2.G
