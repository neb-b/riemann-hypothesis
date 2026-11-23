module

public import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.Divisibility.CoeffLemmas
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0003
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleWeightMiddleEntries

@[expose] public section

open NumberField IsDedekindDomain IntermediateField

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.Host Formalism.L2.DIV

instance fin_KQ (d : ℕ) : FiniteDimensional ℚ (KQ d) := fin_sqQ _

instance normal_KQ (d : ℕ) : Normal ℚ (KQ d) := normal_sqQ _

def quadFields (d : ℕ) (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ d ≤ LL) : Fields where
  F := ℚ
  E := KQ d
  K := CoF ι LL
  nfE := { to_charZero := inferInstance, to_finiteDimensional := fin_KQ d }
  starE := starLL ι (KQ d)
  Tau := Unit
  emb := fun _ => (tauLL hE (KQ d).val).toRingHom

section QuadOk

variable (d : ℕ) (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ d ≤ LL)

end QuadOk

section DegTwo

variable (X : Fields)

theorem conjO_coe (x : 𝓞 X.E) : ((X.conjO x : 𝓞 X.E) : X.E) = star (x : X.E) := rfl

theorem conjO_conjO (x : 𝓞 X.E) : X.conjO (X.conjO x) = x := by
  apply RingOfIntegers.ext
  rw [conjO_coe, conjO_coe, star_star]

end DegTwo

section Gauss

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ 1 ≤ LL)

def iQb : Qb := Classical.choose (exists_sqrt (-((1 : ℕ) : ℤ)))

theorem iQb_mem : iQb ∈ sqrts (-((1 : ℕ) : ℤ)) := Classical.choose_spec (exists_sqrt (-((1 : ℕ) : ℤ)))

abbrev gaussFields : Fields := quadFields 1 ι LL hE

def iE : (gaussFields ι LL hE).E := (⟨iQb, sqrts_sub _ iQb_mem⟩ : KQ 1)


end Gauss

section Roots

end Roots

section GaussChars

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ 1 ≤ LL)

end GaussChars

section GaussChars2

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ 1 ≤ LL)

end GaussChars2

section Gauss

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ 1 ≤ LL)

end Gauss

end Formalism.L2.Col
