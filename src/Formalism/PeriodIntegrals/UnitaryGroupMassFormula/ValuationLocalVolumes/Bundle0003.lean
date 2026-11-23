module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.LocVol
public import Formalism.LocalRingCardinality.SpanPowerMembership.Adelic
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0002

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.AriEta
section
noncomputable section

open Polynomial IsDedekindDomain NumberField IsLocalRing
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.NcVal.AriEta

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem val_int (x : 𝓞 F) : Valued.v (((x : F) : v.adicCompletion F)) ≤ 1 := by
  have h : Valued.v (((x : F) : v.adicCompletion F)) = v.valuation F (x : F) :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : F)
  rw [h]
  exact v.valuation_le_one x

theorem val_int_lt (x : 𝓞 F) (hx : x ∈ v.asIdeal) : Valued.v (((x : F) : v.adicCompletion F)) < 1 := by
  have h : Valued.v (((x : F) : v.adicCompletion F)) = v.valuation F (x : F) :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : F)
  rw [h]
  exact (v.valuation_lt_one_iff_mem x).mpr hx

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

end Formalism.L2.SG.Pf.NcVal.AriEta
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.DVIsDiffVal
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem dV_isDiffVal : IsDiffVal v (dV v) := by
  have h : ∃ d, IsDiffVal v d := diffExists v
  unfold dV
  rw [dite_eq_left h]
  exact h.choose_spec

theorem val_pow_le (k : ℕ) (x : 𝓞 F) (hx : x ∈ differentIdeal ℤ (𝓞 F) ^ k) :
    Valued.v (algebraMap F (Fv F v) (x : F)) ≤ Valued.v (dV v) ^ k := by
  have hint : ∀ y : 𝓞 F, Valued.v (algebraMap F (Fv F v) (y : F)) ≤ 1 := by
    intro y
    have e := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v y
    have hle := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := F) v y
    exact e.le.trans hle
  induction k generalizing x with
  | zero =>
    rw [pow_zero]
    exact hint x
  | succ k ih =>
    rw [pow_succ'] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · have h1 := (dV_isDiffVal v).2.1 a ha
      have h2 := ih b hb
      rw [show ((a * b : 𝓞 F) : F) = (a : F) * (b : F) from rfl, map_mul, map_mul, pow_succ']
      exact mul_le_mul' h1 h2
    · rw [show ((a + b : 𝓞 F) : F) = (a : F) + (b : F) from rfl, map_add (f := _)]
      exact Valuation.map_add_le _ ha hb

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
end
end

