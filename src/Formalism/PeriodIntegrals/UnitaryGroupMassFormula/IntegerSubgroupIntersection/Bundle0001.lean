module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerSubgroupIntersection.IntInter
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerSubgroupIntersection.Imports
section
noncomputable section

namespace PI.GaugeCharW

theorem extChar : ExtChar := by
  intro G _ _ _ K U hU g hg hKU
  let j : K →+ G ⧸ U := (QuotientAddGroup.mk' U).comp K.subtype
  have hker : ∀ k ∈ j.ker, g.comp K.subtype k = 0 := by
    intro k hk
    have hkU : (k : G) ∈ U := (QuotientAddGroup.eq_zero_iff _).mp hk
    exact hKU k k.2 hkU
  let g' : K ⧸ j.ker →+ AddCircle (1 : ℝ) := QuotientAddGroup.lift j.ker (g.comp K.subtype) hker
  obtain ⟨η', hη'⟩ := (Module.Baer.of_divisible (AddCircle (1 : ℝ))).extension_property_addMonoidHom
    (QuotientAddGroup.kerLift j) (QuotientAddGroup.kerLift_injective j) g'
  let η : G →+ AddCircle (1 : ℝ) := η'.comp (QuotientAddGroup.mk' U)
  have hηU : ∀ x ∈ U, η x = 0 := fun x hx => by
    show η' (QuotientAddGroup.mk' U x) = 0
    rw [QuotientAddGroup.mk'_apply, (QuotientAddGroup.eq_zero_iff x).mpr hx, map_zero]
  refine ⟨g - η, ?_, ?_, ?_⟩
  · refine continuous_of_continuousAt_zero (g - η) ?_
    have hmem : (U : Set G) ∈ nhds (0 : G) := hU.mem_nhds U.zero_mem
    refine hg.continuousAt.congr ?_
    filter_upwards [hmem] with u hu
    rw [AddMonoidHom.sub_apply, hηU u hu, sub_zero]
  · intro x hx
    have h1 : η x = g' (QuotientAddGroup.mk (⟨x, hx⟩ : K)) := by
      rw [← hη']; rfl
    rw [AddMonoidHom.sub_apply, h1]
    show g x - (g.comp K.subtype) ⟨x, hx⟩ = 0
    exact sub_self _
  · intro x hx
    rw [AddMonoidHom.sub_apply, hηU x hx, sub_zero]

end PI.GaugeCharW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerSubgroupIntersection.IntInterAlt
section
namespace PI.GaugeCharW

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem intInter : IntInter := by
  intro F _ _ a ha
  have h : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F a ≤ 1 := by
    intro v
    have h1 := ha v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1
    rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a]
    exact h1
  obtain ⟨b, hb⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F a h
  exact ⟨b, hb⟩

theorem openInt : OpenInt := by
  intro F _ _
  exact RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)

end PI.GaugeCharW
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IntegerSubgroupIntersection.IsOpenIntSub
section
noncomputable section

namespace PI.GaugeCharW

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section

variable (F : Type) [Field F] [NumberField F]

def intSub : AddSubgroup (AF F) where
  carrier := {x | ∀ v : HeightOneSpectrum (𝓞 F), sndA F x v ∈ v.adicCompletionIntegers F}
  add_mem' {a b} ha hb v := by
    rw [map_add (f := _)]
    exact add_mem (ha v) (hb v)
  zero_mem' v := by
    rw [map_zero]
    exact zero_mem _
  neg_mem' {a} ha v := by
    rw [map_neg]
    exact neg_mem (ha v)

theorem isOpen_intSub (h3 : OpenInt) : IsOpen (intSub F : Set (AF F)) := by
  exact (h3 F).preimage (continuous_snd : Continuous (Prod.snd : Ainf F × Af F → Af F))

end

end PI.GaugeCharW
end
end

