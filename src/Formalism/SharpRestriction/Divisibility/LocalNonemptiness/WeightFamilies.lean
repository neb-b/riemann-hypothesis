module

public import Formalism.SharpRestriction.Divisibility.WeightFamilies

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.DIV.Inh

open Formalism.BasicNotions NumberField

def OsRingOfIntegers (D : D7) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : NumberField K), Nonempty (𝓞 K ≃+* D.what₂.O)

def OsConcrete (D : D7) : Prop :=
  Function.Injective D.what₂.OtoLL ∧ ∃ K : IntermediateField ℚ D.what₂.LL,
    Set.range D.what₂.OtoLL = {x | x ∈ K ∧ IsIntegral ℤ x}

theorem OsRingOfIntegers_of_concrete (D : D7) (h : OsConcrete D) : OsRingOfIntegers D := by
  obtain ⟨hinj, K, hK⟩ := h
  letI : NumberField D.what₂.LL := D.nfLL
  haveI : FiniteDimensional ℚ K := inferInstance
  haveI : NumberField K := { to_charZero := inferInstance, to_finiteDimensional := inferInstance }
  let g : 𝓞 K →+* D.what₂.LL := (algebraMap K D.what₂.LL).comp (algebraMap (𝓞 K) K)
  have hg : Function.Injective g :=
    (algebraMap K D.what₂.LL).injective.comp (IsFractionRing.injective (𝓞 K) K)
  have hrange : g.range = D.what₂.OtoLL.range := by
    ext y
    rw [RingHom.mem_range, RingHom.mem_range]
    constructor
    · rintro ⟨a, rfl⟩
      have hy : g a ∈ Set.range D.what₂.OtoLL := by
        rw [hK, Set.mem_setOf_eq]
        exact ⟨(algebraMap (𝓞 K) K a).2,
          IsIntegral.algebraMap (R := ℤ) (A := K) (B := D.what₂.LL)
            ((IsIntegralClosure.isIntegral_iff (A := 𝓞 K) (R := ℤ) (B := K)).mpr ⟨a, rfl⟩)⟩
      exact hy
    · rintro ⟨x, rfl⟩
      have hx : D.what₂.OtoLL x ∈ Set.range D.what₂.OtoLL := ⟨x, rfl⟩
      rw [hK, Set.mem_setOf_eq] at hx
      obtain ⟨hxK, hxI⟩ := hx
      have hz : IsIntegral ℤ (⟨D.what₂.OtoLL x, hxK⟩ : K) :=
        (isIntegral_algebraMap_iff ).mp hxI
      obtain ⟨a, ha⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 K) (R := ℤ) (B := K)).mp hz
      refine ⟨a, ?_⟩
      show algebraMap K D.what₂.LL (algebraMap (𝓞 K) K a) = _
      rw [ha]
      rfl
  exact ⟨K, inferInstance, inferInstance, ⟨(RingEquiv.ofBijective g.rangeRestrict
    ⟨fun a b hab => hg (by have h := congrArg Subtype.val hab; exact h), g.rangeRestrict_surjective⟩).trans
    ((RingEquiv.subringCongr hrange).trans (RingEquiv.ofBijective D.what₂.OtoLL.rangeRestrict
      ⟨fun a b hab => hinj (by have h := congrArg Subtype.val hab; exact h), D.what₂.OtoLL.rangeRestrict_surjective⟩).symm)⟩⟩

end Formalism.MainNotions.DIV.Inh

end
