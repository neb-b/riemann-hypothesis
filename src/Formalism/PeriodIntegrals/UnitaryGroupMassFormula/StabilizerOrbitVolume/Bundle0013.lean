module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensHL
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0012

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensHH
section
noncomputable section

namespace PI.VolStabSW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  Matrix

section Mat

variable {A : Type} [CommRing A] (s : A →+* A)

end Mat

section Int

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))

variable {b v}

theorem sigR_incl (σ : E →ₐ[F] E) (e : E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (inclR (Fv F v) e) = inclR (Fv F v) (σ e) := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, inclR, Algebra.TensorProduct.map_tmul]

theorem sigR_smul (σ : E →ₐ[F] E) (c : Fv F v) (z : Fv F v ⊗[F] E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ (c • z) = c • Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ z := by
  rw [Algebra.smul_def, map_mul, sigR_algebraMap, ← Algebra.smul_def]

end Int

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensHI
section
noncomputable section

namespace PI.VolStabSW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW

theorem measure_eq_relIndex_mul {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V]
    (μ : Measure V) [μ.IsAddLeftInvariant] (Λ L : AddSubgroup V) (hΛL : Λ ≤ L)
    (hL : MeasurableSet (L : Set V)) (hΛ : MeasurableSet (Λ : Set V)) (hfin : Λ.relIndex L ≠ 0) :
    μ L = (Λ.relIndex L : ENNReal) * μ Λ := by
  have emb : MeasurableEmbedding ((↑) : L → V) := MeasurableEmbedding.subtype_coe hL
  have hadd : ∀ g : L, Measurable (fun x : L => g + x) := fun g =>
    ((measurable_const_add (g : V)).comp measurable_subtype_coe).subtype_mk
  have : MeasurableAdd L := ⟨hadd, fun g =>
    ((measurable_add_const (g : V)).comp measurable_subtype_coe).subtype_mk⟩
  have : (Λ.addSubgroupOf L).FiniteIndex := ⟨hfin⟩
  have : (μ.comap ((↑) : L → V)).IsAddLeftInvariant := by
    refine ⟨fun g => ?_⟩
    ext s hs
    rw [Measure.map_apply (hadd g) hs, emb.comap_apply, emb.comap_apply]
    have e : ((↑) : L → V) '' ((fun x : L => g + x) ⁻¹' s) =
        (fun x : V => (g : V) + x) ⁻¹' (((↑) : L → V) '' s) := by
      ext x
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨g + y, hy, rfl⟩
      · rintro ⟨z, hz, hzx⟩
        have hxL : x ∈ L := by
          have : x = (z : V) - g := by rw [hzx]; abel
          rw [this]
          exact L.sub_mem z.2 g.2
        refine ⟨⟨x, hxL⟩, ?_, rfl⟩
        have : g + (⟨x, hxL⟩ : L) = z := Subtype.ext (by simp [hzx])
        rw [this]
        exact hz
    rw [e, measure_preimage_add]
  have key := AddSubgroup.index_mul_measure (Λ.addSubgroupOf L)
    (measurable_subtype_coe hΛ) (μ.comap ((↑) : L → V))
  rw [emb.comap_apply, emb.comap_apply, Set.image_univ, Subtype.range_coe] at key
  have e2 : ((↑) : L → V) '' ((Λ.addSubgroupOf L : AddSubgroup L) : Set L) = Λ := by
    ext x
    simp only [Set.mem_image, SetLike.mem_coe, AddSubgroup.mem_addSubgroupOf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hΛL hx⟩, hx, rfl⟩
  rw [e2] at key
  rw [← key]
  rfl

end PI.VolStabSW
end
end

