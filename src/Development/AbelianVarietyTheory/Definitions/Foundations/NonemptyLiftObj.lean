module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DatumCurveIntegralUnitDiscModel

@[expose] public section

noncomputable section
namespace GlobalTheory.Glob.IntegralWittCoefficients.Model
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric

def stdLat (E : Type) [Field E] [NumberField E] (N : ℕ) : Submodule (𝓞 E) (Fin N → E) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)

theorem mem_range_iff {E : Type} [Field E] [NumberField E] (x : E) :
    x ∈ (algebraMap (𝓞 E) E).range ↔ IsIntegral ℤ x :=
  ⟨by rintro ⟨a, rfl⟩; exact a.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

theorem mem_stdLat {E : Type} [Field E] [NumberField E] {N : ℕ} (x : Fin N → E) :
    x ∈ stdLat E N ↔ ∀ k, IsIntegral ℤ (x k) := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, forall_true_left, Submodule.mem_one]
  exact forall_congr' fun k => mem_range_iff (x k)

theorem isSDLat_std (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ) : IsSDLat E N (stdLat E N) := by
  have hs : ∀ k : Fin N, (Pi.single k 1 : Fin N → E) ∈ stdLat E N := fun k => by
    rw [mem_stdLat]
    intro j
    rw [Pi.single_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  refine ⟨Submodule.fg_pi fun _ => ?_, ?_, fun y => ⟨fun hy x hx => ?_, fun h => ?_⟩⟩
  · rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _
  · rw [eq_top_iff, ← (Pi.basisFun E (Fin N)).span_eq]
    refine Submodule.span_mono ?_
    rintro _ ⟨k, rfl⟩
    simpa using hs k
  · rw [mem_range_iff]
    rw [mem_stdLat] at hx hy
    exact IsIntegral.sum _ fun i _ => ((hx i).map (starRingEnd E).toIntAlgHom).mul (hy i)
  · rw [mem_stdLat]
    intro k
    have := h _ (hs k)
    rw [mem_range_iff] at this
    simpa [stdH, Pi.single_apply, apply_ite] using this

end GlobalTheory.Glob.IntegralWittCoefficients.Model
