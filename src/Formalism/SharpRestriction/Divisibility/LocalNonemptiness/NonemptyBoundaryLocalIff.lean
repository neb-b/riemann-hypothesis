module

public import Formalism.SharpRestriction.Divisibility.BoundaryLocalData

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.DIV.Inh

open Formalism.BasicNotions NumberField Formalism.MainNotions

def integersConjugation (D : D7) : 𝓞 D.host.E →+* 𝓞 D.host.E :=
  RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)

theorem integers_conjugation_coe (D : D7) (c : 𝓞 D.host.E) : ((integersConjugation D c : 𝓞 D.host.E) : D.host.E) = D.host.conj (c : D.host.E) := rfl

def XT (_D : D7) (Y : Type) : Type := Y

instance (D : D7) (Y : Type) [AddCommGroup Y] : AddCommGroup (XT D Y) := inferInstanceAs (AddCommGroup Y)

instance (D : D7) (Y : Type) [AddCommGroup Y] [Module (𝓞 D.host.E) Y] : Module (𝓞 D.host.E) (XT D Y) :=
  Module.compHom Y (integersConjugation D)

def XT.mk (D : D7) (Y : Type) [AddCommGroup Y] : Y ≃+ XT D Y := AddEquiv.refl Y

theorem XT.smul_mk (D : D7) {Y : Type} [AddCommGroup Y] [Module (𝓞 D.host.E) Y] (c : 𝓞 D.host.E) (a : Y) :
    c • XT.mk D Y a = XT.mk D Y (integersConjugation D c • a) := rfl

theorem XT.symm_smul (D : D7) {Y : Type} [AddCommGroup Y] [Module (𝓞 D.host.E) Y] (c : 𝓞 D.host.E) (χ : XT D Y) :
    (XT.mk D Y).symm (c • χ) = integersConjugation D c • (XT.mk D Y).symm χ := rfl

theorem exists_alp (D : D7) (p n : ℕ) (h : ModuliIntegralCharts.NHyp D p n) : ∃ α : 𝓞 D.host.E,
    (α : D.host.E) * D.host.conj (α : D.host.E) = (n : D.host.E) ∧
    ((∃ mm : ℕ, n = mm ^ 2 ∧ α = (mm : 𝓞 D.host.E)) ∨ (α : D.host.E) ∈ D.host.K) := by
  obtain ⟨-, -, h⟩ := h
  rcases h with ⟨mm, rfl⟩ | ⟨π, hK, hπ⟩
  · refine ⟨(mm : 𝓞 D.host.E), ?_, Or.inl ⟨mm, rfl, rfl⟩⟩
    have h1 : ((mm : 𝓞 D.host.E) : D.host.E) = (mm : D.host.E) := by
      first
      | simp
      | norm_cast
    rw [h1, map_natCast]
    push_cast
    ring
  · exact ⟨π, hπ, Or.inr hK⟩

end Formalism.MainNotions.DIV.Inh

end
