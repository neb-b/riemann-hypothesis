module

public import Mathlib

@[expose] public section

open NumberField
open scoped ComplexConjugate

namespace GlobalTheory

structure CMType (E : Type*) [Field E] where

  carrier : Set (E →+* ℂ)

  mem_iff_conjugate_notMem' : ∀ τ, τ ∈ carrier ↔ ComplexEmbedding.conjugate τ ∉ carrier

namespace CMType

section Field

variable {E : Type*} [Field E]

instance : SetLike (CMType E) (E →+* ℂ) where
  coe := carrier
  coe_injective := by
    rintro ⟨a, _⟩ ⟨b, _⟩ h
    congr

theorem mem_iff_conjugate_notMem (Φ : CMType E) (τ : E →+* ℂ) :
    τ ∈ Φ ↔ ComplexEmbedding.conjugate τ ∉ Φ := Φ.mem_iff_conjugate_notMem' τ

theorem conjugate_mem_iff (Φ : CMType E) (τ : E →+* ℂ) :
    ComplexEmbedding.conjugate τ ∈ Φ ↔ τ ∉ Φ := by
  rw [mem_iff_conjugate_notMem Φ τ, not_not]

theorem mem_or_conjugate_mem (Φ : CMType E) (τ : E →+* ℂ) :
    τ ∈ Φ ∨ ComplexEmbedding.conjugate τ ∈ Φ := by
  rw [conjugate_mem_iff]
  exact em _

noncomputable def sumEquiv (Φ : CMType E) : Φ ⊕ Φ ≃ (E →+* ℂ) :=
  Equiv.ofBijective (Sum.elim (fun τ => τ.1) (fun τ => ComplexEmbedding.conjugate τ.1)) <| by
    have hinv : Function.Involutive (ComplexEmbedding.conjugate (K := E)) := star_involutive
    constructor
    · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
      · rw [Subtype.ext h]
      · exact absurd (h ▸ a.2) ((Φ.mem_iff_conjugate_notMem _).mp b.2)
      · exact absurd (h ▸ b.2) ((Φ.mem_iff_conjugate_notMem _).mp a.2)
      · rw [Subtype.ext (hinv.injective h)]
    · intro τ
      rcases Φ.mem_or_conjugate_mem τ with h | h
      · exact ⟨.inl ⟨τ, h⟩, rfl⟩
      · exact ⟨.inr ⟨_, h⟩, hinv τ⟩

end Field

section NumberField

variable {E : Type*} [Field E] [NumberField E] (Φ : CMType E)

noncomputable instance : Fintype Φ := Fintype.ofFinite _

theorem sum_univ_eq {M : Type*} [AddCommMonoid M] (g : (E →+* ℂ) → M) :
    ∑ τ, g τ = ∑ τ : Φ, (g τ + g (ComplexEmbedding.conjugate τ.1)) := by
  rw [← Φ.sumEquiv.sum_comp, Fintype.sum_sum_type, Finset.sum_add_distrib]
  rfl

theorem two_mul_card : 2 * Fintype.card Φ = Module.finrank ℚ E := by
  rw [← Embeddings.card E ℂ, ← Fintype.card_congr Φ.sumEquiv, Fintype.card_sum, two_mul]

instance : Nonempty Φ := by
  rw [← Fintype.card_pos_iff]
  have h := Φ.two_mul_card
  have := Module.finrank_pos (R := ℚ) (M := E)
  omega

theorem trace_eq_sum_two_mul_re (x : E) :
    ((Algebra.trace ℚ E x : ℚ) : ℝ) = ∑ τ : Φ, 2 * (τ.1 x).re := by
  have h : ((Algebra.trace ℚ E x : ℚ) : ℂ) = ∑ σ : E →+* ℂ, σ x := by
    rw [Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) (fun f => f x) (fun φ => φ x)
      (fun _ => rfl), ← trace_eq_sum_embeddings ℂ (K := ℚ) (x := x)]
    simp
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, h, Φ.sum_univ_eq, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [ComplexEmbedding.conjugate_coe_eq, Complex.add_conj]

theorem eq_zero_of_sum_re_eq_zero (δ : Φ → ℂ)
    (h : ∀ a : 𝓞 E, ∑ τ : Φ, (τ.1 (a : E) * δ τ).re = 0) : δ = 0 := by
  have hli : LinearIndependent ℂ (fun τ : E →+* ℂ => (fun a : 𝓞 E => τ (a : E))) := by
    have h1 := linearIndependent_monoidHom (𝓞 E) ℂ
    refine h1.comp (fun τ : E →+* ℂ => (τ.comp (algebraMap (𝓞 E) E)).toMonoidHom) ?_
    intro τ τ' hτ
    refine IsFractionRing.ringHom_ext (A := 𝓞 E) fun a => ?_
    exact DFunLike.congr_fun hτ a
  have h2 := Fintype.linearIndependent_iff.mp hli
    (fun τ => Sum.elim δ (fun σ => conj (δ σ)) (Φ.sumEquiv.symm τ)) (by
      funext a
      rw [Finset.sum_apply, ← Φ.sumEquiv.sum_comp, Fintype.sum_sum_type]
      simp only [Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply]
      rw [← Finset.sum_add_distrib]
      have h3 : ((∑ τ : Φ, 2 * (τ.1 (a : E) * δ τ).re : ℝ) : ℂ) = 0 := by
        rw [← Finset.mul_sum, h a]; simp
      rw [← h3, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [← Complex.add_conj, map_mul]
      change δ τ * τ.1 a + conj (δ τ) * ComplexEmbedding.conjugate τ.1 a = _
      rw [ComplexEmbedding.conjugate_coe_eq]
      ring)
  funext τ
  simpa using h2 (Φ.sumEquiv (.inl τ))

end NumberField

end CMType

end GlobalTheory
