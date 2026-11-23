module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements.Gauss

open NumberField Polynomial
open scoped Matrix ComplexConjugate

abbrev Em : Type := CyclotomicField 4 ℚ

instance : NeZero ((4 : ℕ) : ℚ) := ⟨by norm_num⟩

instance cycl4 : IsCyclotomicExtension {4} ℚ Em := CyclotomicField.isCyclotomicExtension 4 ℚ

instance : IsCMField Em :=
  IsCyclotomicExtension.Rat.isCMField Em (S := {4}) ⟨4, Set.mem_singleton _, by norm_num⟩

def ζ : Em := IsCyclotomicExtension.zeta 4 ℚ Em

theorem hζ : IsPrimitiveRoot ζ 4 := IsCyclotomicExtension.zeta_spec 4 ℚ Em

theorem ζ_sq : ζ ^ 2 = -1 := by
  have h4 : ζ ^ 4 = 1 := hζ.pow_eq_one
  have h2 : ζ ^ 2 ≠ 1 := hζ.pow_ne_one_of_pos_of_lt (l := 2) (by norm_num) (by norm_num)
  have h : (ζ ^ 2 - 1) * (ζ ^ 2 + 1) = ζ ^ 4 - 1 := by ring
  rw [h4, sub_self] at h
  rcases mul_eq_zero.1 h with h | h
  · exact absurd (sub_eq_zero.1 h) h2
  · exact eq_neg_of_add_eq_zero_left h

abbrev cc : Em ≃ₐ[maximalRealSubfield Em] Em := IsCMField.complexConj Em

def φ₀ : Em →+* ℂ := Classical.choice inferInstance

theorem emb_ζ (σ : Em →+* ℂ) : σ ζ = Complex.I ∨ σ ζ = -Complex.I := by
  have hs : σ ζ ^ 2 = -1 := by rw [← map_pow, ζ_sq, map_neg, map_one]
  have h : (σ ζ - Complex.I) * (σ ζ + Complex.I) = σ ζ ^ 2 - Complex.I ^ 2 := by ring
  rw [hs, Complex.I_sq, sub_self] at h
  rcases mul_eq_zero.1 h with h | h
  · exact Or.inl (sub_eq_zero.1 h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

theorem ringHom_ext {σ σ' : Em →+* ℂ} (h : σ ζ = σ' ζ) : σ = σ' := by
  have : σ.toRatAlgHom = σ'.toRatAlgHom :=
    AlgHom.ext_of_adjoin_eq_top (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ)
      (fun x hx => by rw [Set.mem_singleton_iff] at hx; subst hx; exact h)
  ext x
  exact congrArg (fun f : Em →ₐ[ℚ] ℂ => f x) this

theorem conj_emb_ζ (σ : Em →+* ℂ) : conj (σ ζ) = -σ ζ := by
  rcases emb_ζ σ with h | h <;> rw [h] <;> simp [Complex.conj_I]

theorem cc_ζ : cc ζ = -ζ := by
  apply φ₀.injective
  rw [IsCMField.complexEmbedding_complexConj, map_neg, conj_emb_ζ]

end GroundTheory.Heights₂.Heights.NineStatements.Gauss
