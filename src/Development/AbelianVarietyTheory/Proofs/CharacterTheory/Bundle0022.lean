module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharacterInnerEqIntMulCard
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.BI

open Polynomial in
private lemma exists_nat_sum_mul_apply_inv_eq_mul_card (G : Type) [Group G] [Fintype G] (x y : G → ℂ)
    (hx : _root_.GlobalTheory.BI.IsChar ℂ ℂ x) (hy : _root_.GlobalTheory.BI.IsChar ℂ ℂ y) :
    ∃ n : ℕ, ∑ g, x g * y g⁻¹ = n * (Nat.card G : ℂ) := by
  obtain ⟨n, hn⟩ := (_root_.GlobalTheory.BI.pair_add_nat_pos_symm ℂ ℂ G).2.1 x y hx hy
  unfold _root_.GlobalTheory.BI.pair at hn
  rw [finsum_eq_sum_of_fintype] at hn
  have hc : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  refine ⟨n, ?_⟩
  rw [← hn, inv_mul_eq_div, div_mul_cancel₀ _ hc]


open Polynomial in
theorem _root_.GlobalTheory.BI.finsum_mul_star_virt_int : ∀ (G : Type) [Group G] [Finite G] (a b : G → ℂ),
    a ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G → b ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G →
    ∃ m : ℤ, ∑ᶠ g, a g * star (b g) = m * (Nat.card G : ℂ) := by
  intro G _ _ a b ha hb
  haveI := Fintype.ofFinite G
  have hstar : ∀ g, star (b g) = b g⁻¹ := _root_.GlobalTheory.CuspGL.star_virt_eq_inv G b hb
  rw [finsum_eq_sum_of_fintype]
  simp_rw [hstar]
  obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := (_root_.GlobalTheory.BI.mem_virt_iff_sub ℂ ℂ G a).mp ha
  obtain ⟨b₁, b₂, hb₁, hb₂, rfl⟩ := (_root_.GlobalTheory.BI.mem_virt_iff_sub ℂ ℂ G b).mp hb
  obtain ⟨n₁₁, h₁₁⟩ := exists_nat_sum_mul_apply_inv_eq_mul_card G a₁ b₁ ha₁ hb₁
  obtain ⟨n₁₂, h₁₂⟩ := exists_nat_sum_mul_apply_inv_eq_mul_card G a₁ b₂ ha₁ hb₂
  obtain ⟨n₂₁, h₂₁⟩ := exists_nat_sum_mul_apply_inv_eq_mul_card G a₂ b₁ ha₂ hb₁
  obtain ⟨n₂₂, h₂₂⟩ := exists_nat_sum_mul_apply_inv_eq_mul_card G a₂ b₂ ha₂ hb₂
  refine ⟨n₁₁ - n₁₂ - n₂₁ + n₂₂, ?_⟩
  simp only [Pi.sub_apply, sub_mul, mul_sub, Finset.sum_sub_distrib, h₁₁, h₁₂, h₂₁, h₂₂]
  push_cast
  ring

end GlobalTheory.BI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharacterIrreducibleExpansionNormSq
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

open Polynomial in
private theorem exists_irreducible_expansion_of_isCharacter_lemma_3 {G : Type} [Group G] [Finite G]
    (a : G → ℂ) (ha : _root_.GlobalTheory.BI.IsChar ℂ ℂ a) :
    ∃ c : (G → ℂ) →₀ ℤ, (∀ χ ∈ c.support, _root_.GlobalTheory.BI.IsIrrChar ℂ ℂ χ) ∧
      a = c.sum (fun χ m => m • χ) := by
  classical
  refine _root_.GlobalTheory.BI.isChar_induction ℂ ℂ G
    (fun a => ∃ c : (G → ℂ) →₀ ℤ, (∀ χ ∈ c.support, _root_.GlobalTheory.BI.IsIrrChar ℂ ℂ χ) ∧
      a = c.sum (fun χ m => m • χ)) ⟨0, by simp, by simp⟩ ?_ a ha
  rintro φ b hφ - ⟨c, hc, rfl⟩
  refine ⟨Finsupp.single φ 1 + c, fun χ hχ => ?_, ?_⟩
  · rcases Finset.mem_union.1 (Finsupp.support_add hχ) with h | h
    · rw [Finsupp.mem_support_iff, Finsupp.single_apply] at h
      split_ifs at h with e
      · exact e ▸ hφ
      · exact absurd rfl h
    · exact hc χ h
  · rw [Finsupp.sum_add_index' (by simp) (fun _ _ _ => add_smul _ _ _),
      Finsupp.sum_single_index (by simp), one_smul]

open Polynomial in
private theorem exists_irreducible_expansion_of_mem_lemma {G : Type} [Group G] [Finite G]
    (φ : G → ℂ) (hφ : φ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G) :
    ∃ c : (G → ℂ) →₀ ℤ, (∀ χ ∈ c.support, _root_.GlobalTheory.BI.IsIrrChar ℂ ℂ χ) ∧
      φ = c.sum (fun χ m => m • χ) := by
  classical
  obtain ⟨a, b, ha, hb, rfl⟩ := (_root_.GlobalTheory.BI.mem_virt_iff_sub ℂ ℂ G φ).1 hφ
  obtain ⟨ca, hca, rfl⟩ := exists_irreducible_expansion_of_isCharacter_lemma_3 a ha
  obtain ⟨cb, hcb, rfl⟩ := exists_irreducible_expansion_of_isCharacter_lemma_3 b hb
  refine ⟨ca - cb, fun χ hχ => ?_, ?_⟩
  · rcases Finset.mem_union.1 (Finsupp.support_sub hχ) with h | h
    · exact hca χ h
    · exact hcb χ h
  · rw [Finsupp.sum_sub_index (fun _ _ _ => sub_smul _ _ _)]

open Polynomial in
private theorem sum_mul_inv_irreducible_lemma_2 {G : Type} [Group G] [Fintype G] (χ ψ : G → ℂ)
    (hχ : _root_.GlobalTheory.BI.IsIrrChar ℂ ℂ χ) (hψ : _root_.GlobalTheory.BI.IsIrrChar ℂ ℂ ψ) :
    ∑ g, χ g * ψ g⁻¹ = if χ = ψ then (Nat.card G : ℂ) else 0 := by
  classical
  have hG : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  split_ifs with h
  · subst h
    have := _root_.GlobalTheory.BI.pair_self_of_isIrrChar_algClosed ℂ G χ hχ
    unfold _root_.GlobalTheory.BI.pair at this
    rw [inv_mul_eq_one₀ hG, finsum_eq_sum_of_fintype] at this
    exact this.symm
  · have := _root_.GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne G χ ψ hχ hψ h
    unfold _root_.GlobalTheory.BI.pair at this
    rw [finsum_eq_sum_of_fintype] at this
    simpa [hG] using this


open Polynomial in
theorem _root_.GlobalTheory.BI.virt_expand : ∀ (G : Type) [Group G] [Finite G]
    (φ : G → ℂ), φ ∈ _root_.GlobalTheory.BI.Virt ℂ ℂ G →
    ∃ c : (G → ℂ) →₀ ℤ, (∀ χ ∈ c.support, _root_.GlobalTheory.BI.IsIrrChar ℂ ℂ χ) ∧
      φ = c.sum (fun χ m => m • χ) ∧
      ∑ᶠ g, φ g * star (φ g) = (c.sum fun _ m => (m : ℂ) ^ 2) * (Nat.card G : ℂ) := by
  intro G _ _ φ hφ
  classical
  haveI := Fintype.ofFinite G
  obtain ⟨c, hc, he⟩ := exists_irreducible_expansion_of_mem_lemma φ hφ
  refine ⟨c, hc, he, ?_⟩
  have hev : ∀ g, φ g = ∑ χ ∈ c.support, (c χ : ℂ) * χ g := by
    intro g
    rw [he, Finsupp.sum, Finset.sum_apply]
    simp [zsmul_eq_mul]
  rw [finsum_eq_sum_of_fintype]
  simp_rw [_root_.GlobalTheory.CuspGL.star_virt_eq_inv G φ hφ, hev, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  calc ∑ χ ∈ c.support, ∑ g, ∑ ψ ∈ c.support, (c χ : ℂ) * χ g * ((c ψ : ℂ) * ψ g⁻¹)
      = ∑ χ ∈ c.support, ∑ ψ ∈ c.support, (c χ : ℂ) * c ψ * ∑ g, χ g * ψ g⁻¹ := by
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ψ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        ring
    _ = ∑ χ ∈ c.support, (c χ : ℂ) ^ 2 * (Nat.card G : ℂ) := by
        refine Finset.sum_congr rfl fun χ hχ => ?_
        rw [Finset.sum_congr rfl fun ψ hψ => by rw [sum_mul_inv_irreducible_lemma_2 χ ψ (hc χ hχ) (hc ψ hψ)]]
        simp only [mul_ite, mul_zero]
        rw [Finset.sum_ite_eq c.support χ, if_pos hχ]
        ring
    _ = _ := by rw [Finsupp.sum, Finset.sum_mul]

end GlobalTheory.BI
end
end

