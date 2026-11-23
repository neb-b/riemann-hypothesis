module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsIrreducibleIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0016

@[expose] public section

noncomputable section

open GlobalTheory.PRep

namespace PositivityTheory.Rg.BcB.F.EigA

section Sums

theorem out_mk_inv {H M : Type} [Group H] (A : Subgroup H) (F : H → M) (hF : ∀ x, ∀ a ∈ A, F (x * a) = F x)
    (y : H) : F ((y : H ⧸ A).out) = F y := by
  obtain ⟨a, ha⟩ := QuotientGroup.mk_out_eq_mul A y
  rw [ha, hF _ _ a.2]

end Sums

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem mem_fixed_iff {ρ : Representation ℂ G V} {K : Subgroup G} {v : V} :
    v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v := by
  change (∀ h : K, ρ (h : G) v = ((1 : K →* ℂˣ) h : ℂ) • v) ↔ _
  constructor
  · intro h k hk
    simpa using h ⟨k, hk⟩
  · intro h k
    simpa using h k k.2


def GelPair (K : Subgroup G) : Prop :=
  (∀ g : G, (K.map (MulAut.conj g).toMonoidHom).relIndex K ≠ 0) ∧
    ∃ τ : G → G, (∀ a b, τ (a * b) = τ b * τ a) ∧ (∀ a, τ (τ a) = a) ∧
      (∀ g : G, ∃ k₁ ∈ K, ∃ k₂ ∈ K, τ g = k₁ * g * k₂) ∧ ∀ k ∈ K, τ k ∈ K

end PositivityTheory.Rg.BcB.F.EigA

end
