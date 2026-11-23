module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002

@[expose] public section

noncomputable section

open GlobalTheory.PRep Topology Filter

namespace UpperTheory.Dv.CoinvFin

section Alg

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def stab (ρ : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
    rw [hy, hx]
  one_mem' := by simp
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← hx]
    rw [← Module.End.mul_apply, ← map_mul]
    simp

def av (ρ : Representation ℂ G V) (K K' : Subgroup G) [Fintype (K ⧸ K'.subgroupOf K)] (v : V) : V :=
  ∑ q : K ⧸ K'.subgroupOf K, ρ (q.out : K) v

theorem av_fixed (ρ : Representation ℂ G V) (K K' : Subgroup G) [Fintype (K ⧸ K'.subgroupOf K)] {v : V}
    (hv : K' ≤ stab ρ v) : ∀ k ∈ K, ρ k (av ρ K K' v) = av ρ K K' v := by
  intro k hk
  unfold av
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Fintype.sum_equiv (MulAction.toPerm (⟨k, hk⟩ : K)) _ _ fun q => ?_
  have h1 : ((((⟨k, hk⟩ : K) • q).out : K) : K ⧸ K'.subgroupOf K) = ((⟨k, hk⟩ * q.out : K) : K ⧸ K'.subgroupOf K) := by
    rw [QuotientGroup.out_eq', ← smul_eq_mul, MulAction.Quotient.mk_smul_out]
  have h2 : ρ _ v = v := hv (Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 h1))
  rw [MulAction.toPerm_apply]
  conv_rhs => rw [← h2]
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  simp

theorem av_of_fixed (ρ : Representation ℂ G V) (K K' : Subgroup G) [Fintype (K ⧸ K'.subgroupOf K)] {v : V}
    (hv : ∀ k ∈ K, ρ k v = v) : av ρ K K' v = (Fintype.card (K ⧸ K'.subgroupOf K) : ℂ) • v := by
  unfold av
  rw [Finset.sum_congr rfl fun q _ => hv _ (q.out).2, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]

end Alg

section Top

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W]

theorem finite_quot {K K' : Subgroup G} (c : IsCompact (K : Set G)) (o : IsOpen (K' : Set G)) :
    Finite (K ⧸ K'.subgroupOf K) := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 c
  exact Subgroup.quotient_finite_of_isOpen _ (Subgroup.subgroupOf_isOpen K K' o)

theorem mem_of_span (ρ : Representation ℂ G V) {K : Subgroup G} (c : IsCompact (K : Set G)) (S : Set V) (W₀ : Submodule ℂ V)
    (hS : ∀ s ∈ S, ∃ K₀ : Subgroup G, IsOpen (K₀ : Set G) ∧ ∀ K' ≤ K₀, ∀ [Fintype (K ⧸ K'.subgroupOf K)], av ρ K K' s ∈ W₀)
    {w : V} (hw : w ∈ Submodule.span ℂ S) (hfix : ∀ k ∈ K, ρ k w = w) : w ∈ W₀ := by
  have key : ∀ w ∈ Submodule.span ℂ S, ∃ K₀ : Subgroup G, IsOpen (K₀ : Set G) ∧
      ∀ K' ≤ K₀, ∀ [Fintype (K ⧸ K'.subgroupOf K)], av ρ K K' w ∈ W₀ := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem s hs => exact hS s hs
    | zero => exact ⟨⊤, isOpen_univ, fun K' _ _ => by simp [av]⟩
    | add x y _ _ hx hy =>
      obtain ⟨K₁, o₁, h₁⟩ := hx
      obtain ⟨K₂, o₂, h₂⟩ := hy
      refine ⟨K₁ ⊓ K₂, o₁.inter o₂, fun K' h _ => ?_⟩
      have := add_mem (h₁ K' (h.trans inf_le_left)) (h₂ K' (h.trans inf_le_right))
      simpa [av, Finset.sum_add_distrib] using this
    | smul a x _ hx =>
      obtain ⟨K₁, o₁, h₁⟩ := hx
      refine ⟨K₁, o₁, fun K' h _ => ?_⟩
      have := W₀.smul_mem a (h₁ K' h)
      simpa [av, Finset.smul_sum] using this
  obtain ⟨K₀, o, h⟩ := key w hw
  haveI := finite_quot c o
  letI := Fintype.ofFinite (K ⧸ K₀.subgroupOf K)
  have h1 := h K₀ le_rfl
  rw [av_of_fixed ρ K K₀ hfix] at h1
  exact (Submodule.smul_mem_iff _ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)).1 h1

end Top

end UpperTheory.Dv.CoinvFin

end
