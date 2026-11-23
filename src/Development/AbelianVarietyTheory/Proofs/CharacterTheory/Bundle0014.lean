module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.SumPrimitiveEndClassFunctionRestrictMixedSubspac

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.MemVirtualCharactersIffSubCharacters
section
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem mem_virt_iff_sub (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (f : G → L) :
    f ∈ Virt K L G ↔ ∃ a b : G → L, IsChar K L a ∧ IsChar K L b ∧ f = a - b := by
  obtain ⟨h0, hadd⟩ := _root_.GlobalTheory.BI.isChar_zero_and_add K L G
  unfold Virt
  constructor
  · intro hf
    induction hf using AddSubgroup.closure_induction with
    | mem x hx => exact ⟨x, 0, hx, h0, (sub_zero x).symm⟩
    | zero => exact ⟨0, 0, h0, h0, (sub_zero 0).symm⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨a, b, ha, hb, rfl⟩ := ihx
      obtain ⟨c, d, hc, hd, rfl⟩ := ihy
      exact ⟨a + c, b + d, hadd a c ha hc, hadd b d hb hd, by abel⟩
    | neg x _ ih =>
      obtain ⟨a, b, ha, hb, rfl⟩ := ih
      exact ⟨b, a, hb, ha, by abel⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact AddSubgroup.sub_mem _ (AddSubgroup.subset_closure ha) (AddSubgroup.subset_closure hb)
end GlobalTheory.BI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.SumPrimitiveEndClassFunctionRestrictMixedSubspacStatement
section
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_primitiveEndClassFunction_restrict_mixed_subspace : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (A W : Submodule F V) (g : Module.End F V), (∀ x ∈ A, g x ∈ A) → W ⊓ A ≠ ⊥ → ¬ W ≤ A → ∀ φ : Module.End F W → ℂ, IsPrimitive φ → ∑ᶠ h : {h : Module.End F V // h ∈ nilRad A ∧ ∀ x ∈ W, (g + h) x ∈ W}, φ ((g + h.1).restrict h.2.2) = 0 := by
  first | exact @GlobalTheory.CuspGL.sum_restrict_eq_zero_of_mixed | exact GlobalTheory.CuspGL.sum_restrict_eq_zero_of_mixed | (intros; apply GlobalTheory.CuspGL.sum_restrict_eq_zero_of_mixed <;> assumption)
end

