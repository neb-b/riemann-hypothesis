module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0003

@[expose] public section

-- Interpret the original scalar argument as the identity ring homomorphism.
local notation:max "MultilinearMap" R:max M:max N:max =>
  _root_.MultilinearMap (RingHom.id R) M N

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_span_multilinear_values' : ∀ {ι : Type} [Fintype ι] (E : ι → Type) [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)] (F : Type) [AddCommGroup F] [Module ℂ F] (T : MultilinearMap ℂ E F) (W : ∀ i, Submodule ℂ (E i)), (∀ i, FiniteDimensional ℂ (W i)) → FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ v : ∀ i, E i, (∀ i, v i ∈ W i) ∧ f = T v}) := by
  intro ι _ E _ _ F _ _ T W hW
  letI : ∀ i, FiniteDimensional ℂ (W i) := hW
  let restricted : (∀ i, W i) →ₘₗ[ℂ] F := T.compLinearMap (fun i => (W i).subtype)
  apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (PiTensorProduct.lift restricted))
  rw [Submodule.span_le]
  rintro _ ⟨v, hv, rfl⟩
  refine ⟨PiTensorProduct.tprod ℂ (fun i => ⟨v i, hv i⟩), ?_⟩
  rw [PiTensorProduct.lift.tprod]
  rfl
