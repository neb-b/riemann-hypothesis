module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.AwChain
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.ValAbsPowNegOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.AutomorphyRankFourPolarizedAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0057
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.PTenInd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0033
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Bundle0001
public import GroundTheory.GlobalFields.ExistenceTheorem.ExistsIsAbelianGaloisRangeIdeleClassNormEqOfFini

@[expose] public section

open UpperTheory.GalN.V UpperTheory.V.Z.Win.Birth

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd UpperTheory.V.Ws UpperTheory.V.Z.Bc UpperTheory.V.Cu

private theorem deg_two {Ω : Type} [Field Ω] [CharZero Ω] (A B M : IntermediateField ℚ Ω) [FiniteDimensional ℚ A]
    [FiniteDimensional ℚ B] (hM : M = A ⊔ B) (hA : Module.finrank ℚ A = 2) (hn : ¬ A ≤ B) [Algebra B M] [IsScalarTower ℚ B M] :
    Module.finrank B M = 2 := by
  have h1 : Module.finrank ℚ M ≤ Module.finrank ℚ A * Module.finrank ℚ B := hM ▸ IntermediateField.finrank_sup_le A B
  haveI : FiniteDimensional ℚ M := hM ▸ IntermediateField.finiteDimensional_sup A B
  haveI : Module.Free B M := Module.Free.of_divisionRing B M
  have h2 := Module.finrank_mul_finrank ℚ B M
  have h3 : 0 < Module.finrank ℚ B := Module.finrank_pos
  have h4 : 0 < Module.finrank ℚ M := Module.finrank_pos
  have h5 : Module.finrank ℚ B ≠ Module.finrank ℚ M := fun e =>
    hn (IntermediateField.eq_of_le_of_finrank_eq (hM ▸ le_sup_right : B ≤ M) e ▸ (hM ▸ le_sup_left : A ≤ M))
  generalize Module.finrank B M = n at h2 ⊢
  rw [hA, ← h2, mul_comm 2] at h1
  have h6 := Nat.le_of_mul_le_mul_left h1 h3
  rw [← h2] at h4 h5
  interval_cases n <;> simp_all

private theorem two_emb {L M : Type} [Field L] [Field M] [CharZero L] [Algebra L M] (h : Module.finrank L M = 2) (φ : L →+* ℂ) :
    ∃ τ τ' : M →+* ℂ, τ ≠ τ' ∧ τ.comp (algebraMap L M) = φ ∧ τ'.comp (algebraMap L M) = φ := by
  letI : Algebra L ℂ := φ.toAlgebra
  haveI : FiniteDimensional L M := Module.finite_of_finrank_pos (by omega)
  have hc := AlgHom.card L M ℂ
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (α := M →ₐ[L] ℂ) (by omega)
  exact ⟨a, b, fun e => hab (AlgHom.coe_ringHom_injective e), a.comp_algebraMap, b.comp_algebraMap⟩

private theorem hom_ext_sup {Ω : Type} [Field Ω] [CharZero Ω] (A B M : IntermediateField ℚ Ω) (hA : A ≤ M) (hB : B ≤ M)
    (hM : M ≤ A ⊔ B) (τ τ' : M →+* ℂ) (eA : ∀ x : A, τ ⟨x, hA x.2⟩ = τ' ⟨x, hA x.2⟩) (eB : ∀ x : B, τ ⟨x, hB x.2⟩ = τ' ⟨x, hB x.2⟩) :
    τ = τ' := by
  let S : IntermediateField ℚ M := (τ.eqLocusField τ').toIntermediateField fun q => by
    rw [RingHom.mem_eqLocusField]
    simp
  have h : M ≤ IntermediateField.lift S := hM.trans <| sup_le
    (fun x hx => (IntermediateField.mem_lift (⟨x, hA hx⟩ : M)).2 (eA ⟨x, hx⟩))
    (fun x hx => (IntermediateField.mem_lift (⟨x, hB hx⟩ : M)).2 (eB ⟨x, hx⟩))
  ext x
  exact (IntermediateField.mem_lift x).1 (h x.2)

private theorem as_infOf (M : Multiset ℂ) (h2 : M.card = 2) (hz : ∀ z ∈ M, ∃ k : ℤ, z = (k : ℂ) + (((4 : ℕ) : ℂ) - 1) / 2) :
    ∃ a b : ℤ, M = infOf ![a, b] ∧ M = {(a : ℂ) + 1 / 2, (b : ℂ) + 1 / 2} := by
  obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 h2
  obtain ⟨a, rfl⟩ := hz x (by simp)
  obtain ⟨b, rfl⟩ := hz y (by simp)
  have e : ∀ a : ℤ, (a : ℂ) + (((4 : ℕ) : ℂ) - 1) / 2 = ((a + 1 : ℤ) : ℂ) + 1 / 2 := fun a => by push_cast; ring
  refine ⟨a + 1, b + 1, ?_, by rw [e, e]⟩
  have : (Finset.univ : Finset (Fin 2)).val = {0, 1} := rfl
  rw [infOf, this, e, e]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Matrix.cons_val_zero, Matrix.cons_val_one]
  congr 1 <;> [skip; congr 1] <;> push_cast <;> ring

private theorem irr_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (κ : Γ →* kˣ) (h : IsIrr r) : IsIrr (tw r κ) := by
  refine ⟨h.1, fun _ _ _ => trivial, fun W hW hi => h.2.2 W hW fun s v hv => ?_⟩
  have := W.smul_mem (((κ s)⁻¹ : kˣ) : k) (hi s v hv)
  rw [tw_val, Matrix.smul_mulVec, smul_smul, Units.inv_mul, one_smul] at this
  exact this

private theorem irr_tw_comp {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (κ : Γ →* kˣ) (φ : Γ' →* Γ)
    (h : IsIrr (r.comp φ)) : IsIrr ((tw r κ).comp φ) :=
  irr_tw (r.comp φ) (κ.comp φ) h

private theorem tw_one {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (κ : Γ →* kˣ) (s : Γ) (h : r s = 1) (h' : κ s = 1) :
    tw r κ s = 1 := Units.ext (by rw [tw_val, h, h']; simp)

