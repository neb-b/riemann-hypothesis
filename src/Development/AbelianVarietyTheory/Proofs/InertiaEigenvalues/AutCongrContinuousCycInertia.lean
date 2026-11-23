module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0003

@[expose] public section

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal TensorProduct

noncomputable section
namespace GlobalTheory.ConsCompare

theorem autCongr_continuous_cyc_inertia : ∀ (E Ω Ω₁ : Type) [Field E] [NumberField E] [Field Ω] [Field Ω₁] [Algebra E Ω] [Algebra E Ω₁] [IsAlgClosure E Ω] [IsAlgClosure E Ω₁] (σ : Ω ≃ₐ[E] Ω₁), Continuous (fun g : G E Ω => (AlgEquiv.autCongr σ g : G E Ω₁)) ∧ (∀ (p : ℕ) [Fact p.Prime] (g : G E Ω), cycZ E Ω₁ p (AlgEquiv.autCongr σ g) = cycZ E Ω p g) ∧ ∀ (A : ValuationSubring Ω) (A₁ : ValuationSubring Ω₁), (∀ y, σ y ∈ A₁ ↔ y ∈ A) → ∀ g : G E Ω, g ∈ Ine (F := E) A → (AlgEquiv.autCongr σ g : G E Ω₁) ∈ Ine (F := E) A₁ := by
  intro E Ω Ω₁ _ _ _ _ _ _ _ _ σ
  refine ⟨?_, fun p _ g => ?_, fun A A₁ hA g hg => ?_⟩
  · apply continuous_of_continuousAt_one (AlgEquiv.autCongr σ).toMonoidHom
    intro s hs
    rw [map_one, krullTopology_mem_nhds_one_iff] at hs
    obtain ⟨F, hF, hs⟩ := hs
    rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
    refine ⟨F.map σ.symm.toAlgHom,
      (IntermediateField.equivMap F σ.symm.toAlgHom).toLinearEquiv.finiteDimensional, fun g hg => hs ?_⟩
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hg ⊢
    intro x hx
    have := hg (σ.symm x) ⟨x, hx, rfl⟩
    show σ (g (σ.symm x)) = x
    rw [this, σ.apply_symm_apply]
  · have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
    have : IsAlgClosed Ω₁ := IsAlgClosure.isAlgClosed E
    have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
    have : CharZero Ω₁ := charZero_of_injective_algebraMap (algebraMap E Ω₁).injective
    have : NeZero ((p : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
    have : NeZero ((p : ℕ) : Ω₁) := ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
    apply Units.ext
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (p ^ n)
    have hζ' : IsPrimitiveRoot (σ ζ) (p ^ n) := hζ.map_of_injective σ.injective
    have h1 : g ζ = ζ ^ (PadicInt.toZModPow n ((cycZ E Ω p g : ℤ_[p]ˣ) : ℤ_[p])).val :=
      cyclotomicCharacter.spec (L := Ω) p (MulSemiringAction.toRingAut (G E Ω) Ω g) ζ hζ.pow_eq_one
    have h2 : σ (g (σ.symm (σ ζ))) = σ ζ ^ (PadicInt.toZModPow n
        ((cycZ E Ω₁ p (AlgEquiv.autCongr σ g) : ℤ_[p]ˣ) : ℤ_[p])).val :=
      cyclotomicCharacter.spec (L := Ω₁) p
        (MulSemiringAction.toRingAut (G E Ω₁) Ω₁ (AlgEquiv.autCongr σ g)) (σ ζ) hζ'.pow_eq_one
    rw [σ.symm_apply_apply, h1, map_pow] at h2
    apply ZMod.val_injective
    exact (hζ'.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h2).symm
  · have hv : ∀ y, A₁.valuation (σ y) < 1 ↔ A.valuation y < 1 := fun y => by
      rw [valuation_lt_one_iff', valuation_lt_one_iff', hA, ← map_inv₀, hA, map_eq_zero_iff _ σ.injective]
    refine ⟨?_, fun x hx => ?_⟩
    · show AlgEquiv.autCongr σ g ∈ Dec (F := E) A₁
      rw [mem_Dec]
      ext y
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      obtain ⟨z, rfl⟩ := σ.surjective y
      have : (AlgEquiv.autCongr σ g)⁻¹ • σ z = σ ((g⁻¹ : G E Ω) z) := by
        rw [← map_inv]
        show σ ((g⁻¹ : G E Ω) (σ.symm (σ z))) = _
        rw [σ.symm_apply_apply]
      rw [this, hA, hA]
      exact apply_mem_iff_of_mem_Dec ((Dec (F := E) A).inv_mem hg.1) z
    · obtain ⟨z, rfl⟩ := σ.surjective x
      have : (AlgEquiv.autCongr σ g) (σ z) - σ z = σ (g z - z) := by
        rw [map_sub]
        show σ (g (σ.symm (σ z))) - _ = _
        rw [σ.symm_apply_apply]
      rw [this, hv]
      apply hg.2
      rwa [ValuationSubring.valuation_le_one_iff, hA, ← ValuationSubring.valuation_le_one_iff] at hx

section CharpolySeries
variable {k A : Type} [Field k] [Ring A] [Algebra k A]

def cpOn (k : Type) [Field k] [Algebra k A] (a : A) (M : Type) [AddCommGroup M] [Module k M] [Module A M]
    [IsScalarTower k A M] [FiniteDimensional k M] : Polynomial k :=
  LinearMap.charpoly (Algebra.lsmul k k M a)

variable (a : A) {M M' : Type} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  [FiniteDimensional k M] [AddCommGroup M'] [Module k M'] [Module A M'] [IsScalarTower k A M']
  [FiniteDimensional k M']

theorem cpOn_congr (e : M ≃ₗ[A] M') : cpOn k a M = cpOn k a M' := by
  unfold cpOn
  rw [← LinearEquiv.charpoly_conj (e.restrictScalars k)]
  congr 1
  ext v
  simp [LinearEquiv.conj_apply]

instance finiteDimensional_sub (N : Submodule A M) : FiniteDimensional k N :=
  inferInstanceAs (FiniteDimensional k (N.restrictScalars k))

theorem cpOn_sub_quot (N : Submodule A M) : cpOn k a M = cpOn k a N * cpOn k a (M ⧸ N) :=
  GlobalTheory.CuspGL.charpoly_eq_restrict_mul_mapQ (N.restrictScalars k) (Algebra.lsmul k k M a)
    fun _ hx => N.smul_mem a hx

theorem last_eq_mul_prod {P : Type} [CommMonoid P] : ∀ (n : ℕ) (u : Fin (n + 1) → P) (c : Fin n → P),
    (∀ j, u j.succ = u j.castSucc * c j) → u (Fin.last n) = u 0 * ∏ j, c j
  | 0, u, c, _ => by simp
  | n + 1, u, c, h => by
    have := last_eq_mul_prod n (fun j => u j.castSucc) (fun j => c j.castSucc) fun j => h j.castSucc
    rw [Fin.prod_univ_castSucc, ← Fin.succ_last, h, this, mul_assoc]
    rfl

theorem cpOn_series (s : CompositionSeries (Submodule A M)) (h0 : s.head = ⊥) (h1 : s.last = ⊤) :
    cpOn k a M = ∏ j : Fin s.length,
      cpOn k a (↥(s j.succ) ⧸ (s j.castSucc).submoduleOf (s j.succ)) := by
  have := last_eq_mul_prod s.length (fun j => cpOn k a (s j)) _ fun j =>
    (cpOn_sub_quot a ((s j.castSucc).submoduleOf (s j.succ))).trans (congrArg (· * _)
      (cpOn_congr a (Submodule.submoduleOfEquivOfLe (s.step j).le)))
  have e1 : cpOn k a (s (Fin.last _)) = cpOn k a M :=
    cpOn_congr a (LinearEquiv.ofTop _ h1)
  have e0 : cpOn k a (s 0) = 1 := by
    have : Subsingleton (s 0) := by
      have h0' : s 0 = ⊥ := h0
      rw [h0']
      infer_instance
    unfold cpOn
    rw [← (LinearMap.charpoly_monic _).natDegree_eq_zero, LinearMap.charpoly_natDegree]
    exact Module.finrank_zero_of_subsingleton
  rw [← e1, this, e0, one_mul]

end CharpolySeries

end GlobalTheory.ConsCompare
end
