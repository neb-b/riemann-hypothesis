module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.MemHomogIffIsHomogeneous
public import ReciprocityTheory.SemistableReduction.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsDetEquivOfSubsingleton
section
open TensorProduct Module Function

namespace GlobalTheory
namespace TopExt

variable {R F H L : Type*} [CommRing R] [AddCommGroup F] [Module R F] [AddCommGroup H] [Module R H]
  [AddCommGroup L] [Module R L]


variable (R H) in
noncomputable def wedgeMul (a b : ℕ) : (⋀[R]^a H) ⊗[R] (⋀[R]^b H) →ₗ[R] ⋀[R]^(a + b) H :=
  LinearMap.codRestrict _
    (LinearMap.mul' R (ExteriorAlgebra R H) ∘ₗ
      TensorProduct.map (⋀[R]^a H).subtype (⋀[R]^b H).subtype) fun t => by
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | tmul x y =>
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
        ExteriorAlgebra.exteriorPower, pow_add]
      exact Submodule.mul_mem_mul x.2 y.2

theorem coe_map (n : ℕ) (i : F →ₗ[R] H) (x : ⋀[R]^n F) :
    (exteriorPower.map n i x : ExteriorAlgebra R H) =
      ExteriorAlgebra.map i (x : ExteriorAlgebra R F) := by
  have : (⋀[R]^n H).subtype ∘ₗ exteriorPower.map n i =
      (ExteriorAlgebra.map i).toLinearMap ∘ₗ (⋀[R]^n F).subtype := by
    apply exteriorPower.linearMap_ext
    ext v
    simp
  exact LinearMap.congr_fun this x

noncomputable def wedgeMap (i : F →ₗ[R] H) (s : L →ₗ[R] H) (a b : ℕ) :
    (⋀[R]^a F) ⊗[R] (⋀[R]^b L) →ₗ[R] ⋀[R]^(a + b) H :=
  wedgeMul R H a b ∘ₗ TensorProduct.map (exteriorPower.map a i) (exteriorPower.map b s)

theorem coe_wedgeMap_tmul (i : F →ₗ[R] H) (s : L →ₗ[R] H) {a b : ℕ} (x : ⋀[R]^a F)
    (y : ⋀[R]^b L) : (wedgeMap i s a b (x ⊗ₜ y) : ExteriorAlgebra R H) =
      ExteriorAlgebra.map i (x : ExteriorAlgebra R F) *
        ExteriorAlgebra.map s (y : ExteriorAlgebra R L) := by
  simp [wedgeMap, wedgeMul]

theorem range_pow_eq_map (i : F →ₗ[R] H) (n : ℕ) :
    LinearMap.range (ExteriorAlgebra.ι R ∘ₗ i) ^ n =
      (⋀[R]^n F).map (ExteriorAlgebra.map i).toLinearMap := by
  rw [ExteriorAlgebra.exteriorPower, Submodule.map_pow, ← LinearMap.range_comp,
    ExteriorAlgebra.map_comp_ι]

section Exact

variable {i : F →ₗ[R] H} {π : H →ₗ[R] L}

end Exact

section Dual




variable (F) in
theorem rankAtStalk_dual [Module.Finite R F] [Module.Projective R F] (p : PrimeSpectrum R) :
    rankAtStalk (Dual R F) p = rankAtStalk F p := by
  let S := p.asIdeal.primeCompl
  have h₁ := LocalizedModule.isBaseChange S F
  have h₂ := LocalizedModule.isBaseChange S (Dual R F)
  have : Module.Free (Localization S) (LocalizedModule S F) :=
    Module.free_of_flat_of_isLocalRing
  have e := h₂.equiv.symm ≪≫ₗ (SymAlg.isBaseChange_dual h₁).equiv
  exact e.finrank_eq.trans (Module.finrank_linearMap_self _ _ _)

end Dual

end TopExt
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.Imports
section
namespace GlobalTheory.IntSmulIntegral

open NumberField

theorem exists_int_mul_integral {K : Type} [Field K] [NumberField K] (a : K) :
    ∃ (m : ℤ) (z : 𝓞 K), m ≠ 0 ∧ (z : K) = m • a := by
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  have : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.of_finite ℚ K
  obtain ⟨m, hm, hint⟩ := ((Algebra.IsAlgebraic.isAlgebraic a : IsAlgebraic ℚ a).restrictScalars ℤ).exists_integral_multiple
  exact ⟨m, ⟨m • a, hint⟩, hm, rfl⟩

theorem exists_int_smul_mem {r : ℕ} {K : Type} [Field K] [NumberField K]
    {Λ : Submodule (𝓞 K) (Fin r → K)} (hΛ : ReciprocityTheory.MultiplicativeHeights.IsLattice Λ) (v : Fin r → K) :
    ∃ n : ℤ, n ≠ 0 ∧ n • v ∈ Λ := by
  have hv : v ∈ Submodule.span K (Λ : Set (Fin r → K)) := hΛ.2 ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact Λ.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨n₁, hn₁, h₁⟩ := hx
    obtain ⟨n₂, hn₂, h₂⟩ := hy
    refine ⟨n₁ * n₂, mul_ne_zero hn₁ hn₂, ?_⟩
    rw [smul_add, mul_comm, mul_smul, mul_comm, mul_smul]
    exact Λ.add_mem (Λ.toAddSubgroup.zsmul_mem h₁ n₂) (Λ.toAddSubgroup.zsmul_mem h₂ n₁)
  | smul c x _ hx =>
    obtain ⟨n, hn, h⟩ := hx
    obtain ⟨m, z, hm, hz⟩ := exists_int_mul_integral c
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩

    have e : (n * m) • (c • x) = z • (n • x) := by
      rw [mul_smul, ← smul_assoc m c x, ← hz, smul_comm]
      rfl
    rw [e]
    exact Λ.smul_mem z h

end GlobalTheory.IntSmulIntegral
end

