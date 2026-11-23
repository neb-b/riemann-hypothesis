module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvertibleEndInnerProductRootPowerSumMobiusStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_mobius : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → 0 < Module.finrank F V → ∀ k l : ℕ, ipGL (psi (rootSum θ k) V) (fun g : Module.End F V => rootSum θ l (LinearMap.charpoly g)) = glCard F (Module.finrank F V) * (((Finset.range (Module.finrank F V)).filter (fun i => k * Nat.card F ^ i ≡ l [MOD (Nat.card F ^ Module.finrank F V - 1)])).card : ℂ) := by
  first | exact @GlobalTheory.CuspGL.ipGL_psi_rootSum | exact GlobalTheory.CuspGL.ipGL_psi_rootSum | (intros; apply GlobalTheory.CuspGL.ipGL_psi_rootSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharOfIsPrimitiveRoot
section
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem isChar_of_isPrimitiveRoot : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] [IsAlgClosed L] (m : ℕ) (ζ : K), m ≠ 0 → IsPrimitiveRoot ζ m → ∀ (G : Type) [Group G] [Finite G], (∀ g : G, g ^ m = 1) → ∀ χ : G → L, IsChar L L χ → IsChar K L χ := by
  intro K L _ _ _ _ _ _ m ζ hm hζ G _ _ hG χ hχ
  refine GlobalTheory.T.isCharacterOverSubfield_of_virtual_and_character K L G χ hχ (GlobalTheory.T.mem_virtualCharacters_of_abelianByPrimePower K L G (fun H hH ψ hψ => ?_) χ hχ)
  exact _root_.GlobalTheory.BI.isChar_of_abByP K L m ζ hm hζ H (fun h => Subtype.ext (by simpa using hG (h : G))) hH ψ hψ
end GlobalTheory.BI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.PrimitiveEndClassFunctionZeroOfCharpolyMassZeroStatement
section
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitiveEndClassFunction_zero_of_charpoly_mass_zero : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → ∀ g : Module.End F V, mass φ (LinearMap.charpoly g) = 0 → φ g = 0 := by
  first | exact @GlobalTheory.CuspGL.eq_zero_of_mass_charpoly_eq_zero | exact GlobalTheory.CuspGL.eq_zero_of_mass_charpoly_eq_zero | (intros; apply GlobalTheory.CuspGL.eq_zero_of_mass_charpoly_eq_zero <;> assumption)
end

