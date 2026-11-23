module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsIntCoeffPrimitiveGLCharacterStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_int_coeff_primitive_GL_character : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ (d : ℕ) (χ : GL (Fin d) F → ℂ), 0 < d → IsChar ℂ ℂ χ → IsPrimitive (extZero χ) → ∃ a : ℕ → ℤ, (∀ k : ℕ, ipGL (extZero χ) (fun g : Module.End F (Fin d → F) => rootSum θ k (LinearMap.charpoly g)) = a k * glCard F d) ∧ (d : ℂ) * χ 1 = (∑ k ∈ Finset.range (Nat.card F ^ d - 1), (a k : ℂ)) * ∏ i ∈ Finset.Ico 1 d, (1 - (Nat.card F : ℂ) ^ i) := by
  first | exact @GlobalTheory.CuspGL.exists_int_coeff_of_isPrimitive | exact GlobalTheory.CuspGL.exists_int_coeff_of_isPrimitive | (intros; apply GlobalTheory.CuspGL.exists_int_coeff_of_isPrimitive <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterCuspidalRootSumRegularStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCharacter_cuspidal_rootSum_regular : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ d k : ℕ, 0 < d → (∀ i : ℕ, 0 < i → i < d → ¬ k * Nat.card F ^ i ≡ k [MOD Nat.card F ^ d - 1]) → IsChar ℂ ℂ (fun x : GL (Fin d) F => (-1) ^ (d - 1) * psi (rootSum θ k) (Fin d → F) (Matrix.toLin' (x : Matrix (Fin d) (Fin d) F))) ∧ ipGL (psi (rootSum θ k) (Fin d → F)) (psi (rootSum θ k) (Fin d → F)) = glCard F d := by
  first | exact @GlobalTheory.CuspGL.isChar_psi_rootSum_of_regular | exact GlobalTheory.CuspGL.isChar_psi_rootSum_of_regular | (intros; apply GlobalTheory.CuspGL.isChar_psi_rootSum_of_regular <;> assumption)
end

