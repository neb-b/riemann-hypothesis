module

public import Mathlib
public import Formalism.GL3MeanSquares.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplChi
section
noncomputable section

open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

def ExplChi : Prop :=
  ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive → ∀ x T : ℝ, 2 ≤ x → 2 ≤ T →
    ‖psiChi χ x + zsum χ 0 T (fun ρ => (x : ℂ) ^ ρ / ρ) + ((Real.log (x - 1) / 2 : ℝ) : ℂ) +
        χ (-1) / 2 * ((Real.log (x + 1) : ℝ) : ℂ) -
        (deriv (DirichletCharacter.LFunction χ⁻¹) 1 / DirichletCharacter.LFunction χ⁻¹ 1 +
          ((Real.log (q / (2 * Real.pi)) - Real.eulerMascheroniConstant : ℝ) : ℂ))‖ ≤
      C * (Real.log x + x / T * Real.log (q * x * T) ^ 2)

end GlobalTheory.Mem.An
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplZeta
section
noncomputable section

open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

def ExplZeta : Prop :=
  ∃ C : ℝ, ∀ x T : ℝ, 2 ≤ x → 2 ≤ T →
    ‖psiChi (1 : DirichletCharacter ℂ 1) x - (x : ℂ) + zsum (1 : DirichletCharacter ℂ 1) 0 T (fun ρ => (x : ℂ) ^ ρ / ρ) +
        ((Real.log (2 * Real.pi) + Real.log (1 - 1 / x ^ 2) / 2 : ℝ) : ℂ)‖ ≤
      C * (Real.log x + x / T * Real.log (x * T) ^ 2)

end GlobalTheory.Mem.An
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsExcRat
section
noncomputable section

open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

def IsExcRat {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (β : ℝ) : Prop :=
  χ ^ 2 = 1 ∧ 1 - 1 / (8 * Real.log M) < β ∧ β < 1 ∧
    haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    DirichletCharacter.LFunction χ.primitiveCharacter β = 0

def TZRat : Prop :=
  ∃ c₂ c₃ CA cS : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ 0 < CA ∧ 0 < cS ∧ ∀ (M : ℕ) [NeZero M], 3 ≤ M → M % 4 ≠ 2 →
    (∀ (χ χ' : DirichletCharacter ℂ M) (β β' : ℝ), IsExcRat χ β → IsExcRat χ' β' → χ = χ' ∧ β = β') ∧
    (∀ (χ : DirichletCharacter ℂ M) (β : ℝ), IsExcRat χ β → cS / ((M : ℝ) ^ 2 * Real.log M) ≤ 1 - β) ∧
    ∀ (b : ℕ) (θ : ℤ) (β : ℝ), Nat.Coprime b M →
      ((θ = 0 ∧ ∀ (χ : DirichletCharacter ℂ M) (β' : ℝ), ¬ IsExcRat χ β') ∨
        ∃ χ : DirichletCharacter ℂ M, IsExcRat χ β ∧ χ (b : ZMod M) = (θ : ℂ)) →
      ∀ X : ℝ, (M : ℝ) ^ c₂ ≤ X →
        |(M.totient : ℝ) * (((Icc 1 ⌊X⌋₊).filter (fun p => p.Prime ∧ p ≡ b [MOD M])).card : ℝ) - Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X| ≤
          CA * (Real.exp (-c₃ * Real.log X / Real.log M) + Real.exp (-Real.sqrt (c₃ * Real.log X))) *
            Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X

end GlobalTheory.Mem.An
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Jutila
section
noncomputable section

open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

def Jutila : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, ∀ α Q T : ℝ, 4 / 5 ≤ α → α ≤ 1 → 1 ≤ Q → 1 ≤ T →
    (({p : (Σ q : ℕ, DirichletCharacter ℂ (q + 1)) × ℂ | 1 ≤ p.1.1 ∧ ((p.1.1 + 1 : ℕ) : ℝ) ≤ Q ∧ p.1.2.IsPrimitive ∧
        α ≤ p.2.re ∧ |p.2.im| ≤ T ∧ DirichletCharacter.LFunction p.1.2 p.2 = 0}.encard : ℕ∞) : ENNReal) ≤
      ENNReal.ofReal (c * (Q ^ 2 * T) ^ ((2 + ε) * (1 - α)))

end GlobalTheory.Mem.An
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
section
noncomputable section

open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

def LogDerOne : Prop :=
  ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
    ‖deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1 - zsum χ 0 1 (fun ρ => 1 / (1 - ρ))‖ ≤
      C * Real.log (3 * q)

end GlobalTheory.Mem.An
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.PageThm
section
noncomputable section

open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

def PageThm : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ Q : ℝ, 3 ≤ Q → ∀ (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂]
    (χ₁ : DirichletCharacter ℂ q₁) (χ₂ : DirichletCharacter ℂ q₂) (β₁ β₂ : ℝ),
    χ₁.IsPrimitive → χ₂.IsPrimitive → χ₁ ^ 2 = 1 → χ₂ ^ 2 = 1 → (q₁ : ℝ) ≤ Q → (q₂ : ℝ) ≤ Q →
    1 - c / Real.log Q < β₁ → β₁ < 1 → 1 - c / Real.log Q < β₂ → β₂ < 1 →
    DirichletCharacter.LFunction χ₁ β₁ = 0 → DirichletCharacter.LFunction χ₂ β₂ = 0 →
    q₁ = q₂ ∧ ∀ n : ℕ, χ₁ (n : ZMod q₁) = χ₂ (n : ZMod q₂)

end GlobalTheory.Mem.An
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.QuadraticHeckeZeroEstimates
section
noncomputable section

open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

def QuadraticHeckeZeroEstimates : Prop :=
  ∃ c₂ c₃ CA cS : ℝ, 0 < c₂ ∧ 0 < c₃ ∧ 0 < CA ∧ 0 < cS ∧
    ∀ (K : Type) [Field K] [NumberField K], IsTotallyComplex K → Module.finrank ℚ K = 2 →
    ∀ 𝔮 : Ideal (𝓞 K), 𝔮 ≠ ⊥ → ∃ (𝒬 β : ℝ) (θ : ℤ) (S : Set (HeightOneSpectrum (𝓞 K))),
      4 * |(discr K : ℝ)| ≤ 𝒬 ∧ 𝒬 ≤ 4 * |(discr K : ℝ)| * (Ideal.absNorm 𝔮 : ℝ) ∧ (θ = 0 ∨ θ = 1) ∧
      (θ = 1 → 1 - 1 / (8 * Real.log 𝒬) < β ∧ cS / (𝒬 ^ 2 * Real.log 𝒬) ≤ 1 - β) ∧
      (∀ v ∈ S, v.asIdeal ∣ 𝔮) ∧
      ∀ X : ℝ, 𝒬 ^ c₂ ≤ X →
        |(rayNo 𝔮 : ℝ) * (((rayPrimes 𝔮 X).ncard : ℝ) + ({v ∈ S | (Ideal.absNorm v.asIdeal : ℝ) ≤ X}.ncard : ℝ)) -
            Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X| ≤
          CA * (Real.exp (-c₃ * Real.log X / Real.log 𝒬) + Real.exp (-Real.sqrt (c₃ * Real.log X / 2))) *
            Formalism.HermitianLattices.GL2PrimeSums.Emain θ β X

end GlobalTheory.Mem.An
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ZeroCount
section
noncomputable section

open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An

def ZeroCount : Prop :=
  ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ t : ℝ,
    zsumR χ t 1 (fun _ => 1) ≤ C * Real.log (q * (|t| + 2))

end GlobalTheory.Mem.An
end
end

