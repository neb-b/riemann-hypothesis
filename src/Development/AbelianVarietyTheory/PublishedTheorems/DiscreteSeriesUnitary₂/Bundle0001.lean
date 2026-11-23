module

public import Mathlib
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.AutomorphicFormsFiniteUnitaryIff
section
open NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL GlobalTheory.Count GlobalTheory.Dec

noncomputable section

namespace GlobalTheory.Published

def AutomorphicFormsFiniteUnitary : Prop := GlobalTheory.Dec.AutFinite

namespace AutFinU

end AutFinU

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.Published

def DiscreteSeriesClassification : Prop :=
  ∀ n : ℕ, ∃ (H : (Fin n → Bool) → (Fin n → ℝ) → Type) (_ : ∀ ε lam, NormedAddCommGroup (H ε lam))
    (_ : ∀ ε lam, InnerProductSpace ℂ (H ε lam))
    (π : ∀ ε lam, Matrix (Fin n) (Fin n) ℂ → (H ε lam →L[ℂ] H ε lam)),
    (∀ (ε : Fin n → Bool) (lam : Fin n → ℝ),
      (StrictAnti lam ∧ ∀ a, ∃ m : ℤ, lam a - ((n : ℝ) - 1) / 2 = (m : ℝ)) →

      (CompleteSpace (H ε lam) ∧ Nontrivial (H ε lam) ∧ IsURepOn (UJset ε) (π ε lam) ∧
          IsIrredOn (UJset ε) (π ε lam) ∧ IsSqIntOn ε (π ε lam)) ∧

        HasInfChar ε (fun a => (lam a : ℂ)) (π ε lam) ∧

        (∃! S : Submodule ℂ (H ε lam), IsKTypeOf ε (π ε lam) (lam + rhoN ε - rhoC ε) S) ∧

        ∀ (μ : Fin n → ℝ) (S : Submodule ℂ (H ε lam)), IsKTypeOf ε (π ε lam) μ S →
          ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → a < b) ∧
            μ = (lam + rhoN ε - rhoC ε) + ∑ a, ∑ b, (c a b : ℝ) • root a b) ∧

    ∀ (ε : Fin n → Bool) (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
      (σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
      (CompleteSpace H' ∧ Nontrivial H' ∧ IsURepOn (UJset ε) σ ∧ IsIrredOn (UJset ε) σ ∧ IsSqIntOn ε σ) →
      ∃ (s : Equiv.Perm (Fin n)) (mu : Fin n → ℝ),
        (StrictAnti mu ∧ ∀ a, ∃ m : ℤ, mu a - ((n : ℝ) - 1) / 2 = (m : ℝ)) ∧
        (∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) ∧
        ∃ T : H' ≃ₗᵢ[ℂ] H (ε ∘ s) mu, ∀ g ∈ UJset (ε ∘ s), ∀ v,
          T (σ (g.submatrix s.symm s.symm) v) = π (ε ∘ s) mu g (T v)

theorem discreteSeriesClassification_iff : DiscreteSeriesClassification ↔ DSClass := Iff.rfl

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesCoefficientsCuspidalIffOneSided
section
open MeasureTheory Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.Published

def DiscreteSeriesCoefficientsCuspidal : Prop := GlobalTheory.Dec.CoefCusp

theorem discreteSeriesCoefficientsCuspidal_iff : DiscreteSeriesCoefficientsCuspidal ↔
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsSqIntIrr ε σ →
      ∀ u v : H, IsKFin ε σ u → IsKFin ε σ v →
      ∀ W : Submodule ℂ (Fin n → ℂ), IsIsoC ε W →
      ∀ ν : @Measure (UJ ε) (borel (UJ ε)), @IsHaarSub (UJ ε) _ _ (borel (UJ ε)) (NW ε W) ν →
      ∀ x y : UJ ε,
        @Integrable ℂ _ _ (UJ ε) (borel (UJ ε)) (fun m => ⟪v, σ (umat (x * m * y)) u⟫_ℂ) ν ∧
          @integral (UJ ε) ℂ _ _ (borel (UJ ε)) ν (fun m => ⟪v, σ (umat (x * m * y)) u⟫_ℂ) = 0 :=
  Iff.rfl

namespace CoefficientsCuspidal

variable {n : ℕ} {ε : Fin n → Bool}

end CoefficientsCuspidal

end GlobalTheory.Published
end
end

