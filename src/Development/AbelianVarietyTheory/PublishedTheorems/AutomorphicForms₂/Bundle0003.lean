module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL

noncomputable section

namespace GlobalTheory.Published

def DiscreteSeriesUpqExists : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ),
    (StrictAnti lam ∧ ∀ a, ∃ m : ℤ, lam a - ((N : ℝ) - 1) / 2 = (m : ℝ)) →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)),
      CompleteSpace H ∧ Nontrivial H ∧
      IsURepOn {g | gᴴ * Jm ε * g = Jm ε} σ ∧
      IsIrredOn {g | gᴴ * Jm ε * g = Jm ε} σ ∧
      (∀ v w : H, MemLp (coefOn (ε := ε) σ v w) 2 (muG ε)) ∧
      (∃ S : Submodule ℂ H, IsKTypeOf ε σ (lam + rhoN ε - rhoC ε) S) ∧
      ∀ (μ : Fin N → ℝ) (S : Submodule ℂ H), IsKTypeOf ε σ μ S →
        nsq (lam + rhoN ε - rhoC ε + (2 : ℝ) • rhoC ε) ≤ nsq (μ + (2 : ℝ) • rhoC ε)

theorem discreteSeriesUpqExists_iff : DiscreteSeriesUpqExists ↔ GlobalTheory.Mem.Vol.DiscreteSeriesExist := Iff.rfl

theorem discreteSeriesUpqExists_iff_dsExists : DiscreteSeriesUpqExists ↔ GlobalTheory.Dec.DSExists := Iff.rfl

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
section
open Formalism.BasicNotions Formalism.MainNotions.S MeasureTheory

namespace GlobalTheory.Published

def FormalDegreeCompactDual : Prop :=
  ∀ (cd : CDHaar) (sc : ∀ n : ℕ, (Fin n → Bool) → NNReal),
    (∀ (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
      (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
      ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
        ((sc n ε : ENNReal) • Formalism.REAL.muG ε) A =
          cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (UpqT.mat g)}) →
    ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ),
      (StrictAnti lam ∧ ∀ a, ∃ m : ℤ, lam a - ((N : ℝ) - 1) / 2 = (m : ℝ)) →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (w : H), IsDS ε lam σ → w ≠ 0 →
        ‖w‖ ^ 4 / ∫ g, ‖inner ℂ w (σ (umat g) w)‖ ^ 2 ∂((sc N ε : ENNReal) • Formalism.REAL.muG ε) =
          (∏ a : Fin N, ∏ b ∈ Finset.univ.filter (fun b : Fin N => a < b), |lam a - lam b|) /
            ∏ a : Fin N, ∏ b ∈ Finset.univ.filter (fun b : Fin N => a < b),
              (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))

theorem formalDegreeCompactDual_iff : FormalDegreeCompactDual ↔ GlobalTheory.Mem.Vol.FormalDegreeFormula₂ := Iff.rfl

end GlobalTheory.Published
end

