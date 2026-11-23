module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Published

open GlobalTheory.Eis

def SiegelEisensteinContinuation : Prop :=
  ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a →
    HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) →
    ∀ (μ : (AE D)ˣ →* Circle) (b : ℕ), IsHeckeChar D μ → ResEta D μ b →
    ∀ (s₁ : ℂ) (φ : GA D (dblSp V) → ℂ), φ ∈ degPS V a μ s₁ →
      EisContinues V (flat V a φ s₁) ∧ ∀ s₀, ∃ k, EisRegularAt V (flat V a φ s₁) s₀ k

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
section
noncomputable section

open scoped Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.Doubling GlobalTheory.Cont

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

variable {D : D7} {n : ℕ}

def IsSection (χ : (AE D)ˣ →* Circle) (s : ℂ) (φ : G D n → ℂ) : Prop :=
  (∀ p ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat p) = a.1 → ∀ g,
    φ (p * g) = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) *
      npow (absA D (Matrix.GeneralLinearGroup.det a)) (s + (n : ℂ) / 2) * φ g) ∧
  Continuous φ ∧ IsKFinite (K D n) φ

def stdSec (H : G D n → ℝ≥0) (φ : G D n → ℂ) (s₁ s : ℂ) : G D n → ℂ := fun g => φ g * npow (H g) (s - s₁)

end GlobalTheory.StdUnn

namespace GlobalTheory.Published

open GlobalTheory.StdUnn

end GlobalTheory.Published

end
end

