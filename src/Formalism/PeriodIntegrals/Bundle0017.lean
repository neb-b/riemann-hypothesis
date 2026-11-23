module

public import Formalism.PeriodIntegrals.Bundle0015
public import Mathlib
public import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.QmRowExp
section
namespace PI

def QmRowExp : Prop := ExpFirstRow ∧ ExpLastRow

end PI
end

-- bundled from Formalism.PeriodIntegrals.QmRowForm
section
namespace PI

def QmRowForm : Prop := RowForm

end PI
end

-- bundled from Formalism.PeriodIntegrals.QmSkip
section
namespace PI

def QmSkip : Prop := SkipSucc ∧ SkipSucc2

end PI
end

-- bundled from Formalism.PeriodIntegrals.QmStar
section
namespace PI

def QmStar : Prop := StarMinor

end PI
end

-- bundled from Formalism.PeriodIntegrals.QuotProdK
section
noncomputable section

open MeasureTheory

namespace PI.QuotProdK

def QuotProdK : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ι → ℕ) (ε : ∀ v, Fin (n v) → Bool)
    (N H : ∀ v, Set (Formalism.REAL.UJ (ε v))),
    (∀ v, IsClosed (N v)) → (∀ v, IsCompact (H v)) →
    (∀ v, (1 : Formalism.REAL.UJ (ε v)) ∈ N v ∧ (∀ a ∈ N v, ∀ b ∈ N v, a * b ∈ N v) ∧ ∀ a ∈ N v, a⁻¹ ∈ N v) →
    (∀ v, (1 : Formalism.REAL.UJ (ε v)) ∈ H v ∧ (∀ a ∈ H v, ∀ b ∈ H v, a * b ∈ H v) ∧ ∀ a ∈ H v, a⁻¹ ∈ H v) →
    (∀ v, ∀ h ∈ H v, ∀ m ∈ N v, h * m * h⁻¹ ∈ N v) →
    (∀ v (μ : Measure (Formalism.REAL.UJ (ε v))), SigmaFinite μ → μ ≠ 0 → μ (N v)ᶜ = 0 →
      (∀ s ∈ N v, μ.map (fun x => s * x) = μ) → ∀ s ∈ N v, μ.map (fun x => x * s) = μ) →
    ∀ muN muH nuQ : Measure (∀ v, Formalism.REAL.UJ (ε v)),
      (SigmaFinite muN ∧ muN ≠ 0 ∧ muN (Set.pi Set.univ N)ᶜ = 0 ∧
        ∀ s ∈ Set.pi Set.univ N, muN.map (fun x => s * x) = muN) →
      (SigmaFinite muH ∧ muH ≠ 0 ∧ muH (Set.pi Set.univ H)ᶜ = 0 ∧
        ∀ s ∈ Set.pi Set.univ H, muH.map (fun x => s * x) = muH) →
      (∀ f : (∀ v, Formalism.REAL.UJ (ε v)) → ENNReal, Measurable f →
        ∫⁻ x, f x ∂(Measure.pi fun v => Formalism.REAL.muG (ε v)) =
          ∫⁻ x, (∫⁻ s, f (s * x) ∂((muN.prod muH).map (fun p => p.1 * p.2))) ∂nuQ) →
      ∃ (μS νl : ∀ v, Measure (Formalism.REAL.UJ (ε v))) (C : ENNReal), C ≠ 0 ∧ C ≠ ⊤ ∧
        (∀ v, (SigmaFinite (μS v) ∧ μS v ≠ 0 ∧ μS v {s | ∃ m ∈ N v, ∃ h ∈ H v, s = m * h}ᶜ = 0 ∧
          ∀ s ∈ {s | ∃ m ∈ N v, ∃ h ∈ H v, s = m * h}, (μS v).map (fun x => s * x) = μS v) ∧
          ∀ F : Formalism.REAL.UJ (ε v) → ENNReal, Measurable F →
            ∫⁻ x, F x ∂(Formalism.REAL.muG (ε v)) = ∫⁻ x, (∫⁻ s, F (s * x) ∂(μS v)) ∂(νl v)) ∧
        ∀ F : ∀ v, Formalism.REAL.UJ (ε v) → ENNReal, (∀ v, Measurable (F v)) →
          (∀ v, ∀ m ∈ N v, ∀ h ∈ H v, ∀ x, F v (m * h * x) = F v x) →
          ∫⁻ x, ∏ v, F v (x v) ∂nuQ = C * ∏ v, ∫⁻ y, F v y ∂(νl v)

end PI.QuotProdK
end
end

-- bundled from Formalism.PeriodIntegrals.UJUnimod
section
noncomputable section

open MeasureTheory

namespace PI.UJUnimod

def UJRightInv : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool), (Formalism.REAL.muG ε).IsMulRightInvariant

end PI.UJUnimod
end
end

