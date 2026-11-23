module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0027
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveJetsUnitBall
public import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.FinalA

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.LatModel
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM
open Formalism.L2.Th1

structure LatModel (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l]) (g2 g3 : ℂ_[l]) :
    Prop where
  eq2 : g2 = ι L.g₂
  eq3 : g3 = ι L.g₃
  n2 : ‖g2‖ ≤ 1
  n3 : ‖g3‖ ≤ 1

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedKerProd
section
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

theorem kerProd (d : ℕ) (L : PeriodPair) (hsq : Squarefree d) (hd4 : d % 4 = 3) (hCM : HasCMBy d L) (l : ℕ)
    (hl : l.Prime) (h5 : 5 ≤ l) (hld : ¬ l ∣ d) (e : ℕ) (he : e = 2 ∨ e = 3 ∧ d ≠ 3) :
    KerProdAt d L l e := by
  rcases he with he | ⟨he, hd3⟩
  · exact kerProd_prin d L hd4 hCM l hl h5 hld e (Or.inl he)
  · by_cases h3 : 3 ∣ d
    · subst he
      exact kerProd_ideal d L hsq hd4 hCM l hl h3 hd3
    · exact kerProd_prin d L hd4 hCM l hl h5 hld e (Or.inr ⟨he, h3⟩)

end ReciprocityTheory.ChartRestriction.L1
end
end

