module

public import Formalism.Bundle0001

@[expose] public section

-- bundled from Formalism.DefsOC
section
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

def Sa (a : ℕ → ℝ) (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * (x / n - 1)

def MellinSgen : Prop :=
  ∀ (a : ℕ → ℝ) (K : ℝ), (∀ n : ℕ, |a n| ≤ K * ArithmeticFunction.vonMangoldt n) →
    Measurable (Sa a) ∧
    (∀ σ : ℝ, 1 < σ → IntegrableOn (fun x : ℝ => |Sa a x| * x ^ (-σ - 1)) (Ioi 1)) ∧
    ∀ s : ℂ, 1 < s.re →
      ∫ x in Ioi (1:ℝ), (Sa a x : ℂ) * (x : ℂ) ^ (-s - 1) =
        LSeries (fun n => (a n : ℂ)) s / (s * (s - 1))

end Formalism
end
end

-- bundled from Formalism.StatementCM
section
open Finset

noncomputable section

namespace Formalism

def counts {l : ℕ} (Φ : Finset (ZMod l)ˣ) (σ : (ZMod l)ˣ) : Prop := σ ∉ Φ ∧ σ ≠ -1



end Formalism
end
end

-- bundled from Formalism.StatementU
section
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

def Gzbar (x : ℝ) : ℝ := ∫ u in (1 : ℝ)..2, u * Gz (x / u)

def GzLipschitz : Prop :=
  ∃ K : ℝ, ∀ t t' : ℝ, 1 / 2 ≤ t → 1 / 2 ≤ t' → |Gz t| ≤ K * t ∧ |Gz t - Gz t'| ≤ K * |t - t'|

end Formalism
end
end

