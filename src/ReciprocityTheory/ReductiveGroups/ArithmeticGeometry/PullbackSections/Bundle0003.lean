module

public import Formalism.SharpRestriction.Divisibility.WeightAlgebra

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra

def SpanAt {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (ka : WeightFamilies.Wt D j) : Prop :=
  Submodule.span B.KO ((X.shortTh ka : Submodule (𝓞 B.KO) (B.Cusp j ka)) : Set (B.Cusp j ka)) = ⊤

def LatOfLamSt : Prop :=
  ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j)
    (large₂ : SizeData₂ D) (C A : ℝ), (∀ i, 0 < D.host.g i) → S.sK ≠ 0 →
    (∀ F : B.Cusp j ka, F ∈ B.Mlat j ka → F ≠ 0 →
      -(WeightFamilies.PP0v D large₂ C A * (1 + Real.log ka.size) * ka.size) ≤ WeightFamilies.meanLogSup B F) →
    SpanAt X ka → H2 X S ka wL wF → Submodule.IsLattice B.KO (B.Mlat j ka)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra

def SupBoundPageRows (D : D7) (large₂ : SizeData₂ D) {j : ℕ} (ka : WeightFamilies.Wt D j) : Prop :=
  (∀ i, Real.log (D.host.g i) ≤ 9 * large₂.sc.L + 1) ∧
  lrd D ≤ 2 * large₂.sc.L ∧
  Real.log D.host.d ≤ 2 * large₂.sc.L ∧
  Real.log (Ideal.absNorm D.host.ccK) ≤ 2 * large₂.sc.L ∧
  Real.log D.R.f ≤ 2 * large₂.sc.L ∧
  Real.log D.host.pde ≤ large₂.sc.L ∧
  Real.log D.host.pde' ≤ large₂.sc.L ∧
  Real.log (1 + DF ka) ≤ 2 * large₂.sc.L ∧
  Real.log ka.n ≤ large₂.sc.L

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

