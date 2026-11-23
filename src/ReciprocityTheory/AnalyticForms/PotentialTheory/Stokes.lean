module

public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsSt
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.HessCRestrictThm
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
public import ReciprocityTheory.AnalyticForms.PotentialTheory.StokesD

@[expose] public section

namespace ReciprocityTheory.AnForm.M

open MeasureTheory FinHolAtlas
open scoped ContDiff

noncomputable section

def LocalSymmStatement : Prop :=
  ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (e + 1) X) (j : Fin A.n) (χ w : X → ℝ), A.Smooth χ → A.Smooth w →
    tsupport χ ⊆ (A.chart j).source → ∀ Φ : Fin e → LocPot X, (∀ i, IsPotential A (Φ i)) →
      mInt A (Fin.cons (LocPot.ofFun w) Φ) χ = mInt A (Fin.cons (LocPot.ofFun χ) Φ) w

theorem localSymm : LocalSymmStatement := by
  intro e X _ _ _ A _ χ w hχ hw _ Φ hΦ
  exact st_byPartsSymm_of ReciprocityTheory.AnForm.A.parts_thm A χ w hχ hw Φ hΦ

theorem stokes : StokesStatement := st_stokes_of ReciprocityTheory.AnForm.A.parts_thm
theorem byPartsSymm : ByPartsSymmStatement := st_byPartsSymm_of ReciprocityTheory.AnForm.A.parts_thm
theorem byPartsNonpos : ByPartsNonposStatement :=
  st_byPartsNonpos_of ReciprocityTheory.AnForm.A.parts_thm ReciprocityTheory.AnForm.A.gradDensNonneg_thm
theorem massIndep : MassIndepStatement := st_massIndep_of ReciprocityTheory.AnForm.A.parts_thm

end

end ReciprocityTheory.AnForm.M
