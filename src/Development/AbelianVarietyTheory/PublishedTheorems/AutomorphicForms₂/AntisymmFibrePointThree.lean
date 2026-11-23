module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0505

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open scoped Matrix ComplexOrder

namespace GlobalTheory.GoodMetric.Model

theorem exists_flagSpace {F : Type} [Field F] (X : Var F) {ι : Type} [Fintype ι] {m : ι → ℕ} (E : Fr (ratOf X) m 0) :
    ∃ (Y : Var F) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (gr : Root m → Y.Dv),
      Y.dim = X.dim + ∑ τ, (m τ).choose 2 ∧ Refines E E' φ f ∧ IsGraded E' gr := by
  obtain ⟨Y, φ, f, E', hd, hR⟩ := tower _ (ratOf X) X.dim E (good_ratOf X) (fun _ => Nat.zero_le _) rfl
  obtain ⟨B, hB⟩ := E'.nonempty (genericPoint Y.X)
  obtain ⟨gr, hgr⟩ := GlobalTheory.ShFam.GradedDiv.exists_div E' hB
  refine ⟨Y, E', φ, f, fun x => gr x.1 x.2, by simpa using hd, hR, B, hB, fun y x => ?_⟩
  obtain ⟨A, hA, t, h1, -, h3⟩ := hgr y
  exact ⟨A, hA, t x.1 x.2, h1 _ _, h3 _ _⟩

end GlobalTheory.GoodMetric.Model
