module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorsionEqOneOfTranslationKeepsRatios

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaGroupTest

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
  ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits GlobalTheory.ThetaScalar

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S}

theorem weilIs_unique_of_local (p : T.left) (hp : ∀ V : T.left.Opens, p ∈ V → V = ⊤) (hL : L.IsLB) {x y : T ⟶ A}
    {c c' : Γ(T.left, ⊤)ˣ} (h : WeilIs A L k x y c) (h' : WeilIs A L k x y c') :
    unitRes (T := T) ⊤ c = unitRes (T := T) ⊤ c' := by
  obtain ⟨V, hV, ⟨θx, θy, hx, hy⟩, H⟩ := h p
  obtain ⟨V', hV', -, H'⟩ := h' p
  obtain rfl := hp V hV
  obtain rfl := hp V' hV'
  exact commIsOf_unique hL θx θy _ _ (H θx θy hx hy) (H' θx θy hx hy)

end GlobalTheory.ThetaGroupTest
