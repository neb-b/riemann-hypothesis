module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt

namespace GlobalTheory.Published.Amb

def MixOn {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (D : ℕ) (ι : Type) [Fintype ι]
    (M : HermLB p) (L : ι → HermLB p) : Prop :=
  ∀ (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ), IsArFun (fun o : Option ι => o.elim M L) D Φ →
    ∀ (n : ι → ℤ) (h : X → ℝ), (comb L n).IsArithHeight h →
    ∀ (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), (comb L n).ArchIntegrable M D hr ∧
      Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) =
        ∑ᶠ z, ((M.div hr).mult z : ℝ) * h z - (comb L n).archInt M D hr

end GlobalTheory.Published.Amb
