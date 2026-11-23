module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepPrincipalSiegelAdjointOrderActionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rep_principalSiegel_adjoint_orderAction : ∀ (h' M : ℕ), 1 ≤ h' → 3 ≤ M → Odd M → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (eO : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d₀ : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range eO) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d₀ → ∑ i, ∑ j, W i j • (eO j * bar (eO i)) = (d₀ : O) → ∃ (H : Scheme.{0}) (sH : H ⟶ Sp (cycAway M)) (zH : SiegPre h' M (zetaAway M) sH) (actH : O → (zH.A ⟶ zH.A)), zH.Principal ∧ IsRAct zH.A actH ∧ Adj zH.A zH.P bar actH ∧ IsQProjOver sH ∧ IsLocallyNoetherian H ∧ ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (z : SiegPre h' M (zetaAway M) t) (act : O → (z.A ⟶ z.A)), z.Principal → IsRAct z.A act → Adj z.A z.P bar act → ∃! g : S ⟶ H, g ≫ sH = t ∧ ActPB z act zH actH g := by
  first | (exact @GlobalTheory.ActSieg.exists_rep) | (exact GlobalTheory.ActSieg.exists_rep) | (intros; apply GlobalTheory.ActSieg.exists_rep  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTripleChartUnitaryBoundaryPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tripleChart_unitary_boundary_point : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x := by
  first | exact @GlobalTheory.UChart.uPre_of_boundary | exact GlobalTheory.UChart.uPre_of_boundary | (intros; apply GlobalTheory.UChart.uPre_of_boundary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOfRelativeDimension_repFam_of_isQProjOver : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ F : RepFam b N, IsQProjOver F.s → SmoothOfRelativeDimension (D.a * (D.n - 1)) F.s := by
  first | (exact @GlobalTheory.UPel.HT.RepFam.smoothOfRelativeDimension) | (exact GlobalTheory.UPel.HT.RepFam.smoothOfRelativeDimension) | (intros; apply GlobalTheory.UPel.HT.RepFam.smoothOfRelativeDimension  <;> assumption)
end

