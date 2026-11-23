module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntegralFramedPointBaseChangeCdvrTransitiv
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniformisedChartAfterValuationRingExt
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0053
public import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsFiniteExtUniformisedChartRationalTorsion
section
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
namespace GlobalTheory.PlacePrep

theorem exists_good_chart_allRat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), T.FinRes → ∀ M : ℕ, 0 < M → ∃ (T' : CDVR) (iT : T.Fr →+* T'.Fr) (e : ℕ) (y' : IntFr Xo c T' (iT.comp io)) (C' : IntegralChartA3 Xo c T' (iT.comp io) y'), IsExt y iT e y' ∧ T'.FinRes ∧ Good3 C' ∧ AllRat Xo (xOf y') M := by
  intro E _ _ _ H Dw l Xo c _ hstar T io y hfin M hM
  obtain ⟨T₁, i₁, e₁, y₁, C₁, hext₁, hfin₁, hgood₁⟩ := _root_.GlobalTheory.PlaceInt.exists_ext_intChart_unif E H Dw l Xo c hstar T io y hfin
  obtain ⟨L, _, _, hL, hrat⟩ := (_root_.GlobalTheory.torsion_rational_over_finite_extension E H Dw l Xo T₁.Fr (xOf y₁) M hM).1
  obtain ⟨T₂, i₂, e₂, ψ, φ, he₂, hv₂, hψ, -, hfin₂⟩ := GlobalTheory.PlaceExtField.exists_cdvr_finite_extension T₁ L
  obtain ⟨⟨y₂, hext₂⟩, hy⟩ := _root_.GlobalTheory.PlaceInt.exists_isExt_and_trans E H Dw l Xo c T₁ T₂ (i₁.comp io) y₁ i₂ e₂ he₂ hv₂
  have hx₂ := (hy y₂ hext₂).1
  obtain ⟨C₂, hgood₂⟩ := _root_.GlobalTheory.GoodChartExt.exists_good_chart_ext E H Dw l Xo c hstar T₁ (i₁.comp io) y₁ C₁ hgood₁ T₂ i₂ e₂ y₂ hext₂
  have htr := ((_root_.GlobalTheory.PlaceInt.exists_isExt_and_trans E H Dw l Xo c T T₁ io y i₁ e₁ hext₁.1 hext₁.2.1).2 y₁ hext₁).2 T₂ i₂ e₂ y₂ hext₂
  have hrat₂ := ((_root_.GlobalTheory.torsion_rational_over_finite_extension E H Dw l Xo L _ M hM).2 hrat).1 T₂.Fr ψ.toRingHom
  have hi : i₂ = ψ.toRingHom.comp (algebraMap T₁.Fr L) := RingHom.ext fun a => (hψ a).symm
  have hsp : spMap ψ.toRingHom ≫ spMap (algebraMap T₁.Fr L) ≫ xOf y₁ = xOf y₂ := by
    rw [hx₂, hi, ← Category.assoc]
    congr 1
    simp only [spMap, ← Spec.map_comp]
    rfl
  rw [hsp] at hrat₂
  exact ⟨T₂, i₂.comp i₁, e₂ * e₁, y₂, C₂, htr, hfin₂ hfin₁, hgood₂, hrat₂⟩

end GlobalTheory.PlacePrep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ScaledThetaLatticeLeSupLatticeEveryWeightStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie GlobalTheory.PlaceTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaledThetaLattice_le_supLattice_every_weight : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D), Oriented T EX → ∀ w : WeightFamilies.Wt D j, GlobalTheory.RunIn.ThInt (recPJ h j hj) hinj EX w := by
  first | exact @GlobalTheory.PlaceTop.thInt_of_oriented | exact GlobalTheory.PlaceTop.thInt_of_oriented | (intros; apply GlobalTheory.PlaceTop.thInt_of_oriented <;> assumption)
end

