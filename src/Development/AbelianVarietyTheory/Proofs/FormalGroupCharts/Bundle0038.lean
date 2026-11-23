module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0046
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0022
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0019
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0022

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem chartIndependence_unconditional : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 :=
  Formalism.MainNotions.ModuliIntegralCharts.H1.chartIndep2_of_glob
    GlobalTheory.lawsFieldsSeparately.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIsNabUncond
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.CanonConn

theorem exists_isNab_uncond : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∃ (_ : StarRing (𝓞 E)) (nab : NabV Xo c), IsNab Xo c nab :=
  GlobalTheory.CanonConn.exists_isNab GlobalTheory.firstFiveLaws.1

end GlobalTheory.CanonConn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IntegralFramedPointDiagonalBiextensionIsoCompati
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory

theorem chartPrimTr_holds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ChartPrimTrSt Xo c := by
  intro E _ _ _ H Dw l Xo c T io y I wPT hT
  obtain ⟨wP, hP⟩ := GermB.exists_wP Xo.univ.t
  obtain ⟨w₁, hw₁, h₁⟩ := _root_.GlobalTheory.primG_pullback E H _ _ _ _ _ I.m1 I.w1 I.rig1 wP hP
  obtain ⟨w₂, hw₂, h₂⟩ := _root_.GlobalTheory.primG_pullback E H _ _ _ _ _ I.m2 I.w2 I.rig2 wPT hT
  have hab := GlobalTheory.isAbelianScheme_of_pullback_univ E H Dw l Xo _ _ _ I.m1
  have e : w₁ = w₂ := _root_.GlobalTheory.isPrimG_unique GlobalTheory.firstFiveLaws.1.globalFns E H _ I.t' hab w₁ w₂ hw₁ hw₂
  subst e
  exact ⟨wP, (isPrim_iff wP).2 hP, w₁, hw₁.1, h₂, h₁⟩

end GlobalTheory
end

