module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JetSubstPCompJetBC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIsoIntegralModelsMatchingLieBases
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantCoeffEv
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0087

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsChartPull
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain

namespace GlobalTheory.DepthExt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem grp_id {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 _) (𝟙 _) :=
  ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun _ x y x₀ y₀ hx hy =>
    (mul_left_congr (Category.comp_id _) x₀ y₀ x y (hx.trans (Category.comp_id _))
      (hy.trans (Category.comp_id _))).trans (Category.comp_id _).symm⟩

section Tangent
variable {V V' : Type} [CommRing V] [CommRing V']

theorem comb_iff (t : SAB H (Sp V)) {m : ℕ} (v : Fin m → (epsR V ⟶ t.G)) (cf : Fin m → V) (w : epsR V ⟶ t.G) :
    IsLieComb cf v w ↔ IsCombAtG t (𝟙 _) (fun i => (v i).left) cf w.left := by
  simp only [Chart.comb_push (grp_id t.G), Category.comp_id]
  exact Iff.rfl

theorem tan_iff (t : SAB H (Sp V)) (w : epsR V ⟶ t.G) : IsTangent w ↔ IsTanAtG t (𝟙 _) w.left := by
  simp only [Chart.tan_push (grp_id t.G), Category.comp_id]
  exact ⟨fun h => ⟨(Over.w w).trans (Category.comp_id _).symm, h⟩, fun h => h.2⟩

variable (ψ : V →+* V') {t : SAB H (Sp V)} {t' : SAB H (Sp V')} (mp : SABMap t' t (spMap ψ))

end Tangent

end GlobalTheory.DepthExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FiniteTorsionSpecialFibreOfUnif
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem finite_torsion_of_pullback {S S' Z : Scheme.{0}} (G : Over S) [GrpObj G] (f : S' ⟶ S) (t : Z ⟶ S')
    (r : Z ⟶ S) (hr : t ≫ f = r) (N : ℕ)
    (h : Finite {x : Over.mk t ⟶ (Over.pullback f).obj G // x ^ N = 1}) :
    Finite {x : Over.mk r ⟶ G // x ^ N = 1} := by
  subst hr
  let e := ObjPull.pushEquiv (isGrpPullback_pullback G f) (Over.mk t)
  refine Finite.of_injective (β := {x : Over.mk t ⟶ (Over.pullback f).obj G // x ^ N = 1})
    (fun x => ⟨e.symm x.1, ?_⟩) ?_
  · have hx : (show Over.mk ((Over.mk t).hom ≫ f) ⟶ G from x.1) ^ N = 1 := x.2
    rw [← map_pow, hx, map_one]
  · intro x y hxy
    exact Subtype.ext (e.symm.injective (congrArg Subtype.val hxy))

theorem finite_torsion_special_fibre_of_unif : ∀ (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G] (D : Out.DegData T (maximalIdeal T)) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing T)))) (_ : Out.UnifPre (maximalIdeal T) D A G) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (β : T →+* Ω), (∀ a ∈ maximalIdeal T, β a = 0) → ∀ N : ℕ, 1 ≤ N → Finite {x : Over.mk (spMap β) ⟶ G // x ^ N = 1} := by
  intro T _ _ _ G _ _ D A U Ω _ _ β hβ N hN
  let β' : T ⧸ (maximalIdeal T) ^ (0 + 1) →+* Ω :=
    Ideal.Quotient.lift _ β (fun a ha => hβ a (by simpa using ha))
  have g := U.gt 0
  have : IsCommMonObj (Out.thickObj T (maximalIdeal T) 0 G) := Functor.isCommMonObj_obj
  have h := GlobalTheory.TorusExtTorsion.finite_torsion_geomPoint _ (Out.thickObj T (maximalIdeal T) 0 G) (Out.thickObj T (maximalIdeal T) 0 D.toPre.P.A)
    D.toPre.X g.q g.i g.q_hom g.i_hom g.isKernel (Out.TLinPf.isAb_pullback _ _ D.toPre.P.isAb) Ω
    (Geo.Tor.spMap β') N hN
  refine finite_torsion_of_pullback G (Out.thick T (maximalIdeal T) 0) (Geo.Tor.spMap β') _ ?_ N h
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

end GlobalTheory
end

