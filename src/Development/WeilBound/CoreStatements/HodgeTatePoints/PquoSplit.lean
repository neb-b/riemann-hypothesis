module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0162
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0022

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace PositivityTheory.HtPt.Pquo

theorem split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (r : V →+* ℂ) (tV : SAB H (Sp V)), Function.Surjective r → RingHom.ker r = IsLocalRing.maximalIdeal V → ∀ P : AbPart tV (spMap r), GlobalTheory.LN.SplitOver tV.G (IsLocalRing.maximalIdeal V) := by
  intro E _ _ _ H V _ _ _ r tV hs hk P
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ℂ →+* V ⧸ IsLocalRing.maximalIdeal V,
      ψ.comp r = Ideal.Quotient.mk (IsLocalRing.maximalIdeal V) :=
    ⟨r.liftOfRightInverse _ (Function.rightInverse_surjInv hs)
      ⟨Ideal.Quotient.mk (IsLocalRing.maximalIdeal V), by rw [hk, Ideal.mk_ker]⟩,
      RingHom.liftOfRightInverse_comp _ _ _ _⟩
  letI : Field (V ⧸ IsLocalRing.maximalIdeal V) := Ideal.Quotient.field _
  have e : spMap ψ ≫ spMap r = spMap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal V)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
  obtain ⟨T⟩ := GlobalTheory.SS.nonempty_torusExtension_pullback (Ω := V ⧸ IsLocalRing.maximalIdeal V) (spMap ψ) P.tK.G ⟨P.τ⟩
  obtain ⟨i, hi, -⟩ := grpPullback_iso
    (((isGrpPullback_pullback P.tK.G (spMap ψ)).comp P.m.cart).congr e rfl)
    (isGrpPullback_pullback tV.G (spMap (Ideal.Quotient.mk (IsLocalRing.maximalIdeal V))))
  exact GlobalTheory.exists_splitExt_isGt_of_torusExtension (V ⧸ IsLocalRing.maximalIdeal V) _ ⟨torusExtOfIso i T⟩

end PositivityTheory.HtPt.Pquo
