module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsStandardSmoothOfRelativeDimensionAwayJacobian
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusToAbelianVarietyConst
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RingKrullDimLeOfQuasiFinite

@[expose] public section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.WeierstrassCurve (scheme toSpec chartZ)
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ProjHol

theorem valuationRing_stalk {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Sp K)
    [hf : SmoothOfRelativeDimension 1 f] (x : X) : ValuationRing (X.presheaf.stalk x) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : GlobalTheory.IsNormalScheme X := GlobalTheory.isNormalScheme_of_smooth f
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have h : Order.coheight x ≤ 1 := by simpa using GlobalTheory.AffineCover.coheight_le_of_smooth f hf x
  rcases h.eq_or_lt with h | h
  · have := GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk h
    infer_instance
  · have h0 : Order.coheight x = 0 := by simpa using h
    have : Ring.KrullDimLE 0 (X.presheaf.stalk x) := krullDimLE_of_coheight_le h0.le
    letI := (Ring.KrullDimLE.isField_of_isDomain (R := X.presheaf.stalk x)).toField
    exact ValuationRing.of_field _

end GlobalTheory.ProjHol
