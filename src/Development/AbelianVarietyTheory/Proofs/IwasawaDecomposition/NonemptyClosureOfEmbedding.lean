module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0531

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DRFlag GlobalTheory.ProjSpace
open GlobalTheory.FlagMod (ev ev_spMap le_preimage_comp)

namespace GlobalTheory.SubClosure

section General

variable {O S S' : Type} [CommRing O] [CommRing S] [CommRing S'] {N : ℕ}

instance subsingleton_sp (K : Type) [Field K] : Subsingleton (Sp K) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum K))

end General

end GlobalTheory.SubClosure
