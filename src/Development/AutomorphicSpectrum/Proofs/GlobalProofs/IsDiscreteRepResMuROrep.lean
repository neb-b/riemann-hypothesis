module

public import Mathlib
public import ReciprocityTheory.Hypotheses.GalCoh
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.LocalMaps
public import GroundTheory.ProfiniteCohomology.CohomologicalDimension.Subgroup
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.EqZeroOfBrauerLocalApplyEqZero
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.OpenSubgroups
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.Vanishing

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.GSCd

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global FiniteSubfield
open GroundTheory.Global.IdeleGroup GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open scoped DirectSum

noncomputable section

attribute [local instance 2000] Rep.hV2

variable (K : FiniteSubfield) (S : Finset (HeightOneSpectrum (𝓞 K.1)))

abbrev Gs : Type := galUnramifiedOutside K.1 (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K.1)))

end
end GlobalTheory.CompanionTheory.GSCd
