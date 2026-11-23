module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0018

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.NLink

structure Hypotheses₂ : Prop where
  font : GlobalTheory.Published.FontaineBcris
  artin : GlobalTheory.Published.GlobalArtinReciprocity
  bk : GlobalTheory.Published.BlochKatoLocal
  tate : Formalism.GaloisCohomology.LocalTateDualityK
  euler : Formalism.GaloisCohomology.LocalEulerCharK
  fin : Formalism.GaloisCohomology.LocalFinitenessK
  bs : GlobalTheory.Published.BhattScholzeIntegral

variable {D : D7}

def rowC (C₂ : ℝ) : KillingConditions.RowK := ⟨C₂, 320, 25, 23, 32, 32⟩

def SetPt (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) : Prop :=
  TruncatedSeriesCountingIdentities.admG1 i r ∧ TruncatedSeriesCountingIdentities.admG2 i r ρ π ∧ TruncatedSeriesCountingIdentities.admG3 i r ρ π ∧ TruncatedSeriesCountingIdentities.admG4 i r ∧ TruncatedSeriesCountingIdentities.admG5 i r ∧ TruncatedSeriesCountingIdentities.TameGeneratorConditions i ∧
    TruncatedSeriesCountingIdentities.admG6 i r ∧ TruncatedSeriesCountingIdentities.admBK i ∧ TruncatedSeriesCountingIdentities.FamilyContinuous i r ∧ TruncatedSeriesCountingIdentities.admSS i r ∧ TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π ∧ TruncatedSeriesCountingIdentities.CyclotomicInertiaImage i ∧
    TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i ∧ TruncatedSeriesCountingIdentities.CyclotomicCompletionAdmissible i ∧ TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i ∧ TruncatedSeriesCountingIdentities.admH2 i ∧ TruncatedSeriesCountingIdentities.UnramifiedClassFieldBound i

def WAll (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    EmbeddingTypeJumps.WachHypothesisLocal (LocalSituation.sit D.loc HW l (D.locA l) K s LL h) ((F l).E K s LL h).tie

end GlobalTheory.NLink

end
