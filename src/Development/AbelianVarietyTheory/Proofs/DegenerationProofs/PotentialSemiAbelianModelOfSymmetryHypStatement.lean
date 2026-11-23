module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PotentialSemiAbelianModelOfSymmetryHyp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potentialSemiAbelianModel_of_symmetryHyp : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (Q : Out.PolAV (Sp K)), (letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L) → PotModel V K Q.A (fun _ _ _ G _ => IsSemiAbelian G) := by
  first | exact @GlobalTheory.SymSemistable.potModel_semiAbelian_of_hypS | exact GlobalTheory.SymSemistable.potModel_semiAbelian_of_hypS | (intros; apply GlobalTheory.SymSemistable.potModel_semiAbelian_of_hypS <;> assumption)
