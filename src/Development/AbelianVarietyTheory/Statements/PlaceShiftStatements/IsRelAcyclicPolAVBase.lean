module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsL2OnDiagonalOfIsL2Metric
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SubsingletonOfForallIsMaximalSmulEqZero
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxForm (IsRelAcyclic)
open GlobalTheory GlobalTheory.AbLaw
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleSymModel

def polPull {S : Scheme.{0}} (P : Out.PolAV S) {R : Type} [CommRing R] (f : Sp R ⟶ S) : Out.PolAV (Sp R) :=
  have h := isGrpPullback_pullback P.A f
  have hL' := pull_isLB P.isLB (pullback.fst P.A.hom f)
  have := P.isAb.proper
  { A := (Over.pullback f).obj P.A
    isAb := isAbelianScheme_pullback_obj f P.A P.isAb
    g := P.g
    smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
    L := P.L.pull (pullback.fst P.A.hom f)
    isLB := hL'
    rigid := PolBaseChange.rigidified_pull h P.rigid
    sym := PolBaseChange.sym_pull h P.sym
    ample := AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample h.1
    ktriv := by
      obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl hL'
      exact kTriv_pull h P.isLB hL' ((isGen_iff w).1 hw) P.ktriv }

end GlobalTheory.AmpleSymModel
