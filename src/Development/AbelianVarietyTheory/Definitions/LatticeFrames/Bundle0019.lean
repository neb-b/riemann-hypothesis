module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.SobContId
section
noncomputable section

open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaDens

variable {D : D7}

def Sobolev₂ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T S' T' : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T))
    (μ' : Measure (WO S' T')) (𝓕' : Set (WO S' T')) (Z : (WO S T → ℂ) → WO S' T' → ℂ) : Prop :=
  ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∃ U' : AddSubgroup (WO S' T'), IsOpen (U' : Set (WO S' T')) ∧
    (∀ f ∈ thetaLevel ψ S T U, Z f ∈ thetaLevel ψ S' T' U') ∧
    ∀ d : ℕ, ∃ (d' : ℕ) (C : ℝ≥0), ∀ f ∈ thetaLevel ψ S T U, sobO ψ θ μ' 𝓕' d (Z f) ≤ C * sobO ψ θ μ 𝓕 d' f

theorem sobCont_id (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) :
    Sobolev₂ ψ θ μ 𝓕 μ 𝓕 id := fun U hU => ⟨U, hU, fun _ h => h, fun d => ⟨d, 1, fun _ _ => by simp⟩⟩

def SobBdd (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) {S T : HSp D} (μ : Measure (WO S T)) (𝓕 : Set (WO S T))
    (L : (WO S T → ℂ) → GA D S → ℝ≥0∞) : Prop :=
  ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ K : Set (GA D S), IsCompact K →
    ∃ (d : ℕ) (C : ℝ≥0), ∀ f ∈ thetaLevel ψ S T U, ∀ x ∈ K, L f x ≤ C * sobO ψ θ μ 𝓕 d f

end GlobalTheory.ThetaDens

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepVanOfStepX
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.TupModel

variable {D : D7} {u : D.what₂.Word}

variable (d : Dat D u) (hb : d.Base)


section Ind

variable {c : Comm D} {𝒯 : Type} (t : 𝒯 → Tup c)

end Ind

end GlobalTheory.SeeSaw.TupModel

end
end

