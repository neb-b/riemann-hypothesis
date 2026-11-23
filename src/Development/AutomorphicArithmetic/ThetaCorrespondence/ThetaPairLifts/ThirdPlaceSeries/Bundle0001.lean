module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0322

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsRc
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain
namespace GlobalTheory.TypeRec
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
local instance  (D : D7) (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
def IsSeriesCorrespondence (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {D : D7} (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D)
    (rc : GlobalTheory.SerSys.Corr D) : Prop :=
  ∀ k v n (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)))
    (π : Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k])), Nonempty (π ≅ pull I k v σ) →
    T.e _ (rc k v n π) = _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 (D.naut.plGw k v)) (GlobalTheory.LocLanglands.cls σ)
end GlobalTheory.TypeRec
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NbcOf
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.AutQuot
variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
variable {L n}
variable (L n)
variable {L n}
section
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
end
end GlobalTheory.AutQuot
end
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.AutQuot
variable (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut)
open Classical in
def locOf_alt (π : NG.AutRep D.host.E D.R.nV) (w : PlE D.host) : D.naut.LP w :=
  if h : ∃ x, LocAt π w x then (T.e w).symm (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) h.choose)
  else D.naut.lpZero w
set_option synthInstance.maxHeartbeats 400000 in
def boundaryConditionOfNoLocal (hE : IsEmpty D.nd.Loc) : NBC D.naut where
  AU := fun _ => AUq D.host.E D.R.nV
  multAU := fun _ X => X.rep.mult
  sphAU := fun _ X w => ∃ v, NG.OverPl w v ∧ X.rep.SphAt v
  locAU := fun _ X w => _root_.GlobalTheory.AutQuot.locOf_alt hL D T X.rep w
  satAU := fun _ X w => satOf X.rep w
  satAU_card := fun _ X w => satOf_card X.rep w
  Wt := fun _ => WtQ D.host.E D.R.nV
  infW := fun _ Y τ => NG.infOf (hwOf Y.rep τ)
  infW_card := fun _ Y τ => infOf_card _
  wtAU := fun _ X => wtOf D X.rep
  infW_alg := fun _ Y τ => infOf_nodup_alg (hwOf_antitone Y.rep τ)
  embAV := fun i => isEmptyElim i
  embAV_inj := fun i => isEmptyElim i
  embAV_loc := fun i => isEmptyElim i
  embAV_sat := fun i => isEmptyElim i
  embAV_sph := fun i => isEmptyElim i
  embAV_inf := fun i => isEmptyElim i
end GlobalTheory.AutQuot
end
end
end

