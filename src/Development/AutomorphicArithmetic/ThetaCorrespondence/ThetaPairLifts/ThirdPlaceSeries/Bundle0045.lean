module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacteristicFunctionIntegralApply
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0020
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0293
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0003
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0041
public import Formalism.LocalToGlobal.Divisibility.DivisibilityConstruction.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0008
public import Formalism.LocalToGlobal.Divisibility.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1555
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0747
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0034
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0040
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0031
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.ConstituentConditionAtDistinguishedPrime
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0295
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0292

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MapMemISupIsLinAt
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.ThetaTri
open MeasureTheory Formalism.IndefR.Datum GlobalTheory.ThetaLoc
variable {D : D7} {V W : Formalism.BasicNotions.TH.HSp D}
  (om : Formalism.L2.Theta.GA D V × Formalism.L2.Theta.GA D W →* Module.End ℂ (WO V W → ℂ))
  {TauV Fm C : Type} [AddCommGroup TauV] [Module ℂ TauV]
  [AddCommGroup Fm] [Module ℂ Fm] [AddCommGroup C] [Module ℂ C]
  (fV : Fm →ₗ[ℂ] (Formalism.L2.Theta.GA D V → TauV)) (yv : C →ₗ[ℂ] (Formalism.L2.Theta.GA D W → ℂ))
  (νV : Measure (Formalism.L2.Theta.GA D V)) (𝓕V : Set (Formalism.L2.Theta.GA D V)) (νW : Measure (Formalism.L2.Theta.GA D W)) (𝓕W : Set (Formalism.L2.Theta.GA D W))
variable (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ) {G : Type} [Monoid G] (ω : G →* Module.End ℂ (WO V W → ℂ))
end GlobalTheory.ThetaTri
end
noncomputable section
namespace GlobalTheory.ThetaTri
open MeasureTheory Formalism.IndefR.Datum GlobalTheory.ThetaLoc
variable {D : D7} {V W : Formalism.BasicNotions.TH.HSp D}
  (om : Formalism.L2.Theta.GA D V × Formalism.L2.Theta.GA D W →* Module.End ℂ (WO V W → ℂ))
  {TauV Fm C : Type} [AddCommGroup TauV] [Module ℂ TauV]
  [AddCommGroup Fm] [Module ℂ Fm] [AddCommGroup C] [Module ℂ C]
  (fV : Fm →ₗ[ℂ] (Formalism.L2.Theta.GA D V → TauV)) (yv : C →ₗ[ℂ] (Formalism.L2.Theta.GA D W → ℂ))
  (νV : Measure (Formalism.L2.Theta.GA D V)) (𝓕V : Set (Formalism.L2.Theta.GA D V)) (νW : Measure (Formalism.L2.Theta.GA D W))
  (𝓕W : Set (Formalism.L2.Theta.GA D W)) (c : ℂ)
variable (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ) {G : Type} [Monoid G]
  (ω : G →* Module.End ℂ (WO V W → ℂ))
end GlobalTheory.ThetaTri
end
noncomputable section
namespace GlobalTheory.ThetaTri
open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ThetaLoc
open scoped TensorProduct
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}
def eWloc_alt (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) : (X.R.cV j).W ≃ₗ[ℂ] (P.M.loc i).wt.W := by
  have key : ∀ (k : ℕ) (hk : j.1 + 1 = k) (p1 : 1 ≤ k) (p2 : k ≤ D.R.m),
      (X.R.cV j).W ≃ₗ[ℂ] (P.M (D.nd.mu i) k p1 p2).wt.W := by
    rintro k rfl p1 p2
    exact A.eW _ hμ j
  exact key _ hj _ _
def formToVectorMap (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) :
    ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ) →ₗ[ℂ] (Formalism.L2.Theta.GA D (Vc D j) → (X.R.cV j).W) :=
  (X.R.cV j).ext ∘ₗ
    { toFun := fun F k => (_root_.GlobalTheory.ThetaTri.eWloc_alt A i j hj hμ).symm
        ((F : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) (A.a j * preF (A.PV j) k))
      map_add' := fun F F' => by funext k; simp
      map_smul' := fun c F => by funext k; simp }
def canonicalEmbedding' {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) :
    Y.A →ₗ[ℂ] Formalism.IndefR.Mult.MMap (X.R.MW j (sg0 D X.A)) :=
  Classical.choose hc
def canonicalConstant {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) : ℝ :=
  Classical.choose (Classical.choose_spec hc)
def thetaEvaluationMap {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) :
    ↥Y.C →ₗ[ℂ] (Formalism.L2.Theta.GA D (Wc D j) → ℂ) :=
  LinearMap.applyₗ (PiTensorProduct.map (fun τ => (lowT (X.R.MW j (sg0 D X.A)) τ).subtype)
      (kUnit (X.R.MW j (sg0 D X.A)))) ∘ₗ
    (PiTensorProduct.lift : Formalism.IndefR.Mult.MMap (X.R.MW j (sg0 D X.A)) ≃ₗ[ℂ] _).toLinearMap ∘ₗ _root_.GlobalTheory.ThetaTri.canonicalEmbedding' hc ∘ₗ Y.C.subtype
def standardWeilRepresentation (A : GlobalTheory.NJoin.Agree X P.M P.rep) (j : Fin D.R.m) (t : X.T) :
    GAf D.host.E D.R.nV × GAf D.host.E D.R.r →* Module.End ℂ (WO (Vc D j) (Wc D j) → ℂ) :=
  (X.R.ωP j t).comp ((A.PV j).ψ.prodMap (X.PW j).ψ)
def OmegaSubmoduleAtLocal (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    {Y : RowMod D P.rep (D.nd.j i)} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) :
    Submodule ℂ ((X.R.cV j).W →ₗ[ℂ] (WO (Vc D j) (Wc D j) → ℂ)) :=
  OmSub (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ) (_root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc) (X.R.νV j (X.tupT (D.nd.mu i)))
    (X.R.fdV j (X.tupT (D.nd.mu i))) (X.R.νW j) (X.R.fdW j) X.R.ψ
    (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i)))
def canonicalPairingValue (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    {Y : RowMod D P.rep (D.nd.j i)} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i))
    (φ : (X.R.cV j).W →ₗ[ℂ] (WO (Vc D j) (Wc D j) → ℂ))
    (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) (y : ↥Y.C) : ℂ :=
  lamV (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ) (_root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc) (X.R.νV j (X.tupT (D.nd.mu i)))
    (X.R.fdV j (X.tupT (D.nd.mu i))) (X.R.νW j) (X.R.fdW j) (_root_.GlobalTheory.ThetaTri.canonicalConstant hc : ℂ) φ F y
def standardSchwartzFunctionMap (j : Fin D.R.m) (t : X.T) : (X.R.cV j).W →ₗ[ℂ] (WO (Vc D j) (Wc D j) → ℂ) :=
  pureTensorO X.R.ψ X.R.θ (Vc D j) (Wc D j) (fun _ => 1) (cart (X.R.MW j (sg0 D X.A))) (X.R.BV j)
    (onb (X.R.MW j (sg0 D X.A))) (X.R.vP j t) ∘ₗ X.R.ioP j (kUnit (X.R.MW j (sg0 D X.A)))
end GlobalTheory.ThetaTri
end
noncomputable section
namespace GlobalTheory.ThetaTri
open MeasureTheory Formalism.IndefR.Datum GlobalTheory.ThetaLoc
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n r : ℕ}
theorem map_mem_iSup_range_isLinAt {Θ Ω : Type} [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup Ω] [Module ℂ Ω]
    (ω₁ : GAf E n × GAf E r →* Module.End ℂ Θ) (ω₂ : GAf E n × GAf E r →* Module.End ℂ Ω)
    (P : Θ → Prop) (Q : Ω → Prop) (T : Θ →ₗ[ℂ] Ω) (hT : ∀ p f, P f → T (ω₁ p f) = ω₂ p (T f))
    (hTQ : ∀ f, P f → Q (T f)) (s : SplitPlace E) (μ η : (s.w.adicCompletion E)ˣ →* ℂˣ) {f : Θ}
    (hf : f ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Θ)
      (_ : IsLinAt ω₁ s μ η ι ∧ ∀ Φ, P (ι Φ)), LinearMap.range ι) :
    T f ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Ω)
      (_ : IsLinAt ω₂ s μ η ι ∧ ∀ Φ, Q (ι Φ)), LinearMap.range ι := by
  have hle : (⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Θ)
      (_ : IsLinAt ω₁ s μ η ι ∧ ∀ Φ, P (ι Φ)), LinearMap.range ι).map T ≤
      ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Ω)
      (_ : IsLinAt ω₂ s μ η ι ∧ ∀ Φ, Q (ι Φ)), LinearMap.range ι := by
    rw [Submodule.map_iSup]
    refine iSup_le fun ι => ?_
    rw [Submodule.map_iSup]
    refine iSup_le fun hι => ?_
    rw [← LinearMap.range_comp]
    exact le_iSup₂_of_le (T ∘ₗ ι) ⟨isLinAt_comp ω₁ ω₂ P T hT s μ η ι hι.2 hι.1, fun Φ => hTQ _ (hι.2 Φ)⟩ le_rfl
  exact hle (Submodule.mem_map_of_mem hf)
theorem mem_iSup_range_isLinAt_valAct1 {Θ B : Type} [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup B] [Module ℂ B]
    [FiniteDimensional ℂ B] (ω : GAf E n × GAf E r →* Module.End ℂ Θ) (P : Θ → Prop) (Q : (B →ₗ[ℂ] Θ) → Prop)
    (hQ : ∀ β f, P f → Q (single1 β f))
    (s : SplitPlace E) (μ η : (s.w.adicCompletion E)ˣ →* ℂˣ) (φ : B →ₗ[ℂ] Θ)
    (hφ : ∀ b, φ b ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] Θ)
      (_ : IsLinAt ω s μ η ι ∧ ∀ Φ, P (ι Φ)), LinearMap.range ι) :
    φ ∈ ⨆ (ι : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin r) (s.w.adicCompletion E)) →ₗ[ℂ] (B →ₗ[ℂ] Θ))
      (_ : IsLinAt (valAct1 ω) s μ η ι ∧ ∀ Φ, Q (ι Φ)), LinearMap.range ι := by
  let bB := Module.finBasis ℂ B
  rw [eq_sum_single1 bB φ]
  refine Submodule.sum_mem _ fun l _ => ?_
  exact _root_.GlobalTheory.ThetaTri.map_mem_iSup_range_isLinAt ω (valAct1 ω) P Q (single1 (bB.coord l))
    (fun p f _ => single1_valAct1 ω _ p f) (fun f hf => hQ _ f hf) s μ η (hφ _)
variable {D : D7} {V W : Formalism.BasicNotions.TH.HSp D}
  (om : Formalism.L2.Theta.GA D V × Formalism.L2.Theta.GA D W →* Module.End ℂ (WO V W → ℂ))
  {TauV Fm C : Type} [AddCommGroup TauV] [Module ℂ TauV]
  [AddCommGroup Fm] [Module ℂ Fm] [AddCommGroup C] [Module ℂ C]
  (fV : Fm →ₗ[ℂ] (Formalism.L2.Theta.GA D V → TauV)) (yv : C →ₗ[ℂ] (Formalism.L2.Theta.GA D W → ℂ))
  (νV : Measure (Formalism.L2.Theta.GA D V)) (𝓕V : Set (Formalism.L2.Theta.GA D V)) (νW : Measure (Formalism.L2.Theta.GA D W))
  (𝓕W : Set (Formalism.L2.Theta.GA D W)) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ)
  (ω : GAf E n × GAf E r →* Module.End ℂ (WO V W → ℂ))
end GlobalTheory.ThetaTri
end
noncomputable section
namespace GlobalTheory.ThetaTri
open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ThetaLoc
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}
def omegaMapAtLocal (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    {Y : RowMod D P.rep (D.nd.j i)} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) :
    GAf D.host.E D.R.nV × GAf D.host.E D.R.r →* Module.End ℂ ↥(_root_.GlobalTheory.ThetaTri.OmegaSubmoduleAtLocal A i j hj hc hμ) :=
  omSub (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ) (_root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc) (X.R.νV j (X.tupT (D.nd.mu i)))
    (X.R.fdV j (X.tupT (D.nd.mu i))) (X.R.νW j) (X.R.fdW j) X.R.ψ (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i)))
def canonicalPairingMap (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    {Y : RowMod D P.rep (D.nd.j i)} (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) :
    ↥(_root_.GlobalTheory.ThetaTri.OmegaSubmoduleAtLocal A i j hj hc hμ) →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ) →ₗ[ℂ] ↥Y.C →ₗ⋆[ℂ] ℂ :=
  lam (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ) (_root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc) (X.R.νV j (X.tupT (D.nd.mu i)))
    (X.R.fdV j (X.tupT (D.nd.mu i))) (X.R.νW j) (X.R.fdW j) (_root_.GlobalTheory.ThetaTri.canonicalConstant hc : ℂ) X.R.ψ (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i)))
end GlobalTheory.ThetaTri
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealRtEqOfGoodInertStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.operator_eigen_good_place_first_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.UG.IsInertAt D.host.F D.host.E (Pp.under (𝓞 D.host.F)) Pp → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))), NG.OverPl Pp v → ∀ g : D.what₂.Mt (D.nd.mu i) (D.nd.j i), ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {v} κ → NG.rt D.host.E D.R.nV κ ((P.M.loc i).real g) = (P.M.loc i).real g := by
  first | exact @_root_.GlobalTheory.InertFormFix.real_rt_eq_of_good_inert_alt | exact _root_.GlobalTheory.InertFormFix.real_rt_eq_of_good_inert_alt | (intros; apply _root_.GlobalTheory.InertFormFix.real_rt_eq_of_good_inert_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsUOfColPins
section
set_option synthInstance.maxHeartbeats 200000

section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows GlobalTheory.ColRows
open scoped ComplexOrder
namespace GlobalTheory.ColRows
set_option maxHeartbeats 2000000 in
theorem rowsU_of_colPins_alt : ∀ CY CT : ℝ, 0 ≤ CT → ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) [_root_.NumberField.IsTotallyComplex D.what₂.LL] (T : _root_.Formalism.L2.TiedDataSKAlt ex) (P : RowSideFamily ex) (K : _root_.Formalism.L2.DIV.SquareIntegrableColumns T P) (W : Formalism.L2.Col.Wts T.ker.X T.ker.Pr.Word D.R) (Del h0 : ℕ), _root_.Formalism.L2.DIV.ColumnCharactersCompatible K → HEq K.c.W W → KerTies T.ker W Del h0 → KerSizes T.ker W Del h0 CY CT → DV.NprimeDef D L → D.NuFull → (∀ u, 0 < (D.div.Nu u).rank) → ∀ (Zsc : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) (cf : ConvFace P.A3.fam3.base3) (Cl CHl : ℝ) (Pk : IndefPkgR P.A3.fam3.amb3 (Formalism.IndefR.Cx.faceOf3 P.A3 P.P0 P.ψ0 P.Ps P.ψs K.c.face K.Sp Zsc) cf Cl CHl), Pk.Zs = P.Zs → ∀ (u : D.what₂.Word) (lam0 c0 ce Ch Sw C1 : ℝ) (H : (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) L.Nc lam0 c0 ce Ch Sw C1) (w : (K.c.face Pk.Zs).Mem) (e : (Fin ((K.c.face Pk.Zs).a w) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V), HEq w u → C0 ≤ Ch → ∃ (ch : ColChain (K.c.face Pk.Zs) w) (Tc : ChainTie ch (K.c.memQ w)), FirstCols K.c.hE Tc ∧ ∃ (X0 : InfinitePlace D.what₂.LL → Matrix (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0)) (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0)) ℂ) (_ : ∀ v, IsUnit (X0 v).det ∧ ((X0 v)⁻¹).conjTranspose * (X0 v)⁻¹ = ((P.A3.side3 P.Ps P.ψs Pk.Zs).HV P.A3.fam3.base3.μ0).map v.embedding) (hn : HtNums (RecNums.ofNum (ofRecord D L Del h0) (Equiv.refl _) (letterOf D L Del h0 u) (D.mem u).A.T L.Nc lam0 c0 ce Ch Sw C1 H) (InfinitePlace D.what₂.LL)) (_ : ∀ v, Formalism.HN.opNormAt (Pi.basisFun D.what₂.LL (Fin (ch.c (Fin.last ch.mm)))) (ch.X (Fin.last ch.mm)) (Pi.basisFun D.what₂.LL (Fin ((P.A3.side3 P.Ps P.ψs Pk.Zs).nV P.A3.fam3.base3.μ0))).dualBasis (Formalism.HN.dualFrame X0) v ch.PtL ^ 2 ≤ Real.exp hn.hPn) (cb : CBData ch.X ch.Kj), (∀ j v, Real.log (cb.sq j v) ≤ ∑ l ∈ Finset.univ.filter (fun l => ch.lf l = j), hn.sz l v) ∧ (∀ v, IsUnit ((K.c.face Pk.Zs).Xc w v).det) ∧ 0 < (K.c.face Pk.Zs).a w ∧ Submodule.IsLattice D.what₂.LL (Cons.nuOf L u e) := by
  intro CY CT hCT
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.memberRows_of_kernelDatum_sizes CY CT hCT
  refine ⟨C0, ?_⟩
  intro D L hT Gi Gl Kc Y cX ex _ T P K W Del h0 hPins hW hKT hKS hN hNu hrk Zsc cf Cl CHl Pk hZs u lam0 c0 ce Ch Sw C1 H w e hwu hCh
  have hmu0 : P.I.tup P.A3.fam3.base3.μ0 = D.what₂.mu0 := P.tied.div.tup.mu0
  have hpos : ∀ v : InfinitePlace D.what₂.LL, (((P.A3.side3 P.Ps P.ψs Pk.Zs).HV P.A3.fam3.base3.μ0).map v.embedding).PosDef :=
    fun v => Formalism.L2.DIV.BlockDat.HV_pos (ℓ := P.A3.fam3.F.lvl P.Ps P.ψs) K.ok1.ok2.conj (K.ok1.ok2.what₂ _) K.ok1.ok2.irr v
  have hlat : Submodule.IsLattice D.what₂.LL (Cons.nuOf L u e) :=
    nuLat_comap_isLattice D L hN u ⟨(hNu u).1, by
      intro s hs hli
      exact (LinearIndependent.iff_fractionRing _ _).mp hli⟩ _ e
  have ha : 0 < (K.c.face Pk.Zs).a w := by
    have h := hrk u
    change 0 < Module.finrank D.what₂.LL (Submodule.span D.what₂.LL ((D.div.Nu u).L : Set (D.div.Nu u).V)) at h
    rw [(hNu u).2, finrank_top, ← e.finrank_eq, Module.finrank_fin_fun] at h
    exact h
  have hev := _root_.GlobalTheory.T.frames_tilde_gamma_values_alt D L hT Gi Gl Kc Y cX ex T P K hPins
  rw [← hZs] at hev
  clear hPins hrk hNu
  obtain ⟨X, e', c, Sp, colTie, kerTie, wTie, lvTie, sgTie, v0, TU, xiVal, trIv, famEq, gEq, plEq, i0Eq, tEq, muTie, ok1⟩ := K
  obtain ⟨toS, ker, crd, crd_gram, crd_lat, ker_sharp, ker_frm⟩ := T
  obtain ⟨cc, cc_rec, cc_ok, δ, δ_ok, B, χ, χ_ok, idl, idl_ok, χ_rec, cD, kX, seam, seam_ok, kPr, pr_ok, g_rec, kCh, ksel, kS, kword, T_rec, ktup, Q_rec, kcst, kidx, km2, kglob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf, kf_un, served⟩ := ker
  obtain ⟨Pr, Rk, W', Ch', sel, Sg, hX, Lv, Xg, m2, Gc, mu, cst, Li, hL, hP, Mem, wd, b, hY, Am, hK, hF, hE, ev⟩ := c
  have hXe : kX = fieldsLL D X e' := kerTie.1
  subst hXe
  have hRk : Rk = D.R := kerTie.2.1
  subst hRk
  have hPr : Pr = kPr := eq_of_heq kerTie.2.2.1
  subst hPr
  have hChE : Ch' = kCh := eq_of_heq kerTie.2.2.2.1
  subst hChE
  have hsel : sel = ksel := eq_of_heq kerTie.2.2.2.2.1
  subst hsel
  have hSg : Sg = kS := eq_of_heq kerTie.2.2.2.2.2.1
  subst hSg
  have hmu : mu = fun t => ktup (P.I.tup t) := eq_of_heq kerTie.2.2.2.2.2.2.1
  subst hmu
  have hcst : cst = fun t => kcst (P.I.tup t) := eq_of_heq kerTie.2.2.2.2.2.2.2.1
  subst hcst
  have hLi : Li = fun t => kidx (P.I.tup t) := eq_of_heq kerTie.2.2.2.2.2.2.2.2.1
  subst hLi
  have hm2 : m2 = km2 := kerTie.2.2.2.2.2.2.2.2.2.1
  subst hm2
  have hGc : Gc = kglob := eq_of_heq kerTie.2.2.2.2.2.2.2.2.2.2.1
  subst hGc
  have hAm : Am = Formalism.L2.Ker.ambOf seam B χ cD := eq_of_heq kerTie.2.2.2.2.2.2.2.2.2.2.2.1
  subst hAm
  have hMem : Mem = D.what₂.Word := kerTie.2.2.2.2.2.2.2.2.2.2.2.2.1
  subst hMem
  have hwd : wd = kword := eq_of_heq kerTie.2.2.2.2.2.2.2.2.2.2.2.2.2
  subst hwd
  have hW' : W' = W := eq_of_heq hW
  subst hW'
  have hLv : Lv = Formalism.L2.Col.rPsymF (R := D.R) Ch' := lvTie
  subst hLv
  have hwu' : w = u := eq_of_heq hwu
  subst hwu'
  have hmuOne : ktup (P.I.tup P.A3.fam3.base3.μ0) = 1 := by rw [hmu0]; exact hKT.mu0
  have hev' := hev hmuOne
  dsimp only at hev'
  have key := hC0 D L hT Gi Gl Kc Y cX ex
    (⟨cc, cc_rec, cc_ok, δ, δ_ok, B, χ, χ_ok, idl, idl_ok, χ_rec, cD, fieldsLL D X e', seam, seam_ok, Pr, pr_ok, g_rec, Ch',
      sel, Sg, wd, T_rec, ktup, Q_rec, kcst, kidx, m2, Gc, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th,
      unf, ent, ent_lam, kf, kf_un, served⟩ : Formalism.L2.Ker.KerEntTied ex) W' Del h0 hX P.A3.fam3.base3
    (P.A3.side3 P.Ps P.ψs Pk.Zs) Xg P.I.tup hP b hY hK hF hE (ev Pk.Zs) w (Equiv.refl _) L.Nc lam0 c0 ce Ch Sw C1 H hmu0
    hKT hKS hCh hpos hev'
  dsimp only at key ha hlat ⊢
  obtain ⟨⟨ch, Tc, h1, X0, hX0, hn, hop, cb, hcb⟩, hXc⟩ := key
  exact ⟨ch, Tc, h1, X0, hX0, hn, hop, cb, hcb, hXc, ha, hlat⟩
end GlobalTheory.ColRows
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SParts
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
namespace UpperTheory.GalS.Parts
open UpperTheory.GalS GlobalTheory.NRows GlobalTheory.AbsIrrConstituents Pointwise
theorem p41'_alt (D : D7) (t0 : SumRepresentations.tie0 D) (hO : SumRepresentations.hypO D) (a1 : SumRepresentations.adm1 D) (a2 : AutomorphicGaloisAdmissible D.nd D.naut) (a5 : SumRepresentations.adm5 D)
    (_ : _root_.Formalism.MainNotions.SumRepresentations.AdmAtAlt D) : HeckeGaloisFamilyProperties D := heckeGaloisFamilyProperties_of_admissible D t0 hO a1 a2 a5
theorem main_alt_alt : ∀ D : D7, _root_.GlobalTheory.NRows.SummandsSuffice D := fun D a t s hk l th g =>
  ⟨_root_.UpperTheory.GalS.Parts.p41'_alt D a.1.1 a.1.2.1 a.1.2.2.1 a.1.2.2.2.1 a.1.2.2.2.2.2.2 a, g, (SumRepresentations.proposition_parameters_iff_reduced D t).2 (_root_.GlobalTheory.NRows.Parts.conclusion42_of_parts D a s hk l th)⟩
end UpperTheory.GalS.Parts
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ToSTiesR
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.Mem.SRe
open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}
def SRest.toRealSpectralMatching (Rc : _root_.Formalism.L2.RecTAlt ex) {P : SPack D fun u => (Rc.T.cols.forms u).to0} (S : SRest P) :
    _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc where
  toSTies := S.toSTies
  tr := P.tr
  into := P.into
  bij := P.bij
  lev := P.lev
  colPin := fun _ => S.colPin
  inst := P.inst
  G := P.G
  rowTie := fun _ => S.rowTie
  locTied := S.locTied
section
end
end GlobalTheory.Mem.SRe
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TransportLabel
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
namespace GlobalTheory.LabelTransport
set_option maxHeartbeats 2000000 in
theorem is_split_of_hk3_good_transport_label : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (sp : SplitPlace D.host.E), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) sp.w → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (sp.w.under (𝓞 D.host.F)) → (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) sp.w d → ∃ Ds : Set (GAf D.host.E D.R.nV), (∀ x ∈ Ds, TrivOutside {sp.v} x) ∧ (∀ x ∈ Ds, ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {sp.v} κ → x * κ ∈ Ds ∧ κ * x ∈ Ds) ∧ {c : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J | ∃ x ∈ Ds, (x : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J) = c}.Finite ∧ ∀ (f : D.what₂.Mt (D.nd.mu i) (j.1 + 1)) (c : ℂ), (∀ g, ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w d, X.fn hμ j f (g * γ) = c • X.fn hμ j f g) → NG.heckeD (P.M.loc i).J Ds ((P.M.loc i).real (hj ▸ f)) = c • (P.M.loc i).real (hj ▸ f) := by
  intro _ hL D P X hA _ _ _ i hμ j hj sp _ _ hJ d hd
  classical
  obtain ⟨e, f, ϖ, α, -, hef, -, -, -, -, -, -, -, hRs, hR1, hR2⟩ := GlobalTheory.SphLabelOps.sphOp_rep hd
  have hsupp := suppF_iff_trivOutside D sp hA.hF _ _ (hA.PV j) (hA.stdV j) e f hef
  have hpre : ∀ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w d,
      (hA.PV j).ψ (Formalism.IndefR.principalLevelFrame.pre (hA.PV j) γ) = γ := by
    intro γ hγ
    have h := (hA.PV j).onto γ (hR1 γ hγ).1
    rw [Formalism.IndefR.principalLevelFrame.pre, dite_eq_left h]
    exact h.choose_spec
  obtain ⟨Ds, d1, d2, d3, d4⟩ := coset_transport (hA.PV j).ψ (GlobalTheory.InertSph.Gv D.host.E D.R.nV sp.v)
    (Umax D.host.E D.R.nV) (P.M.loc i).J {k | k ∈ Formalism.L2.Theta.KsphC (Formalism.IndefR.Links.Vc D j) ∅ ∧ Formalism.IndefR.Mult.SuppF (Formalism.IndefR.Links.Vc D j) f k} α (GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w d)
    (fun x => and_congr ((hA.stdV j).2 x).symm (hsupp x)) (fun k hk => (hA.PV j).onto k hk.1.1)
    (fun x hx => (hJ x hx).1) (Formalism.IndefR.principalLevelFrame.pre (hA.PV j))
    (fun γ hγ => ⟨hpre γ hγ, (hsupp _).1 (by rw [hpre γ hγ]; exact hRs γ hγ)⟩) (fun γ hγ => (hR1 γ hγ).2) hR2
  refine ⟨Ds, d1, d2, d3, fun φ c hc => ?_⟩
  have key : ∀ (k : ℕ) (ek : j.1 + 1 = k) (k1 : 1 ≤ k) (k2 : k ≤ D.R.m) (g : GAf D.host.E D.R.nV),
      ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) sp.w d,
        (P.M (D.nd.mu i) k k1 k2).real (ek ▸ φ) (g * Formalism.IndefR.principalLevelFrame.pre (hA.PV j) γ) =
        c • (P.M (D.nd.mu i) k k1 k2).real (ek ▸ φ) g := by
    intro k ek k1 k2 g
    subst ek
    have hr := hA.real (D.nd.mu i) hμ j φ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hr g, ← map_smul, ← hc, map_sum]
    refine Finset.sum_congr rfl fun γ hγ => ?_
    rw [hr, ← mul_assoc, map_mul, hpre γ hγ]
  have hty : (P.M.loc i).real (hj ▸ φ) ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    rw [← (P.M.loc i).real_range]
    exact ⟨_, rfl⟩
  funext g
  refine (d4 _ ((P.M.loc i).real (hj ▸ φ)) (fun x κ hκ hκ' => ?_) g).trans (key _ hj _ _ g)
  have h := congrFun (hty.2 ⟨κ, hκ⟩) x
  rw [(hJ κ hκ').2 hκ, Units.val_one, one_smul] at h
  exact h
end GlobalTheory.LabelTransport
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypeNZRecOfJoinStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_nonzero_recursion_of_eigen' : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), (∀ j t, GlobalTheory.DownLift.TypeNZ X.R j t) → ∀ i, GlobalTheory.NJoin.EigString X i → GlobalTheory.NJoin.EigGood X i → GlobalTheory.RowCopy.TypeNZRec D.nd D.naut i :=
  _root_.GlobalTheory.TypeNZJoin.typeNZRec_of_join_alt
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ValInertStatement
section
alias GlobalTheory.T.good_place_split_condition_alt := GlobalTheory.ValInert.val_inert_alt
end

