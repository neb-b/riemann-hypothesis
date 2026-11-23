module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0022
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalRingCardinality.Bundle0005
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ConcreteSettingExists
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0142
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTw

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockOperatorsDistinctRealPlacesCommuteTheta
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwoPlaceComm

open GlobalTheory.OrientedHeis (theta_add theta_smul theta_dRho)

section Generic

variable {ι X : Type} {A : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}

theorem foldr_comm {B : (X → ℂ) → (X → ℂ)} (hA : ∀ i f, P f → P (A i f))
    (hBA : ∀ i f, P f → B (A i f) = A i (B f)) {f : X → ℂ} (hf : P f) (l : List ι) :
    B (l.foldr (fun i g => A i g) f) = l.foldr (fun i g => A i g) (B f) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons]
    rw [hBA _ _ (GlobalTheory.FockIndep.foldr_mem hA hf l), ih]

theorem pure_comm {B : (X → ℂ) → (X → ℂ)} (hadd : ∀ f f', P f → P f' → P (f + f'))
    (hsm : ∀ (a : ℂ) f, P f → P (a • f)) (hA : ∀ i f, P f → P (A i f))
    (Badd : ∀ f f', P f → P f' → B (f + f') = B f + B f') (Bsm : ∀ (a : ℂ) f, P f → B (a • f) = a • B f)
    (hBA : ∀ i f, P f → B (A i f) = A i (B f)) {f : X → ℂ} (hf : P f) (Q : MvPolynomial ι ℂ) :
    B (pureTensorL A f Q) = pureTensorL A (B f) Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial k c =>
    rw [GlobalTheory.FockIndep.pure_monomial, GlobalTheory.FockIndep.pure_monomial]
    unfold opPow
    rw [Bsm _ _ (GlobalTheory.FockIndep.foldr_mem hA hf _), foldr_comm hA hBA hf]
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _), Badd _ _ (GlobalTheory.FockIndep.pure_mem hadd hsm hA hf _) (GlobalTheory.FockIndep.pure_mem hadd hsm hA hf _),
      hp, hq]

theorem pure_fun_add (hA : ∀ i f, P f → P (A i f)) (hadd : ∀ f f', P f → P f' → P (f + f'))
    (hsm : ∀ (a : ℂ) f, P f → P (a • f))
    (Aadd : ∀ i f f', P f → P f' → A i (f + f') = A i f + A i f') {f f' : X → ℂ} (hf : P f) (hf' : P f')
    (Q : MvPolynomial ι ℂ) : pureTensorL A (f + f') Q = pureTensorL A f Q + pureTensorL A f' Q := by
  have hl : ∀ l : List ι, l.foldr (fun i g => A i g) (f + f') =
      l.foldr (fun i g => A i g) f + l.foldr (fun i g => A i g) f' := fun l => by
    induction l with
    | nil => rfl
    | cons i l ih =>
      simp only [List.foldr_cons]
      rw [ih, Aadd _ _ _ (GlobalTheory.FockIndep.foldr_mem hA hf l) (GlobalTheory.FockIndep.foldr_mem hA hf' l)]
  induction Q using MvPolynomial.induction_on' with
  | monomial k c =>
    rw [GlobalTheory.FockIndep.pure_monomial, GlobalTheory.FockIndep.pure_monomial, GlobalTheory.FockIndep.pure_monomial]
    unfold opPow
    rw [hl, smul_add]
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
    abel

theorem pure_fun_smul (hA : ∀ i f, P f → P (A i f))
    (Asm : ∀ i (a : ℂ) f, P f → A i (a • f) = a • A i f) (a : ℂ) {f : X → ℂ} (hf : P f)
    (Q : MvPolynomial ι ℂ) : pureTensorL A (a • f) Q = a • pureTensorL A f Q := by
  have hl : ∀ l : List ι, l.foldr (fun i g => A i g) (a • f) = a • l.foldr (fun i g => A i g) f := fun l => by
    induction l with
    | nil => rfl
    | cons i l ih =>
      simp only [List.foldr_cons]
      rw [ih, Asm _ _ _ (GlobalTheory.FockIndep.foldr_mem hA hf l)]
  induction Q using MvPolynomial.induction_on' with
  | monomial k c =>
    rw [GlobalTheory.FockIndep.pure_monomial, GlobalTheory.FockIndep.pure_monomial]
    unfold opPow
    rw [hl, smul_comm]
  | add p q hp hq =>
    rw [map_add (f := _), map_add (f := _), hp, hq, smul_add]

end Generic

section Places

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
  (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {τ τ' : D.what₂.Tau} (hne : τ ≠ τ')
include hψ hθ hne

theorem dRho_comm_ne (z z' : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    Datum.dRho (heisO ψ S T) θ τ z (Datum.dRho (heisO ψ S T) θ τ' z' f) =
      Datum.dRho (heisO ψ S T) θ τ' z' (Datum.dRho (heisO ψ S T) θ τ z f) := by
  rw [GlobalTheory.FockIndep.dRho_comm hψ hθ τ z τ' z' hf]
  simp [GlobalTheory.FockIndep.omDir, hne]

theorem dRho_aPlus_ne (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ) (u : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    Datum.dRho (heisO ψ S T) θ τ z (aPlus (heisO ψ S T) θ τ' J u f) =
      aPlus (heisO ψ S T) θ τ' J u (Datum.dRho (heisO ψ S T) θ τ z f) := by
  have ht := fun ρ y => theta_dRho hθ hψ ρ y hf
  rw [GlobalTheory.FockIndep.aPlus_eq, GlobalTheory.FockIndep.aPlus_eq,
    GlobalTheory.FockIndep.dRho_smul hψ hθ _ _ _ (theta_add (ht _ _) (theta_smul _ (ht _ _))),
    GlobalTheory.FockIndep.dRho_add hψ hθ _ _ (ht _ _) (theta_smul _ (ht _ _)), GlobalTheory.FockIndep.dRho_smul hψ hθ _ _ _ (ht _ _),
    dRho_comm_ne hψ hθ hne _ _ hf, dRho_comm_ne hψ hθ hne _ _ hf]

theorem aPlus_comm_ne (J J' : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z u : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    aPlus (heisO ψ S T) θ τ J z (aPlus (heisO ψ S T) θ τ' J' u f) =
      aPlus (heisO ψ S T) θ τ' J' u (aPlus (heisO ψ S T) θ τ J z f) := by
  have ht := fun ρ y => theta_dRho hθ hψ ρ y hf
  rw [GlobalTheory.FockIndep.aPlus_eq τ J z (aPlus (heisO ψ S T) θ τ' J' u f), dRho_aPlus_ne hψ hθ hne _ _ _ hf,
    dRho_aPlus_ne hψ hθ hne _ _ _ hf, ← GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ _ (ht _ _),
    ← GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ (ht _ _) (theta_smul _ (ht _ _)),
    ← GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ _ (theta_add (ht _ _) (theta_smul _ (ht _ _))), ← GlobalTheory.FockIndep.aPlus_eq]

theorem annih_aPlus_ne (J J' : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z u : Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    annih (heisO ψ S T) θ τ J z (aPlus (heisO ψ S T) θ τ' J' u f) =
      aPlus (heisO ψ S T) θ τ' J' u (annih (heisO ψ S T) θ τ J z f) := by
  have ht := fun ρ y => theta_dRho hθ hψ ρ y hf
  rw [annih, annih, dRho_aPlus_ne hψ hθ hne _ _ _ hf, dRho_aPlus_ne hψ hθ hne _ _ _ hf,
    ← GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ _ (ht _ _),
    ← GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ (ht _ _) (theta_smul _ (ht _ _))]

end Places

section Weil

variable {D : D7} {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hW : IsWeilDatumO ψ V W χS χT ω) (hθ : IsInfFam θ)
  {τ τ' : D.what₂.Tau} (hne : τ ≠ τ') {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ'))
include hW hθ hne hg

theorem om_dRho_fix (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    ω (atTau θ V τ' g, 1) (Datum.dRho (heisO ψ V W) θ τ z f) =
      Datum.dRho (heisO ψ V W) θ τ z (ω (atTau θ V τ' g, 1) f) := by
  rw [GlobalTheory.OrientedHeis.om_dRho hW hθ _ _ τ z hf]
  have h1 : compAt θ τ (Formalism.L2.Theta.mt W 1) = 1 := by
    unfold Formalism.L2.Theta.mt
    rw [map_one, Units.val_one]
    exact Matrix.map_one _ (((θ τ).comp (infPart D)).map_zero) (((θ τ).comp (infPart D)).map_one)
  have h2 : compAt θ τ (Formalism.L2.Theta.mt V (atTau θ V τ' g)) = 1 :=
    (GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ' hg).2.2 τ hne
  have h3 := GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := θ) τ (atTau θ V τ' g)
  rw [h2, Matrix.one_mul] at h3
  rw [h1, h3, Matrix.one_mul, Matrix.mul_one]

theorem om_aPlus_fix (J : Matrix (Fin W.rank) (Fin V.rank) ℂ → Matrix (Fin W.rank) (Fin V.rank) ℂ)
    (u : Matrix (Fin W.rank) (Fin V.rank) ℂ) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    ω (atTau θ V τ' g, 1) (aPlus (heisO ψ V W) θ τ J u f) = aPlus (heisO ψ V W) θ τ J u (ω (atTau θ V τ' g, 1) f) := by
  rw [GlobalTheory.FockIndep.aPlus_eq, GlobalTheory.FockIndep.aPlus_eq, map_smul, map_add (f := _), map_smul, om_dRho_fix hW hθ hne hg _ hf,
    om_dRho_fix hW hθ hne hg _ hf]

theorem om_annih_fix (J : Matrix (Fin W.rank) (Fin V.rank) ℂ → Matrix (Fin W.rank) (Fin V.rank) ℂ)
    (u : Matrix (Fin W.rank) (Fin V.rank) ℂ) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    ω (atTau θ V τ' g, 1) (annih (heisO ψ V W) θ τ J u f) = annih (heisO ψ V W) θ τ J u (ω (atTau θ V τ' g, 1) f) := by
  rw [annih, annih, map_add (f := _), map_smul, om_dRho_fix hW hθ hne hg _ hf, om_dRho_fix hW hθ hne hg _ hf]

end Weil

theorem twoPlace_comm : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → ∀ (τ τ' : D.what₂.Tau), τ ≠ τ' → ∀ F, IsThetaFunO ψ V W F → let pt := fun ρ => GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt ψ θ V W ρ (cart M ρ) (cart M' ρ) (onb M ρ) (onb M' ρ); let vac := IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)); (∀ P, IsThetaFunO ψ V W (pt τ' F P)) ∧ (∀ P, vac F → vac (pt τ' F P)) ∧ (∀ P Q, pt τ (pt τ' F Q) P = pt τ' (pt τ F P) Q) ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ'), (vac F → vac (ω (atTau θ V τ' g, 1) F)) ∧ ∀ P, ω (atTau θ V τ' g, 1) (pt τ F P) = pt τ (ω (atTau θ V τ' g, 1) F) P := by
  intro D V W S S' M M' θ ψ χS χT ω hθ hW τ τ' hne F hF
  dsimp only
  have hψ := hW.std
  have hadd : ∀ f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → IsThetaFunO ψ V W (f + f') :=
    fun _ _ => theta_add
  have hsm : ∀ (a : ℂ) f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (a • f) := fun a _ => theta_smul a
  have hA : ∀ ρ (k : Fin W.rank × Fin V.rank) g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W
      (aPlus (heisO ψ V W) θ ρ (cplxO (cart M ρ) (cart M' ρ)) (unitMap (onb M ρ) (onb M' ρ) k.1 k.2) g) :=
    fun ρ _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ ρ _ _ h
  have Aadd : ∀ ρ (k : Fin W.rank × Fin V.rank) g g', IsThetaFunO ψ V W g → IsThetaFunO ψ V W g' →
      aPlus (heisO ψ V W) θ ρ (cplxO (cart M ρ) (cart M' ρ)) (unitMap (onb M ρ) (onb M' ρ) k.1 k.2) (g + g') =
      aPlus (heisO ψ V W) θ ρ (cplxO (cart M ρ) (cart M' ρ)) (unitMap (onb M ρ) (onb M' ρ) k.1 k.2) g +
      aPlus (heisO ψ V W) θ ρ (cplxO (cart M ρ) (cart M' ρ)) (unitMap (onb M ρ) (onb M' ρ) k.1 k.2) g' :=
    fun ρ _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ ρ _ _ h h'
  have Asm : ∀ ρ (k : Fin W.rank × Fin V.rank) (a : ℂ) g, IsThetaFunO ψ V W g →
      aPlus (heisO ψ V W) θ ρ (cplxO (cart M ρ) (cart M' ρ)) (unitMap (onb M ρ) (onb M' ρ) k.1 k.2) (a • g) =
      a • aPlus (heisO ψ V W) θ ρ (cplxO (cart M ρ) (cart M' ρ)) (unitMap (onb M ρ) (onb M' ρ) k.1 k.2) g :=
    fun ρ _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ ρ _ _ a h
  unfold GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.ptAt
  refine ⟨fun P => GlobalTheory.FockIndep.pure_mem hadd hsm (hA τ') hF P, fun P hv z => ?_, fun P Q => ?_, fun g hg => ⟨?_, ?_⟩⟩
  · rw [pure_comm hadd hsm (hA τ') (fun _ _ h h' => GlobalTheory.FockIndep.annih_add hψ hθ τ _ z h h')
      (fun a _ h => GlobalTheory.FockIndep.annih_smul hψ hθ τ _ z a h)
      (fun k g hg => annih_aPlus_ne hψ hθ hne _ _ _ _ hg) hF P, hv z]
    have h0 := pure_fun_smul (hA τ') (Asm τ') 0 hF P
    rwa [zero_smul, zero_smul] at h0
  · symm
    refine pure_comm (B := fun g => pureTensorL (fun k : Fin W.rank × Fin V.rank =>
        aPlus (heisO ψ V W) θ τ' (cplxO (cart M τ') (cart M' τ')) (unitMap (onb M τ') (onb M' τ') k.1 k.2)) g Q)
      hadd hsm (hA τ) (fun _ _ h h' => pure_fun_add (hA τ') hadd hsm (Aadd τ') h h' Q)
      (fun a _ h => pure_fun_smul (hA τ') (Asm τ') a h Q) (fun k g hg => ?_) hF P
    exact (pure_comm hadd hsm (hA τ') (Aadd τ k) (Asm τ k)
      (fun j h hh => aPlus_comm_ne hψ hθ hne _ _ _ _ hh) hg Q).symm
  · intro hv z
    rw [← om_annih_fix hW hθ hne hg _ _ hF, hv z, map_zero]
  · intro P
    exact pure_comm hadd hsm (hA τ) (fun f f' _ _ => map_add _ f f') (fun a f _ => map_smul _ a f)
      (fun k h hh => om_aPlus_fix hW hθ hne hg _ _ hh) hF P

end GlobalTheory.TwoPlaceComm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierCoefficientBessel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.PhCol

variable {D : D7}

theorem one_le_level (X : HidaSetting D) : 1 ≤ X.B.g := by
  rw [X.g_eq]
  exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos

theorem one_mem_level (X : HidaSetting D) : (1 : X.B.I.Gf) ∈ X.B.I.Kg X.B.g := by
  refine ⟨(Formalism.UG.stabGL X.B.I.Lf).one_mem, fun y _ => ⟨0, zero_mem _, ?_⟩⟩
  have h1 : X.B.I.fmat 1 = 1 := rfl
  rw [h1, sub_self, Matrix.zero_mulVec, smul_zero]

theorem psiInfU_of_mem_Hinf (X : HidaSetting D) (u : D.what₂.Word) (η : X.B.I.Ginf) (hη : η ∈ Hinf X u) :
    X.psiInfU u η = 1 := by
  have e := Formalism.L2.SG.PoincareInHH.Cut.psiInf_mul_H X u 1 η hη
  rw [one_mul] at e
  rw [e]
  exact Formalism.L2.SG.CovariantRepresentation.psiInfU_one X u

theorem castGA_mem_rat {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (x : I.GA) :
    x ∈ I.GFset ↔ castGA e x ∈ I'.GFset := by
  subst e; rfl

theorem iotaX_mem_rat (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (g : GA D (D.sp.Y 0))
    (hg : g ∈ GQ (D.sp.Y 0)) : iotaX X h g ∈ X.B.I.GFset := by
  have e : iotaX X h g = castGA h.symm (Formalism.IndefR.RationalEmbedding.iota D g) := rfl
  rw [e]
  exact (castGA_mem_rat h.symm _).1 ((Formalism.IndefR.RationalEmbedding.iota_rat D g).1 hg)

theorem Ph_of_dec (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (y : X.B.I.GA)
    (n : X.B.I.Gf) (hh : Hfin X u) (k : X.B.I.Gf) (hd : IsDec X u y.2 n hh k) :
    Ph X u hK T y = phVal X u hK T y.1 n hh k := by
  have hex : ∃ n h k, IsDec X u y.2 n h k := ⟨n, hh, k, hd⟩
  unfold Ph
  rw [dite_eq_left hex]
  exact Formalism.L2.SG.Pf.phWellDef_holds X u T y.1 y.2 _ n _ k _ hh hex.choose_spec.choose_spec.choose_spec hd

variable {X : HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
  {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D}

theorem continuous_toH (B : SBes X h u ψ A) : Continuous B.toH := by
  have he : Continuous (embA B.d B.o) := by
    have e : (embA B.d B.o : GA D A → GA D (D.sp.Y 0)) = fun a => B.d.emb0 (B.o.emb (a, 1)) := rfl
    rw [e]
    exact B.d.continuous_embed.comp (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const))
  have hc : Continuous fun a => iotaX X h (embA B.d B.o a) := (iotaX X h).continuous.comp he
  unfold SBes.toH
  exact (hc.fst.subtype_mk _).prodMk (hc.snd.subtype_mk _)

theorem continuous_col (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (ξ : X.Vpi u) :
    Continuous fun p : Hinf X u × Hfin X u => (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) ξ p := by
  obtain ⟨hT1, hT2⟩ := T.2
  have hL := Formalism.L2.SG.Closed.level_subgroup_properties X
  rw [continuous_iff_continuousAt]
  intro p0
  have hπ : Continuous fun η : Hinf X u => X.piU u η ξ :=
    ((X.piU_rep u).2.2.2.2 ξ).comp_continuous continuous_subtype_val (fun η => hinf_le_sinf X u _ η.2)
  let L : X.Vpi u →ₗ[ℂ] ℂ :=
    (LinearMap.proj (R := ℂ) (φ := fun _ : Hinf X u × Hfin X u => ℂ) ((1 : Hinf X u), p0.2)).comp
      (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ))
  have hG : Continuous fun p : Hinf X u × Hfin X u => L (X.piU u p.1 ξ) :=
    L.continuous_of_finiteDimensional.comp (hπ.comp continuous_fst)
  have hUo : IsOpen {p : Hinf X u × Hfin X u |
      (X.xu u)⁻¹ * ((p0.2⁻¹ * p.2 : Hfin X u) : X.B.I.Gf) * X.xu u ∈ X.B.I.Kg X.B.g} := by
    refine (X.B.I.topf_open X.B.g (one_le_level X)).preimage ?_
    exact (continuous_const.mul (continuous_subtype_val.comp (continuous_const.mul continuous_snd))).mul
      continuous_const
  have hp0 : p0 ∈ {p : Hinf X u × Hfin X u |
      (X.xu u)⁻¹ * ((p0.2⁻¹ * p.2 : Hfin X u) : X.B.I.Gf) * X.xu u ∈ X.B.I.Kg X.B.g} := by
    show (X.xu u)⁻¹ * ((p0.2⁻¹ * p0.2 : Hfin X u) : X.B.I.Gf) * X.xu u ∈ X.B.I.Kg X.B.g
    rw [inv_mul_cancel]
    simpa using one_mem_level X
  refine hG.continuousAt.congr (Filter.eventually_of_mem (hUo.mem_nhds hp0) fun p hp => ?_)
  obtain ⟨η, k⟩ := p
  have hp' : (X.xu u)⁻¹ * ((p0.2⁻¹ * k : Hfin X u) : X.B.I.Gf) * X.xu u ∈ X.B.I.Kg X.B.g := hp
  obtain ⟨hK2, hχ⟩ := hL.1 _ hp'
  let κ : Ku X u hK := ⟨p0.2⁻¹ * k, hK2⟩
  have e1 : ((η, k) : Hinf X u × Hfin X u) = (η, p0.2) * (1, ((κ : Hfin X u))) := by
    ext
    · simp
    · simp [κ]
  have e2 : ((η, p0.2) : Hinf X u × Hfin X u) = (1, p0.2) * (η, 1) := by
    ext <;> simp
  have hψ : ((psiK X u hK κ : ℂˣ) : ℂ) = 1 := hχ
  show L (X.piU u η ξ) = (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) ξ (η, k)
  rw [e1, (hT1 ξ).2 (η, p0.2) κ, hψ, one_mul, e2, ← hT2 η ξ (1, p0.2)]
  rfl

end GlobalTheory.Core.Mi.PhCol

namespace GlobalTheory.Core.Mi.PhCol

theorem ph_colForm : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK),
    (∀ ξ, IsContAut A (B.colForm T.1 ξ)) ∧ ∀ n ∈ flagN B.d, ∀ (a : GA D A) (y : X.B.I.Ginf),
      Ph X u hK T (iotaX X h (n * embA B.d B.o a) * (y, X.xu u)) =
        star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) * B.colForm T.1 (X.Wu u y) a := by
  intro D X h u ψ A B hK T
  obtain ⟨hT1, hT2⟩ := T.2
  refine ⟨fun ξ => ⟨fun γ hγ g => ?_, ?_⟩, fun n hn a y => ?_⟩
  ·
    have hrat : embA B.d B.o γ ∈ GQ (D.sp.Y 0) := by
      have e : embA B.d B.o γ = B.d.emb0 (B.o.emb (γ, 1)) := rfl
      rw [e]
      exact B.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints (B.o.emb_mem_GQ hγ (one_mem _))
    have hr := iotaX_mem_rat X h _ hrat
    have hH := (B.tieH (embA B.d B.o γ)).1 ⟨γ, rfl⟩
    let γ' : Gam X u := ⟨iotaX X h (embA B.d B.o γ), Subgroup.mem_inf.2 ⟨hr, Subgroup.mem_prod.2 hH⟩⟩
    have e : B.toH (γ * g) = (iotaI X u γ', iotaF X u γ') * B.toH g := by
      refine Prod.ext ?_ ?_ <;> apply Subtype.ext
      · show (iotaX X h (embA B.d B.o (γ * g))).1 = (iotaX X h (embA B.d B.o γ)).1 * (iotaX X h (embA B.d B.o g)).1
        rw [map_mul, map_mul, Prod.fst_mul]
      · show (iotaX X h (embA B.d B.o (γ * g))).2 = (iotaX X h (embA B.d B.o γ)).2 * (iotaX X h (embA B.d B.o g)).2
        rw [map_mul, map_mul, Prod.snd_mul]
    show (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) ξ (B.toH (γ * g)) =
      (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) ξ (B.toH g)
    rw [e]
    exact (hT1 ξ).1 γ' (B.toH g)
  ·
    exact (continuous_col hK T ξ).comp (continuous_toH B)
  ·
    obtain ⟨hn1, hn2⟩ := (B.tieN n).1 hn
    obtain ⟨ha1, ha2⟩ := (B.tieH (embA B.d B.o a)).1 ⟨a, rfl⟩
    set m := iotaX X h n with hm
    set b := iotaX X h (embA B.d B.o a) with hb
    have e : iotaX X h (n * embA B.d B.o a) * (y, X.xu u) = (m.1 * b.1 * y, m.2 * b.2 * X.xu u * 1) := by
      rw [map_mul, ← hm, ← hb]
      ext <;> simp [mul_assoc]
    have hd : IsDec X u (m.1 * b.1 * y, m.2 * b.2 * X.xu u * 1).2 m.2 ⟨b.2, ha2⟩ 1 :=
      ⟨hn2, one_mem_level_subgroup X, rfl⟩
    rw [e, Ph_of_dec X u hK T _ _ _ _ hd]
    unfold phVal
    have hm1S : m.1 ∈ X.SinfU u := fun v => (hn1 v).1
    have hb1S : b.1 ∈ X.SinfU u := hinf_le_sinf X u _ ha1
    have hW : X.Wu u (m.1 * b.1 * y) = X.psiInfU u m.1 • X.piU u b.1 (X.Wu u y) := by
      rw [mul_assoc, (X.Wu_spec u).1 m.1 hm1S, (X.piU_rep u).2.2.2.1 m.1 hn1, ContinuousLinearMap.one_apply,
        (X.Wu_spec u).1 b.1 hb1S]
      have hpsi : X.psiInfU u b.1 = 1 := psiInfU_of_mem_Hinf X u b.1 ha1
      change X.psiInfU u m.1 • (X.psiInfU u b.1 • X.piU u b.1 (X.Wu u y)) = _
      rw [hpsi, one_smul]
    have hC : (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (X.piU u b.1 (X.Wu u y)) (1, ⟨b.2, ha2⟩) =
        B.colForm T.1 (X.Wu u y) a := by
      have := hT2 ⟨b.1, ha1⟩ (X.Wu u y) (1, ⟨b.2, ha2⟩)
      refine this.trans ?_
      show (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (X.Wu u y) ((1, ⟨b.2, ha2⟩) * (⟨b.1, ha1⟩, 1)) =
        (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (X.Wu u y) (B.toH a)
      refine congrArg ((T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (X.Wu u y)) ?_
      refine Prod.ext ?_ ?_ <;> apply Subtype.ext
      · show (1 : X.B.I.Ginf) * b.1 = (iotaX X h (embA B.d B.o a)).1
        rw [one_mul]
      · show b.2 * (1 : X.B.I.Gf) = (iotaX X h (embA B.d B.o a)).2
        rw [mul_one]
    rw [hW, map_smul, Pi.smul_apply, smul_eq_mul, hC, chi2_apply_one X hK, B.tieψ n hn]
    ring

end GlobalTheory.Core.Mi.PhCol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameMatrixWeilPairActionLeftInv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.FrameAct

theorem mt_one' {D : D7} (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  show (matHom V 1).1 = 1
  simp

theorem finE_inv_val' {D : D7} (V : HSp D) (g : GA D V) :
    ((Lev.finE V g)⁻¹).1 = (Formalism.L2.Theta.mt V g⁻¹).map (toEAf D) := by
  rw [← map_inv]; rfl

theorem conj_inv_val' {D : D7} {n : ℕ} (β y : GL (Fin n) (Lev.EAf D)) :
    ((β⁻¹ * y * β)⁻¹ : GL (Fin n) (Lev.EAf D)).1 = (β⁻¹).1 * (y⁻¹).1 * β.1 := by
  rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul, Matrix.mul_assoc]

theorem frMapO_actO_left : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (g : GA D S) (x : WO S T), frMapO S T βS βT (actO S T g 1 x) = HMul.hMul (frMapO S T βS βT x) ((βS⁻¹ * Lev.finE S g * βS)⁻¹ : GL (Fin S.rank) (Lev.EAf D)).val := by
  intro D S T βS βT g x
  rw [frMapO, frMapO, actO, mt_one', Matrix.one_mul, Matrix.map_mul, conj_inv_val', finE_inv_val']
  have hb : βS.1 * (βS⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc βS.1, hb, Matrix.one_mul]

end GlobalTheory.ChainOnto.FrameAct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraNodesFarApartOfCubicNodeGap
section
open Formalism.BasicNotions

namespace GlobalTheory.Core.Rk.GapOfNodes

theorem harishChandraNodesFarApart_of_cubic_node_gap : ∀ D : D7, D.NodeGap (4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6) →
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D := by
  intro D H
  have hN : D.R.N D.R.m = D.R.rankX' + 1 := factXm D.R
  refine ⟨D.R.N D.R.m, hN.ge, fun τ i hi => ?_⟩
  have h := H D.u₀ τ i.1 hi
  rw [D.hcW_b D.u₀ τ] at h
  simp only [Fin.eta] at h
  have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := by positivity
  have hc : (0 : ℝ) ≤ ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 := by positivity
  have key : (((D.R.t : ℚ) + 2 * ((D.R.N D.R.m : ℕ) : ℚ) ^ 3 + 1 : ℚ) : ℝ) ≤
      (((D.hc τ).b ⟨i.1 + 1, hi⟩ - (D.hc τ).b i : ℚ) : ℝ) := by
    push_cast
    push_cast at h
    linarith
  exact_mod_cast key

end GlobalTheory.Core.Rk.GapOfNodes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasProdPartialLFunctionTwistedByCharLocalFactors
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory

theorem LSD_hasProd_LvTw : ∀ (D : D7) (Sf : Finset (FinPl D)) (par : GlobalTheory.LFun.Fam D.host.E) (χ : (AE D)ˣ →* Circle) (r : ℕ) (κ : ℝ), GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (Sf : Set (FinPl D))) par r κ → ∀ z : ℂ, κ + 1 < z.re → HasProd (fun v : {v : FinPl D // v ∉ (Sf : Set (FinPl D))} => GlobalTheory.LFun.LvTw par (GlobalTheory.LFun.val χ) v.1 z) (GlobalTheory.LFun.LSD D Sf par χ z) := by
  intro D Sf par χ r κ h z hz
  exact GlobalTheory.LFun.hasProd_Lv (h.converges_twist_val χ hz)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastStepTestFunctionEqColumnsTestFunctionStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge GlobalTheory.SymBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStepTestFunction_eq_columnsTestFunction : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), AtTwist (R := R) sel mu cst σ₀ P ι s W → PhiAgree Ch sel mu cst σ₀ P ι s W →
  ∀ (e' : XIx (Fin R.k) (Fin R.t) (s + 1) ≃ Fin (R.N (s + 1))) (e : Ix (Fin R.k ⊕ Fin (s + 1)) (Fin R.t) (s + 2) ⊕ Unit ≃ Fin (R.N R.m)),
    IsOrd xPos e' → IsOrd (Sum.elim zPos fun _ => R.N R.m - 1) e → ∀ (y : HomE X.E (R.N (s + 1)) (R.N R.m)),
      (W.T s R).PhiTop (fromCols (toLoc ι e e' y).toRows₁ 0) =
        σ₀ (PhiTop Ch mu cst.sharp s P.1 (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (s + 1))))) := by
  first | exact @GlobalTheory.TwBridge.TopPhi.topPhi | exact GlobalTheory.TwBridge.TopPhi.topPhi | (intros; apply GlobalTheory.TwBridge.TopPhi.topPhi <;> assumption)
end

