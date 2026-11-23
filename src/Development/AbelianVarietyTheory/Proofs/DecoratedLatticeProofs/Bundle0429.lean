module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0416
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0822
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurFiniteHeisenbergFockVacuumThetaFunctions
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0534
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0410
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumTransportSchwartzBruhatStandard
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn

section Model

variable {X Y G H : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [Monoid G] [Monoid H]

theorem exists_hom_of_model (P : X → Prop) (s : X → Y) (S : Submodule ℂ Y)
    (hadd : ∀ f f', P f → P f' → P (f + f') ∧ s (f + f') = s f + s f')
    (hsmul : ∀ (c : ℂ) f, P f → P (c • f) ∧ s (c • f) = c • s f)
    (hin : ∀ f, P f → s f ∈ S) (honto : ∀ φ ∈ S, ∃ f, P f ∧ s f = φ)
    (hinj : ∀ f f', P f → P f' → s f = s f' → f = f')
    (om : G →* Module.End ℂ X) (hpres : ∀ g f, P f → P (om g f)) (κ : G ≃* H) :
    ∃ ρ : H →* Module.End ℂ S, ∀ g f, P f → ∀ Φ : S, Φ.1 = s f → (ρ (κ g) Φ).1 = s (om g f) := by
  classical
  choose lift hlP hls using fun Φ : S => honto Φ.1 Φ.2
  have hlift : ∀ (Φ : S) f, P f → Φ.1 = s f → lift Φ = f := fun Φ f hf h =>
    hinj _ _ (hlP Φ) hf ((hls Φ).trans h)
  let act : H → Module.End ℂ S := fun h =>
    { toFun := fun Φ => ⟨s (om (κ.symm h) (lift Φ)), hin _ (hpres _ _ (hlP Φ))⟩
      map_add' := fun Φ Ψ => by
        have e : lift (Φ + Ψ) = lift Φ + lift Ψ :=
          hlift _ _ (hadd _ _ (hlP Φ) (hlP Ψ)).1 (by rw [(hadd _ _ (hlP Φ) (hlP Ψ)).2, hls, hls]; rfl)
        apply Subtype.ext
        simp only [Submodule.coe_add]
        rw [e, map_add (f := _)]
        exact (hadd _ _ (hpres _ _ (hlP Φ)) (hpres _ _ (hlP Ψ))).2
      map_smul' := fun c Φ => by
        have e : lift (c • Φ) = c • lift Φ :=
          hlift _ _ (hsmul c _ (hlP Φ)).1 (by rw [(hsmul c _ (hlP Φ)).2, hls]; rfl)
        apply Subtype.ext
        simp only [Submodule.coe_smul, RingHom.id_apply]
        rw [e, map_smul]
        exact (hsmul c _ (hpres _ _ (hlP Φ))).2 }
  have hact : ∀ h (Φ : S), ((act h Φ : S) : Y) = s (om (κ.symm h) (lift Φ)) := fun _ _ => rfl
  refine ⟨{ toFun := act, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · refine LinearMap.ext fun Φ => Subtype.ext ?_
    rw [hact, map_one, map_one]
    exact hls Φ
  · intro h₁ h₂
    refine LinearMap.ext fun Φ => Subtype.ext ?_
    rw [Module.End.mul_apply, hact, hact, map_mul, map_mul, Module.End.mul_apply,
      hlift (act h₂ Φ) _ (hpres _ _ (hlP Φ)) (hact h₂ Φ)]
  · intro g f hf Φ hΦ
    show s (om (κ.symm (κ g)) (lift Φ)) = s (om g f)
    rw [κ.symm_apply_apply, hlift Φ f hf hΦ]

end Model

theorem exists_transport_std : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ θ : InfFam D, IsInfFam θ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, ∃ omS : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank), IsTransport ψ θ A B ν 𝓨 omh κ omS := by
  intro D ψ A B χB omh hW ν 𝓨 hν θ hθ κ
  have hS := _root_.GlobalTheory.SchSchwartzAll.schSchwartz D ψ hW.std θ hθ A B ν 𝓨 hν
  have hL := _root_.GlobalTheory.StdUnn.sch_linear D ψ hW.std A B ν 𝓨 hν
  obtain ⟨ρ, hρ⟩ := exists_hom_of_model (IsThetaFunO ψ (dblSp A) B) (sch ψ A B ν 𝓨) (schwartzA θ B.rank A.rank)
    (fun f f' hf hf' => ⟨(hL f f' hf hf' 0).1, (hL f f' hf hf' 0).2.2.1⟩)
    (fun c f hf => ⟨(hL f f hf hf c).2.1, (hL f f hf hf c).2.2.2⟩)
    hS.1 hS.2.1 hS.2.2 (omh.comp (MonoidHom.inl _ _)) (fun g f hf => hW.om_pres _ _ hf) κ
  exact ⟨ρ, fun g f hf Φ hΦ => hρ g f hf Φ hΦ⟩

end GlobalTheory.StdUnn

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockMatrixCoefficientSplitsRealFiniteFactors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockCoefSplit


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem actO_inf : ∀ (D : D7) (S T : HSp D) (a : GA D S) (b : GA D T), a ∈ GinfC S → b ∈ GinfC T →
    ∀ w : WO S T, w.map (infPart D) = 0 → actO S T a b w = w := by
  intro D S T a b ha hb w hw
  have hfb : (Formalism.L2.Theta.mt T b).map (finPart D) = 1 := by
    have h := congrArg (fun g : GL (Fin T.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) => g.val)
      (MonoidHom.mem_ker.1 hb)
    exact h
  have hfa : (Formalism.L2.Theta.mt S a⁻¹).map (finPart D) = 1 := by
    have h := congrArg (fun g : GL (Fin S.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) => g.val)
      (MonoidHom.mem_ker.1 (Subgroup.inv_mem _ ha))
    exact h
  have h0 : ∀ k j, infPart D (w k j) = 0 := fun k j => by
    have := congrFun (congrFun hw k) j
    simpa using this
  have e1 : Formalism.L2.Theta.mt T b * w = w := by
    ext i j
    refine GlobalTheory.UnitarySplit.parts_inj D _ _ ?_ ?_
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.mul_apply, map_sum]
      simp [map_mul, h0]
    · have h1 : ∀ k, finPart D (Formalism.L2.Theta.mt T b i k) = if i = k then 1 else 0 := fun k => by
        have := congrFun (congrFun hfb i) k
        simpa [Matrix.one_apply] using this
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.mul_apply, map_sum]
      simp [map_mul, h1]
  have e2 : w * Formalism.L2.Theta.mt S a⁻¹ = w := by
    ext i j
    refine GlobalTheory.UnitarySplit.parts_inj D _ _ ?_ ?_
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.mul_apply, map_sum]
      simp [map_mul, h0]
    · have h1 : ∀ k, finPart D (Formalism.L2.Theta.mt S a⁻¹ k j) = if k = j then 1 else 0 := fun k => by
        have := congrFun (congrFun hfa k) j
        simpa [Matrix.one_apply] using this
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.mul_apply, map_sum]
      simp [map_mul, h1]
  unfold actO
  rw [e1, e2]

open GlobalTheory.VacPairSchur GlobalTheory.RawLift

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem om_heisO_inf {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hom : IsWeilDatumO ψ S T χS χT om) {a : GA D S} (ha : a ∈ GinfC S) {b : GA D T} (hb : b ∈ GinfC T)
    {w : WO S T} (hw : w.map (infPart D) = 0) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om (a, b) (heisO ψ S T w f) = heisO ψ S T w (om (a, b) f) := by
  rw [hom.om_heis a b w f hf, actO_inf D S T a b ha hb w hw]

theorem fockVac_om_fin {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om)
    (hθ : IsInfFam θ) {x : GA D S} (hx : x ∈ GfC S) {y : GA D T} (hy : y ∈ GfC T) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hv : IsFockVacAt (heisO ψ S T) θ τ J f) :
    IsFockVacAt (heisO ψ S T) θ τ J (om (x, y) f) := by
  have e : ∀ z : Matrix (Fin T.rank) (Fin S.rank) ℂ,
      compAt θ τ (Formalism.L2.Theta.mt T y) * z * compAt θ τ (Formalism.L2.Theta.mt S x⁻¹) = z := fun z => by
    rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hy, GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (Subgroup.inv_mem _ hx),
      Matrix.one_mul, Matrix.mul_one]
  intro z
  have h := congrArg (om (x, y)) (hv z)
  unfold annih at h ⊢
  rw [map_add (f := _), map_smul, GlobalTheory.OrientedHeis.om_dRho hom hθ x y τ z hf, GlobalTheory.OrientedHeis.om_dRho hom hθ x y τ (J z) hf,
    e, e, map_zero] at h
  exact h

theorem om_fin_pureTensorO {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om)
    (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {x : GA D S} (hx : x ∈ GfC S) {y : GA D T}
    (hy : y ∈ GfC T) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    om (x, y) (pureTensorO ψ θ S T sS sT BS BT f P) = pureTensorO ψ θ S T sS sT BS BT (om (x, y) f) P :=
  (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hom hθ sS sS BS BS sT sT BT BT x y
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hx, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hy, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hx, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hy, Matrix.one_mul]) f hf P).2

theorem l2_eq_star (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f g : WO S T → ℂ) :
    l2 μ 𝓕 f g = star (thetaIP μ 𝓕 f g) := by
  unfold l2 Formalism.IndefR.Lift.pet thetaIP
  change _ = (starRingEnd ℂ) (∫ w in 𝓕, star (f w) * g w ∂μ)
  rw [← integral_conj]
  congr 1
  funext w
  simp [mul_comm]

theorem pair_eq_inf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (pS pT : D.what₂.Tau → ℕ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → (∀ τ, IsONBasis (gramAt D S τ) (sS τ) (BS τ) (pS τ)) → (∀ τ, IsONBasis (gramAt D T τ) (sT τ) (BT τ) (pT τ)) → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ a ∈ GinfC S, ∀ b ∈ GinfC T, ∀ P P' : MvPolynomial (FVar D T.rank S.rank) ℂ, ∃ c : ℂ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → thetaIP μ 𝓕 (om (a, b) (pureTensorO ψ θ S T sS sT BS BT f P)) (pureTensorO ψ θ S T sS sT BS BT g P') = c * thetaIP μ 𝓕 f g := by
  intro D ψ θ S T χS χT om hom hθ sS BS sT BT pS pT hcS hcT hoS hoT μ 𝓕 hcv a ha b hb P P'
  have hψ := hom.std
  have hμ := hcv.1
  have h𝓕 := hcv.2.1
  have thp : ∀ f, IsThetaFunO ψ S T f → ∀ Q, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f Q) :=
    fun f hf Q => GlobalTheory.Chain.InnerSteps.theta_pureTensorO hψ hθ sS BS sT BT hf Q
  have thom : ∀ f, IsThetaFunO ψ S T f → ∀ Q,
      IsThetaFunO ψ S T (om (a, b) (pureTensorO ψ θ S T sS sT BS BT f Q)) :=
    fun f hf Q => hom.om_pres _ _ (thp f hf Q)
  have key : ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → ∀ Q,
      thetaIP μ 𝓕 (pureTensorO ψ θ S T sS sT BS BT f Q) (pureTensorO ψ θ S T sS sT BS BT f Q) =
        GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp Q Q * (nrm2 μ 𝓕 f : ℂ) := by
    intro f hf vf Q
    rw [thetaIP_eq_ipO]
    exact GlobalTheory.FockIsometry.ipO_pureTensorO D ψ θ S T hψ hθ sS BS sT BT (fun τ => min (pS τ) S.rank)
      (fun τ => min (pT τ) T.rank) (fun τ => min_le_right _ _) (fun τ => min_le_right _ _) hcS hcT
      (fun τ => onb_min (hoS τ)) (fun τ => onb_min (hoT τ)) f hf vf μ 𝓕 hcv Q Q
  set Φ : (WO S T → ℂ) → (WO S T → ℂ) → ℂ := fun f g =>
    thetaIP μ 𝓕 (om (a, b) (pureTensorO ψ θ S T sS sT BS BT f P)) (pureTensorO ψ θ S T sS sT BS BT g P') with hΦ
  have hl : ∀ (z : ℂ) (f f' g : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → IsThetaFunO ψ S T g →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f') → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → Φ (z • f + f') g = star z * Φ f g + Φ f' g := by
    intro z f f' g hf hf' hg _ _ _
    simp only [hΦ]
    rw [pT_lin hψ hθ sS BS sT BT z hf hf' P, map_add (f := _), map_smul, thetaIP_eq_ipO, thetaIP_eq_ipO, thetaIP_eq_ipO,
      GlobalTheory.Size.ipO_add_right hψ hμ h𝓕 (thp g hg P') (GlobalTheory.OrientedHeis.theta_smul z (thom f hf P)) (thom f' hf' P),
      GlobalTheory.Size.ipO_smul_right]
    rfl
  have hr : ∀ (z : ℂ) (f g g' : WO S T → ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g') → Φ f (z • g + g') = z * Φ f g + Φ f g' := by
    intro z f g g' hf hg hg' _ _ _
    simp only [hΦ]
    rw [pT_lin hψ hθ sS BS sT BT z hg hg' P', thetaIP_eq_ipO, thetaIP_eq_ipO, thetaIP_eq_ipO,
      GlobalTheory.Size.ipO_add_left hψ hμ h𝓕 (GlobalTheory.OrientedHeis.theta_smul z (thp g hg P')) (thp g' hg' P') (thom f hf P),
      GlobalTheory.Size.ipO_smul_left]
  have hbd : ∃ C : ℝ, ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) →
      ‖Φ f g‖ ^ 2 ≤ C * (nrm2 μ 𝓕 f * nrm2 μ 𝓕 g) := by
    refine ⟨(GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp P P).re * (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp P' P').re, fun f g hf hg vf vg => ?_⟩
    simp only [hΦ]
    have h1 := cs hψ hcv (thom f hf P) (thp g hg P')
    rw [GlobalTheory.WeilPairing.thetaInner_weilRep D ψ S T χS χT om μ 𝓕 hom hcv _ _ _ (thp f hf P) (thp f hf P),
      key f hf vf P, key g hg vg P', Complex.re_mul_ofReal, Complex.re_mul_ofReal] at h1
    linarith
  have hi : ∀ w : WO S T, w.map (infPart D) = 0 → ∀ f g : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g →
      (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) g) → Φ (heisO ψ S T w f) (heisO ψ S T w g) = Φ f g := by
    intro w hw f g hf hg _ _
    simp only [hΦ]
    rw [pT_heisO hθ sS BS sT BT f hw, pT_heisO hθ sS BS sT BT g hw, om_heisO_inf hom ha hb hw (thp f hf P),
      thetaInner_heisenberg hψ hcv (thom f hf P) (thp g hg P')]
  exact _root_.GlobalTheory.VacSchurFin.vacSchur D ψ θ S T hψ hθ sS sT hcS hcT μ 𝓕 hcv Φ hl hr hbd hi

end GlobalTheory.FockCoefSplit

namespace GlobalTheory.FockCoefSplit

open GlobalTheory.RawLift

theorem coef_split : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ (μ : Measure (WO S T)) (𝓧 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓧 → ∀ (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ pS pT : D.what₂.Tau → ℕ, (∀ τ, IsONBasis (gramAt D S τ) (sS τ) (BS τ) (pS τ)) → (∀ τ, IsONBasis (gramAt D T τ) (sT τ) (BT τ) (pT τ)) → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → (∀ Q, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f Q)) → ∀ a ∈ GinfC S, ∀ b ∈ GinfC T, ∀ x ∈ GfC S, ∀ y ∈ GfC T, ∀ Q Q', l2 μ 𝓧 (om (x * a, y * b) (pureTensorO ψ θ S T sS sT BS BT f Q)) (pureTensorO ψ θ S T sS sT BS BT f Q') * l2 μ 𝓧 f f = l2 μ 𝓧 (om (a, b) (pureTensorO ψ θ S T sS sT BS BT f Q)) (pureTensorO ψ θ S T sS sT BS BT f Q') * l2 μ 𝓧 (om (x, y) f) f := by
  intro D ψ θ S T χS χT om hθ hom μ 𝓧 hcv sS BS sT BT hcS hcT pS pT hoS hoT f hf hvf hpt a ha b hb x hx y hy Q Q'
  obtain ⟨c, hc⟩ := pair_eq_inf D ψ θ S T χS χT om hom hθ sS BS sT BT pS pT hcS hcT hoS hoT μ 𝓧 hcv a ha b hb Q Q'
  have hx' : x⁻¹ ∈ GfC S := Subgroup.inv_mem _ hx
  have hy' : y⁻¹ ∈ GfC T := Subgroup.inv_mem _ hy
  have hg : IsThetaFunO ψ S T (om (x⁻¹, y⁻¹) f) := hom.om_pres _ _ hf
  have hvg : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (om (x⁻¹, y⁻¹) f) :=
    fun τ => fockVac_om_fin hom hθ hx' hy' τ _ hf (hvf τ)
  have inv : ∀ A B : WO S T → ℂ, IsThetaFunO ψ S T A → IsThetaFunO ψ S T B →
      thetaIP μ 𝓧 (om (x, y) A) B = thetaIP μ 𝓧 A (om (x⁻¹, y⁻¹) B) := by
    intro A B hA hB
    have e : om (x, y) (om (x⁻¹, y⁻¹) B) = B := by
      rw [← Module.End.mul_apply, ← map_mul,
        show ((x, y) * (x⁻¹, y⁻¹) : GA D S × GA D T) = 1 from mul_inv_cancel (x, y), map_one, Module.End.one_apply]
    calc thetaIP μ 𝓧 (om (x, y) A) B = thetaIP μ 𝓧 (om (x, y) A) (om (x, y) (om (x⁻¹, y⁻¹) B)) := by rw [e]
      _ = thetaIP μ 𝓧 A (om (x⁻¹, y⁻¹) B) :=
        GlobalTheory.WeilPairing.thetaInner_weilRep D ψ S T χS χT om μ 𝓧 hom hcv _ _ _ hA (hom.om_pres _ _ hB)
  have e1 : om (x * a, y * b) (pureTensorO ψ θ S T sS sT BS BT f Q) =
      om (x, y) (om (a, b) (pureTensorO ψ θ S T sS sT BS BT f Q)) := by
    rw [← Module.End.mul_apply, ← map_mul]
    rfl
  simp only [l2_eq_star]
  rw [← star_mul', ← star_mul']
  congr 1
  rw [e1, inv _ _ (hom.om_pres _ _ (hpt Q)) (hpt Q'), om_fin_pureTensorO hom hθ sS BS sT BT hx' hy' hf Q',
    hc f _ hf hg hvf hvg, inv _ _ hf hf, hc f f hf hf hvf hvf]
  ring

end GlobalTheory.FockCoefSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FormTranslateRealPointReadByPeriod
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.TopTranslate

open GlobalTheory.Mem.ColAd GlobalTheory.Core.Rk.TopLift

theorem infM_eq_reindex {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (τ : D.what₂.Tau) :
    infM θ V hn g τ = (infMat D.sp.cm.sig V.gram (θ τ) g).reindex (finCongr hn) (finCongr hn) := by
  subst hn
  rfl

theorem infPt_eq_infM {D : D7} (θ : InfFam D) (x : GA D D.sp.X') (τ : D.what₂.Tau) :
    ((infPt θ x τ : GL _ ℂ) : Matrix _ _ ℂ) = infM θ D.sp.X' (rankP D) x τ := by
  rw [infM_eq_reindex]
  exact GlobalTheory.Core.Rk.TopOnto.infN_eq (rankP D) x τ

theorem infPt_mul_inv {D : D7} (θ : InfFam D) (x : GA D D.sp.X') (τ : D.what₂.Tau) :
    (infPt θ x τ).1 * (infPt θ x⁻¹ τ).1 = 1 := by
  rw [← Units.val_mul, ← Pi.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem top_translate : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ s : ℕ → ℂ) J, PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → JOf R j J → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (r : RowCh R P u g t) (a : I.ι) (k : ColCh (D := (I.rec7 l Z)) u ((I.rec7 l Z).chTw u a)) (tl : ColT I l u a B.R.m → CXP R P t → ℂ) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, k.Ch j → Ch₀ j) w, PinChL R g k c₀ A ι w → ∀ UT ε, PinTopL R g P (t := t) k UT ε → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → (∀ ψ f, ∃ G', ReadsG K eW j g.bT G' f.1 ∧ tl ψ f = (I.per l u a).Ptil ψ G') → ∀ h : (I.fm l u a).clsP → GA (I.rec7 l Z) (I.rec7 l Z).sp.X', (∀ c, GlobalTheory.Core.Rk.Top.HasMat (h c) (K.y c).1) → ∀ G' : CXP R P t → (I.per l u a).Mt, (∀ f, ReadsG K eW j g.bT (G' f) f.1) → ∀ (f : CXP R P t) v c, ∀ x ∈ GinfC (I.rec7 l Z).sp.X', f.1 v (h c * x * g.bT) = (Nat.card ((I.fm l u a).stabilizer₂ c) : ℂ) * (I.per l u a).period (eW.symm (Pi.single c fun y : FrP (I.rec7 l Z) => J v x ⟨y.1, y.2⟩)) (G' f) := by
  intro B X I _ _ l Z u G _ _ Pl0 T F Ks _ _ _ R g c₀ s J hX j hj hJ P t r a k tl Ch₀ A ι w _ UT ε _ bad K eW _ _ hbT _ _ h hh G' hG' f v c x hx
  obtain ⟨v', e1, e2⟩ := GlobalTheory.Core.Rk.TopOnto.real_translate (J := levS _ R.βX (datXP R P t))
    (χ := levChi _ R.βX (datXP R P t)) hX.inf hj x hx v
  have ex : h c * x * g.bT = h c * g.bT * x := by
    rw [mul_assoc, GlobalTheory.PointAtPlaceHom.comm_of_mem _ hx hbT, ← mul_assoc]
  have key : j v' = fun y : FrP (I.rec7 l Z) => J v x ⟨y.1, y.2⟩ := by
    funext y
    have h1 : j v' y = j v (frL _ (infPt R.θ x⁻¹) y) := by
      rw [← e1, lT_apply]
      refine congrArg (j v') (Subtype.ext (funext fun τ => ?_))
      show y.1 τ = _ * (_ * y.1 τ)
      rw [← Matrix.mul_assoc, infPt_mul_inv, Matrix.one_mul]
    rw [h1]
    refine (hJ v x hx ⟨(frL _ (infPt R.θ x⁻¹) y).1, (frL _ (infPt R.θ x⁻¹) y).2⟩ ⟨y.1, y.2⟩ fun τ => ?_).symm
    show y.1 τ = infM R.θ _ (rankP (I.rec7 l Z)) x τ * (_ * y.1 τ)
    rw [← infPt_eq_infM, ← Matrix.mul_assoc, infPt_mul_inv, Matrix.one_mul]
  rw [ex, ← e2 f.1 f.2 (h c * g.bT), hG' f c v' (h c) (hh c), key]

end GlobalTheory.AdForm.TopTranslate

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealLocallyPrincipalAdelic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.FinPl.idV_principal_at : ∀ (D : D7) (v : Pl D) (𝔞 : FI D), 𝔞 ≠ 0 → ∃ g ∈ idV 𝔞 v, ∃ g' ∈ idAt D (· = v), (∀ s ∈ idAt D (· = v), g' * g * s = s) ∧ ∀ s, s ∈ idV 𝔞 v ↔ s ∈ idAt D (· = v) ∧ g' * s ∈ intAt D (· = v) := by
  intro D v 𝔞 h𝔞
  obtain ⟨x, hx0, hx⟩ := _root_.GlobalTheory.IdVGen.idV_gen D v 𝔞 h𝔞
  obtain ⟨ε, hεε, -, hεint, hεid, -⟩ := (_root_.GlobalTheory.FinPl.localComponents D (· = v)).1
  have hεI : ε ∈ idAt D (· = v) := hεint.1
  have hxx : incA D x⁻¹ * incA D x = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
  refine ⟨incA D x * ε, ?_, incA D x⁻¹ * ε, Ideal.mul_mem_left _ _ hεI, ?_, ?_⟩
  · rw [hx]
    refine ⟨?_, Ideal.mul_mem_left _ _ hεI⟩
    rw [← mul_assoc, hxx, one_mul]; exact hεint
  · intro s hs
    have : incA D x⁻¹ * ε * (incA D x * ε) = ε * ε := by
      calc incA D x⁻¹ * ε * (incA D x * ε) = (incA D x⁻¹ * incA D x) * (ε * ε) := by ring
        _ = ε * ε := by rw [hxx, one_mul]
    rw [this, hεε]; exact (hεid s).1 hs
  · intro s
    rw [hx]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h2, ?_⟩
      rw [mul_assoc, (hεid s).1 h2]; exact h1
    · rintro ⟨h2, h1⟩
      refine ⟨?_, h2⟩
      rw [mul_assoc, (hεid s).1 h2] at h1; exact h1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeCharUnramifiedAtQuotientSameResidual
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ResUnr

open Formalism.L2.Host

theorem exists_int_div {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (k : E)
    (hk : P.valuation E k = 1) :
    ∃ a s : 𝓞 E, a ∉ P.asIdeal ∧ s ∉ P.asIdeal ∧ k * algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E a := by
  obtain ⟨n, d, h | h⟩ := P.exists_primeCompl_mul_eq_or_mul_eq (K := E) k
  · refine ⟨n, d, ?_, d.2, h⟩
    rw [← HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E), ← h, map_mul, hk, one_mul,
      HeightOneSpectrum.valuation_eq_one_iff_notMem]
    exact d.2
  · refine ⟨d, n, d.2, ?_, h⟩
    have h2 := congrArg (P.valuation E) h
    rw [map_mul, hk, one_mul, (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) (r := (d : 𝓞 E)) P).2 d.2] at h2
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := E) P).1 h2

theorem loc_eq_of_isRes {D : D7} {H₁ H₂ : Formalism.L2.Host.HChar D.host.E} {PP : Pl D.host.E} {ξ : (kP PP)ˣ →* ℂˣ}
    (h₁ : IsRes H₁ PP ξ) (h₂ : IsRes H₂ PP ξ) (x : (PP.adicCompletion D.host.E)ˣ) (hx : IsUnitAt PP x) :
    H₁.loc PP x = H₂.loc PP x := by
  have hc : IsClopen {x : (PP.adicCompletion D.host.E)ˣ | IsUnitAt PP x} := by
    have := (Valued.isClopen_sphere (PP.adicCompletion D.host.E) (r := 1) one_ne_zero).preimage
      (Units.continuous_val (M := PP.adicCompletion D.host.E))
    convert this using 1
    ext x
    simp [IsUnitAt]
  have hK : ∀ k : D.host.Eˣ, PP.valuation D.host.E (k : D.host.E) = 1 → H₁.locK PP k = H₂.locK PP k := by
    intro k hk
    obtain ⟨a, s, ha, hs, hks⟩ := exists_int_div PP (k : D.host.E) hk
    haveI : PP.asIdeal.IsMaximal := PP.isMaximal
    have hne : ∀ b : 𝓞 D.host.E, b ∉ PP.asIdeal → algebraMap (𝓞 D.host.E) D.host.E b ≠ 0 := fun b hb h0 =>
      hb (by rw [(IsFractionRing.injective (𝓞 D.host.E) D.host.E) (h0.trans (map_zero _).symm)]; exact PP.asIdeal.zero_mem)
    have hq : ∀ b : 𝓞 D.host.E, b ∉ PP.asIdeal → (Ideal.Quotient.mk PP.asIdeal b : kP PP) ≠ 0 := fun b hb h0 =>
      hb (Ideal.Quotient.eq_zero_iff_mem.1 h0)
    let A : D.host.Eˣ := Units.mk0 _ (hne a ha)
    let S : D.host.Eˣ := Units.mk0 _ (hne s hs)
    let ua : (kP PP)ˣ := Units.mk0 _ (hq a ha)
    let us : (kP PP)ˣ := Units.mk0 _ (hq s hs)
    have hkS : k * S = A := Units.ext hks
    have e1 : H₁.locK PP A = H₂.locK PP A := ((h₁ a A ua rfl rfl).symm.trans (h₂ a A ua rfl rfl))
    have e2 : H₁.locK PP S = H₂.locK PP S := ((h₁ s S us rfl rfl).symm.trans (h₂ s S us rfl rfl))
    rw [← hkS, map_mul, map_mul, e2] at e1
    exact mul_right_cancel e1
  refine (GlobalTheory.Mem.Chr.Determ.denseRange_atFin PP).induction_on
    (p := fun x => IsUnitAt PP x → H₁.loc PP x = H₂.loc PP x) x ?_
    (fun k hk => hK k ((PP.valuedAdicCompletion_eq_valuation' _).symm.trans hk)) hx
  exact isClosed_imp hc.2 (isClosed_eq (H₁.2.1.comp (GlobalTheory.Mem.Chr.Determ.continuous_localIdele PP))
    (H₂.2.1.comp (GlobalTheory.Mem.Chr.Determ.continuous_localIdele PP)))

theorem unrAt_div_of_isRes : ∀ (D : D7) (c₁ c₂ : (AE D)ˣ →* Circle) (H₁ H₂ : Formalism.L2.Host.HChar D.host.E) (PP : Pl D.host.E) (ξ : (kP PP)ˣ →* ℂˣ), ChrEq c₁ H₁ → ChrEq c₂ H₂ → IsRes H₁ PP ξ → IsRes H₂ PP ξ → GlobalTheory.LFun.UnrAt (F := D.host.F) (c₁ * c₂⁻¹) PP := by
  intro D c₁ c₂ H₁ H₂ PP ξ hc₁ hc₂ h₁ h₂ x hx
  have e : GlobalTheory.LFun.locChar (c₁ * c₂⁻¹) PP x = GlobalTheory.LFun.locChar c₁ PP x * (GlobalTheory.LFun.locChar c₂ PP x)⁻¹ := by
    simp only [GlobalTheory.LFun.locChar, MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv]
  rw [e, GlobalTheory.LFun.locChar_eq_of_chrEq hc₁, GlobalTheory.LFun.locChar_eq_of_chrEq hc₂, loc_eq_of_isRes h₁ h₂ x hx, mul_inv_cancel]

end GlobalTheory.ResUnr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastDoubleThetaLiftIntegrableLinearStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastDoubleThetaLift_integrable_linear : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c), c.Is → t.Is → WeilOK (t := t) v → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (Y : WO (c.V (j + 1)) c.T → ℂ), IsThetaFunO c.ψ _ _ Y → ∀ φ, IsContAut (c.X j) φ → (∀ X : WO (c.V j) (c.V (j + 1)) → ℂ, IsThetaFunO c.ψ _ _ X → ∀ f, IsContAut c.T f → IntegrableOn (fun h' => f h' * c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) X Y) ((c.oT (j + 1 + 1) h).emb (h', 1))) c.volT.𝓕 c.volT.μ) ∧ ∀ (G : Type) (s : Finset G) (a : G → ℂ) (X : G → WO (c.V j) (c.V (j + 1)) → ℂ), (∀ g, IsThetaFunO c.ψ _ _ (X g)) → ∑ g ∈ s, a g • c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (X g) Y) = c.bl j (t.kom j) (t.kom (j + 1)) φ (c.lst j h (v.τ j h) (t.sBF j 0 h) (∑ g ∈ s, a g • X g) Y) := by
  first | exact @GlobalTheory.LastDbl.main | exact GlobalTheory.LastDbl.main | (intros; apply GlobalTheory.LastDbl.main <;> assumption)
end

