module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0583
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0414
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0203
public import Formalism.LocalRingCardinality.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0156
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0780
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0526
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0527
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevChiLift
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.Inhab

variable {D : D7}

theorem pt_sum {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    {ι : Type} (s : Finset ι) (a : ι → ℂ) (g : ι → WO S T → ℂ) (hg : ∀ i, IsThetaFunO ψ S T (g i)) (φ : PolF D T.rank S.rank) :
    IsThetaFunO ψ S T (∑ i ∈ s, a i • g i) ∧
      pureTensorO ψ θ S T sS sT BS BT (∑ i ∈ s, a i • g i) φ = ∑ i ∈ s, a i • pureTensorO ψ θ S T sS sT BS BT (g i) φ := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact ⟨GlobalTheory.OrientedHeis.theta_zero, GlobalTheory.FockFiniteHeis.pureTensorO_zero ψ θ S T hψ hθ sS BS sT BT φ⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    refine ⟨GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul _ (hg i)) ih.1, ?_⟩
    rw [GlobalTheory.FockFiniteHeis.pureTensorO_lin ψ θ S T hψ hθ sS BS sT BT (a i) (hg i) ih.1 φ, ih.2]

theorem pt_om {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {k : GA D S}
    (hk : k ∈ GfC S) (φ : PolF D T.rank S.rank) :
    pureTensorO ψ θ S T sS sT BS BT (om (k, 1) f) φ = om (k, 1) (pureTensorO ψ θ S T sS sT BS BT f φ) :=
  (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hom hθ sS sS BS BS sT sT BT BT k 1
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hk, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hk, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.one_mul]) f hf φ).2.symm

theorem lift_sum {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hom : IsWeilDatumO ψ S T χS χT om) (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {f f' : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    {ι : Type} [Fintype ι] (κ : ι → GA D S) (hκ : ∀ i, κ i ∈ GfC S) (a : ι → ℂ) (ha : ∀ i, a i ≠ 0)
    (hf' : f' = ∑ i, (a i)⁻¹ • om (κ i, 1) f) (ν : Measure (GA D T)) (𝓕 : Set (GA D T)) (F : GA D T → ℂ) (φ : PolF D T.rank S.rank)
    (hi : ∀ g, IntegrableOn (fun h => thetaKO om g h (pureTensorO ψ θ S T sS sT BS BT f φ) * F h) 𝓕 ν) (U : GA D S → ℂ)
    (hU : ∀ g, Lift.liftInt ν 𝓕 (thetaKO om) (pureTensorO ψ θ S T sS sT BS BT f φ) F g = U g)
    (hl : ∀ i g, U (g * κ i) = a i * U g) :
    (∀ g, IntegrableOn (fun h => thetaKO om g h (pureTensorO ψ θ S T sS sT BS BT f' φ) * F h) 𝓕 ν) ∧
      liftS om ν 𝓕 F (pureTensorO ψ θ S T sS sT BS BT f' φ) = (Nat.card ι : ℂ) • U := by
  have e : ∀ g h, thetaKO om g h (pureTensorO ψ θ S T sS sT BS BT f' φ) * F h =
      ∑ i, (a i)⁻¹ * (thetaKO om (g * κ i) h (pureTensorO ψ θ S T sS sT BS BT f φ) * F h) := fun g h => by
    rw [hf', (pt_sum hom.std hθ sS BS sT BT _ _ _ (fun i => hom.om_pres _ _ hf) φ).2]
    unfold thetaKO
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pt_om hom hθ sS BS sT BT hf (hκ i), map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, ← mul_apply_eq_comp, ← map_mul,
      Prod.mk_mul_mk, mul_one]
  refine ⟨fun g => ?_, funext fun g => ?_⟩
  · simp only [e]
    exact integrable_finsetSum _ fun i _ => (hi _).const_mul _
  · show ∫ h in 𝓕, thetaKO om g h (pureTensorO ψ θ S T sS sT BS BT f' φ) * F h ∂ν = _
    simp only [e]
    rw [integral_finsetSum _ fun i _ => (hi _).const_mul _]
    have : ∀ i, ∫ h in 𝓕, (a i)⁻¹ * (thetaKO om (g * κ i) h (pureTensorO ψ θ S T sS sT BS BT f φ) * F h) ∂ν = U g := fun i => by
      rw [integral_const_mul]
      have h1 := hU (g * κ i)
      unfold Lift.liftInt at h1
      rw [h1, hl, ← mul_assoc, inv_mul_cancel₀ (ha i), one_mul]
    simp only [this, Finset.sum_const, Finset.card_univ, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.card_eq_fintype_card]

theorem levChi_lift {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank} (P : LevelP L.Pg L.r ℂ) (p : P.H)
    {κ : GA D V} (hκ : IsLevelLift V β L p.1 κ) : κ ∈ levS V β (withP L P) :=
  ⟨hκ.1, hκ.2.1, by
    show rTup β L (finE V κ) ∈ P.H
    rw [hκ.2.2]; exact p.2⟩

theorem step_eigen {S T : HSp D} {Sp : D.what₂.Tau → SPar} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ)
    (hCR : GlobalTheory.Published.CuspRapidDecay) {χS χT : (AE D)ˣ →* Circle} {om : Om S T} (hom : IsWeilDatumO ψ S T χS χT om)
    {sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {f : WO S T → ℂ} (hpt : ∀ P, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f P))
    {M : DSModel S Sp} {β : GL (Fin S.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ S.rank} (hL : flag1L L = L)
    {μ : Measure (GA D S)} {𝓔 : Set (GA D S)} (hμ : μ.IsHaarMeasure ∧ IsFundamentalDomain (GQ S) 𝓔 μ)
    {Ds : Type} [AddCommGroup Ds] [Module ℂ Ds] {It : PolF D T.rank S.rank →ₗ[ℂ] Ds →ₗ[ℂ] SmT M} (hIt : It ≠ 0)
    {CC : Submodule ℂ (Ds →ₗ[ℂ] (GA D T → ℂ))} (hCC : ∀ F : CC, ∀ v, ∀ γ ∈ GQ T, ∀ g, F.1 v (γ * g) = F.1 v g)
    {β' : GL (Fin T.rank) (Lev.EAf D)} {L' : LevDat D.host.E ℂ T.rank}
    {ν : Measure (GA D T)} {𝓕 : Set (GA D T)} (hν : ν.IsHaarMeasure ∧ IsFundamentalDomain (GQ T) 𝓕 ν)
    {io : CC →ₗ[ℂ] MultT θ M (levS S β L) (levChi S β L)}
    (hio : Lift.IsIo ν 𝓕 (thetaKO om) (pureTensorO ψ θ S T sS sT BS BT f) It CC _ io)
    {g0 : G0 L.Pg L.r} {κ : GA D S} (hκ : IsLevelLift S β L g0 κ) {g0' : G0 L'.Pg L'.r} {κ' : GA D T}
    (hκ' : IsLevelLift T β' L' g0' κ') {a' : ℂ} (hf : (levChi S β (flagL L) κ)⁻¹ • om (κ, κ') f = a' • f)
    (F : CC) {c : ℂ} (hF : ∀ v h, a' * F.1 v (h * κ') = c * F.1 v h) (v : SmT M) (g : GA D S) :
    (levChi S β (flagL L) κ)⁻¹ * (io F).1 v (g * κ) = c * (io F).1 v g := by
  have := GlobalTheory.ChainEquiv.step ψ θ hθ χS χT om hom sS BS sT BT f hpt M β L hL μ hμ.1 𝓔 hμ.2 (GlobalTheory.MultFinite.schurMult hCR _ _)
    It hIt CC hCC β' L' ν hν.1 𝓕 hν.2 io hio g0 κ hκ g0' κ' hκ' a' hf F (c • F) (fun v h => (hF v h).symm) v g
  rw [← this, map_smul]
  rfl

end GlobalTheory.Fam.Inhab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesIntegralNonzeroConstant
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

namespace GlobalTheory.Core.Rk.Exh.LocalConst

variable {D : D7}

theorem continuous_wcoef {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : WRep S T}
    (hom : IsWeilDatumO ψ S T χS χT om) {ν : Measure (WO S T)} {𝓕 : Set (WO S T)} (hν : IsCovolOne (ratL T S) ν 𝓕)
    {Φ₁ Φ₂ : WO S T → ℂ} (h₁ : IsThetaFunO ψ S T Φ₁) (h₂ : IsThetaFunO ψ S T Φ₂) :
    Continuous (wcoef om ν 𝓕 Φ₁ Φ₂) := by
  have hj := GlobalTheory.Unf.jointCont_all D ψ _ _ _ _ om hom Φ₁ h₁
  show Continuous fun g => ∫ w in 𝓕, om (g, 1) Φ₁ w * conj (Φ₂ w) ∂ν
  exact continuous_covolOne_integral hν (fun g w => om (g, 1) Φ₁ w * conj (Φ₂ w))
    ((hj.comp ((continuous_fst.prodMk continuous_const).prodMk continuous_snd)).mul
      (Complex.continuous_conj.comp (h₂.cont.comp continuous_snd)))
    (fun g => GlobalTheory.Size.mul_conj_periodic hom.std (hom.om_pres _ _ h₁) h₂)

theorem continuous_rcoef {θ : InfFam D} {A : HSp D} {cA : CptF A} (hA : HSpace.SigOK A) (hP : HSpace.IsPosDef A)
    {m : Measure (GA D A)} (hm : m.IsHaarMeasure) {u : GA D A → ℂ} (hu : u ∈ A0 θ A cA) :
    Continuous (rcoef m u u) := by
  obtain ⟨⟨K₀, hK₀, hK₀c⟩, X, K, -, hX, hK, hXK⟩ := _root_.GlobalTheory.DefFund.coCpt_and_fundamentalDomain_subset_compact D A hA hP m hm
  have hu' := (Submodule.mem_inf.1 hu).2
  have huc : Continuous u := hu'.1
  have hul : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ A) u := hu'.2.1
  obtain ⟨C, hC⟩ : ∃ C, ∀ g, ‖u g‖ ≤ C := by
    obtain ⟨C, hC⟩ := hK₀.exists_bound_of_continuousOn huc.continuousOn
    refine ⟨C, fun g => ?_⟩
    obtain ⟨γ, hγ, hg⟩ := hK₀c g
    rw [← hul γ hγ g]
    exact hC _ hg
  have e : ∀ g, rcoef m u u g = ∫ x in X, u (x * g) * conj (u x) ∂m := fun g =>
    GlobalTheory.AutomorphicL2Unitary.pet_eq hX (fun γ hγ x => by simp only [rTr, mul_assoc]; exact hul γ hγ _) hul
  have hfin : m X < ⊤ := (measure_mono hXK).trans_lt hK.measure_lt_top
  rw [show rcoef m u u = fun g => ∫ x in X, u (x * g) * conj (u x) ∂m from funext e]
  refine continuous_of_dominated (bound := fun _ => C * C) (fun g => ?_) (fun g => ?_) ?_ ?_
  · exact ((huc.comp (continuous_id.mul continuous_const)).mul
      (Complex.continuous_conj.comp huc)).aestronglyMeasurable
  · exact .of_forall fun x => by
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (hC _) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hC x))
  · have : IsFiniteMeasure (m.restrict X) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
    exact integrable_const _
  · exact .of_forall fun x => (huc.comp (continuous_const.mul continuous_id)).mul continuous_const

theorem wcoef_mul_fix {S T : HSp D} (om : WRep S T) (ν : Measure (WO S T)) (𝓕 : Set (WO S T)) (Φ₁ Φ₂ : WO S T → ℂ)
    (x κ : GA D S) (h : om (κ, 1) Φ₁ = Φ₁) : wcoef om ν 𝓕 Φ₁ Φ₂ (x * κ) = wcoef om ν 𝓕 Φ₁ Φ₂ x := by
  have e : ((x * κ, 1) : GA D S × GA D T) = (x, 1) * (κ, 1) := by simp
  simp only [wcoef, e, map_mul, Module.End.mul_apply, h]

theorem rcoef_mul_fix {A : HSp D} (m : Measure (GA D A)) (u : GA D A → ℂ) (x κ : GA D A) (h : ∀ g, u (g * κ) = u g) :
    rcoef m u u (x * κ) = rcoef m u u x := by
  have e : rTr A (x * κ) u = rTr A x u := funext fun g => by simp only [rTr, ← mul_assoc, h]
  simp only [rcoef, e]

end GlobalTheory.Core.Rk.Exh.LocalConst

namespace GlobalTheory.Core.Rk.Exh.LocalConst

theorem integral_const : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)), Defin θ A cA a → ∀ (B W H : HSp D) (o : OrthDec B W H) (χA χW : (AE D)ˣ →* Circle) (omB : WRep A B) (omW : WRep A W) (omH : WRep A H), IsWeilDatumO ψ A B χA χW omB → IsWeilDatumO ψ A W χA χW omW → IsWeilDatumO ψ A H χA 1 omH → ∀ (β : GL (Fin A.rank) (Formalism.IndefR.Lev.EAf D)) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)), Places A β Z → ∀ m : Measure (GA D A), m.IsHaarMeasure → ∀ u ∈ A0 θ A cA, (∀ κ ∈ prin A β Z, ∀ g, u (g * κ) = u g) → ∀ (sW : RealMat W) (Φ : WO A W → ℂ), Occ ψ θ sW omW m β Z u Φ → ∀ f, IsThetaFunO ψ A H f → f ≠ 0 → (∀ κ ∈ prin A β Z, omH (κ, 1) f = f) → (∀ b ∈ GinfC A, omH (b, 1) f = f) → (∀ ν 𝓕, IsCovolOne (ratL H A) ν 𝓕 → ∀ g ∈ openOff A (frameLat A) (under Z), g ∉ prinInf A β Z → wcoef omH ν 𝓕 f f g = 0) → ∀ νB 𝓕B, IsCovolOne (ratL B A) νB 𝓕B → ∃ C : ℂ, C ≠ 0 ∧ ∀ s : ℂ, ∫ g in openOff A (frameLat A) (under Z), integrand omB m νB 𝓕B (frameLat A) a (o.boxT A Φ f) (o.boxT A Φ f) u u s g ∂m = C := by
  intro D ψ θ A cA a hD B W H o χA χW omB omW omH hB hW hH β Z hZ m hm u hu hufix sW Φ hOcc f hf hf0 hfκ hfb hoff
    νB 𝓕B hνB
  obtain ⟨νW, 𝓕W, hνW⟩ := GlobalTheory.MixModel.exists_isCovolOne D W.rank A.rank
  obtain ⟨νH, 𝓕H, hνH⟩ := GlobalTheory.MixModel.exists_isCovolOne D H.rank A.rank
  have hΦ : IsThetaFunO ψ A W Φ := hOcc.fock.1
  obtain ⟨hPm, hPsub, hPh, mR, hmR, hint⟩ := _root_.GlobalTheory.Core.Rk.PrinMeas.prinInf_props D θ A cA a hD β Z hZ.frame m hm
  set F : GA D A → ℂ := fun g => wcoef omW νW 𝓕W Φ Φ g * wcoef omH νH 𝓕H f f g * rcoef m u u g with hFdef
  have hFc : Continuous F := ((continuous_wcoef hW hνW hΦ hΦ).mul (continuous_wcoef hH hνH hf hf)).mul
    (continuous_rcoef hD.sig hD.pos hm hu)
  have hbox := _root_.GlobalTheory.Core.Rk.BoxCoef.wcoef_boxT D ψ A B W H o χA χW omB omW omH hB hW hH νB 𝓕B νW 𝓕W νH 𝓕H hνB hνW hνH Φ f hΦ hf
  have hFκ : ∀ (b : GinfC A), ∀ κ ∈ prin A β Z, F ((b : GA D A) * κ) = F b := fun b κ hκ => by
    simp only [hFdef, wcoef_mul_fix omW νW 𝓕W Φ Φ _ κ (hOcc.fix κ hκ), wcoef_mul_fix omH νH 𝓕H f f _ κ (hfκ κ hκ),
      rcoef_mul_fix m u _ κ (hufix κ hκ)]
  set c : ℂ := GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.ip A H νH 𝓕H f f with hc
  have hc0 : c ≠ 0 := by
    have h := GlobalTheory.RawLift.VecNonzero.thetaInner_self_ne_zero hH.std hf hf0 hνH
    have e : c = GlobalTheory.RawLift.thetaIP νH 𝓕H f f := by
      simp only [hc, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.ip, GlobalTheory.RawLift.thetaIP, mul_comm (f _), Complex.star_def]
    rwa [e]
  have hFb : ∀ b : GinfC A, F b = c * (wcoef omW νW 𝓕W Φ Φ b * rcoef m u u b) := fun b => by
    have e : wcoef omH νH 𝓕H f f b = c := by simp only [wcoef, hfb b b.2, hc]
    simp only [hFdef, e]
    ring
  refine ⟨c * ∫ b : GinfC A, wcoef omW νW 𝓕W Φ Φ b * rcoef m u u b ∂mR, mul_ne_zero hc0 (hOcc.real νW 𝓕W hνW mR hmR),
    fun s => ?_⟩
  have hOm : MeasurableSet (openOff A (frameLat A) (under Z)) :=
    (isOpen_openOff A _ (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) _).measurableSet
  have h1 : ∫ g in openOff A (frameLat A) (under Z), integrand omB m νB 𝓕B (frameLat A) a (o.boxT A Φ f) (o.boxT A Φ f)
      u u s g ∂m = ∫ g in openOff A (frameLat A) (under Z), (prinInf A β Z).indicator F g ∂m := by
    refine setIntegral_congr_fun hOm fun g hg => ?_
    by_cases hgP : g ∈ prinInf A β Z
    · rw [Set.indicator_of_mem hgP]
      simp only [integrand, hbox g, hPh g hgP, one_npow, mul_one, hFdef]
    · rw [Set.indicator_of_notMem hgP]
      simp only [integrand, hbox g, hoff νH 𝓕H hνH g hg hgP, mul_zero, zero_mul]
  rw [h1, setIntegral_indicator hPm, Set.inter_eq_right.2 hPsub, hint F hFc hFκ]
  simp only [hFb]
  exact integral_const_mul c _

end GlobalTheory.Core.Rk.Exh.LocalConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockDoubleCosetOperatorKeepsLevelCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LowerBlockHecke

theorem sum_translate {G : Type} [Group G] (J : Subgroup G) (g₀ : G) (R : Finset G) (hRJ : ∀ y ∈ R, y ∈ J)
    (hR : ∀ j ∈ J, ∃! j', j' ∈ R ∧ (j' * g₀)⁻¹ * (j * g₀) ∈ J) (χ : G → ℂ)
    (hmul : ∀ a ∈ J, ∀ b ∈ J, χ (a * b) = χ a * χ b) (hne : ∀ a ∈ J, χ a ≠ 0)
    (hconj : ∀ m ∈ J, g₀⁻¹ * m * g₀ ∈ J → χ (g₀⁻¹ * m * g₀) = χ m)
    (Φ : G → ℂ) (hΦ : ∀ x, ∀ k ∈ J, Φ (x * k) = χ k * Φ x) {y₀ : G} (hy₀ : y₀ ∈ J) :
    ∑ y ∈ R, (χ y)⁻¹ * Φ (y₀ * y * g₀) = χ y₀ * ∑ y ∈ R, (χ y)⁻¹ * Φ (y * g₀) := by
  classical
  let s : G → G → G := fun a y => if h : a * y ∈ J then (hR _ h).exists.choose else y
  have hs : ∀ a ∈ J, ∀ y ∈ R, s a y ∈ R ∧ (s a y * g₀)⁻¹ * (a * y * g₀) ∈ J := by
    intro a ha y hy
    have h : a * y ∈ J := J.mul_mem ha (hRJ y hy)
    have e : s a y = (hR _ h).exists.choose := dif_pos h
    rw [e]
    exact (hR _ h).exists.choose_spec
  have huniq : ∀ a ∈ J, ∀ y ∈ R, ∀ z ∈ R, (z * g₀)⁻¹ * (a * y * g₀) ∈ J → s a y = z := by
    intro a ha y hy z hz hzJ
    exact (hR _ (J.mul_mem ha (hRJ y hy))).unique (hs a ha y hy) ⟨hz, hzJ⟩
  have hinv : ∀ y ∈ R, s y₀⁻¹ (s y₀ y) = y := by
    intro y hy
    obtain ⟨hm, hK⟩ := hs y₀ hy₀ y hy
    apply huniq _ (J.inv_mem hy₀) _ hm _ hy
    have e : (y * g₀)⁻¹ * (y₀⁻¹ * s y₀ y * g₀) = ((s y₀ y * g₀)⁻¹ * (y₀ * y * g₀))⁻¹ := by group
    rw [e]
    exact J.inv_mem hK
  have hinv' : ∀ y ∈ R, s y₀ (s y₀⁻¹ y) = y := by
    intro y hy
    obtain ⟨hm, hK⟩ := hs y₀⁻¹ (J.inv_mem hy₀) y hy
    apply huniq _ hy₀ _ hm _ hy
    have e : (y * g₀)⁻¹ * (y₀ * s y₀⁻¹ y * g₀) = ((s y₀⁻¹ y * g₀)⁻¹ * (y₀⁻¹ * y * g₀))⁻¹ := by group
    rw [e]
    exact J.inv_mem hK
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (s y₀) (s y₀⁻¹) (fun y hy => (hs y₀ hy₀ y hy).1)
    (fun y hy => (hs _ (J.inv_mem hy₀) y hy).1) hinv hinv' ?_
  intro y hy
  obtain ⟨hm, hK⟩ := hs y₀ hy₀ y hy
  set y' := s y₀ y
  set k := (y' * g₀)⁻¹ * (y₀ * y * g₀)
  have hyJ := hRJ y hy
  have hy'J := hRJ y' hm
  have hmJ : y'⁻¹ * (y₀ * y) ∈ J := J.mul_mem (J.inv_mem hy'J) (J.mul_mem hy₀ hyJ)
  have ek : k = g₀⁻¹ * (y'⁻¹ * (y₀ * y)) * g₀ := by simp only [k]; group
  have hχk : χ k = χ (y'⁻¹ * (y₀ * y)) := by rw [ek]; exact hconj _ hmJ (ek ▸ hK)
  have e1 : y₀ * y * g₀ = y' * g₀ * k := by simp only [k]; group
  have e2 : χ y₀ * χ y = χ y' * χ (y'⁻¹ * (y₀ * y)) := by
    rw [← hmul _ hy₀ _ hyJ, ← hmul _ hy'J _ hmJ, mul_inv_cancel_left]
  rw [e1, hΦ _ _ hK, hχk]
  have hy0 := hne y hyJ
  have hy'0 := hne y' hy'J
  have e3 : χ (y'⁻¹ * (y₀ * y)) = χ y₀ * χ y * (χ y')⁻¹ := by
    rw [e2, mul_comm (χ y'), mul_assoc, mul_inv_cancel₀ hy'0, mul_one]
  rw [e3]
  field_simp

end GlobalTheory.LowerBlockHecke

namespace GlobalTheory.LowerBlockHecke

open ValuativeRel GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.ZonalCellDecomposition

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

theorem det_lower_ne {j : GL (A ⊕ D) k} (hj : j ∈ parahoric k A D) : j.1.toBlocks₂₂.det ≠ 0 := by
  obtain ⟨h, hh, rfl⟩ := hj
  intro h0
  have e1 : (GeneralLinearGroup.map (n := A ⊕ D) (algebraMap 𝒪[k] k) h).1.toBlocks₂₂ =
      (algebraMap 𝒪[k] k).mapMatrix h.1.toBlocks₂₂ := rfl
  rw [e1, ← RingHom.map_det] at h0
  have h1 : h.1.toBlocks₂₂.det = 0 := Subtype.ext h0
  set u := GeneralLinearGroup.map (n := A ⊕ D) (IsLocalRing.residue 𝒪[k]) h with hu
  have h21 : u.1.toBlocks₂₁ = 0 := by
    ext i j
    exact hh (i := .inr i) (j := .inl j) (show false < true by decide)
  have h22 : u.1.toBlocks₂₂.det = 0 := by
    have : u.1.toBlocks₂₂ = (IsLocalRing.residue 𝒪[k]).mapMatrix h.1.toBlocks₂₂ := rfl
    rw [this, ← RingHom.map_det, h1, map_zero]
  have := u.det_ne_zero
  rw [← fromBlocks_toBlocks u.1, h21, det_fromBlocks_zero₂₁, h22, mul_zero] at this
  exact this rfl

theorem det_lower_conj_mtor (ϖ : kˣ) (e : D → ℤ) (m : GL (A ⊕ D) k) :
    ((mtor ϖ e)⁻¹ * m * mtor ϖ e : GL (A ⊕ D) k).1.toBlocks₂₂.det = m.1.toBlocks₂₂.det := by
  set c : A ⊕ D → kˣ := fun i => ϖ ^ (Sum.elim (0 : A → ℤ) e i) with hc
  have ht : mtor (A := A) ϖ e = diagT k (A ⊕ D) c := rfl
  have hti : (mtor (A := A) ϖ e)⁻¹ = diagT k (A ⊕ D) c⁻¹ := by rw [ht, map_inv]
  have hb : ((mtor ϖ e)⁻¹ * m * mtor ϖ e : GL (A ⊕ D) k).1.toBlocks₂₂ =
      diagonal (fun i => ((c (.inr i))⁻¹ : kˣ) : D → k) * m.1.toBlocks₂₂ * diagonal (fun i => (c (.inr i) : k)) := by
    rw [hti, ht, Units.val_mul, Units.val_mul, val_diagT, val_diagT]
    ext i j
    simp only [toBlocks₂₂, of_apply, diagonal_mul, mul_diagonal, Pi.inv_apply]
  rw [hb, det_mul, det_mul, det_diagonal, det_diagonal, mul_comm, ← mul_assoc, ← Finset.prod_mul_distrib]
  simp

end GlobalTheory.LowerBlockHecke

namespace GlobalTheory.LowerBlockHecke

open GlobalTheory.ZonalCellDecomposition


set_option maxHeartbeats 2000000 in
theorem hecke_level : ∀ D : D7, ForStageQ D fun c w j s => ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ (ξl : (Fv D.host.F v)ˣ →* ℂˣ), LiftsChar φ PP ξl (w.ξ PP) → ∀ ι, IsChart s j φ ι → ∀ (ϖ : (Fv D.host.F v)ˣ) (e : Blocks j D.R.t → ℤ) (R : Finset (GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v))) (d : GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v) → (Fv D.host.F v)ˣ), GlobalTheory.ParHecke.IsReps (GlobalTheory.ZonalCellDecomposition.mtor ϖ e) R d → ∀ F : GA D s.V → ℂ, (∀ κ ∈ Lev.levG s.V s.β s.L, ∀ g, F (g * κ) = Lev.levChi s.V s.β s.L κ * F g) → ∀ κ ∈ Lev.levG s.V s.β s.L, ∀ g, ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) * F (g * κ * ι (y * GlobalTheory.ZonalCellDecomposition.mtor ϖ e)) = Lev.levChi s.V s.β s.L κ * ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) * F (g * ι (y * GlobalTheory.ZonalCellDecomposition.mtor ϖ e)) := by
  intro D c w hw j hj s hs PP hPP v φ hφ ξl hξ ι hι ϖ e R d hR F hF κ hκ g
  obtain ⟨-, -, -, -, hch⟩ := _root_.GlobalTheory.ChartTwist.chart_dict D c w hw j hj s hs PP hPP v φ hφ
  obtain ⟨⟨eq, hemb, -⟩, hlev, hchi⟩ := hch ι hι
  have hchi' := hchi ξl hξ
  set J := parahoric (Fv D.host.F v) (Fin D.R.r) (Blocks j D.R.t) with hJ
  set g₀ : GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v) := mtor ϖ e with hg₀
  set χ : GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v) → ℂ := fun x => Lev.levChi s.V s.β s.L (ι x) with hχ

  set k0 := gAt s.V (.inl v) κ with hk0def
  have hk0 : k0 ∈ Lev.levG s.V s.β s.L := by
    obtain ⟨hr, hL, hfl⟩ := hs
    have hfr : Formalism.L2.DIV.IsFrame s.β s.Λ := hfl.frame
    have hP : s.L.P.H = ⊥ := by rw [hL]; rfl
    obtain ⟨-, hS, hl⟩ := (LevLoc.mem_lev_iff s.V.gram s.β s.L hP _).1 hκ.2
    have hkS := LevLoc.finE_gAt_mem_St hfr κ v ((_root_.GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D s.V s.β s.Λ hfr κ).1 hS v)
    refine ⟨GlobalTheory.ChainOnto.LevelFacts.emb_mem_GfC s.V v _, ?_⟩
    refine (LevLoc.mem_lev_iff s.V.gram s.β s.L hP _).2 ⟨GlobalTheory.LevSplit.finE_mem_UA s.V _, hkS, fun PP' => ?_⟩
    by_cases e' : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') = v
    · subst e'
      rw [← LevLoc.red_local hfr κ hS PP']
      exact hl PP'
    · rw [_root_.GlobalTheory.ChainOnto.RedOne.redFn_eq_one D s.V s.β _ PP' hkS (GlobalTheory.AdelicU.proj_emb_ne _ _ e' _)]
      exact LevLoc.locOK_one _ _
  set y₀ := eq.symm (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v κ) with hy₀def
  have hy0 : ι y₀ = k0 := by
    rw [hemb, hy₀def, eq.apply_symm_apply]
    rfl
  have hy0J : y₀ ∈ J := (hlev y₀).1 (hy0 ▸ hk0)
  set κ' := k0⁻¹ * κ with hκ'def
  have hκ' : κ' ∈ Lev.levG s.V s.β s.L := mul_mem (inv_mem hk0) hκ
  have hκeq : κ = k0 * κ' := by rw [hκ'def, mul_inv_cancel_left]
  have hpκ' : GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v κ' = 1 := by
    rw [hκ'def, map_mul, map_inv]
    show (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v
      (GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v κ)))⁻¹ *
        GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v κ = 1
    rw [GlobalTheory.AdelicU.proj_emb_self, inv_mul_cancel]
  have hcomm : ∀ x, ι x * κ' = κ' * ι x := fun x => by
    rw [hemb]
    exact (GlobalTheory.AdelicU.commute_emb D.sp.cm.sig s.V.gram (eq x) hpκ').eq

  have hmul : ∀ a ∈ J, ∀ b ∈ J, χ (a * b) = χ a * χ b := fun a ha b hb => by
    simp only [hχ, map_mul]
    exact GlobalTheory.ChainOnto.LevelFacts.levChi_mul ((hlev a).2 ha) ((hlev b).2 hb)
  have hne : ∀ a ∈ J, χ a ≠ 0 := fun a ha => by
    simp only [hχ]
    rw [hchi' a ha (Units.mk0 _ (det_lower_ne ha)) rfl]
    exact Units.ne_zero _
  have hconj : ∀ m ∈ J, g₀⁻¹ * m * g₀ ∈ J → χ (g₀⁻¹ * m * g₀) = χ m := fun m hm hm' => by
    simp only [hχ]
    rw [hchi' _ hm' (Units.mk0 _ (det_lower_ne hm')) rfl, hchi' m hm (Units.mk0 _ (det_lower_ne hm)) rfl]
    have : Units.mk0 _ (det_lower_ne hm') = Units.mk0 _ (det_lower_ne hm) :=
      Units.ext (det_lower_conj_mtor ϖ e m)
    rw [this]
  have hΦ : ∀ x, ∀ k ∈ J, F (g * ι (x * k)) = χ k * F (g * ι x) := fun x k hk => by
    rw [map_mul, ← mul_assoc]
    exact hF _ ((hlev k).2 hk) _
  have hxi : ∀ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) = (χ y)⁻¹ := fun y hy => by
    simp only [hχ]
    rw [hchi' y (hR.1 y hy).1 (d y) (hR.1 y hy).2]
    simp
  have hterm : ∀ y, F (g * κ * ι (y * g₀)) = Lev.levChi s.V s.β s.L κ' * F (g * ι (y₀ * y * g₀)) := fun y => by
    have e1 : g * κ * ι (y * g₀) = g * ι (y₀ * y * g₀) * κ' := by
      rw [hκeq, mul_assoc y₀ y g₀, map_mul ι y₀, hy0]
      simp only [mul_assoc]
      rw [hcomm]
    rw [e1, hF κ' hκ']
  have key := sum_translate J g₀ R (fun y hy => (hR.1 y hy).1) hR.2 χ hmul hne hconj (fun x => F (g * ι x)) hΦ hy0J
  calc ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) * F (g * κ * ι (y * g₀))
      = Lev.levChi s.V s.β s.L κ' * ∑ y ∈ R, (χ y)⁻¹ * F (g * ι (y₀ * y * g₀)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y hy => ?_
        rw [hxi y hy, hterm y]
        ring
    _ = Lev.levChi s.V s.β s.L κ' * (χ y₀ * ∑ y ∈ R, (χ y)⁻¹ * F (g * ι (y * g₀))) := by rw [key]
    _ = Lev.levChi s.V s.β s.L κ * ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) * F (g * ι (y * g₀)) := by
        have h1 : Lev.levChi s.V s.β s.L κ = χ y₀ * Lev.levChi s.V s.β s.L κ' := by
          rw [hκeq, GlobalTheory.ChainOnto.LevelFacts.levChi_mul hk0 hκ']
          simp only [hχ, hy0]
        have h2 : ∑ y ∈ R, ((ξl (d y) : ℂˣ) : ℂ) * F (g * ι (y * g₀)) = ∑ y ∈ R, (χ y)⁻¹ * F (g * ι (y * g₀)) :=
          Finset.sum_congr rfl fun y hy => by rw [hxi y hy]
        rw [h1, h2]
        ring

end GlobalTheory.LowerBlockHecke

end
end

