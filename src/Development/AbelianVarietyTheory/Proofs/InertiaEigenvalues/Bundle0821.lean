module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolynomialEqZeroOfFunction
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0803
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0800
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0807
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1649
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1641
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0014
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneCuspidalUnitaryCharEquivApplySymm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0687
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0693
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0815
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValSqNonsplit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0818
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0814

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsScaleOfChar
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries MvPolynomial Matrix
open Formalism.IndefR.Links
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Scale

variable {D : D7} {n : ℕ}

theorem coefFn_translate (lam : D.what₂.Tau → DomWeight n) (u : GLR D n) (F : Formalism.L2.DIV.Pol ℂ D.what₂.Tau n) (x : GLR D n) :
    coefFn (RingHom.id ℂ) lam (actP lam (invTrK u) F) x = coefFn (RingHom.id ℂ) lam F (u⁻¹ * x) := by
  have e1 : actP lam (invTrK u) F = detTwK lam (invTrK u) • trAct (invTrK u) F := rfl
  have e2 : (eval₂Hom (RingHom.id ℂ) (fun v : D.what₂.Tau × Fin n × Fin n => (x v.1).val v.2.1 v.2.2)).comp
        (trAct (invTrK u) : Formalism.L2.DIV.Pol ℂ D.what₂.Tau n →+* Formalism.L2.DIV.Pol ℂ D.what₂.Tau n) =
      eval₂Hom (RingHom.id ℂ) (fun v => ((u⁻¹ * x) v.1).val v.2.1 v.2.2) := by
    refine MvPolynomial.ringHom_ext (fun a => by simp [trAct, Formalism.GradedWeylDivisibility.blockAct]) fun v => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [RingHom.comp_apply, RingHom.coe_coe, trAct, Formalism.GradedWeylDivisibility.blockAct, aeval_X, map_sum, map_mul, eval₂Hom_C,
      eval₂Hom_X', Pi.mul_apply, Pi.inv_apply, Units.val_mul, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun b _ => rfl
  have e3 : (RingHom.id ℂ) (detTwK lam (invTrK u)) =
      ((detFam (fun τ => (lam τ).detShift) u⁻¹ : ℂˣ) : ℂ) := by
    simp only [detTwK, detPow, detFam, map_prod, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val,
      map_zpow₀, GeneralLinearGroup.val_det_apply]
    refine Finset.prod_congr rfl fun τ _ => ?_
    congr 1
    change (((u τ)⁻¹).valᵀ).det = _
    rw [det_transpose]
    rfl
  rw [coefFn, coefFn, e1, smul_eq_C_mul, map_mul, eval₂Hom_C, e3, ← e2, map_mul, Units.val_mul]
  simp only [RingHom.comp_apply, RingHom.coe_coe]
  ring

theorem coefFn_map {K : Type} [Field K] (σ : K →+* ℂ) (lam : D.what₂.Tau → DomWeight n) (F : Formalism.L2.DIV.Pol K D.what₂.Tau n) :
    coefFn (RingHom.id ℂ) lam (MvPolynomial.map σ F) = coefFn σ lam F := by
  funext x
  rw [coefFn, coefFn, eval₂Hom_map_hom, RingHom.id_comp]

def coefLin (lam : D.what₂.Tau → DomWeight n) : VV ℂ lam →ₗ[ℂ] (GLR D n → ℂ) where
  toFun F := coefFn (RingHom.id ℂ) lam (F : Formalism.L2.DIV.Pol ℂ D.what₂.Tau n)
  map_add' F F' := by
    funext x
    simp only [coefFn, Submodule.coe_add, map_add (f := _), Pi.add_apply, mul_add]
  map_smul' a F := by
    funext x
    simp only [coefFn, Submodule.coe_smul, smul_eq_C_mul, map_mul, eval₂Hom_C, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

theorem coefLin_injective (lam : D.what₂.Tau → DomWeight n) : Function.Injective (coefLin lam) :=
  (injective_iff_map_eq_zero _).2 fun F hF => Subtype.ext (GlobalTheory.T.coeffPolynomial_eq_zero_of_vanishing_on_GLFamily D n lam F (congrFun hF))

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {j : Fin D.R.m}
  {B : Base (Vc D j) (Wc D j)}

theorem io_act (hlev : R.toLevCh.Is A.μ0) (hth : R.IsThP) (hB : B.Good) (hψ : B.F.ψ = R.ψ) (hθ : B.F.θ = R.θ)
    (hsT : B.F.sT = cart (R.MW j (sg0 D A))) (hBS : ∀ τ, (B.F.BS τ).val = R.BV j τ) (hBT : B.F.BT = onb (R.MW j (sg0 D A)))
    (hmu : B.mu0 = R.mu0 ((j : ℕ) + 1)) (heta : B.eta = R.eta) (x : LowT (R.MW j (sg0 D A))) :
    ∀ u ∈ GinfC (Vc D j), ∀ w, R.ioP j x ((R.cV j).ρ u w) = B.act u (R.ioP j x w) := by
  have hinf : IsInfFam R.θ := hθ ▸ hB.frame.vac.2.inf
  have hf : IsThetaFunO R.ψ (Vc D j) (Wc D j) (R.vP j A.μ0) := by
    have := hth.pt_theta j A.μ0 1
    unfold RealDat.ptP pureTensorO at this
    rwa [GlobalTheory.AdTh.VecFock.pureTensorL_one] at this
  have hon : ∀ τ, IsONBasis (gramAt D (Vc D j) τ) 1 (R.BV j τ) (Vc D j).rank := fun τ => hBS τ ▸ hB.frame.onbS τ
  have hinj : Function.Injective (R.ptP j A.μ0) :=
    GlobalTheory.FockIndep.pureTensorO_injective D R.ψ R.θ _ _ _ (R.MW j (sg0 D A)) (R.BV j) (R.vP j A.μ0) (hth.ωP j A.μ0).std hinf
      (fun τ => GlobalTheory.GalLift.Vec.isCartanInv_one (hon τ)) hon hf
      (GlobalTheory.AdTh.VecNe.thPVec_ne_zero (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hlev.βV j))
        (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hlev.βW j)) hB.frame.rank_le (hth.vP j A.μ0))
      (GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ (fun _ => 1) _ _ _ _ _ _ _ _ _ _ (hth.vP j A.μ0) hf)
  have hexp : ∀ τ, HasInfExp D (R.toLevCh.mu A.μ0 ((j : ℕ) + 1)) τ
      ((B.w.c τ : ℚ) - ((B.w.p τ : ℚ) - B.w.q τ) / 2 + 1 / 2) := fun τ => by
    obtain ⟨k, hk, ho⟩ := hlev.xi_fin A.μ0
    have h1 := hB.inf τ
    rw [hmu] at h1
    have h2 := GlobalTheory.Chain.StepVac.hasInfExp_mul h1 (GlobalTheory.Chain.StepVac.hasInfExp_of_order hinf (hlev.xi A.μ0) hk ho τ)
    rwa [add_zero] at h2
  intro u hu w
  exact hinj (((hth.ioP j A.μ0).1 u hu x w).symm.trans
    (_root_.GlobalTheory.RealFockActionP.om_fock_vP D G Pl0 T0 A Ks R j A.μ0 B hth hB hψ hθ hsT hBS hBT heta hexp u hu _))

theorem exists_scale (hlev : R.toLevCh.Is A.μ0) (hth : R.IsThP) (hc : (R.cV j).Is) (hB : B.Good) (hψ : B.F.ψ = R.ψ)
    (hθ : B.F.θ = R.θ) (hsT : B.F.sT = cart (R.MW j (sg0 D A))) (hBS : ∀ τ, (B.F.BS τ).val = R.BV j τ)
    (hBT : B.F.BT = onb (R.MW j (sg0 D A))) (hmu : B.mu0 = R.mu0 ((j : ℕ) + 1)) (heta : B.eta = R.eta)
    (hap : ∀ τ, B.w.ap τ = aPl D j ((Wc D j).sig (tauE D τ)).1 τ)
    (ham : ∀ τ, B.w.am τ = aMi D j ((Wc D j).sig (tauE D τ)).1 ((Wc D j).sig (tauE D τ)).2 τ)
    (c0 : VV D.what₂.LL (FWT.lamV D j) →ₛₗ[D.what₂.embLL] (R.cV j).W)
    (ht : Bridge.CoefMapTie (Vc D j) (R.cV j).coef c0 (rhoVr (labLL D) (FWT.lamV D j)))
    (x : LowT (R.MW j (sg0 D A))) (w₀ : (R.cV j).W) (hw : R.ioP j x w₀ = RealDat.Delta j) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ F : VV D.what₂.LL (FWT.lamV D j), harmFn (Wc D j).rank B.w B.F.BS (R.ioP j x (c0 F)) =
      c • coefFn D.what₂.embLL (FWT.lamV D j) (F : Formalism.L2.DIV.Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) := by
  have hinf : IsInfFam R.θ := hθ ▸ hB.frame.vac.2.inf
  have hT := io_act hlev hth hB hψ hθ hsT hBS hBT hmu heta x
  have hlam : B.w.lam = FWT.lamV D j := _root_.GlobalTheory.BaseLiftWeight.lam_eq D T0 R.toLevCh A.μ0 j B hlev hB hmu hap ham
  have hpq : ∀ τ, B.w.p τ + B.w.q τ ≤ (Wc D j).rank := fun τ => by
    obtain ⟨e, -⟩ := hB.sigOK (tauE D τ)
    rw [← hB.sig τ] at e
    have := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  have hΔ : B.w.delta (Wc D j).rank = RealDat.Delta j := by
    unfold Weight.delta RealDat.Delta
    rw [show B.w.p = _ from funext fun τ => congrArg Prod.fst (hB.sig τ),
      show B.w.q = _ from funext fun τ => congrArg Prod.snd (hB.sig τ), show B.w.ap = _ from funext hap,
      show B.w.am = _ from funext ham]
  have hirr : ∀ U : Submodule ℂ (R.cV j).W, (∀ h : GinfC (Vc D j), U.map ((R.cV j).ρ h) ≤ U) → U = ⊥ ∨ U = ⊤ :=
    fun U hU => hc.2.2.2.2 U fun h => by
      obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D _).1 h
      rw [map_mul, hc.1 k hk, mul_one]
      exact hU ⟨a, ha⟩
  have hΔ0 := GlobalTheory.AdTh.IoExtPf.Delta_ne (D := D) j
  have hharm : ∀ w, R.ioP j x w ∈ harm (Wc D j).rank B.w B.F.BS := by
    rcases hirr ((harm (Wc D j).rank B.w B.F.BS).comap (R.ioP j x)) (fun h => by
      rintro _ ⟨w, hw', rfl⟩
      rw [Submodule.mem_comap, hT h h.2]
      exact fockGL_mem_harm _ _ _ hw') with h | h
    · have h0 : w₀ ∈ (harm (Wc D j).rank B.w B.F.BS).comap (R.ioP j x) := by
        rw [Submodule.mem_comap, hw, ← hΔ]
        exact delta_mem_harm _ _
      rw [h, Submodule.mem_bot] at h0
      rw [h0, map_zero] at hw
      exact absurd hw.symm hΔ0
    · exact fun w => (h ▸ Submodule.mem_top : w ∈ (harm (Wc D j).rank B.w B.F.BS).comap (R.ioP j x))
  obtain ⟨e, he0, he⟩ := GlobalTheory.CoefReal.exists_real_model (Vc D j) R.θ (R.cV j) (FWT.lamV D j) c0 hinf hc ht
  haveI := hc.2.2.2.1
  obtain ⟨c, hcc⟩ := _root_.GlobalTheory.schur_proportional (GinfC (Vc D j)) (R.cV j).W (GLR D (Vc D j).rank → ℂ) (fun h => (R.cV j).ρ h)
    (fun h => LinearMap.funLeft ℂ ℂ fun y => (realGL R.θ (Vc D j) h)⁻¹ * y)
    (harmFn (Wc D j).rank B.w B.F.BS ∘ₗ R.ioP j x) (coefLin (FWT.lamV D j) ∘ₗ e.symm.toLinearMap) hirr
    ((coefLin_injective _).comp e.symm.injective)
    (by
      rintro _ ⟨w, rfl⟩
      have h1 : harmFn (Wc D j).rank B.w B.F.BS (R.ioP j x w) ∈
          (harm (Wc D j).rank B.w B.F.BS).map (harmFn (Wc D j).rank B.w B.F.BS) := Submodule.mem_map_of_mem (hharm w)
      rw [GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions D _ _ B.w B.F.BS hB.wt hpq, hlam] at h1
      refine Submodule.span_le.2 ?_ h1
      rintro _ ⟨F, rfl⟩
      exact ⟨e F, congrArg (coefLin _) (e.symm_apply_apply F)⟩)
    (fun h w => funext fun y => by
      change harmFn _ B.w B.F.BS (R.ioP j x ((R.cV j).ρ h w)) y = harmFn _ B.w B.F.BS (R.ioP j x w) _
      rw [hT h h.2, ← hθ]
      exact harmFn_fockGL _ _ _ _ _)
    (fun h w => funext fun y => by
      obtain ⟨v, rfl⟩ := e.surjective w
      change coefLin _ (e.symm ((R.cV j).ρ h (e v))) y = coefLin _ (e.symm (e v)) _
      rw [he h h.2, e.symm_apply_apply, e.symm_apply_apply]
      exact coefFn_translate _ _ _ _)
  refine ⟨c, fun h0 => hΔ0 ?_, fun F => ?_⟩
  · have h1 := LinearMap.congr_fun hcc w₀
    rw [h0, zero_smul, LinearMap.comp_apply, hw] at h1
    exact _root_.GlobalTheory.ExportSeries.HarmInj.harm_inj D _ _ B.w B.F.BS hB.wt hpq _ (hw ▸ hharm w₀) h1
  · refine (LinearMap.congr_fun hcc (c0 F)).trans ?_
    change c • coefLin _ (e.symm (c0 F)) = _
    rw [show e.symm (c0 F) = _ from e.symm_apply_eq.2 (he0 F).symm, ← coefFn_map]
    rfl

end Scale

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem exists_isScale (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {ρ : Setup D.ntw} (hρ : ρ.Good) (hpin : RealPin Rl cG ρ)
    (hlev : Rl.toLevCh.Is A3.A.μ0) (hfam : Rl.toRealDat.fam_tie) (hcV : Rl.toRealDat.models_cV) (hth : Rl.toRealDat.IsThP)
    (hio : FWT.IoExt Rl.toRealDat) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (hv : FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _)) : ∃ c : ℂ, c ≠ 0 ∧ IsScale Rl v₀ (ρ.B i j b) c := by
  obtain ⟨gramR, c0R, c0L, hft⟩ := hfam
  obtain ⟨u, w₀, hu, -, hw⟩ := FWT.IsChosenExtremalVector.io _ hv hio
  obtain ⟨c, hc0, hc⟩ := Scale.exists_scale hlev hth (hcV j) (hρ.base i j b) (hpin.psi i j b) (hpin.inf i j b)
    (hpin.cartT i j b) (hpin.onbS i j b) (hpin.onbT i j b) (hpin.mu0 i j b) (hpin.eta i j b) (hpin.ap i j b) (hpin.am i j b)
    (c0L j) (hft.mapL j) _ w₀ hw
  exact ⟨c, hc0, gramR, c0R, c0L, hft, u, hu, hc⟩

end GlobalTheory.SeriesTie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsToricCharactersInTwistCoefficientRings
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LamInstall
open ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2.NT Neutral.B1 GlobalTheory.HeckeGal GlobalTheory.GalChar GlobalTheory.LamTie GlobalTheory.LamTie.TrueList

attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

theorem exists_reading {D : D7} {N : NData D.R D.host D.what₂} (T : TwR D.LL0 N) (i : T.Tw) :
    ∃ (κ : FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : Qbar (T.l i) ≃+* ℂ),
      (∀ z : ℤ_[T.l i], κ (algebraMap (T.O0 i) _ (algebraMap ℤ_[T.l i] (T.O0 i) z)) =
        algebraMap ℚ_[T.l i] (Qbar (T.l i)) (z : ℚ_[T.l i])) ∧
      ∀ x : D.LL0, ι (κ (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL) := by
  haveI : CharZero (FractionRing (T.O0 i)) := (T.emb0 i).charZero_iff (T.emb0 i).injective |>.1 inferInstance
  let f : ℤ_[T.l i] →+* FractionRing (T.O0 i) :=
    (algebraMap (T.O0 i) (FractionRing (T.O0 i))).comp (algebraMap ℤ_[T.l i] (T.O0 i))
  have hf : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    by_contra h0
    rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hz
    rcases mul_eq_zero.1 hz with h | h
    · exact ((PadicInt.unitCoeff h0).isUnit.map f).ne_zero h
    · exact (pow_ne_zero _ (Nat.cast_ne_zero.2 (T.lPrime i).out.ne_zero)) h
  have hf0 : Function.Injective (algebraMap ℤ_[T.l i] (T.O0 i)) :=
    Function.Injective.of_comp (f := algebraMap (T.O0 i) (FractionRing (T.O0 i))) hf
  haveI : Module.IsTorsionFree ℤ_[T.l i] (T.O0 i) := Module.isTorsionFree_iff_algebraMap_injective.2 hf0
  haveI : Module.IsTorsionFree ℤ_[T.l i] (Qbar (T.l i)) := Module.isTorsionFree_iff_algebraMap_injective.2
    (by rw [IsScalarTower.algebraMap_eq ℤ_[T.l i] ℚ_[T.l i] (Qbar (T.l i))]
        exact (algebraMap ℚ_[T.l i] (Qbar (T.l i))).injective.comp Subtype.val_injective)
  let g : T.O0 i →ₐ[ℤ_[T.l i]] Qbar (T.l i) := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hg : Function.Injective g := by
    refine (RingHom.injective_iff_ker_eq_bot g.toRingHom).2 (Ideal.eq_bot_of_comap_eq_bot (R := ℤ_[T.l i]) ?_)
    rw [eq_bot_iff]
    intro z hz
    have h1 : algebraMap ℤ_[T.l i] (Qbar (T.l i)) z = 0 := (g.commutes z).symm.trans hz
    exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).1 h1
  haveI : Countable ↥D.LL0 := (Module.finBasis ℚ ↥D.LL0).equivFun.injective.countable
  let κ : FractionRing (T.O0 i) →+* Qbar (T.l i) := IsFractionRing.lift (g := g.toRingHom) hg
  obtain ⟨ι, hι⟩ := GlobalTheory.exists_padicAlgCl_ringEquiv_complex_comp_eq_of_countable (T.l i) ↥D.LL0
    (κ.comp (T.emb0 i)) (embLL0 D)
  exact ⟨κ, ι, fun z => (IsFractionRing.lift_algebraMap hg _).trans (g.commutes z), hι⟩

theorem delta_isGal (hC : GlobalTheory.Published.ChebotarevDegreeOne) {D : D7} {cf : CharFrame D} {b0 b1 : Big D} {Sx : Finset (PlE D.host)}
    {T : TwR D.LL0 D.nd} (Sp : RingSpec D cf b0 b1 Sx T) {art : Ideles D.host.E →* Gab D.host.E D.nd.Om}
    (ha : IsGlobalArtin art) (i : T.Tw) (κ : FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : Qbar (T.l i) ≃+* ℂ)
    (hι : ∀ x : D.LL0, ι (κ (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL)) :
    IsGal art κ ι (cf.delAt (T.l i)) 0 (T.delta i) := _root_.GlobalTheory.DeltaGal.delta_isGal hC Sp ha i κ ι hι

theorem read_of_isGal {D : D7} {N : NData D.R D.host D.what₂} {T : TwR D.LL0 N} {art : Ideles D.host.E →* Gab D.host.E N.Om}
    (ha : IsGlobalArtin art) {i : T.Tw} (κ : FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : Qbar (T.l i) ≃+* ℂ)
    (hι : ∀ x : D.LL0, ι (κ (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL))
    (b : Bool) (embO : ↥D.LL0 →+* FractionRing (T.O i))
    (hO : ∀ (x : ↥D.LL0) (y : T.O0 i), algebraMap (T.O0 i) (FractionRing (T.O0 i)) y = (if b then T.emb0 i else T.emb0b i) x →
      embO x = algebraMap (T.O i) (FractionRing (T.O i)) (algebraMap (T.O0 i) (T.O i) y))
    (χ : HChar D.host.E) (hu : χ.IsUnitary) (S : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (hv : ∀ P ∉ S, χ.UnrAt P ∧ ∃ y : ↥D.LL0, embLL0 D y = ((χ.val P : ℂˣ) : ℂ))
    (H : NC.HC D.host.E) (hH : ∀ x, H.χ x = χ.1 x) {n : (D.host.E →+* ℂ) → ℤ} {r : G D.host.E N.Om →* (T.O0 i)ˣ}
    (hr : IsGal art κ (sideIso ι b) χ n r) :
    NC.Read N.plOm.1 ((Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom).comp r) (algebraMap (T.O i) (FractionRing (T.O i)))
      embO (NC.complexEmbeddingRestrictedToSubfield D) H 0 := _root_.GlobalTheory.HeckeRead.read_of_isGal_side ha κ ι hι b embO hO χ hu S hv H hH hr


set_option maxHeartbeats 4000000 in
theorem exists_twL_installed : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.ToricRational.RatioConj → ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T) (Z : GlobalTheory.LamTie.LamDat D), Z.C = cf → Z.Ok → (∀ a, GlobalTheory.LamTie.TeichTriv D.host (Z.chi a)) → ValLL0 D cf → (∀ a, (Z.chi a).ValuesIn 0 (embLL0 D)) → (∀ i P, (GlobalTheory.ToricDenom.below P).asIdeal ∣ GlobalTheory.LamTie.cond0 D.host Z.w0 → P ∈ T.S0 i) → ∃ L : TwL T, ∀ F : TwF T, GlobalTheory.LamTie.IsLamTieFull (T.ntw hE F L) Z ∧ ∀ (ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T))) (h0 : _) th, Nonempty (SideB (⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).toD7 ((⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).cf cf) ((⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).row Rw) low Pq ((⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).rat S) hL eig θ) → ∀ th', Nonempty (SideB (⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩ : TwNew D).toD7 ((⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩ : TwNew D).cf cf) ((⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩ : TwNew D).row Rw) low Pq ((⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩ : TwNew D).rat S) hL eig θ) := by
  intro hC hA hR D hE cf Rw low Pq S hL eig θ b0 b1 Sx T Sp Z hZC hZ hT hV hχv hS
  subst hZC
  obtain ⟨art, ha⟩ := hA D.host.E D.nd.Om
  choose κ ι hκ hι using fun i => exists_reading T i
  have hμ : ∀ i j, (Z.C.mu0 j).ValuesIn 0 ((ι i).toRingHom.comp (κ i)) := fun i j v hv' => by
    obtain ⟨y, hy⟩ := hV.mu0 j v hv'
    exact ⟨T.emb0 i y, by rw [← hy]; exact hι i y⟩
  have hχ : ∀ i a, (Z.chi a).ValuesIn 0 ((ι i).toRingHom.comp (κ i)) := fun i a v hv' => by
    obtain ⟨y, hy⟩ := hχv a v hv'
    exact ⟨T.emb0 i y, by rw [← hy]; exact hι i y⟩
  have hδ := fun i => delta_isGal hC Sp ha i (κ i) (ι i) (hι i)
  obtain ⟨L, e, hcl, hfull⟩ := exists_twL_full_teich hA hR D D.nd hE T Z hZ art ha κ ι hκ hι hμ hχ hδ hS hT
  refine ⟨L, fun F => ⟨hfull F, fun ex h0 th hB th' => ?_⟩⟩
  obtain ⟨B⟩ := hB
  refine sideB_keep B (fun s lam => FitTw.toHC (Z.chi (e s lam).2.1)) ?_ ?_
  · intro i lam P _
    obtain ⟨-, -, h2, -, h4⟩ := hcl i lam
    rw [h4 P, h2]
    let f : FractionRing (T.O i) →+* ℂ := B.twF.iCq i
    show f (((Ideal.absNorm P.asIdeal : ℕ) : FractionRing (T.O i)) ^ (-((e i lam).2.2.1.1 : ℤ))) = _
    rw [map_zpow₀, map_natCast]
    have e2 : (-(((2 * ((e i lam).2.2.1.1 : ℤ) : ℤ) : ℝ)) / 2) = ((-((e i lam).2.2.1.1 : ℤ) : ℤ) : ℝ) := by
      push_cast; ring
    rw [e2, Real.rpow_intCast, Complex.ofReal_zpow, Complex.ofReal_natCast]
  · intro s lam
    obtain ⟨h1, h2, -, ⟨n, r, hr, hG⟩, -⟩ := hcl s lam
    let C : GlobalTheory.Mem.Chr.HFrame D.host (fun j => eExp D j) :=
      ⟨Z.C.P, Z.C.W, Z.C.mu0, Z.C.eta, Z.C.chiPsi, Z.C.del, Z.C.del', Z.C.isMu0, Z.C.isEta, Z.C.isChi, Z.C.isDel, Z.C.isDel'⟩
    have hpD : ∀ v, v ∈ T.pD s ↔ OverP D.host (if T.l s = D.host.pde then D.host.pde' else D.host.pde) v := fun v => by
      rw [← Finset.mem_coe, T.pD_eq]; rfl
    have hmu : ∀ P, P ∉ T.S0 s → (Z.C.mu0 (e s lam).1).UnrAt P := fun P hP =>
      (Z.C.isMu0 _).unr P fun k hk => hP (T.placesOver_subset_exceptional s k hk)
    have hde : ∀ P, P ∉ T.S0 s → (Z.C.delAt (T.l s)).UnrAt P := fun P hP =>
      (inertialOrderFifteenChar_auxiliaryPrime_spec C (l := T.l s)).2.2.2.2.unr P fun hk => hP (T.primes_subset_exceptional s ((hpD P).2 hk))
    have hcu : ∀ P, P ∉ T.S0 s → (Z.chi (e s lam).2.1).UnrAt P := fun P hP =>
      chi_unr hZ _ fun h => hP (hS s P h)
    have hdel : (Z.C.delAt (T.l s)).ValuesIn 0 (embLL0 D) := by
      unfold CharFrame.delAt
      split_ifs
      exacts [hV.del', hV.del]
    rw [hG, h2]
    refine read_of_isGal ha (κ s) (ι s) (hι s) _ _ (fun x y h => B.chi.ringSpec_sidedEmbedding_fixedField s _ x y h)
      (Z.lam0 (T.l s) (e s lam).1 (e s lam).2.1) ?_ (T.S0 s) ?_ _ ?_ hr
    · intro x
      have e1 := (Z.C.isMu0 (e s lam).1).unitary x
      have e2 := Z.C.delAt_unitary (T.l s) x
      have e3 := (hZ.aux (e s lam).2.1).unitary x
      show ‖(((Z.C.mu0 (e s lam).1).1 x * (Z.C.delAt (T.l s)).1 x * ((Z.chi (e s lam).2.1).1 x)⁻¹ : ℂˣ) : ℂ)‖ = 1
      rw [Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_mul, norm_inv, e1, e2, e3]
      norm_num
    · intro P hP
      refine ⟨((hmu P hP).mul (hde P hP)).mul (hcu P hP).inv, ?_⟩
      obtain ⟨y1, hy1⟩ := hV.mu0 (e s lam).1 P (hmu P hP)
      obtain ⟨y2, hy2⟩ := hdel P (hde P hP)
      obtain ⟨y3, hy3⟩ := hχv (e s lam).2.1 P (hcu P hP)
      simp only [HChar.valTw, Complex.ofReal_zero, neg_zero, Complex.cpow_zero, mul_one] at hy1 hy2 hy3
      refine ⟨y1 * y2 * y3⁻¹, ?_⟩
      rw [map_mul, map_mul, map_inv₀, hy1, hy2, hy3, LamDat.lam0, HChar.val_mul, HChar.val_mul, HChar.val_inv,
        Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val]
    · intro x
      rw [h1]
      have e1 : (B.chiD.mu0 ((e s lam).1.1 + 1)).χ x = (Z.C.mu0 (e s lam).1).1 x := B.ringSpec_normalisedCharacter_eq _ x
      have e2 : (B.chiD.del s).χ x = (Z.C.delAt (T.l s)).1 x := B.del_eq s x
      show (B.chiD.mu0 ((e s lam).1.1 + 1)).χ x * (B.chiD.del s).χ x * ((Z.chi (e s lam).2.1).1 x)⁻¹ = _
      rw [e1, e2]
      rfl

end GlobalTheory.LamInstall
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsZmodEq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TameGenRep

open Formalism.L2.NT

theorem exists_zmod_eq {g : ℕ} [Fact g.Prime] (z : Formalism.CyclotomicNorms.Fbar g) (hz : z ^ g = z) :
    ∃ c : ZMod g, algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c = z := by
  first
  | exact @_root_.GlobalTheory.RangeOfPowerFixed.main
  | exact _root_.GlobalTheory.RangeOfPowerFixed.main
  | (apply _root_.GlobalTheory.RangeOfPowerFixed.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.RangeOfPowerFixed.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RangeOfPowerFixed.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RangeOfPowerFixed.main ..)

theorem exists_rep : ∀ (D : D7), GrpSide D → ∀ (k : Fin 2) (v : D.nd.PlG k), normV (D.naut.plGw k v) = D.host.g k ∧ ∃ (u ϖ : 𝓞 D.host.E) (π : D.nd.Om), u ∉ (D.naut.plGw k v).asIdeal ∧ ϖ ∈ (D.naut.plGw k v).asIdeal ∧ ϖ ∉ (D.naut.plGw k v).asIdeal ^ 2 ∧ π ^ (normV (D.naut.plGw k v) - 1) = algebraMap D.host.E D.nd.Om (ϖ : D.host.E) ∧ (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - algebraMap D.host.E D.nd.Om (u : D.host.E)) < 1 ∧ orderOf (D.ntypes.tg k v π / π) = normV (D.naut.plGw k v) - 1 := by
  intro D hG k v
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  haveI : CharZero D.nd.Om := charZero_of_injective_ringHom (f := algebraMap D.host.E D.nd.Om) (algebraMap D.host.E D.nd.Om).injective
  have hgp : (D.host.g k).Prime := D.host.g_prime k
  have hAP : IsPlaceOver (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) :=
    D.nd.plOm.2 (D.naut.plGw k v)
  have hgP : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw k v).asIdeal := D.naut.plGw_over k v
  have hspl := GlobalTheory.Mem.Chr.splitsC_main D.R D.host (D.host.g k) hgp (D.nd.g_split k) (D.naut.plGw k v) hgP
  have hN : normV (D.naut.plGw k v) = D.host.g k := by
    rw [← hspl.1, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  have hg1 : 0 < D.host.g k - 1 := by have := hgp.two_le; omega
  have hgΩ : ((D.host.g k : ℕ) : D.nd.Om) ≠ 0 := Nat.cast_ne_zero.mpr hgp.ne_zero
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq ((D.host.g k : ℕ) : D.nd.Om) hg1
  have hT : redThrough (D.nd.plOm.1 (D.naut.plGw k v)) (hG.kv k v) (D.ntypes.tg k v π / π) = hG.ζ k 1 :=
    hG.tg_tame k v 1 one_pos π (by rw [pow_one]; exact hπ)
  have hq : D.ntypes.tg k v π / π ∈ D.nd.plOm.1 (D.naut.plGw k v) :=
    tameQuot_mem (D.nd.plOm.1 (D.naut.plGw k v)) (D.ntypes.tg k v) hg1 hgΩ hπ
  have hpow : (D.ntypes.tg k v π / π) ^ (D.host.g k - 1) = 1 := tameQuot_pow (D.ntypes.tg k v) hgΩ hπ
  have hζ := (hG.ζ_gen k 1 one_pos).1
  rw [pow_one] at hζ
  have hζ1 : hG.ζ k 1 ^ (D.host.g k - 1) = 1 := by rw [← hζ]; exact pow_orderOf_eq_one _
  have hζpow : hG.ζ k 1 ^ D.host.g k = hG.ζ k 1 := by
    calc _ = hG.ζ k 1 ^ (D.host.g k - 1) * hG.ζ k 1 := by rw [← pow_succ, Nat.sub_add_cancel hgp.one_le]
      _ = _ := by rw [hζ1, one_mul]
  have hζ0 : hG.ζ k 1 ≠ 0 := by
    intro h
    rw [h, zero_pow hg1.ne'] at hζ1
    exact zero_ne_one hζ1
  obtain ⟨c, hc⟩ := exists_zmod_eq _ hζpow
  have hca : ((c.val : ℕ) : Formalism.CyclotomicNorms.Fbar (D.host.g k)) = hG.ζ k 1 := by
    rw [← hc, ← map_natCast (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))), ZMod.natCast_zmod_val]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = c.val := ⟨_, rfl⟩
  rw [← hn] at hca
  have hcast : algebraMap D.host.E D.nd.Om ((n : 𝓞 D.host.E) : D.host.E) = (n : D.nd.Om) := by
    simp
  have haA : (n : D.nd.Om) ∈ D.nd.plOm.1 (D.naut.plGw k v) := natCast_mem _ _
  have hra : redThrough (D.nd.plOm.1 (D.naut.plGw k v)) (hG.kv k v) (n : D.nd.Om) =
      hG.kv k v (IsLocalRing.residue _ ⟨_, haA⟩) := by
    unfold redThrough; rw [dite_eq_left haA]
  have hra' : hG.kv k v (IsLocalRing.residue _ ⟨_, haA⟩) = hG.ζ k 1 := by
    have : (⟨(n : D.nd.Om), haA⟩ : D.nd.plOm.1 (D.naut.plGw k v)) = (n : D.nd.plOm.1 (D.naut.plGw k v)) :=
      Subtype.ext (by simp)
    rw [this, map_natCast, map_natCast, hca]
  have hrq : redThrough (D.nd.plOm.1 (D.naut.plGw k v)) (hG.kv k v) (D.ntypes.tg k v π / π) =
      hG.kv k v (IsLocalRing.residue _ ⟨_, hq⟩) := by
    unfold redThrough; rw [dite_eq_left hq]
  have hval : (D.nd.plOm.1 (D.naut.plGw k v)).valuation (D.ntypes.tg k v π / π - (n : D.nd.Om)) < 1 := by
    have h1 := (hG.kv k v).injective (((hrq.symm.trans hT).trans hra'.symm))
    have h2 := Ideal.Quotient.eq.1 h1
    have h3 := ((D.nd.plOm.1 (D.naut.plGw k v)).valuation_lt_one_iff _).1 h2
    exact h3
  have hu : (n : 𝓞 D.host.E) ∉ (D.naut.plGw k v).asIdeal := by
    intro h
    have h1 := (hAP _).2 h
    have h2 : (n : D.nd.Om) ∈ D.nd.plOm.1 (D.naut.plGw k v) := haA
    have h3 : (⟨_, haA⟩ : D.nd.plOm.1 (D.naut.plGw k v)) ∈ IsLocalRing.maximalIdeal _ :=
      ((D.nd.plOm.1 (D.naut.plGw k v)).valuation_lt_one_iff _).2 (by rw [hcast] at h1; exact h1)
    rw [← IsLocalRing.residue_eq_zero_iff] at h3
    rw [h3, map_zero] at hra'
    exact hζ0 hra'.symm
  have hord : orderOf (D.ntypes.tg k v π / π) = D.host.g k - 1 := by
    apply Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hpow)
    rw [← hζ]
    apply orderOf_dvd_of_pow_eq_one
    have h1 : (⟨_, hq⟩ : D.nd.plOm.1 (D.naut.plGw k v)) ^ orderOf (D.ntypes.tg k v π / π) = 1 :=
      Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [← hT, hrq, ← map_pow, ← map_pow, h1, map_one, map_one]
  refine ⟨hN, (n : 𝓞 D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E), π, hu, hgP, hspl.2.1, ?_, ?_, ?_⟩
  · rw [hN]; simpa using hπ
  · rw [hcast]; exact hval
  · rw [hN]; exact hord

end GlobalTheory.TameGenRep

end
end

