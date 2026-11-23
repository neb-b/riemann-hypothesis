module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1695
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientConjugateThetaForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0121
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1667
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1697
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1700
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SingleThetaSeriesKEquivariantLowestType
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open Classical

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.SeriesKEquiv

theorem singleSeries_kEquiv : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → ∀ (Q' : Finset (Pl D.host.E)) (Ω : DatFn D i) (φ' : WO (Vc D i) (Wc D i) → ℂ), VecOf R i Q' Ω φ' → ∀ (h : GA D (Vc D i)) (y : (R.cV i).W) (g0 : G) (τ : D.what₂.Tau) (k : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), k ∈ Formalism.REAL.Kset ((R.MW i (sg0 D A)).ε τ) → ∀ (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (u : lowT (R.MW i (sg0 D A)) τ), ((u : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ) = (R.MW i (sg0 D A)).σ τ k ((v τ : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ) → Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g0) (singleSeries R i ω φ' h y (Function.update v τ u)) = Formalism.L2.Theta.rTr (Wc D i) (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ)) (Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g0) (singleSeries R i ω φ' h y v)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i ξ χ ξR Q ω φ hK Q' Ω φ' hφ' h y g0 τ k hk v u hu
  have hθ : IsInfFam R.θ := hR.models.inf
  have hω := hR.thP.ωP

  have hthφ : IsThetaFunO R.ψ (Vc D i) (Wc D i) φ' := by
    obtain ⟨⟨hψ, h0⟩, e, -, hth⟩ := hφ'
    exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ hth h0.theta
  have hvφ : ∀ ρ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ ρ
      (cplxO 1 (cart (R.MW i (sg0 D A)) ρ)) φ' := by
    intro ρ
    obtain ⟨⟨hψ, hv⟩, e, he, hth⟩ := hφ'
    have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
    exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hv.inf ho.conj.infPart_eq ho.conj.conj.infPart_eq hth hv.theta
      hthφ (hv.fock ρ)

  have hthv : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i A.μ0) := by
    obtain ⟨⟨hψ, h0⟩, e, -, hth⟩ := hR.thP.vP i A.μ0
    exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ hth h0.theta
  have hvv := GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hR.thP.vP i A.μ0) hthv
  have hBS : ∀ ρ, (R.BV i ρ)ᴴ * gramAt D (Vc D i) ρ * R.BV i ρ = 1 := fun ρ =>
    GlobalTheory.JointHarm.onb_eq_one (hR.models.BV i ρ)
  have hBu : ∀ ρ, IsUnit (R.BV i ρ) := fun ρ => IsUnit.of_mul_eq_one_right _ (hBS ρ)
  obtain ⟨x₁, x₂, x₃, hx⟩ := GlobalTheory.T.lowestKType_coefficientWeight_eq_minorWeights D i (sg0 D A) (sgAt_mk _ R.hv0) (R.MW i (sg0 D A)) (hR.models.order i)
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hpq : ∀ ρ, ((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2 = (Wc D i).rank := fun ρ =>
    (_root_.GlobalTheory.PairWeightArith.arithAt D i ρ).rank.1.trans hrk.symm
  have hfr : ∀ ρ, (R.MW i (sg0 D A)).fr ρ * ((R.MW i (sg0 D A)).fr ρ)⁻¹ = 1 := fun ρ =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 ((R.MW i (sg0 D A)).fr_unit ρ))

  have hIT := _root_.GlobalTheory.PairInfTypes.infTypesAt D T0 R.toLevCh A.μ0 hR.lev i A.μ0
  obtain ⟨n, hn, ho⟩ := hK.fin
  have hχ0 : ∀ ρ, HasInfExp D χ ρ 0 := fun ρ => GlobalTheory.Chain.StepVac.hasInfExp_of_order hθ hK.chr hn ho ρ
  have h1 : ∀ ρ, HasInfExp D (R.mu0 ((i : ℕ) + 1)) ρ (-GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.eS D i ρ) := fun ρ => by
    have h := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hR.lev.mu0 i)
      (GlobalTheory.PairInfTypes.hasInfQ_tauE D (R.toLevCh.C.isMu0 i).inf) ρ
    simpa only [Formalism.L2.Host.eExp, Equiv.symm_apply_apply] using h
  have hcV : ∀ ρ, HasInfExp D (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).1 ρ (-GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.eS D i ρ) :=
    fun ρ => by
      have := GlobalTheory.Mem.HeckeExp.hasInfExp_mul (h1 ρ) (hχ0 ρ)
      rw [add_zero] at this
      exact this
  have hcW : ∀ ρ, HasInfExp D (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 ρ
      (-GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes.eS D i ρ - 1 / 2) := fun ρ => by
    rw [sub_eq_add_neg]
    exact GlobalTheory.Mem.HeckeExp.hasInfExp_mul (hcV ρ) (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (hIT ρ).eta)

  have hs := GlobalTheory.PointAtPlaceHom.atTau_spec hθ (Wc D i) τ (GlobalTheory.JointHarm.conj_mem_UH (R.MW i (sg0 D A)) τ hk)
  have e : (fun ρ => (R.MW i (sg0 D A)).fr ρ * compAt R.θ ρ (Formalism.L2.Theta.mt (Wc D i)
      (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ))) *
        ((R.MW i (sg0 D A)).fr ρ)⁻¹) = Pi.mulSingle τ k := by
    funext ρ
    rw [GlobalTheory.WeilDeriv.compAt_mt_eq_infMat]
    by_cases hρ : ρ = τ
    · subst hρ
      rw [hs.2.1, Pi.mulSingle_eq_same]
      calc _ = ((R.MW i (sg0 D A)).fr ρ * ((R.MW i (sg0 D A)).fr ρ)⁻¹) * k *
            ((R.MW i (sg0 D A)).fr ρ * ((R.MW i (sg0 D A)).fr ρ)⁻¹) := by simp only [Matrix.mul_assoc]
        _ = k := by rw [hfr, Matrix.one_mul, Matrix.mul_one]
    · rw [hs.2.2 ρ hρ, Pi.mulSingle_eq_of_ne hρ, Matrix.mul_one, hfr]
  have e' : (fun ρ => (R.BV i ρ)⁻¹ * compAt R.θ ρ (Formalism.L2.Theta.mt (Vc D i) 1) * R.BV i ρ) = 1 := by
    funext ρ
    rw [GlobalTheory.JointHarm.compAt_mt_one', Matrix.mul_one,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (hBu ρ))]
    rfl
  have hKk : ∀ ρ, (R.MW i (sg0 D A)).fr ρ * compAt R.θ ρ (Formalism.L2.Theta.mt (Wc D i)
      (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ))) *
        ((R.MW i (sg0 D A)).fr ρ)⁻¹ ∈ Formalism.REAL.Kset ((R.MW i (sg0 D A)).ε ρ) := fun ρ => by
    rw [congrFun e ρ]
    by_cases hρ : ρ = τ
    · subst hρ; rwa [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hρ]; exact GlobalTheory.JointHarm.one_mem_K

  have aω := (_root_.GlobalTheory.FockCompactAction.om_pureTensorO_eq_fact D R.ψ R.θ (Vc D i) (Wc D i) _ _ ω _ (R.MW i (sg0 D A)) (R.BV i) hK.weil hθ
    (D.sp.V_sig _) (D.sp.W_sig _) hBS _ _ hpq (hR.models.order i) _ _ hcV hcW x₁ x₂ x₃
    (fun ρ => (hx ρ).1) (fun ρ => (hx ρ).2.1) (fun ρ => (hx ρ).2.2.1) φ' hthφ hvφ 1 (one_mem _) _ hs.1 hKk).2
  have av := (_root_.GlobalTheory.FockCompactAction.om_pureTensorO_eq_fact D R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i A.μ0) _ (R.MW i (sg0 D A)) (R.BV i) (hω i A.μ0) hθ
    (D.sp.V_sig _) (D.sp.W_sig _) hBS _ _ hpq (hR.models.order i) _ _ (fun ρ => (hIT ρ).chiV) (fun ρ => (hIT ρ).chiW)
    x₁ x₂ x₃ (fun ρ => (hx ρ).1) (fun ρ => (hx ρ).2.1) (fun ρ => (hx ρ).2.2.1) _ hthv hvv 1 (one_mem _) _ hs.1 hKk).2
  rw [e, e'] at aω av

  have hcVI : ∀ ρ, IsCartanInv (gramAt D (Vc D i) ρ)
      ((fun _ => (1 : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ)) ρ) := fun ρ => by
    have hu' := (Matrix.isUnit_iff_isUnit_det _).1 (hBu ρ)
    have h1' := Matrix.mul_nonsing_inv _ hu'
    have hG : gramAt D (Vc D i) ρ = ((R.BV i ρ)⁻¹)ᴴ * (R.BV i ρ)⁻¹ := by
      calc gramAt D (Vc D i) ρ
          = ((R.BV i ρ)⁻¹)ᴴ * ((R.BV i ρ)ᴴ * gramAt D (Vc D i) ρ * R.BV i ρ) * (R.BV i ρ)⁻¹ := by
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h1', Matrix.conjTranspose_one,
              Matrix.one_mul, Matrix.mul_assoc, h1', Matrix.mul_one]
        _ = _ := by rw [hBS ρ, Matrix.mul_one]
    refine ⟨Matrix.one_mul _, by simp, ?_⟩
    rw [Matrix.mul_one, hG]
    exact Matrix.PosDef.conjTranspose_mul_self _
      (Matrix.mulVec_injective_iff_isUnit.2 (Matrix.isUnit_nonsing_inv_iff.2 (hBu ρ)))
  have hne : R.vP i A.μ0 ≠ 0 :=
    GlobalTheory.AdTh.VecNe.thPVec_ne_zero (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hR.lev.βV i))
      (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hR.lev.βW i))
      (hrk.trans_le (r_le_V i)) (hR.thP.vP i A.μ0)
  have hinj := GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) (hω i A.μ0).std hθ
    (fun _ => 1) (R.BV i) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) (fun _ => (Vc D i).rank) _ hcVI
    (fun ρ => GlobalTheory.AdTh.VecFock.isCartanInv_cart _ ρ) (hR.models.BV i)
    (fun ρ => GlobalTheory.AdTh.VecFock.isONBasis_onb _ ρ _ (hR.models.order i ρ))
    (D.sp.V_sig _) (D.sp.W_sig _) (R.vP i A.μ0) hthv hvv hne

  have key := (hR.thP.ioP i A.μ0).2.1 τ k hk v u hu y
  unfold RealDat.ptP at key
  rw [av] at key
  have hfa := hinj key

  have hA := aω (R.ioP i (PiTensorProduct.tprod ℂ v) y)
  rw [hfa] at hA
  have hser : singleSeries R i ω φ' h y (Function.update v τ u) =
      Formalism.L2.Theta.rTr (Wc D i) (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ))
        (singleSeries R i ω φ' h y v) := by
    funext g
    simp only [singleSeries, Datum.thetaKO, Formalism.L2.Theta.rTr]
    rw [← hA, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  rw [hser]
  funext g
  simp only [Formalism.IndefR.Links.actL, LinearMap.coe_mk, AddHom.coe_mk, Formalism.L2.Theta.rTr]
  by_cases hl : ∃ κ, IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g0) κ
  · have hc := GlobalTheory.FinTranslate.comm_fin_real (Wc D i) hl.choose_spec.1
      (GlobalTheory.FinTranslate.atTau_mem R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ))
    simp only [actG0, dif_pos hl, Formalism.L2.Theta.rTr]
    rw [mul_assoc g, hc, ← mul_assoc]
  · simp only [actG0, dif_neg hl, Pi.zero_apply]

end GlobalTheory.SeriesKEquiv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterAndTranslationCoordsSurjectiv
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

namespace GlobalTheory.FlipOnto

theorem det_ne_zero_of_isSkew {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : Base F E} {n r s : ℕ} {X : Spc F E n} (hX : X.IsSkew σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h := GlobalTheory.det_ne_zero_of_hasSig (hX.sig w)
  rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  intro h0
  exact h (by rw [h0, map_zero, mul_zero])

theorem det_ne_zero_of_isHerm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : Base F E} {n r s : ℕ} {X : Spc F E n} (hX : X.IsHerm σ B r s) : X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h := GlobalTheory.det_ne_zero_of_hasSig (hX.sig w)
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h
  intro h0
  exact h (by rw [h0, map_zero])

theorem isUnit_det_map {F E K : Type} [Field F] [Field E] [Field K] [Algebra F E] [Algebra F K] (t : E →ₐ[F] K)
    {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J.det ≠ 0) : IsUnit (J.map t).det := by
  have : (J.map t).det = t J.det := by
    rw [← AlgHom.coe_toRingHom, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rw [this, isUnit_iff_ne_zero]
  exact (map_ne_zero_iff _ t.toRingHom.injective).mpr hJ

theorem coX_coY_onto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (n d r s r' s' : ℕ) (X : Spc F E n) (W : Spc F E d), X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (bb : GL (Fin n) (Fv F v)) (cc : GL (Fin d) (Fv F v)) (Z : Matrix (Fin n) (Fin d) (Fv F v)),
    (∃ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z ∧ z.map (piW (t.comp σ)) = 0 ∧ GlobalTheory.FlipMatch.coX t bb cc z = Z) ∧
    (∃ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z ∧ z.map (piW t) = 0 ∧ GlobalTheory.FlipMatch.coY σ X W t bb cc z = Z) := by
  intro F E _ _ _ _ _ σ B hB n d r s r' s' X W hX hW v t bb cc Z
  constructor
  · obtain ⟨u, hu, h0, h1⟩ := GlobalTheory.SplitComps.exists_mat_comps hB.cm v t (bb.1 * Z * cc.1ᵀ) 0
    refine ⟨u, hu, h1, ?_⟩
    have hc : cc.1ᵀ * (cc⁻¹).1ᵀ = 1 := by
      rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
    unfold GlobalTheory.FlipMatch.coX
    rw [h0, Matrix.mul_assoc, Matrix.mul_assoc, hc, Matrix.mul_one, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  · have hA : IsUnit (bb.1ᵀ * X.J.map t).det := by
      rw [Matrix.det_mul, Matrix.det_transpose]
      exact (Units.isUnit (Matrix.GeneralLinearGroup.det bb)).mul (isUnit_det_map t (det_ne_zero_of_isHerm hX))
    have hC : IsUnit ((W.J.map t)ᵀ * cc.1).det := by
      rw [Matrix.det_mul, Matrix.det_transpose]
      exact (isUnit_det_map t (det_ne_zero_of_isSkew hW)).mul (Units.isUnit (Matrix.GeneralLinearGroup.det cc))
    obtain ⟨u, hu, h0, h1⟩ := GlobalTheory.SplitComps.exists_mat_comps hB.cm v t 0
      (-((bb.1ᵀ * X.J.map t)⁻¹ * Z * ((W.J.map t)ᵀ * cc.1)⁻¹))
    refine ⟨u, hu, h0, ?_⟩
    unfold GlobalTheory.FlipMatch.coY
    rw [h1]
    calc -(bb.1ᵀ * X.J.map t * -((bb.1ᵀ * X.J.map t)⁻¹ * Z * ((W.J.map t)ᵀ * cc.1)⁻¹) * (W.J.map t)ᵀ * cc.1)
        = (bb.1ᵀ * X.J.map t * (bb.1ᵀ * X.J.map t)⁻¹) * Z * (((W.J.map t)ᵀ * cc.1)⁻¹ * ((W.J.map t)ᵀ * cc.1)) := by
          simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
      _ = Z := by
          rw [Matrix.mul_nonsing_inv _ hA, Matrix.nonsing_inv_mul _ hC, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.FlipOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceThetaFunctionVacuumConjugatePlace
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

noncomputable section

namespace GlobalTheory.SplitVacF

end GlobalTheory.SplitVacF

end

noncomputable section

namespace GlobalTheory.SplitVacF

open GlobalTheory.SplitInvFormF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {xi0 : E}
  {ψ : AddChar (AF F) ℂ}

theorem isSplitIdemF_conj {e : AEF F E} (he : IsSplitIdemF σ e) : IsSplitIdemF σ (cAF σ e) := by
  obtain ⟨h1, h2, v, ε, hpl, hsum⟩ := he
  refine ⟨by rw [← map_mul, h1], ?_, v, ε, hpl, ?_⟩
  · rw [cAF_cAF ⟨h1, h2, v, ε, hpl, hsum⟩, mul_comm, h2]
  · rw [cAF_cAF ⟨h1, h2, v, ε, hpl, hsum⟩, add_comm, hsum]

theorem mem_conjHalf_conj {e : AEF F E} (he : IsSplitIdemF σ e) {x : WOF F E nS nT} (hx : ∀ i j, e * x i j = x i j) :
    x ∈ conjHalf σ (cAF σ e) nS nT := fun i j => by rw [cAF_cAF he]; exact hx i j

theorem fin_of_mem {e : AEF F E} (he : IsSplitIdemF σ e) {u : WOF F E nS nT} (hu : u ∈ conjHalf σ e nS nT) :
    u.map (infPartF F E) = 0 := by
  obtain ⟨h1, h2, v, ε, hpl, hsum⟩ := he
  have hs := congrArg (infPartF F E) hsum
  rw [map_add (f := _), GlobalTheory.WeilPartsF.infPartF_placeIdem hpl] at hs
  have hc : infPartF F E (cAF σ e) = 0 := by
    have a1 : infPartF F E (cAF σ e) * infPartF F E (cAF σ e) = infPartF F E (cAF σ e) := by
      rw [← map_mul, ← map_mul, h1]
    have a2 : infPartF F E (cAF σ e) * infPartF F E e = 0 := by rw [← map_mul, mul_comm, h2, map_zero]
    linear_combination -a1 - a2 + infPartF F E (cAF σ e) * hs
  ext i j
  show infPartF F E (u i j) = 0
  rw [← hu i j, map_mul, hc, zero_mul]

theorem commF_add_left (u u' y : WOF F E nS nT) :
    commF σ JS JT xi0 ψ (u + u') y = commF σ JS JT xi0 ψ u y * commF σ JS JT xi0 ψ u' y := by
  unfold commF
  rw [← AddChar.map_add_eq_mul, GlobalTheory.HeisThetaF.symplOHF_add_left, GlobalTheory.HeisThetaF.symplOHF_add_right]
  congr 1; ring

theorem commF_add_right (u y y' : WOF F E nS nT) :
    commF σ JS JT xi0 ψ u (y + y') = commF σ JS JT xi0 ψ u y * commF σ JS JT xi0 ψ u y' := by
  unfold commF
  rw [← AddChar.map_add_eq_mul, GlobalTheory.HeisThetaF.symplOHF_add_left, GlobalTheory.HeisThetaF.symplOHF_add_right]
  congr 1; ring

theorem commF_zero_left (y : WOF F E nS nT) : commF σ JS JT xi0 ψ 0 y = 1 := by
  unfold commF
  rw [GlobalTheory.HeisThetaF.symplOHF_zero_left, GlobalTheory.HeisThetaF.symplOHF_zero_right, sub_zero, AddChar.map_zero_eq_one]

theorem commF_zero_right (u : WOF F E nS nT) : commF σ JS JT xi0 ψ u 0 = 1 := by
  unfold commF
  rw [GlobalTheory.HeisThetaF.symplOHF_zero_left, GlobalTheory.HeisThetaF.symplOHF_zero_right, sub_zero, AddChar.map_zero_eq_one]

theorem commF_neg_right (u y : WOF F E nS nT) : commF σ JS JT xi0 ψ u (-y) * commF σ JS JT xi0 ψ u y = 1 := by
  rw [← commF_add_right, neg_add_cancel, commF_zero_right]

theorem commF_swap (u y : WOF F E nS nT) : commF σ JS JT xi0 ψ y (-u) = commF σ JS JT xi0 ψ u y := by
  unfold commF
  have h1 := GlobalTheory.HeisThetaF.symplOHF_add_right (σ := σ) (JS := JS) (JT := JT) (xi0 := xi0) y (-u) u
  have h2 := GlobalTheory.HeisThetaF.symplOHF_add_left (σ := σ) (JS := JS) (JT := JT) (xi0 := xi0) (-u) u y
  rw [neg_add_cancel, GlobalTheory.HeisThetaF.symplOHF_zero_right] at h1
  rw [neg_add_cancel, GlobalTheory.HeisThetaF.symplOHF_zero_left] at h2
  congr 1
  linear_combination -h1 + h2

theorem commF_nsmul_left (u y : WOF F E nS nT) (n : ℕ) :
    commF σ JS JT xi0 ψ (n • u) y = commF σ JS JT xi0 ψ u y ^ n := by
  induction n with
  | zero => rw [zero_smul, commF_zero_left, pow_zero]
  | succ n ih => rw [succ_nsmul, commF_add_left, ih, pow_succ]

theorem commF_half {e : AEF F E} (he : IsSplitIdemF σ e) {x y : WOF F E nS nT} (hx : x ∈ conjHalf σ e nS nT)
    (hy : y ∈ conjHalf σ e nS nT) : commF σ JS JT xi0 ψ x y = 1 := by
  unfold commF
  rw [symplOHF_half he hx hy, symplOHF_half he hy hx, sub_zero, AddChar.map_zero_eq_one]

theorem heisOF_add_half {e : AEF F E} (he : IsSplitIdemF σ e) {x y : WOF F E nS nT} (hx : x ∈ conjHalf σ e nS nT)
    (hy : y ∈ conjHalf σ e nS nT) (f : WOF F E nS nT → ℂ) :
    heisOF σ JS JT xi0 ψ (x + y) f = heisOF σ JS JT xi0 ψ x (heisOF σ JS JT xi0 ψ y f) := by
  rw [heisOF_heisOF, symplOHF_half he hx hy, AddChar.map_zero_eq_one, one_smul]

end GlobalTheory.SplitVacF

end

noncomputable section

namespace GlobalTheory.SplitVacF

open GlobalTheory.SplitInvFormF

end GlobalTheory.SplitVacF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuConductorExponentsPosProdEqModulus
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

namespace GlobalTheory.NuExpModulus

open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.SqTop

theorem levelLe_mono {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {w : HeightOneSpectrum (𝓞 E)} {m n : ℕ}
    (h : χ.LevelLe w m) (hmn : m ≤ n) : χ.LevelLe w n := fun x hx hv =>
  h x hx (hv.trans (WithZero.exp_le_exp.2 (by omega)))

theorem exp_eq {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {w : HeightOneSpectrum (𝓞 E)} {c n : ℕ}
    (hc : GlobalTheory.CMVal.ExpAt χ w c) (h1 : χ.LevelLe w (n + 1)) (h2 : ¬ χ.LevelLe w n) : c = n + 1 := by
  have a := (hc _).1 h1
  have b := (hc n).not.1 h2
  omega

theorem exp_div {E : Type} [Field E] [NumberField E] {a b : Formalism.L2.Host.HChar E} {w : HeightOneSpectrum (𝓞 E)} {c n : ℕ}
    (hc : GlobalTheory.CMVal.ExpAt (a / b) w c) (ha : a.LevelLe w n) (h1 : b.LevelLe w (n + 1)) (h2 : ¬ b.LevelLe w n) :
    c = n + 1 := by
  refine exp_eq hc ?_ fun h => h2 ?_
  · rw [div_eq_mul_inv]
    exact Formalism.L2.Host.HChar.LevelLe.mul (levelLe_mono ha (Nat.le_succ n)) (Formalism.L2.Host.HChar.LevelLe.inv h1)
  · have e : b = a * (a / b)⁻¹ := by rw [inv_div, mul_div_cancel]
    rw [e]
    exact Formalism.L2.Host.HChar.LevelLe.mul ha (Formalism.L2.Host.HChar.LevelLe.inv h)

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem gridBaseCharacter_unramified_off_badPlaces (j : Fin D.R.m) {P : HeightOneSpectrum (𝓞 D.host.E)} (hS : P.under (𝓞 D.host.F) ∉ S1 D) :
    (L.C.mu0 j).UnrAt P := by
  refine (L.C.isMu0 j).unr P fun k hk => hS ((S1_mem_OmF D).2 ?_)
  have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
    show algebraMap _ (𝓞 D.host.E) _ ∈ P.asIdeal
    rw [map_natCast]; exact hk
  fin_cases k
  · exact Or.inl this
  · exact Or.inr (Or.inl this)

theorem exp_w (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T) (i j : Fin D.R.m) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : v ∈ G.pl.S0) {c : ℕ} (hc : GlobalTheory.CMVal.ExpAt (nuH G t i j) (G.pl.w v) c) : c = condExp G.pl v := by
  have a1 : 1 ≤ D.R.m - i := by have := i.2; omega
  have a2 : D.R.m - i ≤ D.R.m := by omega
  have hu := G.pl.under_w hv
  by_cases h0 : v = G.pl.v0
  · rw [condExp, if_pos h0]
    have hu0 : (G.pl.w v).under (𝓞 D.host.F) = G.pl.v0 := hu.trans h0
    obtain ⟨l1, l2⟩ := G.ch.lev0 _ a1 a2 _ hu0
    have hmu : (L.C.mu0 j).UnrAt (G.pl.w v) := gridBaseCharacter_unramified_off_badPlaces j (by rw [hu0]; exact G.ch.basePlace_not_mem_chiGridBadPlaces)
    have hxi : (L.xiH t).UnrAt (G.pl.w v) := by
      by_contra hn
      rcases (hL.Q_ram t _).1 hn with hq | ⟨PP', hq, hcj⟩
      · exact G.pl.levelPlace_ne_basePlace t _ hq hu0
      · exact G.pl.levelPlace_ne_basePlace t _ hq ((GlobalTheory.BadPlaceExp.under_eq_of_isConjPl hcj).trans hu0)
    exact exp_div (n := 0) hc (Formalism.L2.Host.HChar.UnrAt.levelLe (hmu.mul hxi) 0) l1
      (fun h => l2 ((Formalism.L2.Host.HChar.unrAt_iff _ _).2 h))
  · rw [condExp, if_neg h0]
    have h1 : v ∈ S1 D := (G.pl.mem_S0_of_sum_eq.1 hv).resolve_left h0
    obtain ⟨l1, l2⟩ := G.ch.lev1 _ a1 a2 (G.pl.w v) (by rw [hu]; exact h1)
    exact exp_div (n := 1) hc (Formalism.L2.Host.HChar.LevelLe.mul ((L.C.isMu0 j).tame _) (hL.xi_tame t _)) l1 l2

theorem exp_twPl (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T) (i j : Fin D.R.m) {P : HeightOneSpectrum (𝓞 D.host.E)}
    (hP : P ∈ twPl G t) {c : ℕ} (hc : GlobalTheory.CMVal.ExpAt (nuH G t i j) P c) : c = 1 := by
  have a1 : 1 ≤ D.R.m - i := by have := i.2; omega
  have a2 : D.R.m - i ≤ D.R.m := by omega
  have hP' : P ∈ L.Q t ∧ P ∉ G.pl.W0 := by
    simp only [twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union] at hP
    exact ⟨hP.1.resolve_left hP.2, hP.2⟩
  have hS1 : P.under (𝓞 D.host.F) ∉ S1 D := fun h => by
    have e := G.pl.w_Q t P hP'.1 h
    refine hP'.2 ?_
    rw [e]
    exact Finset.mem_image_of_mem _ (G.pl.mem_S0_of_sum_eq.2 (Or.inr h))
  have hS0 : P.under (𝓞 D.host.F) ∉ G.pl.S0 := fun h =>
    (G.pl.mem_S0_of_sum_eq.1 h).elim (G.pl.levelPlace_ne_basePlace t P hP'.1) hS1
  refine exp_eq (n := 0) hc ?_ fun h => nuH_not_unrAt_twPl G hL t i j P hP ((Formalism.L2.Host.HChar.unrAt_iff _ _).2 h)
  rw [nuH, div_eq_mul_inv]
  exact Formalism.L2.Host.HChar.LevelLe.mul (Formalism.L2.Host.HChar.LevelLe.mul ((L.C.isMu0 j).tame _) (hL.xi_tame t _))
    (Formalism.L2.Host.HChar.LevelLe.inv (Formalism.L2.Host.HChar.UnrAt.levelLe (G.ch.unr _ a1 a2 P hS0) _))

theorem main : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GlobalTheory.ChiGrid.GridData L sc) {μ₀ : T}, L.Is μ₀ →
  ∀ (t : T) (i j : Fin D.R.m) (c : Formalism.L2.DIV.Pl D.host.E → ℕ),
  (∀ w ∈ GlobalTheory.FunObj.locPl G t, GlobalTheory.CMVal.ExpAt (GlobalTheory.FunObj.SqNum.nuH G t i j) w (c w)) →
  (∀ w ∈ GlobalTheory.FunObj.locPl G t, 0 < c w) ∧ ∏ w ∈ GlobalTheory.FunObj.locPl G t, w.asIdeal ^ c w = GlobalTheory.SqTop.modT G t := by
  intro D T L sc G μ₀ hL t i j c hc
  have hW : ∀ v ∈ G.pl.S0, G.pl.w v ∈ locPl G t := fun v hv =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv)
  have hT : ∀ P ∈ twPl G t, P ∈ locPl G t := fun P hP => (Finset.mem_filter.1 hP).1
  have h1 : ∀ v ∈ G.pl.S0, c (G.pl.w v) = condExp G.pl v := fun v hv => exp_w G hL t i j hv (hc _ (hW v hv))
  have h2 : ∀ P ∈ twPl G t, c P = 1 := fun P hP => exp_twPl G hL t i j hP (hc _ (hT P hP))
  refine ⟨fun w hw => ?_, ?_⟩
  · by_cases h : w ∈ G.pl.W0
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
      rw [h1 v hv, condExp]
      split_ifs <;> omega
    · rw [h2 w (Finset.mem_filter.2 ⟨hw, h⟩)]
      omega
  · rw [← Finset.prod_filter_mul_prod_filter_not (locPl G t) (fun w => w ∈ G.pl.W0), modT]
    congr 1
    · have e : (locPl G t).filter (fun w => w ∈ G.pl.W0) = G.pl.S0.image G.pl.w := by
        ext w
        rw [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨Finset.mem_union_left _ h, h⟩⟩
      rw [e, Finset.prod_image fun v hv v' hv' h =>
        (G.pl.under_w hv).symm.trans ((congrArg _ h).trans (G.pl.under_w hv')), condE]
      exact Finset.prod_congr rfl fun v hv => by rw [h1 v hv]
    · refine Finset.prod_congr ?_ fun P hP => by rw [h2 P hP, pow_one]
      ext w
      simp only [twPl, Finset.mem_filter]

end GlobalTheory.NuExpModulus
end

