module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0878
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0227
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0887
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0886
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SqEqOneOfFixDat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFinitePartOfLift
section
noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module

namespace GlobalTheory.UseLoc.DescHf

theorem exists_retraction {l : ℕ} [Fact l.Prime] {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) :
    ∃ p : ↥LL'.1 →ₗ[ℚ_[l]] ↥LL.1, (∀ (a : ↥LL.1) (x : ↥LL'.1), p (IntermediateField.inclusion h a * x) = a * p x) ∧
      (∀ a : ↥LL.1, p (IntermediateField.inclusion h a) = a) ∧ (∀ x : ↥LL'.1, x ∈ OL LL' → p x ∈ OL LL) := by
  obtain ⟨r, hr, hr1⟩ := _root_.GlobalTheory.UseLoc.exists_intRetraction h
  obtain ⟨p, hp, hpr⟩ := _root_.GlobalTheory.UseLoc.extRet_exists h r hr hr1
  have h1 : p 1 = 1 := by
    have := hpr 1
    rw [hr1] at this
    exact this
  refine ⟨p, hp, fun a => ?_, fun x hx => ?_⟩
  · have := hp a 1
    rw [mul_one, h1, mul_one] at this
    exact this
  · have := hpr ⟨x, hx⟩
    rw [show p x = _ from this]
    exact (r ⟨x, hx⟩).2


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem descHf : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (k : ℕ) (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (z : Br.G D.nbr i w hw → (Fin k → Br.LL D.nbr i w hw) ⧸ (Br.locLat D.nbr i w hw M).T),
    (fun g => liftQ C.le k (z g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C (locOC C M)) →
    z ∈ HfD (Br.PD D.loc D.nbr i w hw) (Br.locLat D.nbr i w hw M) := by
  intro D i w hw C k M z hz
  obtain ⟨p, hpm, hp1, hpO⟩ := exists_retraction C.le
  obtain ⟨c, hc, m, hcm⟩ := (GlobalTheory.BlochKatoBaseChangeLe.mem_HfD_gen _ _ _).1 hz
  have hent : ∀ g a b, (mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M) g) a b =
      IntermediateField.inclusion C.le (Br.loc D.nbr i w hw M g a b) := fun g a b => rfl
  have hp : ∀ g (v : Fin k → ↥C.LL.1),
      (fun j => p ((mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M) g).mulVec v j)) =
        (Br.loc D.nbr i w hw M g).mulVec fun j => p (v j) := by
    intro g v
    funext a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, hent, hpm]
  have hc' := GlobalTheory.TwistedSelmerCompare.crystallineCocycle_transport_conjugation (D.loc (D.nd.l i)) (D.nbr i w hw).Kw (D.nbr i w hw).Kw C.LL
    (D.nbr i w hw).LL (MonoidHom.id _) continuous_id 1 (fun g => by simp) _ (Br.loc D.nbr i w hw M) p hp c hc
  refine (GlobalTheory.BlochKatoBaseChangeLe.mem_HfD_gen _ _ _).2 ⟨_, hc', fun j => p (m j), fun g => ?_⟩
  obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ (z g)
  have h1 : (Submodule.Quotient.mk (p := stdG ↥(OL C.LL) ↥C.LL.1 k) (incV C.le k u)) =
      Submodule.Quotient.mk (c g + ((mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M) g).mulVec m - m)) := by
    refine (liftQ_mk C.le k u).symm.trans ?_
    refine Eq.trans ?_ (hcm g)
    exact congrArg (liftQ C.le k) hu
  obtain ⟨n, hn⟩ := (Submodule.Quotient.eq (stdG ↥(OL C.LL) ↥C.LL.1 k)).1 h1
  refine hu.symm.trans ((Submodule.Quotient.eq (stdG (Br.OLL D.nbr i w hw) (Br.LL D.nbr i w hw) k)).2 ?_)
  refine ⟨fun j => ⟨p (n j), hpO _ (n j).2⟩, ?_⟩
  funext j
  have h2 := congrArg p (congrFun hn j)
  have h3 := congrFun (hp g m) j
  change p ((n j : ↥C.LL.1)) = p (IntermediateField.inclusion C.le (u j) - (c g j + ((mapM (algebraMap ↥(OL C.LL) ↥C.LL.1) (locOC C M) g).mulVec m j - m j))) at h2
  change (p (n j) : Br.LL D.nbr i w hw) = u j - (p (c g j) + ((Br.loc D.nbr i w hw M g).mulVec (fun j => p (m j)) j - p (m j)))
  rw [h2, map_sub, map_add (f := _), map_sub, hp1, ← h3]

end GlobalTheory.UseLoc.DescHf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealPointsActFockByRealComponentsBasis
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.RealPtsFock

open GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.RealFockAction GlobalTheory.VacuumCharacter

variable {D : D7}

section Gen

variable {S T : HSp D}

theorem om_vac_of {B : Base S T} {ψ : Twist D Circle} {ω : PairRep S T} (hF : B.F.Good)
    (hsig : ∀ τ, (B.w.p τ, B.w.q τ) = T.sig (tauE D τ)) (hsigOK : T.SigOK) (heta : GlobalTheory.WeilParts.IsEtaTilde D B.eta)
    (hinf : ∀ τ, HasInfExp D (B.mu * ψ.chi) τ ((B.w.c τ : ℚ) - ((B.w.p τ : ℚ) - B.w.q τ) / 2 + 1 / 2))
    (hω : B.IsWeil ψ.chi ω) {f : WO S T → ℂ} (hf : IsThetaFunO B.F.ψ S T f)
    (hv : ∀ τ, IsFockVacAt (heisO B.F.ψ S T) B.F.θ τ (cplxO 1 (B.F.sT τ)) f) {u : GA D S} (hu : u ∈ GinfC S) :
    ω (u, 1) f = (((detFam B.w.c (realGL B.F.θ S u))⁻¹ : ℂˣ) : ℂ) • f := by
  have hθ := hF.vac.2.inf
  have hS := fun τ => GlobalTheory.FockBasis.isCartanInv_one (onb_posDef (hF.onbS τ))
  have hT := hF.cartT
  have one : ∀ τ, compAt B.F.θ τ (Formalism.L2.Theta.mt T 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one T _
  have hpq : ∀ τ, B.w.p τ + B.w.q τ = T.rank := fun τ => by
    obtain ⟨e, -⟩ := hsigOK (tauE D τ)
    rw [← hsig τ] at e
    simpa using (Fintype.card_congr e).symm
  obtain ⟨x, hx, hxv⟩ := exists_root hθ S (fun τ => by
    have := (hS τ).2.2.det_pos.ne'
    rwa [Matrix.mul_one] at this) u hu
  have hy : IsDetRoot T 1 1 := by
    show _ = _
    rw [Units.val_one, RingHom.map_one, mul_one]
    exact (Matrix.det_one).symm
  choose p hp hd using fun τ => detPlus_one (n := S.rank) (B.F.sT τ) (hT τ).1
  have ep : ∀ τ, p τ = B.w.p τ := fun τ => by
    have h1 := hF.onbT τ
    rw [← hsig τ] at h1
    have h2 := (onb_laws h1 (hpq τ ▸ Nat.le_add_right _ _)).2
    rw [hp] at h2
    have h3 : (p τ : ℂ) = B.w.p τ := by linear_combination h2 / 2
    exact_mod_cast h3
  rw [_root_.GlobalTheory.WeilVacChar.vacuum_character D B.F.ψ hω.std S T B.F.θ hθ _ _ ω B.eta heta hω (fun _ => 1) B.F.sT hS hT u hu 1 (one_mem _)
    (fun τ => by rw [one_mul, mul_one]) (fun τ => by rw [one, one_mul, mul_one]) x 1 hx hy f hf hv]
  congr 1
  have hexp : ∀ τ, HasInfExp D (B.mu * ψ.chi * B.eta⁻¹ * (B.eta ^ T.rank)⁻¹) τ ((B.w.c τ - p τ : ℤ) : ℚ) := fun τ => by
    have h1 := hasInfExp_twist (hasInfExp_twist (hinf τ) (heta.2.2.2 τ) 1) (heta.2.2.2 τ) T.rank
    rw [pow_one] at h1
    convert h1 using 1
    rw [← hpq τ, ep]
    push_cast
    ring
  rw [MonoidHom.map_one, mul_one, Circle.coe_inv, hxv _ _ hexp, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib,
    Units.val_inv_eq_inv_val]
  simp only [detFam, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_prod, Units.val_zpow_eq_zpow_val,
    GeneralLinearGroup.val_det_apply]
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have inv := congrArg Matrix.det (GlobalTheory.OrientedHeis.compAt_mt_mul_inv (θ := B.F.θ) τ u)
  rw [Matrix.det_mul, Matrix.det_one] at inv
  have g0 := left_ne_zero_of_mul_eq_one inv
  rw [one, (hd τ _ 1 (by rw [one_mul, mul_one])).1, eq_inv_of_mul_eq_one_right inv, mul_one, ← smul_add,
    add_add_sub_cancel, ← two_smul ℂ, smul_smul, show (1 / 2 * 2 : ℂ) = 1 by norm_num, one_smul, Matrix.det_one, one_pow,
    one_mul, show (realGL B.F.θ S u τ).val = compAt B.F.θ τ (Formalism.L2.Theta.mt S u) from rfl, zpow_sub₀ g0, zpow_natCast,
    inv_pow]
  have := pow_ne_zero (p τ) g0
  have := zpow_ne_zero (B.w.c τ) g0
  field_simp

theorem om_fock_of {B : Base S T} {ψ : Twist D Circle} {ω : PairRep S T} (hF : B.F.Good)
    (hsig : ∀ τ, (B.w.p τ, B.w.q τ) = T.sig (tauE D τ)) (hsigOK : T.SigOK) (heta : GlobalTheory.WeilParts.IsEtaTilde D B.eta)
    (hinf : ∀ τ, HasInfExp D (B.mu * ψ.chi) τ ((B.w.c τ : ℚ) - ((B.w.p τ : ℚ) - B.w.q τ) / 2 + 1 / 2))
    (hω : B.IsWeil ψ.chi ω) {f : WO S T → ℂ} (hf : IsThetaFunO B.F.ψ S T f)
    (hv : ∀ τ, IsFockVacAt (heisO B.F.ψ S T) B.F.θ τ (cplxO 1 (B.F.sT τ)) f) {u : GA D S} (hu : u ∈ GinfC S)
    (P : PolF D T.rank S.rank) : ω (u, 1) (B.F.fock f P) = B.F.fock f (B.act u P) := by
  have hθ := hF.vac.2.inf
  have hBS := fun τ => onb_posDef (hF.onbS τ)
  have one : ∀ τ, compAt B.F.θ τ (Formalism.L2.Theta.mt T 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one T _
  have eu : ∀ τ, (inBasis B.F.BS (realGL B.F.θ S u) τ).val =
      (B.F.BS τ).val⁻¹ * compAt B.F.θ τ (Formalism.L2.Theta.mt S u) * (B.F.BS τ).val := fun τ => by
    rw [← Matrix.coe_units_inv]
    rfl
  have hle : ∀ τ, B.w.p τ ≤ T.rank := fun τ => by
    obtain ⟨e, -⟩ := hsigOK (tauE D τ)
    rw [← hsig τ] at e
    have := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  unfold Frame.fock
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D _ _ S T _ _ ω hω hθ (fun _ => 1) (fun _ => 1) (fun τ => (B.F.BS τ).val)
    (fun τ => (B.F.BS τ).val * (inBasis B.F.BS (realGL B.F.θ S u) τ).val) B.F.sT B.F.sT B.F.BT B.F.BT u 1
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => by rw [one, one_mul, mul_one])
    (fun τ => by rw [eu, ← Matrix.coe_units_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul])
    (fun τ => by rw [one, one_mul]) _ hf P).2, om_vac_of hF hsig hsigOK heta hinf hω hf hv hu,
    GlobalTheory.FiniteFock.pureTensorO_smul,
    pureTensorO_subst (p := B.w.p) hF.vac.1 hθ
      (fun τ => GlobalTheory.FockBasis.isCartanInv_one (hBS τ)) hF.cartT
      (fun τ => (onb_laws (by have := hF.onbT τ; rwa [← hsig τ] at this) (hle τ)).1) _ _
      (fun τ => by rw [eu]; exact conj_unitary (hBS τ) (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ S u τ)) hf,
    Base.act, MonoidHom.comp_apply, fockGL_apply, LinearMap.map_smul]

theorem mem_UH_of_conj {n : ℕ} {G B g : Matrix (Fin n) (Fin n) ℂ} (h : Bᴴ * G * B = 1) (hB : IsUnit B.det)
    (hg : B⁻¹ * g * B ∈ Matrix.unitaryGroup (Fin n) ℂ) : g ∈ Formalism.QuantumDeterminants.UH G := by
  have h1 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B hB
  have h2 : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hB
  have h3 : Bᴴ * (B⁻¹)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h2, Matrix.conjTranspose_one]
  have hU : (B⁻¹ * g * B)ᴴ * (B⁻¹ * g * B) = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.1 hg
    rwa [Matrix.star_eq_conjTranspose] at this
  have hG : G = (B⁻¹)ᴴ * B⁻¹ := by
    calc G = (B * B⁻¹)ᴴ * G * (B * B⁻¹) := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      _ = (B⁻¹)ᴴ * (Bᴴ * G * B) * B⁻¹ := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, Matrix.mul_one]
  have hgB : g = B * (B⁻¹ * g * B) * B⁻¹ := by
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  show gᴴ * G * g = G
  calc gᴴ * G * g = (B⁻¹)ᴴ * ((B⁻¹ * g * B)ᴴ * (Bᴴ * (B⁻¹)ᴴ) * (B⁻¹ * B) * (B⁻¹ * g * B)) * B⁻¹ := by
        conv_lhs => rw [hgB, hG]
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by rw [h3, h2, Matrix.mul_one, Matrix.mul_one, hU, Matrix.mul_one, ← hG]

end Gen

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {F : Face D A} {i : Fin D.R.m}

theorem om_ptP (hC : GlobalTheory.Hk3.Core R F) {B : Base (Vc D i) (Wc D i)} (h : BaseOf R i B) {ψ : Twist D Circle} {t : T0}
    (ht : IsTupOf R B ψ t) {u : GA D (Vc D i)} (hu : u ∈ GinfC (Vc D i)) (P : PolF D (Wc D i).rank (Vc D i).rank) :
    R.ωP i t (u, 1) (R.ptP i t P) = R.ptP i t (B.act u P) := by
  have hL := hC.lev
  have hW := hC.thP.ωP i A.μ0
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hev : Even (Vc D i).rank := rV ▸ (GlobalTheory.ConjTwist.Test.odd_r D).add_odd D.R.t_odd
  obtain ⟨hf, hv, -⟩ := GlobalTheory.CoefActIo.thetaVector_laws (i := i) hC t
  have hω := h.isWeil hC.thP.ωP ht
  have hpt : ∀ P, R.ptP i t P = B.F.fock (R.vP i t) P := fun P => by rw [h.fock_eq]; rfl
  have hf' : IsThetaFunO B.F.ψ (Vc D i) (Wc D i) (R.vP i t) := by rw [h.ψ]; exact hf
  have hv' : ∀ τ, IsFockVacAt (heisO B.F.ψ (Vc D i) (Wc D i)) B.F.θ τ (cplxO 1 (B.F.sT τ)) (R.vP i t) := by
    rw [h.ψ, h.θ, h.sT]; exact hv
  have hsig : ∀ τ, (B.w.p τ, B.w.q τ) = (Wc D i).sig (tauE D τ) := fun τ => by rw [h.p, h.q]
  have heta : GlobalTheory.WeilParts.IsEtaTilde D B.eta := by
    rw [h.eta]
    exact GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd D _ _ hL.eta R.C.isEta _ _ _ hW.resS hW.resT
      (hev.add_odd (rW ▸ GlobalTheory.ConjTwist.Test.odd_r D))
  have hinf : ∀ τ, HasInfExp D (B.mu * ψ.chi) τ ((B.w.c τ : ℚ) - ((B.w.p τ : ℚ) - B.w.q τ) / 2 + 1 / 2) := fun τ => by
    rw [h.mu_mul ht, h.exponent]
    exact (GlobalTheory.PairInfTypes.infTypesAt D T0 R.toLevCh A.μ0 hL i t τ).mu
  rw [hpt, hpt]
  have hF : B.F.Good := by
    refine { rank_le := B.hr, onbS := ?_, cartT := ?_, onbT := ?_, sdS := ?_, sdT := ?_, frS := ?_, frT := ?_, vac := ?_ }
    · intro τ; rw [h.BS]; exact hC.models.BV i τ
    · intro τ; rw [h.sT]; exact GlobalTheory.AdTh.VecFock.isCartanInv_cart _ τ
    · intro τ; rw [h.sT, h.BT]; exact GlobalTheory.AdTh.VecFock.isONBasis_onb _ τ _ (hC.models.order i τ)
    · rw [h.ΛS]; exact GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βV i))
    · rw [h.ΛT]; exact GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βW i))
    · rw [h.ΛS, h.βS]; exact (hC.lev.βV i).choose_spec.1
    · rw [h.ΛT, h.βT]; exact (hC.lev.βW i).choose_spec.1
    · rw [h.ψ, h.θ, h.sT, h.ΛS, h.ΛT, h.vac]; exact (hC.thP.vP i A.μ0).1
  exact om_fock_of hF hsig (D.sp.W_sig _) heta hinf hω hf' hv' hu P

theorem real_points_fock : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), ∃ (w : GlobalTheory.ExportSeries.Weight D (Vc D i).rank) (BS : GlobalTheory.ExportSeries.GLR D (Vc D i).rank) (r : ↥(GinfC (Vc D i)) →* GlobalTheory.ExportSeries.GLR D (Vc D i).rank), (∀ (u : ↥(GinfC (Vc D i))) (P : PolF D (Wc D i).rank (Vc D i).rank), R.ωP i t ((u : GA D (Vc D i)), 1) (R.ptP i t P) = R.ptP i t (GlobalTheory.ExportSeries.fockGL (Wc D i).rank w BS (r u) P)) ∧ (∀ (u : ↥(GinfC (Vc D i))) (τ : D.what₂.Tau), ((GlobalTheory.ExportSeries.inBasis BS (r u) τ : GL (Fin (Vc D i).rank) ℂ) : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ) ∈ Matrix.unitaryGroup (Fin (Vc D i).rank) ℂ) ∧ (∀ g : GlobalTheory.ExportSeries.GLR D (Vc D i).rank, (∀ τ, ((GlobalTheory.ExportSeries.inBasis BS g τ : GL (Fin (Vc D i).rank) ℂ) : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) ℂ) ∈ Matrix.unitaryGroup (Fin (Vc D i).rank) ℂ) → ∃ u, r u = g) ∧ (∀ (τ : D.what₂.Tau) (j : Fin (Wc D i).rank), (R.MW i (sg0 D A)).ε τ j = decide ((j : ℕ) < w.p τ)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t
  have hC := hG.core
  obtain ⟨B, hb, ht, rfl⟩ : ∃ B : Base (Vc D i) (Wc D i), BaseOf R i B ∧ IsTupOf R B (tupTwist R t) t ∧
      B = baseAt R i hC.models.BV (Twist.triv Circle ∅) ⟨⊥, 1⟩ :=
    ⟨_, baseOf_baseAt R hC.models.BV _ _, isTupOf_tupTwist R hC.models.BV t _, rfl⟩
  have hF : (baseAt R i hC.models.BV (Twist.triv Circle ∅) ⟨⊥, 1⟩).F.Good := by
    refine { rank_le := (baseAt R i hC.models.BV (Twist.triv Circle ∅) ⟨⊥, 1⟩).hr, onbS := ?_, cartT := ?_, onbT := ?_, sdS := ?_, sdT := ?_, frS := ?_, frT := ?_, vac := ?_ }
    · intro τ; rw [hb.BS]; exact hC.models.BV i τ
    · intro τ; rw [hb.sT]; exact GlobalTheory.AdTh.VecFock.isCartanInv_cart _ τ
    · intro τ; rw [hb.sT, hb.BT]; exact GlobalTheory.AdTh.VecFock.isONBasis_onb _ τ _ (hC.models.order i τ)
    · rw [hb.ΛS]; exact GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βV i))
    · rw [hb.ΛT]; exact GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hC.lev.βW i))
    · rw [hb.ΛS, hb.βS]; exact (hC.lev.βV i).choose_spec.1
    · rw [hb.ΛT, hb.βT]; exact (hC.lev.βW i).choose_spec.1
    · rw [hb.ψ, hb.θ, hb.sT, hb.ΛS, hb.ΛT, hb.vac]; exact (hC.thP.vP i A.μ0).1
  have hθ : IsInfFam R.θ := hF.vac.2.inf
  have hBS : ∀ τ, (R.BV i τ)ᴴ * gramAt D (Vc D i) τ * R.BV i τ = 1 := fun τ => onb_posDef (hC.models.BV i τ)
  have eu : ∀ (g : GLR D (Vc D i).rank) τ,
      (inBasis (baseAt R i hC.models.BV (Twist.triv Circle ∅) ⟨⊥, 1⟩).F.BS g τ).val = (R.BV i τ)⁻¹ * (g τ).val * R.BV i τ :=
    fun g τ => by
      rw [← hb.BS τ, ← Matrix.coe_units_inv]
      rfl
  refine ⟨liftWeight D i, (baseAt R i hC.models.BV (Twist.triv Circle ∅) ⟨⊥, 1⟩).F.BS,
    (realGL R.θ (Vc D i)).comp (GinfC (Vc D i)).subtype, fun u P => om_ptP hC hb ht u.2 P, fun u τ => ?_, fun g hg => ?_,
    fun τ j => hC.models.order i τ j⟩
  · rw [eu]
    exact conj_unitary (hBS τ) (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ _ (u : GA D (Vc D i)) τ)
  · have hU : ∀ τ, (g τ).val ∈ Formalism.QuantumDeterminants.UH (gramAt D (Vc D i) τ) := fun τ => by
      refine mem_UH_of_conj (hBS τ) ?_ (by rw [← eu]; exact hg τ)
      rw [← hb.BS τ]
      exact (Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)
    refine ⟨⟨GlobalTheory.AdelicScalar.realElt R.θ (Vc D i) (fun τ => (g τ).val), list_prod_mem fun x hx => ?_⟩, ?_⟩
    · obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
      exact GlobalTheory.PointAtPlaceHom.atTau_mem _ τ _
    · funext ρ
      refine Units.ext ?_
      change infMat D.sp.cm.sig (Vc D i).gram (R.θ ρ) (GlobalTheory.AdelicScalar.realElt R.θ (Vc D i) fun τ => (g τ).val) = (g ρ).val
      rw [GlobalTheory.AdelicScalar.realElt, GlobalTheory.RealTransSm.infMat_list_prod hθ _ hU ρ _ (Finset.nodup_toList _),
        if_pos (Finset.mem_toList.2 (Finset.mem_univ ρ))]

end GlobalTheory.RealPtsFock

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealPointsActFockScalarLinearSubstitution
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.ExportSeries GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes

namespace GlobalTheory.RealFockSubst

open scoped ComplexOrder

theorem om_ptP_subst : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → ∀ (i : Fin D.R.m) (t : T), ∀ u ∈ GinfC (Vc D i), ∃ (c : ℂ) (g : GLR D (Vc D i).rank), ∀ P : PolF D (Wc D i).rank (Vc D i).rank, R.ωP i t (u, 1) (R.ptP i t P) = c • R.ptP i t (fockSubst (pS D i) g P) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG i t u hu
  have hC := hG.core
  obtain ⟨hf, hv, -⟩ := GlobalTheory.CoefActIo.thetaVector_laws (i := i) hC t
  have hW := hC.thP.ωP i t
  have hθ : IsInfFam R.θ := hC.models.inf
  have hBS := fun τ => GlobalTheory.RealFockAction.onb_posDef (hC.models.BV i τ)
  have hS : ∀ τ, IsCartanInv (gramAt D (Vc D i) τ) 1 := fun τ => GlobalTheory.FockBasis.isCartanInv_one (hBS τ)
  have hT : ∀ τ, IsCartanInv (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ) :=
    fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart _ τ
  have one : ∀ τ, compAt R.θ τ (Formalism.L2.Theta.mt (Wc D i) 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one (Wc D i) _
  let BU : GLR D (Vc D i).rank := fun τ => (GlobalTheory.ConjTwist.isUnit_of_isONBasis (hC.models.BV i τ)).unit
  let U : GLR D (Vc D i).rank := inBasis BU (realGL R.θ (Vc D i) u)
  have eu : ∀ τ, (U τ).val = (R.BV i τ)⁻¹ * compAt R.θ τ (Formalism.L2.Theta.mt (Vc D i) u) * R.BV i τ := fun τ => by
    show _ = ((BU τ).val)⁻¹ * _ * (BU τ).val
    rw [← Matrix.coe_units_inv]
    rfl
  have hU : ∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin (Vc D i).rank) ℂ := fun τ => by
    rw [eu]; exact GlobalTheory.RealFockAction.conj_unitary (hBS τ) (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ (Vc D i) u τ)
  have hle : ∀ τ, ((Wc D i).sig (tauE D τ)).1 ≤ (Wc D i).rank := fun τ => by
    have hs : (Wc D i).SigOK := D.sp.W_sig _
    obtain ⟨e, -⟩ := hs (tauE D τ)
    have := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  have hev : Even (Vc D i).rank := (D.sp.V_rank _ (Nat.le_add_left _ _) i.2) ▸ (GlobalTheory.ConjTwist.Test.odd_r D).add_odd D.R.t_odd
  have hη := GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd D _ _ hC.lev.eta R.C.isEta _ _ _ hW.resS hW.resT
    (hev.add_odd ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2) ▸ GlobalTheory.ConjTwist.Test.odd_r D))
  obtain ⟨x, hx, -⟩ := GlobalTheory.VacuumCharacter.exists_root hθ (Vc D i) (fun τ => by
    have := (hS τ).2.2.det_pos.ne'
    rwa [Matrix.mul_one] at this) u hu
  have hy : IsDetRoot (Wc D i) 1 1 := by
    show _ = _
    rw [Units.val_one, RingHom.map_one, mul_one]
    exact (Matrix.det_one).symm
  obtain ⟨c, hc⟩ : ∃ c : ℂ, R.ωP i t (u, 1) (R.vP i t) = c • R.vP i t :=
    ⟨_, _root_.GlobalTheory.WeilVacChar.vacuum_character D R.ψ hW.std (Vc D i) (Wc D i) R.θ hθ _ _ (R.ωP i t) _ hη hW (fun _ => 1)
      (cart (R.MW i (sg0 D A))) hS hT u hu 1 (one_mem _) (fun τ => by rw [one_mul, mul_one])
      (fun τ => by rw [one, one_mul, mul_one]) x 1 hx hy _ hf hv⟩
  refine ⟨c, U, fun P => ?_⟩
  unfold RealDat.ptP
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D _ _ (Vc D i) (Wc D i) _ _ (R.ωP i t) hW hθ (fun _ => 1) (fun _ => 1) (R.BV i)
    (fun τ => R.BV i τ * (U τ).val) (cart (R.MW i (sg0 D A))) (cart (R.MW i (sg0 D A)))
    (onb (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) u 1
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => by rw [one, one_mul, mul_one])
    (fun τ => by rw [eu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.ConjTwist.isUnit_of_isONBasis (hC.models.BV i τ))), Matrix.one_mul])
    (fun τ => by rw [one, one_mul]) _ hf P).2, hc, GlobalTheory.FiniteFock.pureTensorO_smul,
    GlobalTheory.RealFockAction.pureTensorO_subst (p := pS D i) hW.std hθ hS hT
      (fun τ => (GlobalTheory.RealFockAction.onb_laws (GlobalTheory.AdTh.VecFock.isONBasis_onb _ τ _ (hC.models.order i τ)) (hle τ)).1)
      _ _ hU hf]

end GlobalTheory.RealFockSubst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealPointsActFockScalarUnitarySubstitution
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.RealFockActionFree

open GlobalTheory.ExportSeries
open scoped ComplexOrder

theorem om_ptP_inf : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T) (u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∃ (p : D.what₂.Tau → ℕ) (c : ℂ) (U : GlobalTheory.ExportSeries.GLR D (Vc D i).rank), (∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin (Vc D i).rank) ℂ) ∧ ∀ P : PolF D (Wc D i).rank (Vc D i).rank, R.ωP i t (u, 1) (R.ptP i t P) = R.ptP i t (c • GlobalTheory.ExportSeries.fockSubst p U P) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC i t u hu
  obtain ⟨hf, hv, -⟩ := GlobalTheory.CoefActIo.thetaVector_laws (i := i) hC t
  have hW := hC.thP.ωP i t
  have hθ : IsInfFam R.θ := hC.models.inf
  have hBS := fun τ => GlobalTheory.RealFockAction.onb_posDef (hC.models.BV i τ)
  have hS : ∀ τ, IsCartanInv (gramAt D (Vc D i) τ) 1 := fun τ => GlobalTheory.FockBasis.isCartanInv_one (hBS τ)
  have hT : ∀ τ, IsCartanInv (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ) :=
    fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart _ τ
  have one : ∀ τ, compAt R.θ τ (Formalism.L2.Theta.mt (Wc D i) 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one (Wc D i) _
  let BU : GLR D (Vc D i).rank := fun τ => (GlobalTheory.ConjTwist.isUnit_of_isONBasis (hC.models.BV i τ)).unit
  let U : GLR D (Vc D i).rank := inBasis BU (realGL R.θ (Vc D i) u)
  have eu : ∀ τ, (U τ).val = (R.BV i τ)⁻¹ * compAt R.θ τ (Formalism.L2.Theta.mt (Vc D i) u) * R.BV i τ := fun τ => by
    show _ = ((BU τ).val)⁻¹ * _ * (BU τ).val
    rw [← Matrix.coe_units_inv]
    rfl
  have hU : ∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin (Vc D i).rank) ℂ := fun τ => by
    rw [eu]; exact GlobalTheory.RealFockAction.conj_unitary (hBS τ) (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ (Vc D i) u τ)
  have hle : ∀ τ, ((Wc D i).sig (tauE D τ)).1 ≤ (Wc D i).rank := fun τ => by
    have hs : (Wc D i).SigOK := D.sp.W_sig _
    obtain ⟨e, -⟩ := hs (tauE D τ)
    have := Fintype.card_congr e
    simp only [Fintype.card_fin, Fintype.card_sum] at this
    omega
  have hev : Even (Vc D i).rank := (D.sp.V_rank _ (Nat.le_add_left _ _) i.2) ▸ (GlobalTheory.ConjTwist.Test.odd_r D).add_odd D.R.t_odd
  have hη := GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd D _ _ hC.lev.eta R.C.isEta _ _ _ hW.resS hW.resT
    (hev.add_odd ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2) ▸ GlobalTheory.ConjTwist.Test.odd_r D))
  obtain ⟨x, hx, -⟩ := GlobalTheory.VacuumCharacter.exists_root hθ (Vc D i) (fun τ => by
    have := (hS τ).2.2.det_pos.ne'
    rwa [Matrix.mul_one] at this) u hu
  have hy : IsDetRoot (Wc D i) 1 1 := by
    show _ = _
    rw [Units.val_one, RingHom.map_one, mul_one]
    exact (Matrix.det_one).symm
  obtain ⟨c, hc⟩ : ∃ c : ℂ, R.ωP i t (u, 1) (R.vP i t) = c • R.vP i t :=
    ⟨_, _root_.GlobalTheory.WeilVacChar.vacuum_character D R.ψ hW.std (Vc D i) (Wc D i) R.θ hθ _ _ (R.ωP i t) _ hη hW (fun _ => 1)
      (cart (R.MW i (sg0 D A))) hS hT u hu 1 (one_mem _) (fun τ => by rw [one_mul, mul_one])
      (fun τ => by rw [one, one_mul, mul_one]) x 1 hx hy _ hf hv⟩
  refine ⟨fun τ => ((Wc D i).sig (tauE D τ)).1, c, U, hU, fun P => ?_⟩
  unfold RealDat.ptP
  rw [(GlobalTheory.OrientedHeis.om_pureTensorO D _ _ (Vc D i) (Wc D i) _ _ (R.ωP i t) hW hθ (fun _ => 1) (fun _ => 1) (R.BV i)
    (fun τ => R.BV i τ * (U τ).val) (cart (R.MW i (sg0 D A))) (cart (R.MW i (sg0 D A)))
    (onb (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) u 1
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => by rw [one, one_mul, mul_one])
    (fun τ => by rw [eu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _
      ((Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.ConjTwist.isUnit_of_isONBasis (hC.models.BV i τ))), Matrix.one_mul])
    (fun τ => by rw [one, one_mul]) _ hf P).2, hc, GlobalTheory.FiniteFock.pureTensorO_smul,
    GlobalTheory.RealFockAction.pureTensorO_subst (p := fun τ => ((Wc D i).sig (tauE D τ)).1) hW.std hθ hS hT
      (fun τ => (GlobalTheory.RealFockAction.onb_laws (GlobalTheory.AdTh.VecFock.isONBasis_onb _ τ _ (hC.models.order i τ)) (hle τ)).1)
      _ _ hU hf, LinearMap.map_smul]

end GlobalTheory.RealFockActionFree
end

