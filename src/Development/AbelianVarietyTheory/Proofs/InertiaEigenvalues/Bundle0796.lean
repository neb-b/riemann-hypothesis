module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0786
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0635
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InnerProductIntegralFormula
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0709
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0506
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0139
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0867
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0640
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0776
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsIdealsPrimeToEqSpan
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0102
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0789
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0792
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0790
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDecompChainSpaceDefiniteAddNormalFrame

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateDefiniteFormsDescendNumberField
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjDesc


set_option maxHeartbeats 1600000 in
theorem vals : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (a : Tp) (x₀ : A.fam.amb.FL i (tup a)) (h : GA D (Vc D i)), ∃ x : VsV D i M.c'.F, (R.HV i (tup a)).e (jVx R i (tup a) x₀) (fin _ h) = M.c0' x := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC i Tp tup M hP a x₀ h
  obtain ⟨_, _, _, hT, hc⟩ := hP.lift.c0
  obtain ⟨x, hx⟩ := GlobalTheory.RationalValues.placeEx R i M.jL (inC M.c') (tup a) (fun _ : Unit => h) M.c0' hC.models.jV hT hc hC.lev
    hC.grp.chiW hC.fam.pl_onto hC.fam.muVal x₀
  exact ⟨x (), hx ()⟩


set_option maxHeartbeats 1600000 in
theorem c_inj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC M.c') M.c0' c → Function.Injective c := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ i Tp tup M hP c hc
  obtain ⟨gramR, c0R, c0L, hFT, hC0⟩ := hP.lift.c0
  have hfield : (inC M.c').comp M.jL = D.what₂.embLL := hP.lift.field
  have hbas : ∀ j, c (GlobalTheory.CoefModel.mapVV D.what₂.embLL (lamV D i) (bVV D.what₂.LL (lamV D i) j)) =
      c0L i (bVV D.what₂.LL (lamV D i) j) := fun j => by
    obtain ⟨v', hv', hcv'⟩ := hC0 (bVV D.what₂.LL (lamV D i) j)
    refine (hc v' _ ?_).trans hcv'
    rw [GlobalTheory.CoefModel.mapVV_coe, hv', MvPolynomial.map_map, hfield]
  have hli : LinearIndependent ℂ fun j => c (GlobalTheory.CoefModel.mapVV D.what₂.embLL (lamV D i) (bVV D.what₂.LL (lamV D i) j)) := by
    have h := (hFT.mapL i).2.1
    simp only [← hbas] at h
    exact h
  have hli0 := GlobalTheory.CoefModel.linearIndependent_mapVV D.what₂.embLL (lamV D i)
  have hsp0 := GlobalTheory.CoefModel.span_mapVV D.what₂.embLL (lamV D i)
  let B := Module.Basis.mk hli0 hsp0.ge
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  have hs := B.sum_repr z
  have h0 : ∑ j, B.repr z j • c (GlobalTheory.CoefModel.mapVV D.what₂.embLL (lamV D i) (bVV D.what₂.LL (lamV D i) j)) = 0 := by
    calc _ = c (∑ j, B.repr z j • B j) := by
            set_option synthInstance.maxHeartbeats 100000 in
              rw [map_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_smul, Module.Basis.mk_apply]
      _ = 0 := by rw [hs, hz]
  have hc0 := Fintype.linearIndependent_iff.1 hli _ h0
  rw [← hs]
  exact Finset.sum_eq_zero fun j _ => by rw [hc0 j, zero_smul]


set_option maxHeartbeats 4000000 in
theorem conj_desc : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC M.c') M.c0' c → (∀ t x, ((R.xi (tup t) x : Circle) : ℂ) ∈ M.c'.F) → ∀ a b : Tp, ConjTup R τ (tup a) (tup b) → ∀ (y : (R.HV i (tup a)).H) (y' : (R.HV i (tup b)).H), ConjForm R i τ c (tup a) (tup b) y y' → ∃ (n : ℕ) (α : Fin n → ℂ) (ys : Fin n → (R.HV i (tup a)).H) (ys' : Fin n → (R.HV i (tup b)).H), y = ∑ k, α k • ys k ∧ y' = ∑ k, τ (α k) • ys' k ∧ ∀ k (h : GA D (Vc D i)), ∃ x x' : VsV D i M.c'.F, (x' : Pol M.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank) ∧ (R.HV i (tup a)).e (ys k) (fin _ h) = M.c0' x ∧ (R.HV i (tup b)).e (ys' k) (fin _ h) = M.c0' x' := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC hFW i Tp tup M hP τ ta hta hFix c hc hxi a b hab y y' hy
  obtain ⟨φ, hφs, hφ⟩ := _root_.GlobalTheory.ConjTwist.exists_conjForm_equiv D G Pl0 T0 A T R F κ v₀ hC hFW i Tp tup M hP c hc τ (tup a) (tup b) hFix hab
  have hy' : y' = φ y := (hφ y y').1 hy
  have hmem : y ∈ Submodule.span ℂ (Set.range (R.jV i (tup a))) := by
    rw [GlobalTheory.HeckeClassSums.span_jV hC.models.HV hC.models.jV i (tup a)]; exact Submodule.mem_top
  obtain ⟨n, α, g, hg⟩ := Submodule.mem_span_set'.1 hmem
  have hinj := c_inj D G Pl0 T0 A T R κ v₀ i Tp tup M hP c hc
  refine ⟨n, α, fun k => (g k : (R.HV i (tup a)).H), fun k => φ (g k : (R.HV i (tup a)).H), hg.symm, ?_, ?_⟩
  · subst hy' hg
    exact (map_sum φ _ _).trans (Finset.sum_congr rfl fun k _ => hφs _ _)
  · intro k h
    have hk : ∃ x₀ : A.fam.amb.FL i (tup a), R.jV i (tup a) x₀ = (g k : (R.HV i (tup a)).H) := (g k).2
    obtain ⟨x₀, hx₀⟩ := hk
    have hv := vals D G Pl0 T0 A T R F κ v₀ hC i Tp tup M hP
    have hv2 := hv a x₀ h
    let x := hv2.choose
    have hx : (R.HV i (tup a)).e (jVx R i (tup a) x₀) (fin _ h) = M.c0' x := hv2.choose_spec
    have hx' : ((g k : (R.HV i (tup a)).H)) = jVx R i (tup a) x₀ := hx₀.symm
    have hcf := (hφ (g k : (R.HV i (tup a)).H) (φ (g k))).2 rfl h
    let x1 := hcf.choose
    let x1' := hcf.choose_spec.choose
    have hcv : ConjVec i τ x1 x1' := hcf.choose_spec.choose_spec.1
    have h1 : (R.HV i (tup a)).e (g k : (R.HV i (tup a)).H) (fin _ h) = c x1 := hcf.choose_spec.choose_spec.2.1
    have h1' : (R.HV i (tup b)).e (φ (g k : (R.HV i (tup a)).H)) (fin _ h) = c x1' := hcf.choose_spec.choose_spec.2.2
    let xC : VsV D i ℂ := GlobalTheory.CoefModel.mapVV (inC M.c') (lamV D i) x
    have hxC : c xC = M.c0' x := hc x xC rfl
    have e0 : (R.HV i (tup a)).e (g k : (R.HV i (tup a)).H) (fin _ h) = M.c0' x := by rw [hx']; exact hx
    have e1 : c x1 = c xC := h1.symm.trans (e0.trans hxC.symm)
    have hx1 : x1 = xC := hinj e1
    let x' : VsV D i M.c'.F := ⟨MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank),
      GlobalTheory.Proof.TensorMapDescent.map_mem_VV (ta : M.c'.F →+* M.c'.F) (lamV D i) _ x.2⟩
    have hcomp : (τ : ℂ →+* ℂ).comp (inC M.c') = (inC M.c').comp (ta : M.c'.F →+* M.c'.F) := by
      ext z; exact (hta z).symm
    have hx1' : (x1' : Pol ℂ D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (inC M.c') (x' : Pol M.c'.F D.what₂.Tau (Vc D i).rank) := by
      rw [hcv, hx1]
      show MvPolynomial.map (τ : ℂ →+* ℂ) (MvPolynomial.map (inC M.c') (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank)) =
        MvPolynomial.map (inC M.c') (MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank))
      rw [MvPolynomial.map_map, MvPolynomial.map_map, hcomp]
    exact ⟨x, x', rfl, e0, h1'.trans (hc x' x1' hx1')⟩

end GlobalTheory.ConjDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardLiftAdjointEqUpwardThetaIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.AdjUp

namespace GlobalTheory.AdjUp


set_option maxHeartbeats 1000000 in
theorem adjFormula_holds : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, AdjFormula R i t := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t th hth v hv n b
  refine (_root_.GlobalTheory.AdjUp.ip_eq_mul_integral_val hP D G Pl0 T A Ks R F hL i v hv).elim fun P hPx => ?_
  refine (_root_.GlobalTheory.AdelicL2Norm.norm_eq_integral D G Pl0 T A Ks R F hL i t).elim fun c hcx => ?_
  have hval : ∀ u, val R i v (th u) = R.thF i t u (fun ρ => v ρ) := fun u => by
    show (R.HW i (sg0 D A)).e (th u) (fun ρ => v ρ) = _
    rw [hth u]
  have hK0 : ∀ k h, upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v 0) h = 0 := fun k h => by
    rw [val_zero]; exact upLift_zero _ _ _ _ h
  exact adjoint_formula_of_kernel th b ((R.νW i).restrict (R.fdW i)) ((R.νV i t).restrict (R.fdV i t)) (val R i v)
    (fun u => R.thF i t u (fun ρ => v ρ)) (R.extV i t)
    (fun k y h => upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v y) h) P c hPx.1 hcx.1 hPx.2
    hval (val_zero R i v) hK0 hcx.2 (fun y u => _root_.GlobalTheory.AdjUnfold.integral_val_thF_eq hP D G Pl0 T A Ks R F hL hF i t v n b y u)
    (fun y => GlobalTheory.T.upwardVectorLift_mem_range_coefficientExtension hP D G Pl0 T A Ks R F hL hF i t v n b y)

end GlobalTheory.AdjUp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftPreservesGood
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.GoodLift

theorem sum_translates {H X W ι : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup W] [Module ℂ W] [Mul X] [Fintype ι]
    (E : H →ₗ[ℂ] (X → W)) (y : H) (yg : ι → H) (a c : ι → ℂ) (κ : ι → X)
    (hext : ∀ g h, E (yg g) h = (c g)⁻¹ • E y (h * κ g))
    (hy : ∀ (l : W →ₗ[ℂ] ℂ) h, ∑ g, a g * ((c g)⁻¹ * l (E y (h * κ g))) = l (E y h)) :
    E (∑ g, a g • yg g) = E y := by
  funext h
  refine sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun l => ?_)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, sub_eq_zero, ← hy l h, map_sum, Finset.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, Pi.smul_apply, map_smul, hext g h, map_smul, smul_eq_mul, smul_eq_mul]

theorem gaL_apply_choose {D : D7} {G : Type} [Group G] [Fintype G] (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D))
    (L : LevDat D.host.E ℂ V.rank) (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (hk : ∀ g, ∃ κ, IsLevelLift V β L (eG g) κ)
    (F : GA D V → ℂ) (h : GA D V) :
    gaL V β L eG c F h = ∑ g, c g * ((levChi V β (flagL L) (hk g).choose)⁻¹ * F (h * (hk g).choose)) := by
  unfold gaL
  rw [LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  show c g * actG0 V β L (eG g) F h = _
  unfold actG0
  rw [dite_eq_left (hk g)]

end GlobalTheory.GoodLift

namespace GlobalTheory.GoodLift

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)


set_option maxHeartbeats 4000000 in
theorem liftsW_of_core (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) : LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv) := by
  obtain ⟨c, hc⟩ := hR.lev.βW i
  exact _root_.GlobalTheory.FiniteGroupLifts.liftsExist_of_twist_empty _ _ _ _ _ hc rfl (_root_.GlobalTheory.TypePlaces.not_isConjPl R.C.P R.Pg hR.lev.Pg)


set_option maxHeartbeats 4000000 in
theorem liftsV_of_core (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) (g : G) :
    ∃ κ, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ := by
  obtain ⟨q, hq⟩ := (R.B.L i t).act_tie.red_surj g
  have h1 := hR.grp.red_L i t q
  obtain ⟨⟨_, h, rfl⟩, hq2⟩ := q
  obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D (Vc D i)).1 h
  have e : finHom (Vc D i) (a * k) = finHom (Vc D i) k := by
    rw [map_mul, show finHom (Vc D i) a = 1 from ha, one_mul]
  refine ⟨k, hk, ?_, ?_⟩
  · rw [finE_eq, ← e]; exact hq2.1
  · rw [finE_eq, ← e, ← hq]; exact h1.symm


set_option maxHeartbeats 4000000 in
theorem translate_of_core (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) (g0 : G0 R.Pg D.R.r) (κ : GA D (Vc D i))
    (hκ : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ) (y : (R.HV i t).H) :
    ∃ y' : (R.HV i t).H, (∀ h, (R.HV i t).e y' h = (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ •
        (R.HV i t).e y (h * (finHom (Vc D i)).rangeRestrict κ)) ∧
      ∀ h, R.extV i t y' h = (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t y (h * κ) := by
  obtain ⟨y', hy', -⟩ := GlobalTheory.RowClassSum.exists_translate (Vc D i) (R.βV i) (R.datVt i t) (R.cV i) (hR.models.cV i)
    (R.HV i t) _ (R.B.L i t).pres.reps (hR.models.HV i t) g0 κ hκ y
  have hc0 : levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ ≠ 0 := levChi_ne_zero _ _
  refine ⟨y', hy', fun h => ?_⟩
  have e := GlobalTheory.ThetaProjEquiv.extV_shift R hR.models.cV i t κ hκ.1 _ hc0 y y' hy' h
  rw [LinearMap.map_smul, Pi.smul_apply] at e
  rw [← e, smul_smul, inv_mul_cancel₀ hc0, one_smul]


set_option maxHeartbeats 4000000 in
theorem thF_translate_low (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T) (g : G) (κ : GA D (Vc D i))
    (hκ : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ) (y y' : (R.HV i t).H)
    (hy : ∀ h, (R.HV i t).e y' h = (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ •
        (R.HV i t).e y (h * (finHom (Vc D i)).rangeRestrict κ))
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    R.thF i t y' (fun ρ => v ρ) = actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (R.thF i t y (fun ρ => v ρ)) := by
  obtain ⟨κ', hκ'⟩ := liftsW_of_core R F hR i (R.eG g)
  funext x
  exact (GlobalTheory.ThetaProjEquiv.thF_shift_core R F hR i t (R.eG g) κ κ' hκ hκ'.1 y y' _ (levChi_ne_zero _ _)
    (_root_.GlobalTheory.VecInv.omega_lifts_vP R hR.lev hR.models.inf hR.thP.ωP hR.thP.vP i t (R.eG g) κ κ' hκ hκ') hy v x).trans
    (GlobalTheory.ThetaProjEquiv.finiteGroup_acts_by_lift_translation_principalType R i (R.eG g) κ' hκ' _ (GlobalTheory.ThetaProjEquiv.thF_type R hR.thP.thF_mem i t y _) x).symm


set_option maxHeartbeats 4000000 in
theorem thF_low_eq (hP : R.IsThP) (i : Fin D.R.m) (t : T) (y z : (R.HV i t).H) (hz : R.extV i t z = R.extV i t y)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) : R.thF i t z (fun ρ => v ρ) = R.thF i t y (fun ρ => v ρ) := by
  obtain ⟨thP, hthP, hthF⟩ := hP.thF i t
  funext w
  refine ((congrFun (hthF _ v) w).trans (hthP.eq _ (PiTensorProduct.tprod ℂ v) w)).trans ?_
  refine Eq.trans ?_ ((congrFun (hthF y v) w).trans (hthP.eq _ (PiTensorProduct.tprod ℂ v) w)).symm
  have e1 : (((R.extV i t).rangeRestrict z : LinearMap.range (R.extV i t)) : GA D (Vc D i) → (R.cV i).W) =
      R.extV i t y := hz
  have e2 : (((R.extV i t).rangeRestrict y : LinearMap.range (R.extV i t)) : GA D (Vc D i) → (R.cV i).W) =
      R.extV i t y := rfl
  unfold Formalism.IndefR.Lift.thetaPInt
  rw [e1, e2]


set_option maxHeartbeats 4000000 in
theorem eWf_apply_sum (i : Fin D.R.m) (f : GA D (Wc D i) → ℂ) :
    R.eWf i (sg0 D A) f = ∑ g, RealDat.eC (A := A) (sg0 D A) g • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) f := by
  unfold RealDat.eWf gaL
  rw [LinearMap.sum_apply]
  rfl

end GlobalTheory.GoodLift

namespace GlobalTheory.GoodLift


set_option maxHeartbeats 8000000 in
theorem goodMem_of_given : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, GoodMem R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t y hy
  have hR := hG.core
  have hLV := liftsV_of_core R F hR i t
  choose yg hyg hext using fun g : G => translate_of_core R F hR i t (R.eG g) _ (hLV g).choose_spec y
  have hz : R.extV i t (∑ g, RealDat.eC (A := A) (sg0 D A) g • yg g) = R.extV i t y :=
    sum_translates (R.extV i t) y yg _ _ (fun g => (hLV g).choose) hext
      (fun l h => (gaL_apply_choose (Vc D i) (R.βV i) (R.datVt i t) R.eG _ hLV _ h).symm.trans (congrFun (hy l) h))
  have hmem : (R.HW i (sg0 D A)).e (R.thG i t y) ∈ R.Wall i (sg0 D A) := by
    rw [← (hR.models.HW i (sg0 D A)).2.1]; exact ⟨_, rfl⟩
  refine sub_eq_zero.1 (GlobalTheory.LiftRows.spanP_of_given R F hG i _ (Submodule.sub_mem _ hmem (hR.thP.thF_mem i t y))
    fun v => ?_)
  refine sub_eq_zero.2 ?_
  rw [hR.thP.thG i t y]
  show R.eWf i (sg0 D A) (R.thF i t y (fun ρ => v ρ)) = _
  rw [eWf_apply_sum R i]
  calc ∑ g, RealDat.eC (A := A) (sg0 D A) g •
        actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (R.thF i t y (fun ρ => v ρ))
      = ∑ g, RealDat.eC (A := A) (sg0 D A) g • R.thF i t (yg g) (fun ρ => v ρ) :=
        Finset.sum_congr rfl fun g _ => by
          rw [thF_translate_low R F hR i t g _ (hLV g).choose_spec y (yg g) (hyg g) v]
    _ = R.thF i t (∑ g, RealDat.eC (A := A) (sg0 D A) g • yg g) (fun ρ => v ρ) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, MultilinearMap.sum_apply]
        simp only [map_smul, MultilinearMap.smul_apply]
    _ = R.thF i t y (fun ρ => v ρ) := thF_low_eq R hR.thP i t y _ hz v

end GlobalTheory.GoodLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EvKEqSum
section
open scoped TensorProduct

namespace GlobalTheory.EvaluationSum

open GlobalTheory.SeriesTie

theorem evK_eq_sum {D : Formalism.BasicNotions.D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 (Formalism.BasicNotions.Rows.Data.LL (Formalism.BasicNotions.D7.what₂ D)) Γ Pl0 I0 (List Nat) T (Formalism.BasicNotions.Ranks.m (Formalism.BasicNotions.D7.R D))}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (Formalism.BasicNotions.Rows.Data.LL (Formalism.BasicNotions.D7.what₂ D))]
    {Rl : Formalism.IndefR.Links.RealDat3 D A3 Ks}
    {cG : MulEquiv (Formalism.L2.DIV.G0 (Formalism.IndefR.Links.LevCh.Pg (Formalism.IndefR.Links.RealDat.toLevCh (Formalism.IndefR.Links.RealDat3.toRealDat Rl))) (Formalism.BasicNotions.Ranks.r (Formalism.BasicNotions.D7.R D))) (Formalism.BasicNotions.G0g (Formalism.BasicNotions.D7.nd D))}
    {S : Formalism.IndefR.NX.RatDat (Formalism.BasicNotions.D7.ntw D)} (YS : Formalism.IndefR.NX.NExpRealS Rl cG S)
    (v₀ : (j : Fin (Formalism.BasicNotions.Ranks.m (Formalism.BasicNotions.D7.R D))) → (σ : RingHom (Formalism.BasicNotions.Rows.Data.LL (Formalism.BasicNotions.D7.what₂ D)) Complex) → Formalism.IndefR.Mult.DSModel.Vec (Formalism.IndefR.Links.RealDat.MW (Formalism.IndefR.Links.RealDat3.toRealDat Rl) j σ))
    {ρ : GlobalTheory.SeriesTie.Setup (Formalism.BasicNotions.D7.ntw D)} (hρ : GlobalTheory.SeriesTie.Setup.Good ρ)
    (i : Formalism.BasicNotions.NTw.Tw (Formalism.BasicNotions.D7.ntw D)) (j : Fin (Formalism.BasicNotions.Ranks.m (Formalism.BasicNotions.D7.R D))) (b : Bool)
    (t : TensorProduct (Formalism.IndefR.NX.RatDat.Ks S) (Formalism.IndefR.NX.KB S i b) (Formalism.IndefR.NX.FmK S ((j : ℕ) + 1))) :
    ∃ (n : ℕ) (a : Fin n → Formalism.IndefR.NX.KB S i b) (x : Fin n → Formalism.IndefR.NX.FmK S ((j : ℕ) + 1)),
      GlobalTheory.SeriesTie.evK YS v₀ hρ i j b t =
        ∑ k : Fin n, GlobalTheory.SeriesTie.Setup.e ρ i b (a k) • GlobalTheory.SeriesTie.evW YS v₀ j (x k).val := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul a f => exact ⟨1, fun _ => a, fun _ => f, by simp [evK_tmul]⟩
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨n₁, a₁, x₁, e₁⟩ := h₁
    obtain ⟨n₂, a₂, x₂, e₂⟩ := h₂
    refine ⟨n₁ + n₂, Fin.append a₁ a₂, Fin.append x₁ x₂, ?_⟩
    rw [map_add (f := _), e₁, e₂, Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]

end GlobalTheory.EvaluationSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFibreIdempotents
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.UnivCover

namespace GlobalTheory.FibreIdem

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

theorem chi_eq_one_of_finPart : ∀ (D : D7) {A : Type} [Group A] (χ : (AE D)ˣ →* A), IsOpen (χ.ker : Set (AE D)ˣ) → ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → χ x = 1 := _root_.GlobalTheory.UnivCover.OpenKerChar.map_eq_one_of_finPart_eq_one

theorem chi_eq_one_of_cong : ∀ (D : D7) {A : Type} [CommGroup A] (PP : Pl D.host.E) (χ : (AE D)ˣ →* A) (κ : GlobalTheory.ExportSeries.ResChars D A), (⟨{PP}, χ, κ⟩ : GlobalTheory.ExportSeries.Twist D A).Good → ∀ N : ℕ, ((N : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → ∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → χ x = 1 := _root_.GlobalTheory.OnePlaceCong.chi_eq_one_of_cong

theorem char_root_eq_one' (V : HSp D) {A : Type} [CommGroup A] (c : (AE D)ˣ →* A) (N : ℕ) (hN : Odd N)
    (hF : ∀ a, c (idF D a) = 1) (hinf : ∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → c x = 1)
    (hcong : ∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → c x = 1)
    (g : GA D V) (x : (AE D)ˣ) (hx : IsDetRoot V g x)
    (hg : ∃ w ∈ intAE D, (((Matrix.GeneralLinearGroup.det (finHom V g)) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
      (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = N • w) : c x = 1 := by
  obtain ⟨w, hw, hwe⟩ := hg
  have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
  have htr : ∀ x : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
    intro x
    apply (D.sp.cm.fixed _).1
    change D.sp.cm.sig _ = _
    rw [map_add (f := _), hσ, add_comm]
  rw [Matrix.GeneralLinearGroup.val_det_apply] at hwe
  have hn := GlobalTheory.RecDict.det_finHom_norm V g
  obtain ⟨y, y', hy, hy', hyy, hroot, p, hp, hpe⟩ := _root_.GlobalTheory.OddRoot.exists_root_odd D N hN _ w hw hwe hn
  obtain ⟨Y, hY1, hY2, hY3⟩ := GlobalTheory.DetRootCong.exists_idele D y y' hyy
  have hcY : c Y = 1 := hcong Y ⟨hY1, hY2 ▸ hy, hY3 ▸ hy'⟩ ⟨p, hp, hY2 ▸ hpe⟩
  have hdet : (finHom V g).1.det = finPart D (matHom V g).1.det := ((finPart D).map_det _).symm
  have hxf : finPart D (x : AE D) =
      (finHom V g).1.det * sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) := by
    rw [hdet, ← GlobalTheory.DetRootCong.finPart_sigR, ← RingHom.map_mul]
    exact congrArg _ hx
  obtain ⟨b, hb⟩ := GlobalTheory.Member.exists_unit_of_sigR_fixed (Af D.host.F) D.sp.cm.sig htr
    (Units.map (finPart D).toMonoidHom (x * Y⁻¹))
    (GlobalTheory.DetRootCong.quot_fixed (finPart D) _ x Y _ y y' hxf hroot hyy hY3)
  obtain ⟨a, ha⟩ := GlobalTheory.DetRootCong.exists_idF D b
  have hb' : finPart D (idF D a : AE D) = finPart D ((x * Y⁻¹ : (AE D)ˣ) : AE D) :=
    ha.trans (congrArg Units.val hb)
  have h1 := hinf (x * Y⁻¹ * (idF D a)⁻¹) (by
    rw [Units.val_mul, RingHom.map_mul, ← hb', ← RingHom.map_mul, Units.mul_inv, RingHom.map_one])
  simpa [hcY, hF a] using h1

end GlobalTheory.FibreIdem

namespace GlobalTheory.FibreIdem

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

end GlobalTheory.FibreIdem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixesUntwistedLiftDataConjugatePrimeValueSqrtNor
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.ConjFix

variable {D : D7}

noncomputable def starOEquiv : 𝓞 D.host.E ≃+* 𝓞 D.host.E :=
  { Formalism.L2.DIV.starOHom (E := D.host.E) with
    invFun := Formalism.L2.DIV.starOHom (E := D.host.E)
    left_inv := fun a => Formalism.L2.DIV.starO_starO a
    right_inv := fun a => Formalism.L2.DIV.starO_starO a }

theorem natCast_mem_conjPl_iff (PP : Pl D.host.E) (N : ℕ) :
    ((N : 𝓞 D.host.E)) ∈ (Formalism.L2.DIV.conjPl PP).asIdeal ↔ ((N : 𝓞 D.host.E)) ∈ PP.asIdeal := by
  show Formalism.L2.DIV.starOHom (N : 𝓞 D.host.E) ∈ PP.asIdeal ↔ _
  rw [map_natCast]

theorem absNorm_conjPl (PP : Pl D.host.E) :
    Ideal.absNorm (Formalism.L2.DIV.conjPl PP).asIdeal = Ideal.absNorm PP.asIdeal := by
  have h : (Formalism.L2.DIV.conjPl PP).asIdeal = PP.asIdeal.map (starOEquiv (D := D)) := by
    rw [← Ideal.comap_symm]; rfl
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv PP.asIdeal (Formalism.L2.DIV.conjPl PP).asIdeal (starOEquiv (D := D)) h).toEquiv).symm

theorem fixBase_split_conj {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (τ : ℂ ≃+* ℂ) (PP : Pl D.host.E) :
    FixBase T R i τ → ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal →
      τ ((((R.C.mu0 i * R.C.eta⁻¹).val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ)) =
        (((R.C.mu0 i * R.C.eta⁻¹).val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ) := by
  intro hF hN
  have hN' : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ (Formalism.L2.DIV.conjPl PP).asIdeal := by
    rwa [natCast_mem_conjPl_iff]
  have := hF.split (Formalism.L2.DIV.conjPl PP) hN'
  rwa [absNorm_conjPl] at this

end GlobalTheory.ConjFix
end

