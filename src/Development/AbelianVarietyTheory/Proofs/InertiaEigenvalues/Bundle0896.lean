module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0878
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0885
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0784
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1635
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0892
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCcIsEquivAtSerOfOneMapRowOfFive
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0544
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0032
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0741
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0738
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0748
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0884
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0871
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedFormSupLatticeFullGroupStableOfEqRational
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0891

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwistedCharacterCocycleOfTorsionLocalCocyc
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

noncomputable section
namespace GlobalTheory.UseLoc.Cases

section Gen1
variable {O : Type} [CommRing O]

def evOneQ (LL : Type) [Field LL] [Algebra O LL] : ((Fin 1 → LL) ⧸ stdG O LL 1) →ₗ[O] (LL ⧸ intO (O := O) LL) :=
  (stdG O LL 1).mapQ (intO (O := O) LL) (LinearMap.proj (R := O) (φ := fun _ : Fin 1 => LL) 0) (by
    rintro _ ⟨u, rfl⟩
    exact ⟨u 0, rfl⟩)

variable {LL : Type} [Field LL] [Algebra O LL]

theorem evOneQ_mk (v : Fin 1 → LL) :
    evOneQ (O := O) LL (Submodule.Quotient.mk v) = Submodule.Quotient.mk (v 0) := rfl

theorem evOneQ_mem {lam : O} {a : ℕ} {q : (Fin 1 → LL) ⧸ stdG O LL 1} (h : lam ^ a • q = 0) :
    evOneQ LL q ∈ Xq LL lam a := by
  show (lam ^ a • (LinearMap.id : (LL ⧸ intO (O := O) LL) →ₗ[O] _)) (evOneQ LL q) = 0
  rw [LinearMap.smul_apply, LinearMap.id_apply, ← map_smul, h, map_zero]

def oneO : ↥(intO (O := O) LL) := ⟨1, 1, map_one (algebraMap O LL)⟩

theorem iotaC_oneO (lam : O) (a : ℕ) (q : (Fin 1 → LL) ⧸ stdG O LL 1) (h : evOneQ LL q ∈ Xq LL lam a) :
    iotaC LL lam a (oneO ⊗ₜ ⟨evOneQ LL q, h⟩) = q := by
  induction q using Submodule.Quotient.induction_on with
  | H v =>
    show iotaG (intO LL) (stdG O LL 1) (constOne LL) (constOne_mem LL) (oneO ⊗ₜ (evOneQ LL (Submodule.Quotient.mk v))) = _
    rw [evOneQ_mk, iotaG_tmul]
    congr 1
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp [constOne, oneO]

def oneT (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] (ψ : G →* Oˣ) : ↥(latOne hinj ψ).T :=
  oneO

theorem actT_latOne_oneT (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] (ψ : G →* Oˣ) (g : G) :
    actT (latOne hinj ψ) g (oneT hinj ψ) = ((ψ g : Oˣ) : O) • oneT hinj ψ := by
  apply Subtype.ext
  show ((tableLineDegreeTwo.charL (LL := LL) ψ g : LLˣ) : LL) • (1 : LL) = ((ψ g : Oˣ) : O) • (1 : LL)
  simp [tableLineDegreeTwo.charL, Algebra.smul_def]

end Gen1

section Gen2
variable {O : Type} [CommRing O] {LL : Type} [Field LL] [Algebra O LL]

theorem actTw_oneO (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] [TopologicalSpace G]
    (X : Type) [AddCommGroup X] [Module O X] (χ ψ : G →* Oˣ) (g : G) (x : X) :
    tableLineDegreeTwo.actTw (latOne hinj ψ) X χ g (oneT hinj ψ ⊗ₜ x) = oneT hinj ψ ⊗ₜ ((((χ g)⁻¹ * ψ g : Oˣ) : O) • x) := by
  rw [tableLineDegreeTwo.actTw, LinearMap.smul_apply, LinearMap.rTensor_tmul, actT_latOne_oneT, TensorProduct.smul_tmul,
    ← TensorProduct.tmul_smul, Units.val_mul, mul_smul]

theorem evOneQ_actD (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] [TopologicalSpace G]
    (N : G →* Matrix (Fin 1) (Fin 1) O) (g : G) (q : (Fin 1 → LL) ⧸ stdG O LL 1) :
    evOneQ LL (actD (stdLatG hinj N) g q) = N g 0 0 • evOneQ LL q := by
  induction q using Submodule.Quotient.induction_on with
  | H v =>
    show evOneQ LL (Submodule.Quotient.mk (matRep (mapM (algebraMap O LL) N) g v)) = _
    rw [evOneQ_mk, evOneQ_mk, ← Submodule.Quotient.mk_smul]
    congr 1
    simp [matRep, mapM, Matrix.mulVec, dotProduct, Algebra.smul_def]

end Gen2

section Gen3
variable {O : Type} [CommRing O] {LL : Type} [Field LL] [Algebra O LL]

theorem liftC_gen (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] [TopologicalSpace G]
    (N : G →* Matrix (Fin 1) (Fin 1) O) (χ ψ : G →* Oˣ) (hN : ∀ g, (((χ g)⁻¹ * ψ g : Oˣ) : O) = N g 0 0)
    (lam : O) (a : ℕ) (f : G → (Fin 1 → LL) ⧸ stdG O LL 1) (hf : f ∈ divisibleCocycles (stdLatG hinj N))
    (htor : ∀ g, lam ^ a • f g = 0) :
    ∃ z' : G → ↥(latOne hinj ψ).T ⊗[O] ↥(Xq LL lam a),
      tableLineDegreeTwo.IsCoc (latOne hinj ψ) ↥(Xq LL lam a) χ z' ∧ ∀ g, iotaC LL lam a (z' g) = f g := by
  classical
  obtain ⟨hlc, hco⟩ := hf
  let F : ((Fin 1 → LL) ⧸ stdG O LL 1) → ↥(latOne hinj ψ).T ⊗[O] ↥(Xq LL lam a) :=
    fun q => if hq : lam ^ a • q = 0 then oneT hinj ψ ⊗ₜ ⟨evOneQ LL q, evOneQ_mem hq⟩ else 0
  refine ⟨fun g => oneT hinj ψ ⊗ₜ ⟨evOneQ LL (f g), evOneQ_mem (htor g)⟩, ⟨?_, ?_⟩, ?_⟩
  · have hF : (fun g => oneT hinj ψ ⊗ₜ[O]
        (⟨evOneQ LL (f g), evOneQ_mem (htor g)⟩ : ↥(Xq LL lam a))) = F ∘ f := by
      funext g
      simp only [F, Function.comp_apply, dif_pos (htor g)]
    rw [hF]
    exact hlc.comp F
  · intro g h
    beta_reduce
    rw [actTw_oneO, ← TensorProduct.tmul_add]
    congr 1
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_smul]
    rw [hco g h, hN g]
    exact ((evOneQ LL).map_add _ _).trans (congrArg (evOneQ LL (f g) + ·) (evOneQ_actD hinj N g (f h)))
  · intro g
    exact iotaC_oneO lam a (f g) _

end Gen3

section AtW
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}

theorem locOC_chiRatO_apply (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (c : ℕ) (g : Br.G D.nbr i w hw) :
    locOC C (chiRatO D.nd i c) g 0 0 =
      ((chiOC C (chiU D.nd i c * (chiU D.nd i 1)⁻¹) g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) := by
  simp [locOC, chiOC, Br.locO, Br.iota, mapM, chiRatO, twistM]

theorem chiT_one_eq_theta (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) : chiT C θ 1 = θ := by
  simp [chiT, chiOC]

theorem chiT_ratio (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c : ℕ)
    (g : Br.G D.nbr i w hw) :
    (((chiT C θ 1 g)⁻¹ * chiT C θ c g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) = locOC C (chiRatO D.nd i c) g 0 0 := by
  rw [locOC_chiRatO_apply, chiT_one_eq_theta]
  congr 1
  simp only [chiT, MonoidHom.mul_apply]
  rw [mul_comm, mul_assoc, mul_inv_cancel, mul_one]

end AtW

theorem liftC_main : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (c a : ℕ) (f : Br.G D.nbr i w hw → (Fin 1 → ↥C.LL.1) ⧸ stdG ↥(OL C.LL) ↥C.LL.1 1),
    f ∈ divisibleCocycles (latC C (locOC C (chiRatO D.nd i c))) → (∀ g, lam ^ a • f g = 0) →
    ∃ z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a),
      tableLineDegreeTwo.IsCoc (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' ∧
      ∀ g, iotaC ↥C.LL.1 lam a (z' g) = f g := by
  intro D i w hw C lam _ θ c a f hf htor
  exact liftC_gen Subtype.val_injective (locOC C (chiRatO D.nd i c)) (chiT C θ 1) (chiT C θ c) (chiT_ratio C θ c)
    lam a f hf htor

end GlobalTheory.UseLoc.Cases

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsVacuumIdentityConstantsUniformisedCover
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.CoverCc

theorem exists_ccIs_cover : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, C.IsUnif → ∃ cc : C.U₂.Comp → ℂ, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) C.U₂ (castDict hV C.dict₂) (castDict hV (T.mu ((i : ℕ) + 1) T.σ₀)) (T.x₀ ((i : ℕ) + 1) T.σ₀) (R.ωP i A.μ0) (R.vacP i) cc := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL hlev hgrp hfam hmods hthP hT i hstd hV C hC
  have hC5 : GlobalTheory.Core5 R F := ⟨hlev, hgrp, hfam, hmods, hthP⟩
  have hσ0 : GoodEmb T.Q.c T.σ₀ := rfl
  obtain ⟨hP, hV0, h1, h2, h3, h4, h5⟩ :=
    GlobalTheory.AdTh.RecPair.isPair_record_ofFive D G Pl0 T0 A _ R F hC5 i A.μ0 hstd
  have hM := GlobalTheory.AdTh.models_at_record_ofFive D G Pl0 T0 A T R F κ v₀ hC5 hT i T.σ₀ rfl
  have hχ : (Lift.chrTh (R.toLevCh.mu A.μ0) R.eta ((i : ℕ) + 1)).1 = T.chiW ((i : ℕ) + 1) T.σ₀ := by
    rw [chiTie_of_chiR T R hT.alg hT.laws.pins.2.2.1 hT.chiR i]
    ext1 x
    change R.mu0 _ x * R.xi A.μ0 x = _
    rw [TwistFactorCompare.eq_one_of_chrEq_one (χ := R.xi A.μ0) (hC5.lev.xi_base ▸ hC5.lev.xi A.μ0) x, mul_one]
  have hcast : ∀ (W : HSp D) (hV : T.V ((i : ℕ) + 1) T.σ₀ = W),
      MuVal W (T.chiW ((i : ℕ) + 1) T.σ₀) (castDict hV (T.mu ((i : ℕ) + 1) T.σ₀)) ∧ ∀ γ ∈ GQ W, ∀ h,
        castDict hV (T.mu ((i : ℕ) + 1) T.σ₀) (γ * h) = castDict hV (T.mu ((i : ℕ) + 1) T.σ₀) h := by
    intro W hV
    subst hV
    have hu := hT.laws.muUnit _ (inR i) _ hσ0
    exact ⟨hT.laws.muVal _ (inR i) _ hσ0, fun γ hγ h => (hu.1 γ h).trans (by rw [hu.2.2.1 γ hγ, one_mul]; rfl)⟩
  obtain ⟨hmu, hmuQ⟩ := hcast _ hV
  obtain ⟨-, -, -, -, -, -, hr1, hrt, -, -, hdom, -⟩ := hM (T.dict ((i : ℕ) + 1) T.σ₀ 1).1
  obtain ⟨hD, hFT, -, hσ₂⟩ := _root_.GlobalTheory.LevelSeries.cover_dict_frameTie D G Pl0 T0 A T R F κ v₀ hL hlev hgrp hfam hmods hthP hT i hstd hV C hC
  exact GlobalTheory.AdTh.CcEx.exists_ccIs_of_pair GlobalTheory.chartIndependence_unconditional hP (hχ ▸ hmu) hmuQ (rank_Wc i) hrt
    C.U₂ hσ₂ hC.2.2.2.1 hr1 hC.2.1 hdom hV0 h1 h2 h3 h4 h5 _ _ hD.2.2.1 (fun k τ => hD.2.2.2.1 k τ.1 τ.2)
    (fun k => (hFT k).1) (hC5.thP.vP i A.μ0).1 _

end GlobalTheory.CoverCc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLambdaPowerTorsionFieldModInt
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

namespace GlobalTheory.UseLoc.Cases

theorem finite_Xq {l : ℕ} [Fact l.Prime] (LL : FinExt l) (lam : ↥(OL LL)) (hlam : Irreducible lam) (a : ℕ) :
    Finite ↥(Xq ↥LL.1 lam a) := by
  classical
  haveI := GlobalTheory.FullCharpoly.hasFiniteQuotients_OL LL
  have hinj : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  have hne : lam ^ a ≠ 0 := pow_ne_zero _ hlam.ne_zero
  have hK : algebraMap ↥(OL LL) ↥LL.1 (lam ^ a) ≠ 0 := by
    intro h; exact hne (hinj (by rw [h, map_zero]))
  haveI : Finite (↥(OL LL) ⧸ Ideal.span {lam ^ a}) := Ring.HasFiniteQuotients.finiteQuotient (by
    rwa [Ne, Ideal.span_singleton_eq_bot])
  have hex : ∀ x : ↥(Xq ↥LL.1 lam a), ∃ c : ↥(OL LL), ∃ s : ↥LL.1,
      Submodule.Quotient.mk (p := intO (O := ↥(OL LL)) ↥LL.1) s = x.1 ∧ algebraMap ↥(OL LL) ↥LL.1 c = lam ^ a • s := by
    intro x
    obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ x.1
    have hx := x.2
    simp only [Xq, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] at hx
    rw [← hs, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨c, hc⟩ := hx
    exact ⟨c, s, hs, hc⟩
  let f : ↥(Xq ↥LL.1 lam a) → ↥(OL LL) ⧸ Ideal.span {lam ^ a} := fun x => Ideal.Quotient.mk _ (hex x).choose
  refine Finite.of_injective f ?_
  intro x y hxy
  obtain ⟨s, hs, hc⟩ := (hex x).choose_spec
  obtain ⟨t, ht, hd⟩ := (hex y).choose_spec
  have h1 := hxy
  simp only [f, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at h1
  obtain ⟨d, hd'⟩ := h1
  apply Subtype.ext
  rw [← hs, ← ht, ← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
  refine ⟨d, ?_⟩
  have h2 : algebraMap ↥(OL LL) ↥LL.1 (lam ^ a) * (s - t) = algebraMap ↥(OL LL) ↥LL.1 (lam ^ a) * algebraMap ↥(OL LL) ↥LL.1 d := by
    rw [← map_mul, mul_comm (lam ^ a) d, hd', map_sub, hc, hd, Algebra.smul_def, Algebra.smul_def, mul_sub]
  have := mul_left_cancel₀ hK h2
  simp only [Algebra.linearMap_apply]
  exact this.symm

end GlobalTheory.UseLoc.Cases
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeQuotientIntegralFramedPointCompleteField
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.GeoTie
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HeckeStableAt

theorem heckeStable : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T1 : Type)
    (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T1 D.R.m) (T0 : CoreJ D) [Algebra T0.Q.c.F D.what₂.LL]
    (Rl : RealDat3 D A3 T0.Q.c.F) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw)
    (YS : NX.NExpRealS Rl cG S) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1))
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (fw : FWTie T0 Rl.toRealDat κ v₀) (i : D.ntw.Tw)
    (iC : FractionRing (D.ntw.O i) →+* ℂ_[D.ntw.l i]),
    (∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).range) →
    ∀ (b : Bool) (j : Fin D.R.m), HeckeStable YS iC b j := by
  intro hI D Γ _ _ Pl0 I0 T1 A3 T0 _ Rl cG S YS κ v₀ fw i iC _ b j k P hk z C
  obtain ⟨hHP, hne⟩ := GlobalTheory.T.isSplitHeckePrimeOffLevel_of_heckeIndexPlace D T0 fw.laws i k P hk
  have hP' := GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.isHeckePrime_iff.2 hHP
  obtain ⟨z', hz'⟩ := GlobalTheory.HeckePointLaw.heckePointLaws.2.1 D.host.E T0.Q.H (T0.Q.Dw ((j : ℕ) + 1)) T0.Q.l
    (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c P.asIdeal (charAt P) k hP' (PAt (embC YS iC b)) z.1 C
  obtain ⟨T, io, kk, h, y, u, hy, hu, w, hw, hb⟩ := z.2
  obtain ⟨C₀, w', hw', hb'⟩ := GlobalTheory.T.heckeQuotient_frame_change_of_triangular_frame_change _ _ _ _ _ _ P.asIdeal (charAt P) k hHP _ u w z.1 hb C z' hz'
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_ramification_overPlace_of_cdvrReadingInCp (D.ntw.l i) T0.Q.c.F (embC YS iC b) T io kk h
  have hpla : ((charAt P : ℕ) : 𝓞 T0.Q.c.F) ∉ (placeAt (embC YS iC b)).asIdeal := by
    intro hm
    have hl := natCast_mem_placeAt (embC YS iC b)
    have hcop : Nat.Coprime (charAt P) (D.ntw.l i) :=
      (Nat.coprime_primes (charAt_prime P) (Fact.out : (D.ntw.l i).Prime)).2 hne
    obtain ⟨a, c, hac⟩ : IsCoprime ((charAt P : ℕ) : 𝓞 T0.Q.c.F) ((D.ntw.l i : ℕ) : 𝓞 T0.Q.c.F) :=
      Nat.Coprime.cast hcop
    exact (placeAt (embC YS iC b)).isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hac ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ hl)))
  letI := io.toAlgebra
  have hint := GlobalTheory.T.heckePoint_integral_upToUnits_anyAlgClosedField hI D.host.E T0.Q.H (T0.Q.Dw ((j : ℕ) + 1)) T0.Q.l (T0.Q.Xo ((j : ℕ) + 1)) T0.Q.c
    (placeAt (embC YS iC b)) P.asIdeal (charAt P) k hHP hpla T io e he y hy (PAt (embC YS iC b)) h.alg w hw C₀ w' hw'
  obtain ⟨T', i', hi', j', hj', y', hy', -, w2, u2, hw2, hb2⟩ := hint
  letI := (i'.comp io).toAlgebra
  let jj : T'.Fr →+* ℂ_[D.ntw.l i] := (toCp (embC YS iC b)).comp j'.toRingHom
  have hjj : jj.comp i' = kk := RingHom.ext fun a => congrArg (toCp (embC YS iC b)) (DFunLike.congr_fun hj' a)
  have hR := _root_.GlobalTheory.GeoTie.ReadExt.isReading_ext (D.ntw.l i) T0.Q.c.F (embC YS iC b) T io kk h T' i' hi' jj hjj
  have hRa : hR.alg = j' := AlgHom.ext fun _ => rfl
  let u2' : Ix (T0.Q.Dw ((j : ℕ) + 1)) → (PAt (embC YS iC b))ˣ :=
    fun a => Units.map (j'.toRingHom.comp (algebraMap T'.V T'.Fr)).toMonoidHom (u2 a)
  have hbor := (GlobalTheory.Frames.frBor_calculus _ _ _ _ _ _ _ w2 w' z').2.2.1 u2' u hb2 hb'
  have hunit : ∀ a, ‖toCp (embC YS iC b) (u2' a)‖ = 1 := fun a => by
    have h1 : ‖jj (algebraMap T'.V T'.Fr (u2 a : T'.V))‖ ≤ 1 := (hR.int _).2 ⟨_, rfl⟩
    have h2 : ‖jj (algebraMap T'.V T'.Fr ((u2 a)⁻¹ : T'.Vˣ))‖ ≤ 1 := (hR.int _).2 ⟨_, rfl⟩
    have h3 : jj (algebraMap T'.V T'.Fr (u2 a : T'.V)) * jj (algebraMap T'.V T'.Fr ((u2 a)⁻¹ : T'.Vˣ)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have h4 := congrArg norm h3
    rw [norm_mul, norm_one] at h4
    have h5 : ‖jj (algebraMap T'.V T'.Fr (u2 a : T'.V))‖ = 1 := by
      refine le_antisymm h1 (by_contra fun hlt => ?_)
      push_neg at hlt
      have : ‖jj (algebraMap T'.V T'.Fr (u2 a : T'.V))‖ * ‖jj (algebraMap T'.V T'.Fr ((u2 a)⁻¹ : T'.Vˣ))‖ < 1 :=
        (mul_le_of_le_one_right (norm_nonneg _) h2).trans_lt hlt
      exact this.ne h4
    exact h5
  have hnorm : ∀ a, ‖toCp (embC YS iC b) ((u * u2') a)‖ = 1 := fun a => by
    rw [Pi.mul_apply, Units.val_mul, map_mul, norm_mul, hu a, hunit a, one_mul]
  refine ⟨⟨z', T', i'.comp io, jj, hR, y', u * u2', hy', hnorm, w2, hRa ▸ hw2, hbor⟩, hz'⟩

end GlobalTheory.HeckeStableAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBlochKatoReadOfTensorSelmerAddCoboundary
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

noncomputable section

namespace GlobalTheory.UseLoc.Cases

theorem chiT_one_eq {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) : chiT C θ 1 = θ := by
  simp [chiT, chiOC]

section GenRead

variable {O : Type} [CommRing O] {LL : Type} [Field LL] [Algebra O LL] {k : ℕ}

def iotaL (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G]
    (M N : G →* Matrix (Fin k) (Fin k) O) (lam : O) (a : ℕ) :
    ↥(stdLatG (LL := LL) hinj M).T ⊗[O] ↥(Xq LL lam a) →ₗ[O] (Fin k → LL) ⧸ (stdLatG (LL := LL) hinj N).T :=
  iotaW LL lam a k

theorem iotaL_tmul (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G]
    (M N : G →* Matrix (Fin k) (Fin k) O) (lam : O) (a : ℕ) (t : ↥(stdLatG (LL := LL) hinj M).T)
    (x : ↥(Xq LL lam a)) (s : LL) (hs : Submodule.Quotient.mk s = (x : LL ⧸ intO (O := O) LL)) :
    iotaL hinj M N lam a (t ⊗ₜ x) = Submodule.Quotient.mk (s • (t : Fin k → LL)) := by
  obtain ⟨x, hx⟩ := x
  change Submodule.Quotient.mk s = x at hs
  subst hs
  rfl

theorem matRep_twistM_apply {G : Type} [Group G] (N : G →* Matrix (Fin k) (Fin k) O) (θ : G →* Oˣ) (g : G)
    (v : Fin k → LL) :
    matRep (mapM (algebraMap O LL) (twistM N θ)) g v = ((θ g : Oˣ) : O) • matRep (mapM (algebraMap O LL) N) g v := by
  have hM : (mapM (algebraMap O LL) (twistM N θ)) g =
      algebraMap O LL ((θ g : Oˣ) : O) • (mapM (algebraMap O LL) N) g := by
    ext p q
    simp [mapM, twistM, Matrix.smul_apply, smul_eq_mul, map_mul]
  change ((mapM (algebraMap O LL) (twistM N θ)) g).mulVec v = ((θ g : Oˣ) : O) • ((mapM (algebraMap O LL) N) g).mulVec v
  rw [hM, Matrix.smul_mulVec, algebraMap_smul]

theorem actD_iotaL (hinj : Function.Injective (algebraMap O LL)) {G : Type} [Group G] [TopologicalSpace G]
    (N : G →* Matrix (Fin k) (Fin k) O) (θ χ : G →* Oˣ) (hχ : ∀ g, (((χ g)⁻¹ : Oˣ) : O) * ((θ g : Oˣ) : O) = 1)
    (lam : O) (a : ℕ) (g : G) (y : ↥(stdLatG (LL := LL) hinj (twistM N θ)).T ⊗[O] ↥(Xq LL lam a)) :
    actD (stdLatG hinj N) g (iotaL hinj (twistM N θ) N lam a y) =
      iotaL hinj (twistM N θ) N lam a (tableLineDegreeTwo.actTw (stdLatG hinj (twistM N θ)) ↥(Xq LL lam a) χ g y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add u v hu hv => simp only [map_add (f := _), hu, hv]
  | tmul t x =>
    obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ (x : LL ⧸ intO (O := O) LL)
    rw [tableLineDegreeTwo.actTw, LinearMap.smul_apply, LinearMap.rTensor_tmul, map_smul, iotaL_tmul hinj _ N lam a _ x s hs,
      iotaL_tmul hinj _ N lam a _ x s hs, ← Submodule.Quotient.mk_smul]
    change Submodule.Quotient.mk (matRep (mapM (algebraMap O LL) N) g (s • (t : Fin k → LL))) =
      Submodule.Quotient.mk ((((χ g)⁻¹ : Oˣ) : O) • s • matRep (mapM (algebraMap O LL) (twistM N θ)) g (t : Fin k → LL))
    congr 1
    rw [matRep_twistM_apply, LinearMap.map_smul, smul_comm _ s, ← mul_smul, hχ g, one_smul]

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [Algebra Qp LL]
    [TopologicalSpace (Fin k → LL)] [ContinuousAdd (Fin k → LL)] [ContinuousConstSMul LL (Fin k → LL)]

theorem readW_gen (PD : PeriodData G Qp K₀ K B BdR) (hinj : Function.Injective (algebraMap O LL))
    (N : G →* Matrix (Fin k) (Fin k) O) (θ χ : G →* Oˣ) (hχ : ∀ g, (((χ g)⁻¹ : Oˣ) : O) * ((θ g : Oˣ) : O) = 1)
    (lam : O) (a : ℕ) (z' : G → ↥(stdLatG (LL := LL) hinj (twistM N θ)).T ⊗[O] ↥(Xq LL lam a))
    (hz : tableLineDegreeTwo.InHfX PD (stdLatG (LL := LL) hinj (twistM N θ)) (stdLatG hinj N) ↥(Xq LL lam a) χ z') :
    (fun g => iotaL hinj (twistM N θ) N lam a (z' g)) ∈ HfD PD (stdLatG (LL := LL) hinj N) := by
  obtain ⟨n, c, x, m, hc, hz⟩ := hz
  choose s hs using fun j => Submodule.Quotient.mk_surjective _ (x j : LL ⧸ intO (O := O) LL)
  have e : (fun g => iotaL hinj (twistM N θ) N lam a (z' g)) =
      (∑ j, LinearMap.compLeft (stdLatG (LL := LL) hinj N).T.mkQ G (s j • fun g => (c j g : Fin k → LL))) +
        LinearMap.pi (fun g => actD (stdLatG (LL := LL) hinj N) g - LinearMap.id)
          (iotaL hinj (twistM N θ) N lam a m) := by
    funext g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hz g, map_add (f := _), map_sum, map_sub, ← actD_iotaL hinj N θ χ hχ lam a g m]
    simp only [Pi.add_apply, Finset.sum_apply, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iotaL_tmul hinj _ N lam a _ (x j) (s j) (hs j)]
    rfl
  rw [e]
  refine add_mem (Submodule.sum_mem _ fun j _ => Submodule.mem_sup_left (Submodule.mem_map_of_mem ?_))
    (Submodule.mem_sup_right (LinearMap.mem_range_self _ _))
  exact (Submodule.restrictScalars_mem O _ _).2 ((finiteCocycles PD _).smul_mem (s j) (hc j).2)

end GenRead

theorem chiT_one_inv_mul {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
    (g : Br.G D.nbr i w hw) :
    (((chiT C θ 1 g)⁻¹ : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) * ((θ g : (↥(OL C.LL))ˣ) : ↥(OL C.LL)) = 1 := by
  rw [chiT_one_eq]
  simp

theorem readW_main : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)) {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL))
    (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (a : ℕ) (z' : Br.G D.nbr i w hw → ↥(latC C (twistM N θ)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.InHfX (Br.PD D.loc D.nbr i w hw) (latC C (twistM N θ)) (latC C N) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) z' →
    (fun g => iotaW ↥C.LL.1 lam a k (z' g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C N) := by
  intro D i w hw C lam k N θ a z' hz
  exact readW_gen (Br.PD D.loc D.nbr i w hw) Subtype.val_injective N θ (chiT C θ 1) (chiT_one_inv_mul C θ) lam a z' hz

end GlobalTheory.UseLoc.Cases

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupLawsOfSides
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs

theorem supLaws_of_sides (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E)
    (h : ∀ j, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt X.core X.R.toRealDat j) :
    SupG D ∧ SupFull D ∧ SupHk D ∧ CommG D ∧ HkComm D := by
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.SupEq.supG_supFull_of_eq D X.Γ X.Pl0 X.I0 X.T X.A3 X.core.Q.c.F X.R X.cG Y.S Y.YS Y.sup X.integral
  obtain ⟨h3, h4⟩ := _root_.GlobalTheory.TwInputs.supHk_commG D X E Y h
  exact ⟨h1, h2, h3, h4, _root_.GlobalTheory.SupLaw.hkComm_of_ties D X E Y⟩

end GlobalTheory.TwInputs
end

