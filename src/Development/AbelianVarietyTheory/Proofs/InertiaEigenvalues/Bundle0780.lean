module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResFinEqOneOfAway
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1641
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0436
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1649
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0771

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterTrivialOnSubfieldOfIdelicReading
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Links NumberField IsDedekindDomain
open Formalism.L2.JoinChr Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TrivOnRead

section General

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem infIdele_snd_one {K : Type} [Field K] [NumberField K] (w : InfinitePlace K) (x : (w.Completion)ˣ) :
    (infIdele K w x : AdeleRing (𝓞 K) K).2 = 1 := rfl

theorem fst_prod_apply {K : Type} [Field K] [NumberField K] {ι : Type} (s : Finset ι) (f : ι → AdeleRing (𝓞 K) K)
    (w : InfinitePlace K) : (∏ i ∈ s, f i).1 w = ∏ i ∈ s, (f i).1 w :=
  map_prod ((Pi.evalMonoidHom (fun v : InfinitePlace K => v.Completion) w).comp
    (MonoidHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))) f s

theorem snd_prod {K : Type} [Field K] [NumberField K] {ι : Type} (s : Finset ι) (f : ι → AdeleRing (𝓞 K) K) :
    (∏ i ∈ s, f i).2 = ∏ i ∈ s, (f i).2 :=
  map_prod (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)) f s

theorem ideleMap_inf (w : InfinitePlace F) (k : Fˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap F E (infIdele F w (atInf w k)) = CharEx.aFi (L := E) F w k := by
  classical
  refine Units.ext (Prod.ext (funext fun w' => ?_) ?_)
  · show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E (infIdele F w (atInf w k) : AdeleRing (𝓞 F) F).1 w' = _
    rw [CharEx.aFi, Units.coe_prod, fst_prod_apply]
    change AbsoluteValue.Completion.map (w'.comap (algebraMap F E)).1 w'.1
      ((infIdele F w (atInf w k) : AdeleRing (𝓞 F) F).1 (w'.comap (algebraMap F E))) = _
    by_cases hw : w'.comap (algebraMap F E) = w
    · have hm : w' ∈ aboveInf (L := E) F w := by simp [aboveInf, hw]
      rw [Finset.prod_eq_single_of_mem w' hm (fun w'' _ h => infIdele_fst_ne E w'' w' (Ne.symm h) _),
        infIdele_fst_self]
      subst hw
      rw [infIdele_fst_self]
      change AbsoluteValue.Completion.map (w'.comap (algebraMap F E)).1 w'.1
        (algebraMap F _ (k : F)) = algebraMap E _ (algebraMap F E (k : F))
      rw [InfinitePlace.Completion.algebraMap_apply, InfinitePlace.Completion.algebraMap_apply,
        AbsoluteValue.Completion.map_coe]
      rfl
    · rw [infIdele_fst_ne F w _ hw, map_one]
      refine (Finset.prod_eq_one fun w'' hw'' => infIdele_fst_ne E w'' w' ?_ _).symm
      rintro rfl
      simp [aboveInf] at hw''
      exact hw hw''
  · show GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap F E (infIdele F w (atInf w k) : AdeleRing (𝓞 F) F).2 = _
    rw [CharEx.aFi, Units.coe_prod, snd_prod]
    rw [Finset.prod_eq_one fun w'' _ => infIdele_snd_one w'' _]
    exact map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap F E)

end General


open GlobalTheory.CharTransport in
set_option maxHeartbeats 800000 in
theorem exists_hom_tmul (D : D7) : ∃ Θ : AE D →+* AdeleRing (𝓞 D.host.E) D.host.E, Continuous Θ ∧
    (∀ a x, Θ (a ⊗ₜ[D.host.F] x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap D.host.F D.host.E a * algebraMap D.host.E _ x) ∧
    (∀ x, Θ (incA D x) = algebraMap D.host.E _ x) ∧
    ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : AE D), IsPlIdem D e P → ∀ k : D.host.Eˣ,
      Θ (locE D e (k : D.host.E)) =
        ((localIdele D.host.E P (atFin P k) : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E) := by
  obtain ⟨Θ, hc, hΘ⟩ := exists_toAdele D.host.F D.host.E
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have hinc : ∀ x, Θ (incA D x) = algebraMap D.host.E _ x := fun x => by
    change Θ ((1 : AF D.host.F) ⊗ₜ[D.host.F] x) = _
    rw [hΘ, map_one, one_mul]
  have hfin : ∀ z, (Θ z).2 = Φ z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [RingHom.map_zero, RingHom.map_zero]; rfl
    | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ← hx, ← hy]; rfl
    | tmul a x =>
      have e : (a ⊗ₜ[D.host.F] x : AE D) = algebraMap (AF D.host.F) (AE D) a * incA D x := by
        change _ = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hΘ, e, RingHom.map_mul, hΦ.inc]
      refine FiniteAdeleRing.ext _ fun Q => ?_
      change _ = Φ _ Q * _
      rw [hΦ.base, locMap_eq]
      rfl
  have hinf : ∀ z, infPart D z = 0 → (Θ z).1 = 0 := fun z hz => by
    let u : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0)
    have h1 : u * z = 0 := by
      refine GlobalTheory.PlaceIdem.parts_inj D _ _ ?_ ?_
      · rw [RingHom.map_mul, hz, mul_zero, RingHom.map_zero]
      · have : finPart D u = 0 := TensorProduct.zero_tmul _ _
        rw [RingHom.map_mul, this, zero_mul, RingHom.map_zero]
    have h2 : (Θ u).1 = 1 := by
      change (Θ (pairA D.host.F 1 0 ⊗ₜ[D.host.F] (1 : D.host.E))).1 = 1
      rw [hΘ, map_one, mul_one]
      exact map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap D.host.F D.host.E)
    have h3 : (Θ u).1 * (Θ z).1 = 0 := by
      change (Θ u * Θ z).1 = 0
      rw [← RingHom.map_mul, h1, RingHom.map_zero]
      rfl
    rwa [h2, one_mul] at h3
  refine ⟨Θ, hc, hΘ, hinc, fun P e he k => ?_⟩
  obtain ⟨d0, d1, d2⟩ := isDelta_of_isPlIdem hΦ he
  have hl : Θ (locE D e (k : D.host.E)) =
      1 + Θ e * (algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E) (k : D.host.E) - 1) :=
    (map_loc Θ e (incA D (k : D.host.E))).trans (by rw [hinc])
  rw [hl]
  refine Prod.ext ?_ (FiniteAdeleRing.ext _ fun Q => ?_)
  · change 1 + (Θ e).1 * _ = 1
    rw [hinf e d0, zero_mul, add_zero]
  · classical
    change 1 + (Θ e).2 Q * (algebraMap D.host.E (Q.adicCompletion D.host.E) (k : D.host.E) - 1) =
      Function.update (fun w : HeightOneSpectrum (𝓞 D.host.E) => (1 : w.adicCompletion D.host.E)) P
        (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) Q
    rw [hfin]
    by_cases hQ : Q = P
    · subst hQ
      rw [d1, Function.update_self]
      ring
    · rw [d2 Q hQ, Function.update_of_ne hQ]
      ring

theorem trivOn_of_chrEq : ∀ (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ →
    (∀ a : (AF D.host.F)ˣ, c (idF D a) = 1) → χ.TrivOn D.host.F := by
  intro D c χ hc ha
  have hχ := GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D c χ hc
  obtain ⟨Θ, hΘc, hΘt, hinc, hloc⟩ := exists_hom_tmul D
  let u : (AE D)ˣ →* Ideles D.host.E := Units.map Θ.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΘc
  let c' : (AE D)ˣ →* Circle :=
    { toFun := fun x => ⟨((χ.1 (u x) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hχ _)⟩
      map_one' := Circle.ext (by simp)
      map_mul' := fun x y => Circle.ext (by
        change ((χ.1 (u (x * y)) : ℂˣ) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) * ((χ.1 (u y) : ℂˣ) : ℂ)
        rw [map_mul, map_mul, Units.val_mul]) }
  have hcoe : ∀ x, ((c' x : Circle) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) := fun x => rfl
  have hc' : ChrEq c' χ := by
    refine ⟨⟨?_, fun x => Circle.ext ?_⟩, fun P e he k x hx => ?_⟩
    · exact Continuous.subtype_mk (Units.continuous_val.comp (χ.2.1.comp hu)) _
    · have : u (Units.map (incA D).toMonoidHom x) = diagUnits D.host.E x := Units.ext (hinc x)
      rw [hcoe, this, χ.2.2]
      rfl
    · have : u x = localIdele D.host.E P (atFin P k) := by
        refine Units.ext ?_
        change Θ (x : AE D) = _
        rw [hx, hloc P e he]
      rw [hcoe, this]
      rfl
  have hcc : c = c' := GlobalTheory.ChrEqUnique.idc_unique D c c' χ hc hc'
  have key : ∀ a : (AF D.host.F)ˣ, χ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap D.host.F D.host.E a) = 1 := fun a => by
    have h1 : u (idF D a) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap D.host.F D.host.E a := Units.ext (by
      change Θ ((a : AF D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) = _
      rw [hΘt, map_one, mul_one]
      rfl)
    have h2 := hcoe (idF D a)
    rw [← hcc, ha, h1] at h2
    exact Units.ext (by rw [← h2]; rfl)
  refine ⟨fun v k => ?_, fun w k => ?_⟩
  · rw [CharEx.resFin_eq]
    change χ.1 (GlobalTheory.Mem.Chr.locF D.host.F v k) = 1
    rw [← GlobalTheory.ToricDistribution.ideleMap_local]
    exact key _
  · rw [CharEx.resInf_eq, ← ideleMap_inf]
    exact key _

end GlobalTheory.TrivOnRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IoPOfIsIoWAt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.JointHarm
open scoped Classical

namespace GlobalTheory.IoAllTuples


set_option maxHeartbeats 1000000 in
theorem ioP_of_isIoW_at : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → R.thP_ωP → R.thP_vP → ∀ (i : Fin D.R.m) (t₀ : T) (y : LowT (R.MW i (sg0 D A)) →ₗ[ℂ] (R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), IsIoW R.θ (R.MW i (sg0 D A)) (R.cV i) (R.ωP i t₀) (R.ptP i t₀) (RealDat.Delta i) y → R.PIoP i y := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hF hM hω hv i t₀ y hy
  have hθ : IsInfFam R.θ := hM.inf
  have hth : ∀ t, IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := fun t => by
    obtain ⟨⟨hψ, h0⟩, e, -, h⟩ := hv i t
    exact GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ h h0.theta
  have hvac := fun t => GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (hv i t) (hth t)
  have hne : R.vP i t₀ ≠ 0 :=
    GlobalTheory.AdTh.VecNe.thPVec_ne_zero (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βV i))
      (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βW i))
      ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2).trans_le (r_le_V i)) (hv i t₀)
  have hinj : Function.Injective (R.ptP i t₀) :=
    GlobalTheory.FockIndep.pureTensorO_injective D R.ψ R.θ _ _ _ (R.MW i (sg0 D A)) (R.BV i) _ (hω i t₀).std hθ
      (fun τ => GlobalTheory.OneMapRef.VecP.isCartanInv_one_of_onb (hM.BV i τ)) (hM.BV i) (hth t₀) hne (hvac t₀)
  have hBS : ∀ τ, (R.BV i τ)ᴴ * gramAt D (Vc D i) τ * R.BV i τ = 1 := fun τ => GlobalTheory.JointHarm.onb_eq_one (hM.BV i τ)
  obtain ⟨x₁, x₂, x₃, hx⟩ := GlobalTheory.T.lowestKType_coefficientWeight_eq_minorWeights D i (sg0 D A) (sgAt_mk _ R.hv0) (R.MW i (sg0 D A)) (hM.order i)
  have hrk : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hpq : ∀ τ, ((Wc D i).sig (tauE D τ)).1 + ((Wc D i).sig (tauE D τ)).2 = (Wc D i).rank := fun τ =>
    (_root_.GlobalTheory.PairWeightArith.arithAt D i τ).rank.1.trans hrk.symm
  have hact := fun t => _root_.GlobalTheory.FockCompactAction.om_pureTensorO_eq_fact D R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) _ (R.MW i (sg0 D A)) (R.BV i) (hω i t) hθ
    (D.sp.V_sig _) (D.sp.W_sig _) hBS _ _ hpq (hM.order i) _ _ (fun τ => (_root_.GlobalTheory.PairInfTypes.infTypesAt D T R.toLevCh A.μ0 hL i t τ).chiV)
    (fun τ => (_root_.GlobalTheory.PairInfTypes.infTypesAt D T R.toLevCh A.μ0 hL i t τ).chiW) x₁ x₂ x₃ (fun τ => (hx τ).1) (fun τ => (hx τ).2.1)
    (fun τ => (hx τ).2.2.1) _ (hth t) (hvac t)
  obtain ⟨y1, y2, y3⟩ := hy
  intro t
  refine ⟨fun u hu x w => ?_, fun τ k hk v u hu w => ?_, y3⟩
  · have hK : ∀ τ, (R.MW i (sg0 D A)).fr τ * compAt R.θ τ (Formalism.L2.Theta.mt (Wc D i) 1) * ((R.MW i (sg0 D A)).fr τ)⁻¹ ∈
        Formalism.REAL.Kset ((R.MW i (sg0 D A)).ε τ) := fun τ => by
      rw [compAt_mt_one', Matrix.mul_one,
        Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 ((R.MW i (sg0 D A)).fr_unit τ))]
      exact one_mem_K
    have a0 := ((hact t₀) u hu 1 (one_mem _) hK).2 (y x w)
    have at' := ((hact t) u hu 1 (one_mem _) hK).2 (y x w)
    have e := hinj (a0.symm.trans (y1 u hu x w))
    exact at'.trans (congrArg (R.ptP i t) e)
  · have hs := GlobalTheory.PointAtPlaceHom.atTau_spec hθ (Wc D i) τ (GlobalTheory.JointHarm.conj_mem_UH (R.MW i (sg0 D A)) τ hk)
    have hfr : ∀ ρ, (R.MW i (sg0 D A)).fr ρ * ((R.MW i (sg0 D A)).fr ρ)⁻¹ = 1 := fun ρ =>
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 ((R.MW i (sg0 D A)).fr_unit ρ))
    have e : (fun ρ => (R.MW i (sg0 D A)).fr ρ * compAt R.θ ρ (Formalism.L2.Theta.mt (Wc D i)
        (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ))) *
        ((R.MW i (sg0 D A)).fr ρ)⁻¹) = Pi.mulSingle τ k := by
      funext ρ
      rw [GlobalTheory.WeilDeriv.compAt_mt_eq_infMat]
      by_cases h : ρ = τ
      · subst h
        rw [hs.2.1, Pi.mulSingle_eq_same]
        calc _ = ((R.MW i (sg0 D A)).fr ρ * ((R.MW i (sg0 D A)).fr ρ)⁻¹) * k *
            ((R.MW i (sg0 D A)).fr ρ * ((R.MW i (sg0 D A)).fr ρ)⁻¹) := by simp only [Matrix.mul_assoc]
          _ = k := by rw [hfr, Matrix.one_mul, Matrix.mul_one]
      · rw [hs.2.2 ρ h, Pi.mulSingle_eq_of_ne h, Matrix.mul_one, hfr]
    have hK : ∀ ρ, (R.MW i (sg0 D A)).fr ρ * compAt R.θ ρ (Formalism.L2.Theta.mt (Wc D i)
        (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ))) *
        ((R.MW i (sg0 D A)).fr ρ)⁻¹ ∈ Formalism.REAL.Kset ((R.MW i (sg0 D A)).ε ρ) := fun ρ => by
      rw [congrFun e ρ]
      by_cases h : ρ = τ
      · subst h; rwa [Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne h]; exact one_mem_K
    have a0 := ((hact t₀) 1 (one_mem _) _ hs.1 hK).2 (y (PiTensorProduct.tprod ℂ v) w)
    have at' := ((hact t) 1 (one_mem _) _ hs.1 hK).2 (y (PiTensorProduct.tprod ℂ v) w)
    have e2 := hinj (a0.symm.trans (y2 τ k hk v u hu w))
    exact at'.trans (congrArg (R.ptP i t) e2)

end GlobalTheory.IoAllTuples

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCartanInvOneOfOnb
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RawLift.VecNonzero

theorem thetaInner_self_ne_zero {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hψ : IsStdChar D ψ (-1))
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (h0 : f ≠ 0) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : IsCovolOne (ratL T S) μ 𝓕) : thetaIP μ 𝓕 f f ≠ 0 := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨-, c, hc⟩ := GlobalTheory.exists_normalise_meanSquare_of_cocompact (WO S T) (ratL T S) K hK hKc f hf.cont h0
    (by
      rintro _ ⟨γ, rfl⟩ w
      exact (congrArg norm (hf.quasi γ w)).trans (by rw [norm_mul, hψ.1.2.1, one_mul]))
  have h1 := hc μ 𝓕 hμ.1 hμ.2.1 hμ.2.2
  have e1 : thetaIP μ 𝓕 f f = ((∫ w in 𝓕, ‖f w‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    unfold thetaIP
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  intro h
  rw [e1, Complex.ofReal_eq_zero] at h
  simp only [norm_mul, mul_pow] at h1
  rw [integral_const_mul, h, mul_zero] at h1
  exact zero_ne_one h1

end GlobalTheory.RawLift.VecNonzero

namespace GlobalTheory.RawLift

open GlobalTheory.RawLift.VecNonzero


open scoped ComplexOrder in
theorem isCartanInv_one_of_onb {k : ℕ} {Gm B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis Gm 1 B k) : IsCartanInv Gm 1 := by
  obtain ⟨ε, hε, hG, -⟩ := h
  have e1 : ∀ a, (ε a : ℂ) = 1 := fun a => by
    rcases hε a with h | h
    · simp [h.1]
    · exact absurd a.2 (not_lt.2 h.2)
  have hB : Bᴴ * Gm * B = 1 := by
    rw [hG]
    simp only [e1, Matrix.diagonal_one]
  have hu : IsUnit B.det := Matrix.isUnit_det_of_left_inverse hB
  have h1 := Matrix.mul_nonsing_inv B hu
  have h2 : Gm = (B⁻¹)ᴴ * B⁻¹ := by
    have h3 : (B⁻¹)ᴴ * (Bᴴ * Gm * B) * B⁻¹ = (B⁻¹)ᴴ * B⁻¹ := by rw [hB, Matrix.mul_one]
    have h4 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    rw [← h3]
    simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
    rw [← Matrix.mul_assoc, h4, Matrix.one_mul]
  refine ⟨Matrix.mul_one _, by simp, ?_⟩
  rw [Matrix.mul_one, h2]
  exact Matrix.PosDef.conjTranspose_mul_self _
    (Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (by
      rw [Matrix.det_nonsing_inv]; exact hu.ringInverse)))

theorem vecNe : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, VecNe R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t μ 𝓕 hμ
  have hW := hL.thP.ωP i t
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hL.thP.pt_theta i t 1
    unfold RealDat.ptP pureTensorO at this
    rwa [GlobalTheory.AdTh.VecFock.pureTensorL_one] at this
  have hv0 : R.vP i t ≠ 0 := GlobalTheory.AdTh.VecNe.thPVec_ne_zero
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.lev.βV i))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.lev.βW i))
    ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2).trans_le (r_le_V i)) (hL.thP.vP i t)
  refine ⟨thetaInner_self_ne_zero hW.std hth hv0 hμ, ?_⟩
  obtain ⟨-, -, v, w, hv1, -, hio⟩ := hL.thP.ioP i t
  have hvac := GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ (fun _ => 1) _ _ _ _ _ _ _ _ _ _ (hL.thP.vP i t) hth
  have hinj := GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) hW.std hL.models.inf (fun _ => 1) (R.BV i)
    (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) (fun _ => (Vc D i).rank) (fun τ => ((Wc D i).sig (tauE D τ)).1)
    (fun τ => isCartanInv_one_of_onb (hL.models.BV i τ)) (GlobalTheory.AdTh.VecFock.isCartanInv_cart _) (hL.models.BV i)
    (fun τ => GlobalTheory.AdTh.VecFock.isONBasis_onb _ τ _ (hL.models.order i τ)) (D.sp.V_sig _) (D.sp.W_sig _) _ hth hvac hv0
  refine ⟨fun ρ => v ρ, w, hv1, ?_⟩
  have hj : jointVec R i t (fun ρ => v ρ) w = R.ptP i t (RealDat.Delta i) := by
    unfold jointVec
    rw [hio]
  rw [hj]
  refine thetaInner_self_ne_zero hW.std (hL.thP.pt_theta i t _) (fun h => ?_) hμ
  refine GlobalTheory.AdTh.IoExtPf.Delta_ne i (hinj ?_)
  exact h.trans (map_zero (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i)
    (onb (R.MW i (sg0 D A))) (R.vP i t))).symm

end GlobalTheory.RawLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceModelCompTensorHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.TwoStepModel

variable {D : D7} {m n : ℕ}

def tensorHalf (a' b : AE D) (Ψ : Mx D m n → ℂ) : (Mx D m n → ℂ) →ₗ[ℂ] (Mx D m n → ℂ) where
  toFun Φ x := Φ (a' • x) * Ψ (b • x) * (if IsHalf (a' + b) x then 1 else 0)
  map_add' Φ Φ' := by funext x; simp only [Pi.add_apply]; ring
  map_smul' c Φ := by funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem tensorHalf_apply (a' b : AE D) (Ψ Φ : Mx D m n → ℂ) (x : Mx D m n) :
    tensorHalf a' b Ψ Φ x = Φ (a' • x) * Ψ (b • x) * (if IsHalf (a' + b) x then 1 else 0) := rfl

open GlobalTheory.ExportSeries.RestrictHalfModel

theorem tensorHalf_halfInd (a' b : AE D) (Λ : AddSubgroup (Mx D m n)) (Ψ : Mx D m n → ℂ) :
    tensorHalf a' b Ψ ((1 : ℂ) • halfInd a' Λ) = restrictHalf b a' Λ Ψ := by
  funext x
  simp only [tensorHalf_apply, restrictHalf_apply, one_smul, add_comm b a']
  ring

theorem isSBHalf_tensorHalf {a' b : AE D} (ha' : a' * a' = a') (hb : b * b = b) {Λ : AddSubgroup (Mx D m n)}
    (hΛ : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ) {Φ Ψ : Mx D m n → ℂ} (hΦ : IsSBHalf a' Λ Φ)
    (hΨ : IsSBHalf b Λ Ψ) : IsSBHalf (a' + b) Λ (tensorHalf a' b Ψ Φ) := by
  obtain ⟨-, k, hk, hinv, hlat⟩ := hΦ
  obtain ⟨-, k', hk', hinv', hlat'⟩ := hΨ
  refine ⟨fun t ht => ?_, k * k', Nat.mul_pos hk hk', fun u hu hhu t => ?_, fun t ht => ?_⟩
  · rw [tensorHalf_apply] at ht
    by_contra h
    exact ht (by rw [if_neg h, mul_zero])
  · rw [isHalf_iff'] at hhu
    simp only [tensorHalf_apply]
    have e1 : a' • (t + (k * k') • u) = a' • t + k • (a' • (k' • u)) := by
      rw [smul_add, mul_comm k k', mul_smul, smul_comm k' k u, smul_comm a' k]
    have e2 : b • (t + (k * k') • u) = b • t + k' • (b • (k • u)) := by
      rw [smul_add, mul_smul, smul_comm k k' u, smul_comm b k']
    have e3 : (a' + b) • ((k * k') • u) = (k * k') • u := by rw [smul_comm, hhu]
    rw [e1, hinv _ (hΛ a' ha' _ (Λ.nsmul_mem hu k')) (isHalf_smul ha' _), e2,
      hinv' _ (hΛ b hb _ (Λ.nsmul_mem hu k)) (isHalf_smul hb _), isHalf_add_iff e3]
  · rw [tensorHalf_apply] at ht
    have h1 : Φ (a' • t) ≠ 0 := fun h => ht (by rw [h, zero_mul, zero_mul])
    have h2 : Ψ (b • t) ≠ 0 := fun h => ht (by rw [h, mul_zero, zero_mul])
    have h3 : IsHalf (a' + b) t := by
      by_contra h
      exact ht (by rw [if_neg h, mul_zero])
    rw [isHalf_iff', add_smul] at h3
    rw [← h3, smul_add, mul_smul, mul_comm k k', mul_smul k']
    exact Λ.add_mem (by rw [smul_comm k k']; exact Λ.nsmul_mem (hlat _ h1) k') (by rw [smul_comm k' k]; exact Λ.nsmul_mem (hlat' _ h2) k)

theorem isPlaceModel_comp_tensorHalf {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)}
    {f₀ : WO S T → ℂ} {a' b : AE D} {T₀ : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} (ha' : a' * a' = a') (hb : b * b = b)
    (hab : a' * b = 0) (hΛ : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ) {Ψ : WO S T → ℂ} (hΨ : IsSBHalf b Λ Ψ)
    (hT : IsPlaceModel ψ (symplO S T) (heisO ψ S T) (a' + b) Λ 1 f₀ T₀) :
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) a' Λ 1 (T₀ (restrictHalf b a' Λ Ψ)) (T₀ ∘ₗ tensorHalf a' b Ψ) := by
  have hsb : ∀ Φ, IsSBHalf a' Λ Φ → IsSBHalf (a' + b) Λ (tensorHalf a' b Ψ Φ) :=
    fun Φ hΦ => isSBHalf_tensorHalf ha' hb hΛ hΦ hΨ
  refine ⟨fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · obtain ⟨hbx, hax⟩ := smul_of_half hab hx
    have hxa : IsHalf (a' + b) x := (isHalf_iff' _ _).2 hax
    have e : tensorHalf a' b Ψ (fun t => Φ (t + x)) = fun t => tensorHalf a' b Ψ Φ (t + x) := by
      funext z
      simp only [tensorHalf_apply]
      rw [smul_add, (isHalf_iff' _ _).1 hx, smul_add b, hbx, add_zero, isHalf_add_iff hax]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e]
    exact hT.trans _ (hsb Φ hΦ) x hxa
  · have hy' : IsHalf (cA D (a' + b)) y := by
      rw [isHalf_iff'] at hy ⊢
      rw [map_add (f := _), add_smul, hy, ← hy, smul_smul, ← map_mul, mul_comm, hab, map_zero, zero_smul, add_zero]
    have e : tensorHalf a' b Ψ (fun t => ψ (symplO S T t y) * Φ t) =
        fun t => ψ (symplO S T t y) * tensorHalf a' b Ψ Φ t := by
      funext z
      simp only [tensorHalf_apply]
      rw [GlobalTheory.SplitScalar.symplO_smul, (isHalf_iff' _ _).1 hy]
      ring
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e]
    exact hT.modul _ (hsb Φ hΦ) y hy'
  · rw [LinearMap.comp_apply, tensorHalf_halfInd]

end GlobalTheory.TwoStepModel

end
end

