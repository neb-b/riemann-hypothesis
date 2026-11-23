module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0786
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0776
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1673
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0684
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0102
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0284
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0787
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateFormsThetaLiftEqThetaSeries
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

noncomputable section

namespace GlobalTheory.ConjTwist

def IsTraceFn {H Γ W : Type} [Group H] [Group Γ] [AddCommGroup W] [Module ℂ W] (ι : Γ →* H)
    (ρ : Γ →* Module.End ℂ W) (J : Subgroup H) (χ : J →* ℂˣ) (z₀ : H) (w : W) (f : H → W) : Prop :=
  (∀ z, (¬ ∃ (γ : Γ) (k : J), z = ι γ * z₀ * k) → f z = 0) ∧
    ∀ L : W →ₗ[ℂ] ℂ, (∀ (γ : Γ) (hγ : z₀⁻¹ * ι γ * z₀ ∈ J), L ((χ ⟨_, hγ⟩ : ℂ) • ρ γ⁻¹ w) = L w) →
      L (f z₀) = (Nat.card (Bridge.stab ι J z₀) : ℂ) * L w

theorem IsTraceFn.post {H Γ W : Type} [Group H] [Group Γ] [AddCommGroup W] [Module ℂ W] (ι : Γ →* H)
    (ρ : Γ →* Module.End ℂ W) {J J' : Subgroup H} (hJ : J' = J) (χ : J →* ℂˣ) (χ' : J' →* ℂˣ) (τ : ℂ ≃+* ℂ) (T : W →+ W)
    (hs : ∀ (a : ℂ) w, T (a • w) = τ a • T w) (hρ : ∀ γ w, T (ρ γ w) = ρ γ (T w))
    (hχ : ∀ k (hk : k ∈ J) (hk' : k ∈ J'), ((χ' ⟨k, hk'⟩ : ℂˣ) : ℂ) = τ ((χ ⟨k, hk⟩ : ℂˣ) : ℂ))
    {z₀ : H} {w : W} {f : H → W} (hf : IsTraceFn ι ρ J χ z₀ w f) :
    IsTraceFn ι ρ J' χ' z₀ (T w) (fun g => T (f g)) := by
  subst hJ
  refine ⟨fun z hz => ?_, fun L hL => ?_⟩
  · show T (f z) = 0
    rw [hf.1 z hz, map_zero]
  · let L' : W →ₗ[ℂ] ℂ :=
      { toFun := fun v => τ.symm (L (T v))
        map_add' := fun a b => by rw [map_add (f := _), map_add (f := _), map_add (f := _)]
        map_smul' := fun a v => by
          rw [hs, map_smul, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply]
          rfl }
    have hL' : ∀ v, L' v = τ.symm (L (T v)) := fun v => rfl
    have key := hf.2 L' fun γ hγ => by
      rw [hL', hL', hs, hρ, ← hχ _ hγ hγ, hL γ hγ]
    rw [hL', hL'] at key
    have := congrArg τ key
    rwa [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, map_natCast] at this

theorem IsTraceFn.sum_eq {H Hf W : Type} [Group H] [Group Hf] [AddCommGroup W] [Module ℂ W] (p : H →* Hf)
    (hp : Function.Surjective p) (Γ F R : Subgroup H) (ρ : H →* Module.End ℂ W) (J : Subgroup Hf) (χ : J →* ℂˣ)
    (hdec : ∀ u : H, ∃ k ∈ F, ∃ a ∈ R, u = k * a ∧ p k = p u) (hρ : ∀ k ∈ F, ρ k = 1)
    (Cl : Type) [Fintype Cl] (y : Cl → Hf) (hy : Bridge.IsReps (p.comp Γ.subtype) J y)
    (hfin : ∀ k, Finite (Bridge.stab (p.comp Γ.subtype) J (y k))) (h₀ : H) (hh₀ : h₀ ∈ F) (v : W) (f : Hf → W)
    (hf : IsTraceFn (p.comp Γ.subtype) (ρ.comp Γ.subtype) J χ (p h₀) v f) :
    ∃ r : Cl → H, (∀ k, r k ∈ F) ∧
      Bridge.IsReps (p.comp Γ.subtype) J (fun k => p (r k)) ∧
      ∀ {G' X : Type} [Group G'] (x₀ : X) (om : H × G' →* Module.End ℂ (X → ℂ)) (Λ : W →ₗ[ℂ] (X → ℂ)),
        (∀ γ ∈ Γ, ∀ z v, om (γ, 1) (om z (Λ v)) x₀ = om z (Λ v) x₀) → (∀ a ∈ R, ∀ v, om (a, 1) (Λ v) = Λ (ρ a v)) →
        (∀ k ∈ F, ∀ hk : p k ∈ J, ∀ v, om (k, 1) (Λ v) = ((χ ⟨p k, hk⟩ : ℂˣ) : ℂ)⁻¹ • Λ v) →
        ∀ g : G', ∑ k, ((J.relIndex J : ℕ) : ℂ)⁻¹ * ((Nat.card (Bridge.stab (p.comp Γ.subtype) J (p (r k))) : ℕ) : ℂ)⁻¹ *
          om (r k, g) (Λ (f (p (r k)))) x₀ = om (h₀, g) (Λ v) x₀ := by
  obtain ⟨y', c₀, hy', e₀⟩ := GlobalTheory.TraceLift.exists_isReps_through _ _ hy (p h₀)
  have hlift : ∀ z : Hf, ∃ k ∈ F, p k = z := fun z => by
    obtain ⟨u, hu⟩ := hp z
    obtain ⟨k, hk, -, -, -, e⟩ := hdec u
    exact ⟨k, hk, e.trans hu⟩
  choose σ hσ hσ' using hlift
  let r : Cl → H := Function.update (fun k => σ (y' k)) c₀ h₀
  have hr : ∀ k, r k ∈ F ∧ p (r k) = y' k := fun k => by
    by_cases hk : k = c₀
    · subst hk
      simp only [r, Function.update_self]
      exact ⟨hh₀, e₀.symm⟩
    · simp only [r, Function.update_of_ne hk]
      exact ⟨hσ _, hσ' _⟩
  have hr0 : r c₀ = h₀ := Function.update_self _ _ _
  have hyr : (fun k => p (r k)) = y' := funext fun k => (hr k).2
  have hf0 := GlobalTheory.TraceLift.finite_stab _ _ hy hfin (p h₀)
  obtain ⟨hz, hv⟩ := hf
  refine ⟨r, fun k => (hr k).1, by rw [hyr]; exact hy', fun {G' X} _ x₀ om Λ hom hΛa hΛk g => ?_⟩
  rw [Finset.sum_eq_single c₀ ?_ (fun h => absurd (Finset.mem_univ _) h)]
  · let L₀ : W →ₗ[ℂ] ℂ := (LinearMap.proj x₀ : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (om (h₀, g)) ∘ₗ Λ
    have hL₀ : ∀ v, L₀ v = om (h₀, g) (Λ v) x₀ := fun v => rfl
    have key := hv L₀ fun γ hγ => ?_
    · have hN : ((Nat.card (Bridge.stab (p.comp Γ.subtype) J (p h₀)) : ℕ) : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.2 (Nat.card_pos).ne'
      rw [hr0, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_mul, ← hL₀, key, inv_mul_cancel_left₀ hN, hL₀]
    · obtain ⟨k, hk, b, hb, e, e'⟩ := hdec ((γ : H)⁻¹ * h₀)
      have hκ : h₀⁻¹ * k ∈ F := mul_mem (inv_mem hh₀) hk
      have eκ : p (h₀⁻¹ * k) = ((p h₀)⁻¹ * (p.comp Γ.subtype) γ * p h₀)⁻¹ := by
        show p (h₀⁻¹ * k) = ((p h₀)⁻¹ * p γ * p h₀)⁻¹
        rw [map_mul, e', map_mul, map_inv, map_inv]
        group
      have hκ' : p (h₀⁻¹ * k) ∈ J := by rw [eκ]; exact inv_mem hγ
      have eχ : ((χ ⟨_, hκ'⟩ : ℂˣ) : ℂ)⁻¹ = χ ⟨_, hγ⟩ := by
        rw [show (⟨_, hκ'⟩ : J) = ⟨_, hγ⟩⁻¹ from Subtype.ext eκ, map_inv, Units.val_inv_eq_inv_val, inv_inv]
      have eρ : (ρ.comp Γ.subtype) γ⁻¹ v = ρ b v := by
        have h1 := congrArg ρ e
        rw [map_mul, map_mul, hρ _ hh₀, hρ _ hk, mul_one, one_mul] at h1
        rw [← h1]
        rfl
      have e3 : ((h₀, g) : H × G') * (h₀⁻¹ * k, 1) * (b, 1) = (((γ : H)⁻¹, 1) : H × G') * (h₀, g) := by
        rw [Prod.mk_mul_mk, Prod.mk_mul_mk, Prod.mk_mul_mk, mul_inv_cancel_left, e, mul_one, mul_one, one_mul]
      rw [hL₀, hL₀, map_smul, eρ, ← eχ, ← hΛk _ hκ hκ', ← hΛa b hb, ← Module.End.mul_apply, ← Module.End.mul_apply,
        ← map_mul, ← map_mul, e3, map_mul]
      exact hom _ (inv_mem γ.2) _ _
  · intro k _ hk
    rw [hz _ ?_, map_zero, map_zero]
    · simp
    · intro hex
      obtain ⟨j, -, hu⟩ := hy' (y' k)
      refine hk ((hu k ⟨1, 1, by simp⟩).trans (hu c₀ ?_).symm)
      show ∃ (γ : Γ) (m : J), y' k = (p.comp Γ.subtype) γ * y' c₀ * m
      rw [e₀, ← (hr k).2]
      exact hex


set_option maxHeartbeats 4000000 in
theorem thF_eq_ser_of_isTraceFn {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (hV : VStd D i) (t : T0) (h : GA D (Vc D i)) (hh : h ∈ GfC (Vc D i))
    (w : (R.cV i).W) (x : (R.HV i t).H)
    (hx : IsTraceFn (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
      (levEnv _ (R.βV i) (R.datVt i t)).χ (Formalism.IndefR.FWT.fin (Vc D i) h) w ((R.HV i t).e x))
    (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)) :
    R.thF i t x (fun ρ => u ρ) g = ser R i t (R.vP i t) u h w g := by
  refine (hR.thP.thF i t).elim fun thP hPF => ?_
  refine (IsTraceFn.sum_eq (finHom (Vc D i)).rangeRestrict (finHom (Vc D i)).rangeRestrict_surjective (GQ (Vc D i))
    (GfC (Vc D i)) (GinfC (Vc D i)) (R.cV i).ρ (levEnv _ (R.βV i) (R.datVt i t)).J (levEnv _ (R.βV i) (R.datVt i t)).χ
    (GlobalTheory.LiftUnfold.exists_fin_mul_real (Vc D i)) (hR.models.cV i).1 _ (R.B.L i t).pres.y (R.B.L i t).pres.reps
    (fun c => Finite.of_equiv _ ((R.B.L i t).pres.stabI c).toEquiv) h hh w ((R.HV i t).e x) hx).elim fun r hr => ?_
  have hf : (R.HV i t).e x ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ
      (levEnv _ (R.βV i) (R.datVt i t)).J (levEnv _ (R.βV i) (R.datVt i t)).χ :=
    (hR.models.HV i t).2.1.le (LinearMap.mem_range_self _ x)
  have hfin : ∀ k ∈ GfC (Vc D i), ∀ hk : Formalism.IndefR.FWT.fin (Vc D i) k ∈ levJ R i t, ∀ P, R.ωP i t (k, 1) (R.ptP i t P) =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨Formalism.IndefR.FWT.fin (Vc D i) k, hk⟩ : ℂˣ) : ℂ)⁻¹ • R.ptP i t P := fun k hk hk' =>
    GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) hR.models.inf
      (hR.thP.ωP i t) _ _ _ _ _ (hR.thP.pt_theta i t) k hk 1 (one_mem _) _
      (GlobalTheory.AdTh.LevelLawCore.omega_level_vP_core D G Pl0 T0 A Ks R F hR i t k hV hk hk')
  have key := GlobalTheory.LiftUnfold.integral_theta (hR.thP.ωP i t) (D.sp.V_sig _) (hR.models.vpos i) (R.cV i) (hR.models.cV i) (R.βV i)
    (R.datVt i t) (fun _ => Iff.rfl) hf
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i t) ∘ₗ R.ioP i (PiTensorProduct.tprod ℂ u)) (fun w => hR.thP.pt_theta i t _)
    (fun a ha w => (hR.thP.ioP i t).1 a ha _ w) (fun k hk hk' w => hfin k hk hk' _)
    (hR.models.νV i t) _ _ r le_rfl (by rw [Subgroup.relIndex_self]; exact one_ne_zero) hr.2.1 hr.1 g
  have key2 := hr.2.2 (0 : WO (Vc D i) (Wc D i)) (R.ωP i t)
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i t) ∘ₗ R.ioP i (PiTensorProduct.tprod ℂ u))
    (fun γ hγ z v => (hR.thP.ωP i t).om_aut γ hγ 1 (one_mem _) _ ((hR.thP.ωP i t).om_pres _ _ (hR.thP.pt_theta i t _)))
    (fun a ha w => (hR.thP.ioP i t).1 a ha _ w) (fun k hk hk' w => hfin k hk hk' _) g
  have h1 := congrFun (hPF.2 x u) g
  have h2 := hPF.1.eq ((R.extV i t).rangeRestrict x) (PiTensorProduct.tprod ℂ u) g
  refine h1.trans (h2.trans (Eq.trans ?_ (key.trans key2)))
  rfl


set_option maxHeartbeats 8000000 in
theorem exists_conjForm_thF_eq_ser : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC M.c') M.c0' c → ∀ (τ : ℂ ≃+* ℂ) (t t' : T0), FixBase T R i τ → ConjTup R τ t t' → ∀ h ∈ GfC (Vc D i), ∀ x x' : VsV D i ℂ, ConjVec i τ x x' → ∃ (y : (R.HV i t).H) (y' : (R.HV i t').H), ConjForm R i τ c t t' y y' ∧ ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)), R.thF i t y (fun ρ => u ρ) g = ser R i t (R.vP i t) u h (c x) g ∧ R.thF i t' y' (fun ρ => u ρ) g = ser R i t' (R.vP i t') u h (c x') g := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hCore hFW i Tp tup M hPins c hc τ t t' hFix hConj h hh x x' hxx
  have hX := GlobalTheory.CoefExtC.exists_extC_bijective_unique D G Pl0 T0 A T R F κ v₀ hCore hFW i Tp tup M hPins
  refine hX.elim fun c₁ hc₁ => ?_
  have hb : Function.Bijective c :=
    (congrArg (fun f : VsV D i ℂ →ₗ[ℂ] (R.cV i).W => Function.Bijective f) (hc₁.2.2 c hc)).mpr hc₁.2.1
  refine (exists_conjW M hPins c hc hb τ hFix.host).elim fun TW hTW => ?_
  have hs := hTW.1
  have hTc := hTW.2.1
  have hρ := hTW.2.2
  have hZ := (_root_.GlobalTheory.ConjRes.conj_res D G Pl0 T0 A T R F κ v₀ hCore τ t t' hConj).2.2.2 i hFix
  have hJ := hZ.1
  have hχ := hZ.2
  have hV := hCore.models.HV i t
  have hV' := hCore.models.HV i t'
  have hfin := GlobalTheory.TraceLift.finite_stab (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.reps
    (fun k => Finite.of_equiv _ ((R.B.L i t).pres.stabI k).toEquiv) (Formalism.IndefR.FWT.fin (Vc D i) h)
  refine (GlobalTheory.TraceLift.exists_traceForm (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
    (levEnv _ (R.βV i) (R.datVt i t)).χ (Formalism.IndefR.FWT.fin (Vc D i) h) hfin (c x)).elim fun f hf => ?_
  have hf1 : IsTraceFn (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
      (levEnv _ (R.βV i) (R.datVt i t)).χ (Formalism.IndefR.FWT.fin (Vc D i) h) (c x) f := hf.2
  have hf2 := IsTraceFn.post (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ hJ _ _ τ TW.toAddMonoidHom hs hρ hχ hf1
  have hm2 := post_mem (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ hJ _ _ τ TW.toAddMonoidHom hs hρ hχ hf.1
  refine (LinearMap.mem_range.1 (hV.2.1.ge hf.1)).elim fun y hy => ?_
  refine (LinearMap.mem_range.1 (hV'.2.1.ge hm2)).elim fun y' hy' => ?_
  have hx' : x' = GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) x :=
    Subtype.ext (hxx.trans (GlobalTheory.CoefModel.mapVV_coe _ _ _).symm)
  have hcx : TW.toAddMonoidHom (c x) = c x' := (hTc x).trans (congrArg c hx').symm
  refine ⟨y, y', fun k => ?_, fun u g => ⟨?_, ?_⟩⟩
  · refine (hb.2 (f (Formalism.IndefR.FWT.fin (Vc D i) k))).elim fun z hz => ?_
    refine ⟨z, GlobalTheory.CoefModel.mapVV (τ : ℂ →+* ℂ) (lamV D i) z, GlobalTheory.CoefModel.mapVV_coe _ _ _,
      (congrFun hy _).trans hz.symm, (congrFun hy' _).trans ?_⟩
    exact (congrArg TW hz.symm).trans (hTc z)
  · refine thF_eq_ser_of_isTraceFn R F hCore i hPins.lift.std t h hh (c x) y ?_ u g
    rw [hy]
    exact hf1
  · refine thF_eq_ser_of_isTraceFn R F hCore i hPins.lift.std t' h hh (c x') y' ?_ u g
    rw [hy', ← hcx]
    exact hf2

end GlobalTheory.ConjTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFieldElementLocalComponentsLevelNumber
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

noncomputable section

namespace GlobalTheory.LevelFieldApprox

open Formalism.L2.Host

theorem val_eq_one_of_close {E : Type} [Field E] [NumberField E] {v : HeightOneSpectrum (𝓞 E)} {y : E}
    (h : v.valuation E (y - 1) < 1) : v.valuation E y = 1 := by
  have e : y = (y - 1) + 1 := by ring
  rw [e, Valuation.map_add_eq_of_lt_right _ (by rwa [map_one])]
  exact map_one _

theorem locK_eq_one {E : Type} [Field E] [NumberField E] (χ : HChar E) (v : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    (hn : χ.LevelLe v n) (y : Eˣ) (h : v.valuation E ((y : E) - 1) ≤ WithZero.exp (-((n : ℤ) + 1))) :
    χ.locK v y = 1 ∧ v.valuation E (y : E) = 1 := by
  have hlt : v.valuation E ((y : E) - 1) < 1 :=
    lt_of_le_of_lt h (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  have hv := val_eq_one_of_close hlt
  have e1 : ((atFin v y : (v.adicCompletion E)ˣ) : v.adicCompletion E) = algebraMap E (v.adicCompletion E) (y : E) := rfl
  have hval : ∀ x : E, Valued.v (algebraMap E (v.adicCompletion E) x) = v.valuation E x :=
    fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  refine ⟨?_, hv⟩
  show χ.loc v (atFin v y) = 1
  refine hn _ ?_ ?_
  · show Valued.v ((atFin v y : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1
    rw [e1, hval, hv]
  · rw [e1, ← map_one (algebraMap E (v.adicCompletion E)), ← map_sub, hval]
    exact h.trans (WithZero.exp_le_exp.mpr (by omega))

theorem exists_approx : ∀ (E : Type) [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (M₀ : ℕ) (u : Eˣ), (u : E) = ((M₀ : ℕ) : E) → ∀ (T : Finset (HeightOneSpectrum (𝓞 E))), ∃ a : Eˣ, IsIntegral ℤ (a : E) ∧ (∀ v ∈ T, χ.locK v a = χ.locK v u ∧ v.valuation E (a : E) = v.valuation E ((M₀ : ℕ) : E)) ∧ ∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal → v ∉ T → χ.locK v a = 1 ∧ v.valuation E (a : E) = 1 := by
  intro E _ _ χ M₀ u hu T
  classical
  have hM0 : M₀ ≠ 0 := by
    rintro rfl
    exact u.ne_zero (by rw [hu]; simp)
  have hM : ((M₀ : ℕ) : 𝓞 E) ≠ 0 := by exact_mod_cast hM0
  have hMe : ((M₀ : ℕ) : E) ≠ 0 := by exact_mod_cast hM0
  have hfin : {v : HeightOneSpectrum (𝓞 E) | ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {((M₀ : ℕ) : 𝓞 E)}) ?_).subset fun v hv => ?_
    · rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    · exact Ideal.dvd_span_singleton.2 hv
  set S : Finset (HeightOneSpectrum (𝓞 E)) := T ∪ hfin.toFinset with hS
  choose n hn using GlobalTheory.Mem.UnrAe.exists_levelLe χ
  have hm : ∀ v : HeightOneSpectrum (𝓞 E), ∃ m : ℕ, v.intValuation ((M₀ : ℕ) : 𝓞 E) = WithZero.exp (-(m : ℤ)) :=
    fun v => ⟨_, v.intValuation_if_neg hM⟩
  choose m hm using hm
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal)
    (fun v => if v ∈ T then m v + n v + 1 else n v + 1)
    (fun v _ => v.prime) (fun v _ w _ h h' => h (HeightOneSpectrum.ext h'))
    (fun v => if (v : HeightOneSpectrum (𝓞 E)) ∈ T then ((M₀ : ℕ) : 𝓞 E) else 1)
  have hvz : ∀ v : HeightOneSpectrum (𝓞 E), ∀ z : 𝓞 E, v.valuation E (z : E) = v.intValuation z :=
    fun v z => HeightOneSpectrum.valuation_of_algebraMap (K := E) v z
  have hT : ∀ v ∈ T, v.valuation E ((y : E) - ((M₀ : ℕ) : E)) ≤ WithZero.exp (-((m v : ℤ) + n v + 1)) := by
    intro v hv
    have h1 := (v.intValuation_le_pow_iff_mem _ _).2 (hy v (Finset.mem_union_left _ hv))
    simp only [hv, if_true] at h1
    have e : (y : E) - ((M₀ : ℕ) : E) = ((y - ((M₀ : ℕ) : 𝓞 E) : 𝓞 E) : E) := by push_cast; rfl
    rw [e, hvz]
    convert h1 using 2
    push_cast; ring
  have hO : ∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal → v ∉ T →
      v.valuation E ((y : E) - 1) ≤ WithZero.exp (-((n v : ℤ) + 1)) := by
    intro v hv hvT
    have h1 := (v.intValuation_le_pow_iff_mem _ _).2
      (hy v (Finset.mem_union_right _ (hfin.mem_toFinset.2 hv)))
    simp only [hvT, if_false] at h1
    have e : (y : E) - 1 = ((y - 1 : 𝓞 E) : E) := by push_cast; rfl
    rw [e, hvz]
    convert h1 using 2
    push_cast; ring
  have hMv : ∀ v, v.valuation E ((M₀ : ℕ) : E) = WithZero.exp (-(m v : ℤ)) := by
    intro v
    rw [← hm v, ← hvz]; simp
  have hTv : ∀ v ∈ T, v.valuation E (y : E) = v.valuation E ((M₀ : ℕ) : E) := by
    intro v hv
    have e : (y : E) = ((y : E) - ((M₀ : ℕ) : E)) + ((M₀ : ℕ) : E) := by ring
    rw [e, Valuation.map_add_eq_of_lt_right]
    rw [hMv]
    exact lt_of_le_of_lt (hT v hv) (WithZero.exp_lt_exp.mpr (by omega))
  have hOv : ∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal → v ∉ T → v.valuation E (y : E) = 1 :=
    fun v hv hvT => val_eq_one_of_close (lt_of_le_of_lt (hO v hv hvT)
      (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega))
  by_cases hy0 : (y : E) = 0
  · refine ⟨1, by simpa using isIntegral_one, fun v hv => ?_, fun v hv hvT => ?_⟩
    · exact absurd (hTv v hv) (by rw [hy0, map_zero, hMv]; exact (WithZero.exp_ne_zero).symm)
    · exact absurd (hOv v hv hvT) (by rw [hy0, map_zero]; exact zero_ne_one)
  set a : Eˣ := Units.mk0 (y : E) hy0 with ha
  refine ⟨a, y.isIntegral_coe, fun v hv => ?_, fun v hv hvT => ?_⟩
  · have hw := (locK_eq_one χ v (hn v) (a * u⁻¹) ?_).1
    · refine ⟨?_, hTv v hv⟩
      have : a = (a * u⁻¹) * u := by group
      rw [this, map_mul, hw, one_mul]
    · rw [Units.val_mul, Units.val_inv_eq_inv_val, hu, ha, Units.val_mk0]
      have e : (y : E) * ((M₀ : ℕ) : E)⁻¹ - 1 = ((y : E) - ((M₀ : ℕ) : E)) / ((M₀ : ℕ) : E) := by
        field_simp
      rw [e, map_div₀, hMv]
      calc _ ≤ WithZero.exp (-((m v : ℤ) + n v + 1)) / WithZero.exp (-(m v : ℤ)) :=
            div_le_div_of_nonneg_right (hT v hv) zero_le'
        _ = _ := by rw [div_eq_mul_inv, ← WithZero.exp_neg, ← WithZero.exp_add]; congr 1; ring
  · exact locK_eq_one χ v (hn v) a (by rw [ha, Units.val_mk0]; exact hO v hv hvT)

end GlobalTheory.LevelFieldApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodFrameRealisation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameOfReal

theorem exists_frame_real : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (F3 : Face3 D A3), Rl.Char3 F3 → ∀ j : Fin D.R.m, ∃ F : Frame (Vc D j) (Wc D j), F.Good ∧ IsStdChar D F.ψ (-1) ∧ F.ψ = Rl.ψ ∧ F.θ = Rl.θ ∧ F.sT = cart (Rl.MW j (sg0 D A3.A)) ∧ (∀ τ, (F.BS τ).val = Rl.BV j τ) ∧ F.BT = onb (Rl.MW j (sg0 D A3.A)) ∧ F.ΛS = Rl.ΛV j ∧ F.ΛT = Rl.ΛW j ∧ F.βS = Rl.βV j ∧ F.βT = Rl.βW j ∧ F.f₀ = Rl.vacP j ∧ Lev.IsBaseFrame (Vc D j) F.βS F.ΛS 1 ∧ Lev.IsBaseFrame (Wc D j) F.βT F.ΛT 1 := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl F3 hC j
  have hBV := hC.models.BV j
  have hu : ∀ τ, IsUnit (Rl.BV j τ) := fun τ => by
    obtain ⟨ε, hε, h2, -⟩ := hBV τ
    have hd : (Matrix.diagonal fun a => (ε a : ℂ)) * Matrix.diagonal (fun a => (ε a : ℂ)) = 1 := by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      rcases hε a with h | h <;> simp [h.1]
    refine IsUnit.of_mul_eq_one_right (Matrix.diagonal (fun a => (ε a : ℂ)) * (Matrix.conjTranspose (Rl.BV j τ) * gramAt D (Vc D j) τ)) ?_
    rw [Matrix.mul_assoc, h2, hd]
  have sdV := hC.lev.βV j
  have sdW := hC.lev.βW j
  have bV : Lev.IsBaseFrame (Vc D j) (Rl.βV j) (Rl.ΛV j) 1 := by
    obtain ⟨c, hc⟩ := sdV
    rwa [one_pow] at hc
  have bW : Lev.IsBaseFrame (Wc D j) (Rl.βW j) (Rl.ΛW j) 1 := by
    obtain ⟨c, hc⟩ := sdW
    rwa [one_pow] at hc
  have hv := (hC.thP.vP j A3.A.μ0).1
  have hstd := (hC.thP.ωP j A3.A.μ0).std
  refine ⟨⟨Rl.ψ, Rl.θ, cart (Rl.MW j (sg0 D A3.A)), fun τ => (hu τ).unit, onb (Rl.MW j (sg0 D A3.A)), Rl.ΛV j, Rl.ΛW j,
    Rl.βV j, Rl.βW j, Rl.vacP j⟩, ?_, hstd, rfl, rfl, rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, bV, bW⟩
  exact
    { rank_le := (D.sp.W_rank _ (Nat.le_add_left _ _) j.2).le.trans (r_le_V j)
      onbS := hBV
      cartT := fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart _ τ
      onbT := fun τ => GlobalTheory.AdTh.VecFock.isONBasis_onb _ τ _ (hC.models.order j τ)
      sdS := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ sdV
      sdT := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ sdW
      frS := bV.1
      frT := bW.1
      vac := hv }

end GlobalTheory.FrameOfReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentSumSubsetAndConjugateFlip
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

namespace GlobalTheory.IdemFlip

theorem idemSum_sub_and_flip : ∀ (D : D7) (e : AE D) (P T : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → T ⊆ P →
    (∃ eT : AE D, IsIdemSum eT T) ∧ ∃ e' : AE D, IsIdemSum e' ((P \ T) ∪ T.image Formalism.L2.DIV.conjPl) := by
  intro D e P T he hT
  have hnc := GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum he
  obtain ⟨⟨es, hes, hsum⟩, h0⟩ := he
  have hmul : ∀ S R : Finset (Formalism.L2.DIV.Pl D.host.E), S ⊆ R → R ⊆ P →
      (∑ a ∈ S, es a) * (∑ b ∈ R, es b) = ∑ a ∈ S, es a := by
    intro S R hSR hRP
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [Finset.mul_sum, Finset.sum_eq_single a]
    · exact (hes a (hRP (hSR ha))).1.1
    · intro b hb hba
      exact Formalism.IndefR.Fin.idem_orth (hnc a (hRP (hSR ha)) a (hRP (hSR ha))) (hes a (hRP (hSR ha))) (hes b (hRP hb))
        (Ne.symm hba)
    · intro h; exact absurd (hSR ha) h
  have h1 : (∑ a ∈ T, es a) * e = ∑ a ∈ T, es a := by rw [hsum]; exact hmul T P hT subset_rfl
  have h2 : (∑ a ∈ T, es a) * (∑ a ∈ T, es a) = ∑ a ∈ T, es a := hmul T T subset_rfl hT
  have hTT : (∑ a ∈ T, es a) * cA D (∑ a ∈ T, es a) = 0 := by
    calc (∑ a ∈ T, es a) * cA D (∑ a ∈ T, es a)
        = ((∑ a ∈ T, es a) * e) * cA D ((∑ a ∈ T, es a) * e) := by rw [h1]
      _ = ((∑ a ∈ T, es a) * cA D (∑ a ∈ T, es a)) * (e * cA D e) := by rw [map_mul]; ring
      _ = 0 := by rw [h0, mul_zero]
  have hIT : IsIdemSum (∑ a ∈ T, es a) T := ⟨⟨es, fun a ha => hes a (hT ha), rfl⟩, hTT⟩
  refine ⟨⟨_, hIT⟩, ?_⟩
  obtain ⟨⟨es2, hes2, hsum2⟩, -⟩ := Formalism.IndefR.Fin.LevelGroupLemmas.isIdemSum_conj hIT
  have hdisj : Disjoint (P \ T) (T.image Formalism.L2.DIV.conjPl) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 ha'
    exact hnc b (hT hb) _ (Finset.mem_sdiff.1 ha).1 (fun c hc => ⟨Formalism.L2.DIV.starO c,
      (Formalism.L2.DIV.isConjPl_conjPl b c _ (by rw [Formalism.L2.DIV.starO_coe])).1 hc, by rw [Formalism.L2.DIV.starO_coe]⟩)
  have hf : ∑ a ∈ P \ T, es a = e - ∑ a ∈ T, es a := by
    rw [eq_sub_iff_add_eq, Finset.sum_sdiff hT, hsum]
  refine ⟨(e - ∑ a ∈ T, es a) + cA D (∑ a ∈ T, es a),
    ⟨⟨fun a => if a ∈ P \ T then es a else es2 a, ?_, ?_⟩, ?_⟩⟩
  · intro a ha
    rcases Finset.mem_union.1 ha with h | h
    · simp only [if_pos h]; exact hes a (Finset.mem_sdiff.1 h).1
    · simp only [if_neg (Finset.disjoint_right.1 hdisj h)]; exact hes2 a h
  · rw [Finset.sum_union hdisj, ← hf, hsum2]
    congr 1
    · exact Finset.sum_congr rfl fun a ha => (if_pos ha).symm
    · exact Finset.sum_congr rfl fun a ha => (if_neg (Finset.disjoint_right.1 hdisj ha)).symm
  · generalize (∑ a ∈ T, es a) = t at h1 h2 hTT ⊢
    have h4 : cA D t * cA D e = cA D t := by rw [← map_mul, h1]
    have h5 : cA D t * cA D t = cA D t := by rw [← map_mul, h2]
    rw [map_add (f := _), map_sub, Formalism.L2.Theta.cA_cA]
    linear_combination h0 - (-(e) * h4 + cA D t * h0) + h1 - (-(cA D e) * h1 + t * h0)
      + 2 * hTT - h2 + h4 - h5

end GlobalTheory.IdemFlip
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicLatticeFgAndSpansValueSpaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockHarmonicLattice_fg_and_spans_value_space : ∀ (D : D7) (m n : ℕ) (w : Weight D n) (B : GLR D n) (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ) (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), w.Good → (∀ τ, w.p τ + w.q τ ≤ m) → IsCoefRing σ emb O → Submodule.IsFullLattice D.host.E M → (harmLat σ emb O m w B M).FG ∧ Submodule.span ℂ (harmLat σ emb O m w B M : Set (PolF D m n)) = harm m w B := by
  intro D m n w B K _ _ σ emb O M hw hm hc hM
  letI := hM
  exact GlobalTheory.ExportSeries.HarmLattice.harmLat_fg_span D m n w B K σ emb O M hw hm hc
    (by infer_instance)
end

