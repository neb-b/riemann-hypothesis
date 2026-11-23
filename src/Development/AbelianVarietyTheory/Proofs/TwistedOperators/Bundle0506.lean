module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0475
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1673
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergTranslateThetaContinuousDifferentiable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0486
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SiegelConeIntegralMatrixLatticeCount
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0490
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaProjectionIntertwinesLevelLifts
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaProjEquiv

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem thF_shift_core (R : RealDat D A Ks) (F : Face D A) (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T0) (g0 : G0 R.Pg D.R.r)
    (κ : GA D (Vc D i)) (κ' : GA D (Wc D i)) (hκ : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0 κ)
    (hκ' : κ' ∈ GfC (Wc D i)) (y y' : (R.HV i t).H) (c : ℂ) (hc0 : c ≠ 0)
    (hv : R.ωP i t (κ, κ') (R.vP i t) = c⁻¹ • R.vP i t)
    (hy : ∀ h, (R.HV i t).e y' h = c⁻¹ • (R.HV i t).e y (h * (finHom (Vc D i)).rangeRestrict κ))
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (x : GA D (Wc D i)) :
    R.thF i t y' (fun ρ => v ρ) x = R.thF i t y (fun ρ => v ρ) (x * κ') := by
  refine (hR.thP.thF i t).elim fun thP hPF => ?_
  have hpt : ∀ P, R.ωP i t (κ, κ') (R.ptP i t P) = c⁻¹ • R.ptP i t P :=
    GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) hR.models.inf (hR.thP.ωP i t) _ _ _ _ _ (hR.thP.pt_theta i t)
      κ hκ.1 κ' hκ' c⁻¹ hv
  have hker := fun P => GlobalTheory.thetaKO_rat_left_and_eigen_right R.ψ (Vc D i) (Wc D i) _ _ (R.ωP i t) (hR.thP.ωP i t)
    (R.ptP i t P) (hR.thP.pt_theta i t P)
  have hm := thetaLift_shift hPF.1 (GQ (Vc D i)) κ κ' c hc0
    (integral_shift (Vc D i) (R.βV i) (R.datVt i t) g0 κ hκ (R.νV i t) (hR.models.νV i t).1.1 (R.fdV i t)
      (hR.models.νV i t).2)
    (fun P γ hγ g h => by
      have := (hker P).1 γ hγ 1 (GQ (Wc D i)).one_mem h g
      rwa [one_mul] at this)
    (fun P g h => (hker P).2 κ κ' c⁻¹ (hpt P) h g)
    ((R.extV i t).rangeRestrict y) ((R.extV i t).rangeRestrict y')
    (extV_left R hR.models.HV i t y)
    (fun h => (congrFun ((R.extV i t).map_smul c y').symm h).trans
      (extV_shift R hR.models.cV i t κ hκ.1 c hc0 y y' hy h))
    (PiTensorProduct.tprod ℂ v) x
  exact (congrFun (hPF.2 y' v) x).trans (hm.trans (congrFun (hPF.2 y v) (x * κ')).symm)

theorem thG_of_value_core (R : RealDat D A Ks) (F : Face D A) (hR : GlobalTheory.Hk3.Core R F) (i : Fin D.R.m) (t : T0) (g : G)
    (y y' : (R.HV i t).H) (v : (R.MW i (sg0 D A)).Vec) (hv : ∀ τ, ‖(v τ : (R.MW i (sg0 D A)).H τ)‖ = 1)
    (hact : R.thF i t y' v = actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (R.thF i t y v)) :
    R.thG i t y' = R.gW i (sg0 D A) g (R.thG i t y) := by
  have hinj := GlobalTheory.EvalAtUnitVector.eval_injective (R.MW i (sg0 D A)) (R.HW i (sg0 D A)).H (R.HW i (sg0 D A)).e _
    (R.νW i) (R.fdW i) (hR.models.HW i (sg0 D A)).2.2 v hv
  have e1 : (R.HW i (sg0 D A)).e (R.thG i t y') v = R.eWf i (sg0 D A) (R.thF i t y' v) :=
    congrArg (fun T : MMap (R.MW i (sg0 D A)) => T v) (hR.thP.thG i t y')
  have e2 : (R.HW i (sg0 D A)).e (R.thG i t y) v = R.eWf i (sg0 D A) (R.thF i t y v) :=
    congrArg (fun T : MMap (R.MW i (sg0 D A)) => T v) (hR.thP.thG i t y)
  have e3 : (R.HW i (sg0 D A)).e (R.gW i (sg0 D A) g (R.thG i t y)) v =
      actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) ((R.HW i (sg0 D A)).e (R.thG i t y) v) :=
    congrArg (fun T : MMap (R.MW i (sg0 D A)) => T v) (hR.models.gW i (sg0 D A) g (R.thG i t y))
  have e4 := (GlobalTheory.ProjComm.proj_comm R hR.lev hR.grp.record).2 i (sg0 D A) g _ (thF_type R hR.thP.thF_mem i t y v)
  exact hinj (e1.trans ((congrArg (R.eWf i (sg0 D A)) hact).trans (e4.trans
    ((congrArg (actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)) e2.symm).trans e3.symm))))

theorem thG_intertwines_core : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ i t g κ, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ → ∀ y y' : (R.HV i t).H, (∀ h, (R.HV i t).e y' h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • (R.HV i t).e y (h * (finHom _).rangeRestrict κ)) → R.thG i t y' = R.gW i (sg0 D A) g (R.thG i t y) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR i t g κ hκ y y' hy
  refine (Classical.em (∃ κ', IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) κ')).elim
    (fun hl => hl.elim fun κ' hκ' => (hR.thP.ioP i t).2.2.elim fun v hv => hv.elim fun _ hw => ?_)
    (fun hl => (eq_zero_of_no_lift R hR.models.HW hR.models.gW i (sg0 D A) g hl _).trans
      (eq_zero_of_no_lift R hR.models.HW hR.models.gW i (sg0 D A) g hl _).symm)
  exact thG_of_value_core R F hR i t g y y' (fun ρ => v ρ) hw.1 (funext fun x =>
    (thF_shift_core R F hR i t (R.eG g) κ κ' hκ hκ'.1 y y' (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)
      (levChi_ne_zero (V := Vc D i) (β := R.βV i) (flagL (R.datVt i t)) κ)
      (_root_.GlobalTheory.VecInv.omega_lifts_vP R hR.lev hR.models.inf hR.thP.ωP hR.thP.vP i t (R.eG g) κ κ' hκ hκ') hy v x).trans
    (finiteGroup_acts_by_lift_translation_principalType R i (R.eG g) κ' hκ' _ (thF_type R hR.thP.thF_mem i t y _) x).symm)

end GlobalTheory.ThetaProjEquiv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesEqThetaLiftDefiniteGroupForm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceLift

theorem exists_traceForm {H Γ W : Type} [Group H] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ι : Γ →* H)
    (ρ : Γ →* Module.End ℂ W) (J : Subgroup H) (χ : J →* ℂˣ) (z₀ : H) (hfin : Finite (Bridge.stab ι J z₀)) (w : W) :
    ∃ f ∈ Bridge.AdForms ι ρ J χ, (∀ z, (¬ ∃ (γ : Γ) (k : J), z = ι γ * z₀ * k) → f z = 0) ∧
      ∀ L : W →ₗ[ℂ] ℂ, (∀ (γ : Γ) (hγ : z₀⁻¹ * ι γ * z₀ ∈ J), L ((χ ⟨_, hγ⟩ : ℂ) • ρ γ⁻¹ w) = L w) →
        L (f z₀) = (Nat.card (Bridge.stab ι J z₀) : ℂ) * L w := by
  let T : H → Γ → W := fun z γ => if h : z₀⁻¹ * ι γ * z ∈ J then (χ ⟨_, h⟩ : ℂ) • ρ γ⁻¹ w else 0
  have hS : ∀ z, Function.support (T z) ⊆ {γ | z₀⁻¹ * ι γ * z ∈ J} := fun z γ hγ => by
    by_contra h
    exact hγ (dif_neg h)
  have hS0 : {γ | z₀⁻¹ * ι γ * z₀ ∈ J} = (Bridge.stab ι J z₀ : Set Γ) := by
    ext γ
    exact (Bridge.mem_stab _).symm
  have hfin' : (Bridge.stab ι J z₀ : Set Γ).Finite := hfin
  have hF : ∀ z, {γ | z₀⁻¹ * ι γ * z ∈ J}.Finite := fun z => by
    rcases Set.eq_empty_or_nonempty {γ | z₀⁻¹ * ι γ * z ∈ J} with h | ⟨δ, hδ⟩
    · rw [h]; exact Set.finite_empty
    · refine (hfin'.image (· * δ)).subset fun γ hγ => ⟨γ * δ⁻¹, ?_, by simp⟩
      rw [← hS0]
      have := J.mul_mem hγ (J.inv_mem hδ)
      simpa [mul_assoc] using this
  have hT : ∀ z, (Function.support (T z)).Finite := fun z => (hF z).subset (hS z)
  refine ⟨fun z => ∑ᶠ γ, T z γ, fun δ z k => ?_, fun z hz => ?_, fun L hL => ?_⟩
  · have h1 : ∀ γ, T (ι δ * z * k) γ = ((χ k : ℂ) • ρ δ) (T z (γ * δ)) := fun γ => by
      have e : z₀⁻¹ * ι γ * (ι δ * z * k) = z₀⁻¹ * ι (γ * δ) * z * k := by rw [map_mul]; group
      by_cases h : z₀⁻¹ * ι (γ * δ) * z ∈ J
      · have h' : z₀⁻¹ * ι γ * (ι δ * z * k) ∈ J := by rw [e]; exact J.mul_mem h k.2
        have e2 : (⟨_, h'⟩ : J) = ⟨_, h⟩ * k := Subtype.ext e
        have e3 : ρ δ (ρ (γ * δ)⁻¹ w) = ρ γ⁻¹ w := by
          rw [← Module.End.mul_apply, ← map_mul, _root_.mul_inv_rev, mul_inv_cancel_left]
        simp only [T]
        rw [dite_eq_left h, dite_eq_left h', e2, map_mul, LinearMap.smul_apply, map_smul, e3, smul_smul, Units.val_mul, mul_comm]
      · have h' : z₀⁻¹ * ι γ * (ι δ * z * k) ∉ J := by rw [e, J.mul_mem_cancel_right k.2]; exact h
        simp only [T]
        rw [dif_neg h, dif_neg h', map_zero]
    show ∑ᶠ γ, T (ι δ * z * k) γ = ((χ k : ℂ) • ρ δ) (∑ᶠ γ, T z γ)
    rw [map_finsum _ (hT z), finsum_congr h1]
    exact finsum_comp_equiv (Equiv.mulRight δ) (f := fun γ => ((χ k : ℂ) • ρ δ) (T z γ))
  · refine finsum_eq_zero_of_forall_eq_zero fun γ => dif_neg fun h => hz ⟨γ⁻¹, ⟨_, h⟩, ?_⟩
    rw [map_inv]; group
  · show L (∑ᶠ γ, T z₀ γ) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [finsum_eq_sum_of_support_subset (s := hfin'.toFinset) _ (by rw [Set.Finite.coe_toFinset, ← hS0]; exact hS z₀),
      map_sum, Finset.sum_congr rfl (g := fun _ => L w) fun γ hγ => ?_]
    · rw [Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card _ hfin']
      rfl
    · have h : z₀⁻¹ * ι γ * z₀ ∈ J := (Bridge.mem_stab _).1 (hfin'.mem_toFinset.1 hγ)
      simp only [T]
      rw [dite_eq_left h, hL]

theorem finite_stab {H Γ I : Type} [Group H] [Group Γ] (ι : Γ →* H) (J : Subgroup H) {y : I → H} (hy : Bridge.IsReps ι J y)
    (hf : ∀ c, Finite (Bridge.stab ι J (y c))) (z : H) : Finite (Bridge.stab ι J z) := by
  obtain ⟨c, ⟨γ, m, e⟩, -⟩ := hy z
  have key : ∀ δ : Bridge.stab ι J z, γ⁻¹ * δ.1 * γ ∈ Bridge.stab ι J (y c) := fun δ => by
    have h1 : z⁻¹ * ι δ.1 * z ∈ J := (Bridge.mem_stab _).1 δ.2
    rw [Bridge.mem_stab]
    have h2 := J.mul_mem (J.mul_mem m.2 h1) (J.inv_mem m.2)
    generalize δ.1 = d at h2
    rw [e] at h2
    simpa [mul_assoc] using h2
  haveI := hf c
  refine Finite.of_injective (fun δ => (⟨_, key δ⟩ : Bridge.stab ι J (y c))) fun a b hab => ?_
  exact Subtype.ext (mul_left_cancel (mul_right_cancel (congrArg Subtype.val hab)))

theorem exists_isReps_through {H Γ I : Type} [Group H] [Group Γ] (ι : Γ →* H) (J : Subgroup H) {y : I → H}
    (hy : Bridge.IsReps ι J y) (z : H) : ∃ (y' : I → H) (c : I), Bridge.IsReps ι J y' ∧ y' c = z := by
  obtain ⟨c, ⟨γ, m, e⟩, -⟩ := hy z
  refine ⟨Function.update y c z, c, fun g => ?_, Function.update_self _ _ _⟩
  have hiff : ∀ j, (∃ (δ : Γ) (k : J), g = ι δ * Function.update y c z j * k) ↔ ∃ (δ : Γ) (k : J), g = ι δ * y j * k := by
    intro j
    by_cases hj : j = c
    · subst hj
      rw [Function.update_self, e]
      constructor
      · rintro ⟨δ, k, h⟩
        exact ⟨δ * γ, m * k, by rw [h, map_mul, Subgroup.coe_mul]; group⟩
      · rintro ⟨δ, k, h⟩
        exact ⟨δ * γ⁻¹, m⁻¹ * k, by rw [h, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]; group⟩
    · rw [Function.update_of_ne hj]
  simp only [hiff]
  exact hy g

theorem exists_form_sum {H Hf W : Type} [Group H] [Group Hf] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (p : H →* Hf)
    (hp : Function.Surjective p) (Γ F R : Subgroup H) (ρ : H →* Module.End ℂ W) (J : Subgroup Hf) (χ : J →* ℂˣ)
    (hdec : ∀ u : H, ∃ k ∈ F, ∃ a ∈ R, u = k * a ∧ p k = p u) (hρ : ∀ k ∈ F, ρ k = 1)
    (Cl : Type) [Fintype Cl] (y : Cl → Hf) (hy : Bridge.IsReps (p.comp Γ.subtype) J y)
    (hfin : ∀ k, Finite (Bridge.stab (p.comp Γ.subtype) J (y k))) (h : H) (w : W) :
    ∃ f ∈ Bridge.AdForms (p.comp Γ.subtype) (ρ.comp Γ.subtype) J χ, ∃ r : Cl → H, (∀ k, r k ∈ F) ∧
      Bridge.IsReps (p.comp Γ.subtype) J (fun k => p (r k)) ∧
      ∀ {G' X : Type} [Group G'] (x₀ : X) (om : H × G' →* Module.End ℂ (X → ℂ)) (Λ : W →ₗ[ℂ] (X → ℂ)),
        (∀ γ ∈ Γ, ∀ z v, om (γ, 1) (om z (Λ v)) x₀ = om z (Λ v) x₀) → (∀ a ∈ R, ∀ v, om (a, 1) (Λ v) = Λ (ρ a v)) →
        (∀ k ∈ F, ∀ hk : p k ∈ J, ∀ v, om (k, 1) (Λ v) = ((χ ⟨p k, hk⟩ : ℂˣ) : ℂ)⁻¹ • Λ v) →
        ∀ g : G', ∑ k, ((J.relIndex J : ℕ) : ℂ)⁻¹ * ((Nat.card (Bridge.stab (p.comp Γ.subtype) J (p (r k))) : ℕ) : ℂ)⁻¹ *
          om (r k, g) (Λ (f (p (r k)))) x₀ = om (h, g) (Λ w) x₀ := by
  obtain ⟨h₀, hh₀, a, ha, rfl, -⟩ := hdec h
  obtain ⟨y', c₀, hy', e₀⟩ := exists_isReps_through _ _ hy (p h₀)
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
  have hf0 := finite_stab _ _ hy hfin (p h₀)
  obtain ⟨f, hf, hz, hv⟩ := exists_traceForm (p.comp Γ.subtype) (ρ.comp Γ.subtype) J χ (p h₀) hf0 (ρ a w)
  refine ⟨f, hf, r, fun k => (hr k).1, by rw [hyr]; exact hy', fun {G' X} _ x₀ om Λ hom hΛa hΛk g => ?_⟩
  rw [Finset.sum_eq_single c₀ ?_ (fun h => absurd (Finset.mem_univ _) h)]
  · let L₀ : W →ₗ[ℂ] ℂ := (LinearMap.proj x₀ : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (om (h₀, g)) ∘ₗ Λ
    have hL₀ : ∀ v, L₀ v = om (h₀, g) (Λ v) x₀ := fun v => rfl
    have key := hv L₀ fun γ hγ => ?_
    · have hN : ((Nat.card (Bridge.stab (p.comp Γ.subtype) J (p h₀)) : ℕ) : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.2 (Nat.card_pos).ne'
      have e1 : (h₀ * a, g) = ((h₀, g) : H × G') * (a, 1) := by rw [Prod.mk_mul_mk, mul_one]
      rw [hr0, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_mul, ← hL₀, key, inv_mul_cancel_left₀ hN, hL₀, e1,
        map_mul, Module.End.mul_apply, hΛa a ha]
    · generalize ρ a w = v
      obtain ⟨k, hk, b, hb, e, e'⟩ := hdec ((γ : H)⁻¹ * h₀)
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


set_option maxHeartbeats 1000000 in
theorem exists_thF_eq_thetaKO : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → ∀ (i : Fin D.R.m) (t : T0) (h : GA D (Vc D i)) (w : (R.cV i).W), ∃ x : (R.HV i t).H, ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)), R.thF i t x (fun ρ => u ρ) g = thetaKO (R.ωP i t) h g (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) w)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hlev hmod hth i t h w
  refine (hth.thF i t).elim fun thP hPF => ?_
  refine (exists_form_sum (finHom (Vc D i)).rangeRestrict (finHom (Vc D i)).rangeRestrict_surjective (GQ (Vc D i))
    (GfC (Vc D i)) (GinfC (Vc D i)) (R.cV i).ρ (levEnv _ (R.βV i) (R.datVt i t)).J (levEnv _ (R.βV i) (R.datVt i t)).χ
    (GlobalTheory.LiftUnfold.exists_fin_mul_real (Vc D i)) (hmod.cV i).1 _ (R.B.L i t).pres.y (R.B.L i t).pres.reps
    (fun c => Finite.of_equiv _ ((R.B.L i t).pres.stabI c).toEquiv) h w).elim fun f hf0 => hf0.2.elim fun r hr => ?_
  have hf : f ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ
      (levEnv _ (R.βV i) (R.datVt i t)).J (levEnv _ (R.βV i) (R.datVt i t)).χ := hf0.1
  refine (LinearMap.mem_range.1 ((hmod.HV i t).2.1.ge hf)).elim fun x hx => ⟨x, fun u g => ?_⟩
  have hlaw : ∀ k ∈ GfC (Vc D i), ∀ hk : fin (Vc D i) k ∈ (levEnv _ (R.βV i) (R.datVt i t)).J,
      R.ωP i t (k, 1) (R.vP i t) =
        (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨fin (Vc D i) k, hk⟩ : ℂˣ) : ℂ)⁻¹ • R.vP i t := by
    intro k hkf hk
    have hl : Formalism.IndefR.Lev.finE (Vc D i) k ∈ Formalism.L2.DIV.lev D.sp.cm (Vc D i).gram (R.βV i)
        (Formalism.IndefR.Lev.flag1L (R.datVt i t)) := hk
    have hκ : Formalism.IndefR.Lev.IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) 1 k := ⟨hkf, hl.1, Subgroup.mem_bot.1 hl.2⟩
    have hκ' : Formalism.IndefR.Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 1 :=
      ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _, by rw [map_one]; exact Formalism.L2.DIV.rTup_one⟩
    refine (GlobalTheory.VecInv.omega_lifts_vP R hlev hmod.inf hth.ωP hth.vP i t 1 k 1 hκ hκ').trans ?_
    exact congrArg (fun z : ℂˣ => (z : ℂ)⁻¹ • R.vP i t)
      (Formalism.IndefR.Lev.levFn_flag1 (V := Vc D i) (β := R.βV i) (L := R.datVt i t) (Formalism.IndefR.Lev.finE (Vc D i) k)).symm
  have hfin : ∀ k ∈ GfC (Vc D i), ∀ hk : fin (Vc D i) k ∈ (levEnv _ (R.βV i) (R.datVt i t)).J, ∀ P,
      R.ωP i t (k, 1) (R.ptP i t P) =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨fin (Vc D i) k, hk⟩ : ℂˣ) : ℂ)⁻¹ • R.ptP i t P := fun k hk hk' =>
    GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) hmod.inf
      (hth.ωP i t) _ _ _ _ _ (hth.pt_theta i t) k hk 1 (one_mem _) _ (hlaw k hk hk')
  have key := GlobalTheory.LiftUnfold.integral_theta (hth.ωP i t) (D.sp.V_sig _) (hmod.vpos i) (R.cV i) (hmod.cV i) (R.βV i)
    (R.datVt i t) (fun _ => Iff.rfl) hf
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i t) ∘ₗ R.ioP i (PiTensorProduct.tprod ℂ u)) (fun w => hth.pt_theta i t _)
    (fun a ha w => (hth.ioP i t).1 a ha _ w) (fun k hk hk' w => hfin k hk hk' _)
    (hmod.νV i t) _ _ r le_rfl (by rw [Subgroup.relIndex_self]; exact one_ne_zero) hr.2.1 hr.1 g
  have key2 := hr.2.2 (0 : WO (Vc D i) (Wc D i)) (R.ωP i t)
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i t) ∘ₗ R.ioP i (PiTensorProduct.tprod ℂ u))
    (fun γ hγ z v => (hth.ωP i t).om_aut γ hγ 1 (one_mem _) _ ((hth.ωP i t).om_pres _ _ (hth.pt_theta i t _)))
    (fun a ha w => (hth.ioP i t).1 a ha _ w) (fun k hk hk' w => hfin k hk hk' _) g
  have h1 := congrFun (hPF.2 x u) g
  have h2 := hPF.1.eq ((R.extV i t).rangeRestrict x) (PiTensorProduct.tprod ℂ u) g
  refine h1.trans (h2.trans (Eq.trans ?_ (key.trans key2)))
  rw [← hx]
  rfl

end GlobalTheory.TraceLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TorusMixedCoordinateSumLeSobolevSeminorm
section
namespace I195MixedCoordinates_36336a34ca84d0e19c17303f

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_36336a34ca84d0e19c17303f

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid

noncomputable section

namespace GlobalTheory.TorusMixedSum

set_option maxHeartbeats 1000000 in
theorem sum_mixS_le : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (θ : InfFam D), IsInfFam θ →
    ∀ (V X S₀ : HSp D) (r : ℕ) (d : GlobalTheory.MixModel.HypDec V S₀ r) (μ' : Measure (Mx D X.rank r))
    (𝓕' : Set (Mx D X.rank r)), IsCovolOne (GlobalTheory.MixModel.ratMx D X.rank r) μ' 𝓕' → ∀ (c : ℝ), 0 < c →
    ∀ (K₀ : Set (WO V X)), K₀ ∈ nhds (0 : WO V X) → IsCompact K₀ →
    ∀ (μ : Measure (WO V X)) (𝓕 : Set (WO V X)), IsCovolOne (ratL X V) μ 𝓕 →
    ∃ (k A : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ Ψ : WO V X → ℂ, IsThetaFunO ψ V X Ψ →
      (∀ u ∈ K₀, u.map (infPart D) = 0 → heisO ψ V X (n • u) Ψ = Ψ) →
      ∀ t ∈ GlobalTheory.SiegelSet.cone r c, ∀ α : Mx D r r, α.map (finPart D) = 1 →
        (∀ τ, compAt θ τ α = diagonal (fun i => (t i : ℂ))) →
        ∑' ξ : Matrix (Fin X.rank) (Fin r) D.host.E, ‖d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0‖ₑ ≤
          ENNReal.ofReal (C * (n : ℝ) ^ A * (GlobalTheory.Size.sobO (V := V) (W := X) ψ θ μ 𝓕 k Ψ).toReal) := by
  intro D ψ hψ θ hθ V X S₀ r d μ' 𝓕' hμ' c hc K₀ hK₀ hK₀c μ 𝓕 hμ
  obtain ⟨N, A₄, C₄, hC₄, h4⟩ := _root_.GlobalTheory.LatCount.lattice_count θ hθ X.rank r c hc
  obtain ⟨k₂, C₂, hC₂, h2⟩ := _root_.GlobalTheory.MixWeight.mixS_weight_le ψ hψ θ hθ V X S₀ r d μ' 𝓕' hμ' N
  obtain ⟨k₁, B, C₁, hC₁, h1⟩ := GlobalTheory.T.thetaFunction_heisenbergWord_sup_le_level_pow ψ hψ θ hθ V X K₀ hK₀ hK₀c μ 𝓕 hμ
  obtain ⟨M, hM, h3⟩ := _root_.GlobalTheory.MixSupport.mixS_support_integral ψ hψ V X S₀ r d μ' 𝓕' hμ' K₀ hK₀ hK₀c
  set Wc : ℝ := ∑ k ∈ Finset.range (k₂ + 1),
    (Fintype.card (D.what₂.Tau × Fin X.rank × Fin V.rank × Bool) : ℝ) ^ k with hWc
  have hWc0 : 0 ≤ Wc := Finset.sum_nonneg fun _ _ => by positivity
  refine ⟨k₁ + k₂, B + A₄, C₂ * Wc * C₁ * C₄ * (M : ℝ) ^ A₄, by positivity, ?_⟩
  intro n hn Ψ hΨ hlev t ht α hα hαc
  set sob := GlobalTheory.Size.sobO (V := V) (W := X) ψ θ μ 𝓕 (k₁ + k₂) Ψ with hsob
  have hsob_ne : sob ≠ ⊤ := GlobalTheory.Size.sobO_ne_top hψ hθ hμ.1 hμ.2.1 hΨ _

  have hw : GlobalTheory.Size.wordSum (GlobalTheory.Size.heisDer ψ θ) GlobalTheory.HeisTaylor.supN k₂ Ψ ≤
      ENNReal.ofReal (Wc * (C₁ * (n : ℝ) ^ B)) * sob := by
    unfold GlobalTheory.Size.wordSum
    have hk : ∀ k ∈ Finset.range (k₂ + 1), ∀ a : Fin k → D.what₂.Tau × Fin X.rank × Fin V.rank × Bool,
        GlobalTheory.HeisTaylor.supN (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) (List.ofFn a) Ψ) ≤
          ENNReal.ofReal (C₁ * (n : ℝ) ^ B) * sob := by
      intro k hk a
      refine (h1 n hn Ψ hΨ hlev (List.ofFn a)).trans ?_
      rw [List.length_ofFn]
      gcongr
      exact GlobalTheory.Size.wordSum_mono (by have := Finset.mem_range.1 hk; omega) Ψ
    calc ∑ k ∈ Finset.range (k₂ + 1), ∑ a : Fin k → D.what₂.Tau × Fin X.rank × Fin V.rank × Bool,
          GlobalTheory.HeisTaylor.supN (GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) (List.ofFn a) Ψ)
        ≤ ∑ k ∈ Finset.range (k₂ + 1), ∑ _a : Fin k → D.what₂.Tau × Fin X.rank × Fin V.rank × Bool,
          ENNReal.ofReal (C₁ * (n : ℝ) ^ B) * sob :=
          Finset.sum_le_sum fun k hk' => Finset.sum_le_sum fun a _ => hk k hk' a
      _ = ENNReal.ofReal (Wc * (C₁ * (n : ℝ) ^ B)) * sob := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
          rw [← Finset.sum_mul, hWc, ENNReal.ofReal_mul hWc0, ← mul_assoc]
          congr 2
          rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
          push_cast; rfl
  set K := ENNReal.ofReal C₂ * (ENNReal.ofReal (Wc * (C₁ * (n : ℝ) ^ B)) * sob) with hK
  set L : ℕ := M * n with hL
  have hLpos : 0 < L := Nat.mul_pos hM hn

  have hpt : ∀ ξ : Matrix (Fin X.rank) (Fin r) D.host.E,
      ‖d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0‖ₑ ≤
        {ξ : Matrix (Fin X.rank) (Fin r) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator
          (fun ξ => ENNReal.ofReal ((1 + ∑ τ, ∑ i, ∑ j,
            ‖(compAt θ τ (ξ.map (incA D) : Mx D X.rank r) * diagonal (fun k => (t k : ℂ))) i j‖) ^ N)⁻¹) ξ * K := by
    intro ξ
    by_cases h0 : (_root_.I195MixedCoordinates_36336a34ca84d0e19c17303f.source d) X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0 = 0
    · have hz : d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0 = 0 := h0
      rw [hz, enorm_zero]; exact bot_le
    have hfin : (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α).map (finPart D) =
        (ξ.map (incA D) : Mx D X.rank r).map (finPart D) := by
      rw [Matrix.map_mul, hα, Matrix.mul_one]
    have hint := h3 n hn Ψ hΨ hlev ξ _ hfin h0
    rw [Set.indicator_of_mem (show ξ ∈ {ξ : Matrix (Fin X.rank) (Fin r) D.host.E |
      ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)} from hint)]
    have hc' : ∀ τ, compAt θ τ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) =
        compAt θ τ (ξ.map (incA D) : Mx D X.rank r) * diagonal (fun k => (t k : ℂ)) := by
      intro τ
      rw [← hαc τ]
      exact Matrix.map_mul (f := ((θ τ).comp (infPart D)))
    have hb := h2 Ψ hΨ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α)
    simp only [hc'] at hb
    set P := ENNReal.ofReal ((1 + ∑ τ, ∑ i, ∑ j,
      ‖(compAt θ τ (ξ.map (incA D) : Mx D X.rank r) * diagonal (fun k => (t k : ℂ))) i j‖) ^ N) with hP
    have hP0 : P ≠ 0 := by
      rw [hP, ne_eq, ENNReal.ofReal_eq_zero, not_le]
      exact pow_pos (by positivity) _
    have hPt : P ≠ ⊤ := ENNReal.ofReal_ne_top
    have hb' : ‖d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0‖ₑ * P ≤ K :=
      hb.trans (by rw [hK]; gcongr)
    rw [ENNReal.ofReal_inv_of_pos (pow_pos (by positivity) _), ← hP, ← ENNReal.div_eq_inv_mul]
    exact (ENNReal.le_div_iff_mul_le (Or.inl hP0) (Or.inl hPt)).2 hb'
  have e : sob = ENNReal.ofReal sob.toReal := (ENNReal.ofReal_toReal hsob_ne).symm
  calc ∑' ξ : Matrix (Fin X.rank) (Fin r) D.host.E,
        ‖d.mixS X ψ μ' 𝓕' Ψ (HMul.hMul (ξ.map (incA D) : Mx D X.rank r) α) 0‖ₑ
      ≤ ∑' ξ : Matrix (Fin X.rank) (Fin r) D.host.E,
        {ξ : Matrix (Fin X.rank) (Fin r) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator
          (fun ξ => ENNReal.ofReal ((1 + ∑ τ, ∑ i, ∑ j,
            ‖(compAt θ τ (ξ.map (incA D) : Mx D X.rank r) * diagonal (fun k => (t k : ℂ))) i j‖) ^ N)⁻¹) ξ * K :=
        ENNReal.tsum_le_tsum hpt
    _ = (∑' ξ : Matrix (Fin X.rank) (Fin r) D.host.E,
        {ξ : Matrix (Fin X.rank) (Fin r) D.host.E | ∀ i j, IsIntegral ℤ ((L : D.host.E) * ξ i j)}.indicator
          (fun ξ => ENNReal.ofReal ((1 + ∑ τ, ∑ i, ∑ j,
            ‖(compAt θ τ (ξ.map (incA D) : Mx D X.rank r) * diagonal (fun k => (t k : ℂ))) i j‖) ^ N)⁻¹) ξ) * K :=
        ENNReal.tsum_mul_right
    _ ≤ ENNReal.ofReal (C₄ * (L : ℝ) ^ A₄) * K := by gcongr; exact h4 L hLpos t ht
    _ = ENNReal.ofReal (C₄ * (L : ℝ) ^ A₄) * (ENNReal.ofReal C₂ *
          (ENNReal.ofReal (Wc * (C₁ * (n : ℝ) ^ B)) * ENNReal.ofReal sob.toReal)) := by rw [hK, ← e]
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hC₂, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [hL]
      push_cast
      ring

end GlobalTheory.TorusMixedSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumFixedOfFixesPureTensorsVacuaOutsideStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_fixed_of_fixes_pureTensors_vacuaOutside : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Wd.J)
    (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))), M.vac v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v) →
    (∀ w ∉ S, M.vac w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1) →
    (∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Fv F w) → ℂ),
      (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F w)) → (∀ w ∉ S, φ w = M.vac w) →
      om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) →
    ∀ ψ : (Fin n × Fin d → Fv F v) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, k)) (M.vac v) ψ → ψ = M.vac v := by
  first | exact @GlobalTheory.TripleAssembly.vac_fixed_of_pure_fixed | exact GlobalTheory.TripleAssembly.vac_fixed_of_pure_fixed | (intros; apply GlobalTheory.TripleAssembly.vac_fixed_of_pure_fixed <;> assumption)
end

