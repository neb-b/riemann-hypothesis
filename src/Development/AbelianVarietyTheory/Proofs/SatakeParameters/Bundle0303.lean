module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharacteristicFunctionIntegralApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0989
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrimeToHostCore
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0265
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftAutomorphicForm
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ThetaRead

open MeasureTheory Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.RecTie
  Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.ThetaTri
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Pair

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem ipM_proj (hM : R.IsModels) (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (i : Fin D.R.m) {S U : MMap (R.MW i (sg0 D A))}
    (hS : S ∈ R.Wall i (sg0 D A)) (hU : U ∈ R.Wall i (sg0 D A)) (hfix : ∀ v, R.eWf i (sg0 D A) (S v) = S v) :
    ipM (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) S (postOn _ (R.eWf i (sg0 D A)) U) =
      ipM (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) S U ∧
    ∃ c, IsMultIP (R.MW i (sg0 D A)) (R.νW i) (R.fdW i) S U c := by
  obtain ⟨hinj, hr, hip⟩ := hM.HW i (sg0 D A)
  obtain ⟨a, rfl⟩ : S ∈ LinearMap.range (R.HW i (sg0 D A)).e := hr ▸ hS
  obtain ⟨b, rfl⟩ : U ∈ LinearMap.range (R.HW i (sg0 D A)).e := hr ▸ hU
  refine ⟨?_, GlobalTheory.LiftLower.IsMultIP₂ (R.HW i (sg0 D A)) hip a b⟩
  have he : ∀ x, (R.HW i (sg0 D A)).e (GlobalTheory.Hk3.eH R i x) = postOn _ (R.eWf i (sg0 D A)) ((R.HW i (sg0 D A)).e x) :=
    fun x => GlobalTheory.LiftLower.e_projH hM.gW i (sg0 D A) x
  have ha : GlobalTheory.Hk3.eH R i a = a := by
    apply hinj
    rw [he]
    exact MultilinearMap.ext fun v => hfix v
  have h1 : ⟪a, GlobalTheory.Hk3.eH R i b⟫_ℂ = ⟪a, b⟫_ℂ := by
    rw [← LinearMap.adjoint_inner_left, GlobalTheory.LiftScalarL.adjoint_eH R hM hX i, ha]
  rw [hip, hip, he] at h1
  have hN : (∏ ρ, ((dimK _ _ (kapAt (Wc D i) (sg0 D A) ρ) : ℚ) : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun ρ _ => by exact_mod_cast (GlobalTheory.Mem.EasyInputs.dimOK D i (sg0 D A) ρ).ne'
  exact mul_left_cancel₀ hN h1

theorem mult_le_wall (F : Face D A) (b : Bool) (i : Fin D.R.m) :
    Mult R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A))))
      (levChi _ (R.βW i) (R.datWp i (R.levL F b (sg0 D A)))) ≤ R.Wall i (sg0 D A) :=
  GlobalTheory.PartDims.mult_le R.θ _ fun k hk => by
    obtain ⟨h1, h2, h3⟩ := GlobalTheory.PartDims.mem_levi_flag_of_mem_parabolic (L := R.datWp i R.triv) rfl rfl (R.levL F b (sg0 D A)) hk
    exact ⟨h1, h2.trans h3.symm⟩

end Pair

section Unit

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)

abbrev emb : LowT M →ₗ[ℂ] SmT M := PiTensorProduct.map fun τ => (lowT M τ).subtype

theorem integral_kUnit (hne : ∀ τ, lowT M τ ≠ ⊥) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T U : MMap M)
    (h : ∃ c, IsMultIP M μ 𝓕 T U c) :
    ∫ g in 𝓕, star (PiTensorProduct.lift T (emb M (kUnit M)) g) * PiTensorProduct.lift U (emb M (kUnit M)) g ∂μ =
      ipM M μ 𝓕 T U := by
  have hu : ∀ τ, ∃ u : ↥(lowT M τ), ‖((u : M.sm τ) : M.H τ)‖ = 1 := by
    intro τ
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).1 (hne τ)
    have h0 : (u : M.H τ) ≠ 0 := fun h => hu0 (Submodule.coe_eq_zero.1 h)
    refine ⟨((‖(u : M.H τ)‖⁻¹ : ℝ) : ℂ) • ⟨u, hu⟩, ?_⟩
    simp only [Submodule.coe_smul, norm_smul, Complex.norm_real, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.2 h0)
  let v : M.Vec := fun τ =>
    ((Classical.epsilon fun u : ↥(lowT M τ) => ‖((u : M.sm τ) : M.H τ)‖ = 1 : ↥(lowT M τ)) : M.sm τ)
  have hv : ∀ τ, ‖(v τ : M.H τ)‖ = 1 := fun τ => Classical.epsilon_spec (hu τ)
  have hk : emb M (kUnit M) = PiTensorProduct.tprod ℂ v := PiTensorProduct.map_tprod _ _
  rw [hk, PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod, (ipM_spec M μ 𝓕 T U h v v).2]
  simp [inner_self_eq_norm_sq_to_K, hv]

theorem emb_eq_zero {τ : D.what₂.Tau} (h : lowT M τ = ⊥) : emb M = 0 := by
  classical
  ext v
  have : (lowT M τ).subtype (v τ) = 0 := (Submodule.mem_bot ℂ).1 (h ▸ (v τ).2)
  simp only [LinearMap.compMultilinearMap_apply, PiTensorProduct.map_tprod, LinearMap.zero_apply]
  exact MultilinearMap.map_coord_zero _ τ this

theorem integral_zero_right (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T U : MMap M) (hU : U = 0) (k : SmT M) :
    ipM M μ 𝓕 T U = ∫ g in 𝓕, star (PiTensorProduct.lift T k g) * PiTensorProduct.lift U k g ∂μ := by
  subst hU
  choose s hs using GlobalTheory.Mem.EasyInputs.smAll D V S M
  have hs0 : ∏ τ, ⟪(s τ : M.H τ), (s τ : M.H τ)⟫_ℂ ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => inner_self_ne_zero.2 fun h => hs τ (Submodule.coe_eq_zero.1 h)
  have hz : IsMultIP M μ 𝓕 T 0 0 := by
    intro v v'; simp
  rw [hasPeterssonInner_unique _ _ _ _ _ s hs0 (ipM_spec _ _ _ _ _ ⟨_, hz⟩) hz]
  simp

end Unit

theorem lift_post {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (L : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (U : MMap M) :
    PiTensorProduct.lift (postOn M L U) = L ∘ₗ PiTensorProduct.lift U := by
  ext v
  simp [postOn]

section Row

variable {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)


set_option maxHeartbeats 1000000 in
theorem ipM_theta {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) (x : D.what₂.Mt μ (j.1 + 1)) (y : D.what₂.Mj (j.1 + 1))
    (T T' : MMap (X.R.MW j (sg0 D X.A))) (hT : PiTensorProduct.lift T = (X.IL.jMj j y).1)
    (hT' : PiTensorProduct.lift T' = (X.IL.jMj j (D.what₂.thetaP μ (j.1 + 1) x)).1) :
    ipM (X.R.MW j (sg0 D X.A)) (X.R.νW j) (X.R.fdW j) T T' =
      ∫ g in X.R.fdW j, star (PiTensorProduct.lift T (emb _ (kUnit (X.R.MW j (sg0 D X.A)))) g) *
        (∫ h in X.R.fdV j (X.tupT μ), thetaKO (X.R.ωP j (X.tupT μ)) h g
          (X.R.ptP j (X.tupT μ) (X.R.ioP j (kUnit (X.R.MW j (sg0 D X.A))) (X.fn hμ j x h))) ∂(X.R.νV j (X.tupT μ)))
        ∂(X.R.νW j) := by
  have hM := X.given.core.models
  obtain ⟨w, hw1, hw2, hw3⟩ := X.fire.2.1 μ hμ j x
  have hth := X.recR.tied.lift.theta μ hμ j x w (X.fire.1 _ hμ j) hw1 hw2 hw3
  obtain ⟨U, hU, hUw⟩ := hw1
  have hUw' : PiTensorProduct.lift U = w := hUw
  obtain ⟨T₀, hT₀, hT₀y⟩ := (X.IL.jMj j y).2
  have hTT : T₀ = T := PiTensorProduct.lift.injective (hT₀y.trans hT.symm)
  subst hTT
  obtain ⟨hT1, hT2⟩ := (mem_goodPart _ _ _ _ _ _).1 hT₀
  have hT'U : T' = postOn (X.R.MW j (sg0 D X.A)) (X.R.eWf j (sg0 D X.A)) U := by
    apply PiTensorProduct.lift.injective
    rw [hT', hth, ← hUw']
    exact (lift_post (X.R.MW j (sg0 D X.A)) _ U).symm
  have hin : ∀ g, (∫ h in X.R.fdV j (X.tupT μ), thetaKO (X.R.ωP j (X.tupT μ)) h g
      (X.R.ptP j (X.tupT μ) (X.R.ioP j (kUnit (X.R.MW j (sg0 D X.A))) (X.fn hμ j x h))) ∂(X.R.νV j (X.tupT μ))) =
      PiTensorProduct.lift U (emb _ (kUnit (X.R.MW j (sg0 D X.A)))) g := by
    intro g
    have e1 := (X.fire.1 _ hμ j).eq (X.IL.jMt μ hμ j x) (kUnit (X.R.MW j (sg0 D X.A))) g
    rw [← hw2, ← hUw'] at e1
    exact e1.symm
  obtain ⟨p1, p2⟩ := ipM_proj X.R hM X.given.irr j (mult_le_wall X.R X.F false j hT1) (mult_le_wall X.R X.F false j hU) hT2
  simp only [hin]
  rw [hT'U]
  refine p1.trans ?_
  by_cases hne : ∀ τ, lowT (X.R.MW j (sg0 D X.A)) τ ≠ ⊥
  · exact (integral_kUnit _ hne _ _ _ _ p2).symm
  · push Not at hne
    obtain ⟨τ, hτ⟩ := hne
    have h0 := emb_eq_zero _ hτ
    have hw0 : w = 0 := X.fire.2.2 j w ⟨U, hU, hUw⟩
      ((congrArg (fun e => w ∘ₗ e) h0).trans (LinearMap.comp_zero _))
    have hU0 : U = 0 := PiTensorProduct.lift.injective (by rw [hUw', hw0, map_zero])
    exact integral_zero_right (X.R.MW j (sg0 D X.A)) _ _ _ _ hU0 _

end Row

section Forms

variable {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} {X : GlobalTheory.NJoin.RealAt D cf nch tp}
  {M : MtFam D} {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}

theorem ext_pre {V : HSp D} {n : ℕ} (c : CoefA V) (hc : ∀ h ∈ GfC V, c.ρ h = 1) (PV : principalLevelFrame.RowPsi V n)
    (f : Bridge.Gf V → c.W) : c.ext (fun k => c.ext f (PV.ψ (preF PV k))) = c.ext f := by
  refine congrArg c.ext (funext fun k => ?_)
  have hex : ∃ κ, (finHom V).rangeRestrict (PV.ψ κ) = k := by
    obtain ⟨κ, hκ, e⟩ := Formalism.IndefR.Eqv.Act.exists_finLift V k
    obtain ⟨h, rfl⟩ := PV.onto κ hκ
    exact ⟨h, Subtype.ext e⟩
  have hp : (finHom V).rangeRestrict (PV.ψ (preF PV k)) = k := by
    unfold preF
    rw [dite_eq_left hex]
    exact hex.choose_spec
  show c.ρ (PV.ψ (preF PV k))⁻¹ (f ((finHom V).rangeRestrict (PV.ψ (preF PV k)))) = _
  rw [hp, hc _ (inv_mem (PV.into _)), Module.End.one_apply]


set_option maxHeartbeats 1000000 in
theorem ext_real (hV : X.R.models_cV) (A : GlobalTheory.NJoin.Agree X M rep) {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m)
    (x : D.what₂.Mt μ (j.1 + 1)) :
    (X.R.cV j).ext (fun k => (A.eW μ hμ j).symm ((M μ (j.1 + 1) (by omega) (by omega)).real x (A.a j * preF (A.PV j) k))) =
      X.fn hμ j x := by
  obtain ⟨z, hz⟩ : X.fn hμ j x ∈ LinearMap.range (X.R.extV j (X.tupT μ)) := (X.IL.jMt μ hμ j x).2.1
  have hz' : (X.R.cV j).ext ((X.R.HV j (X.tupT μ)).e z) = X.fn hμ j x := hz
  have e : (fun k => (A.eW μ hμ j).symm ((M μ (j.1 + 1) (by omega) (by omega)).real x (A.a j * preF (A.PV j) k))) =
      fun k => X.fn hμ j x ((A.PV j).ψ (preF (A.PV j) k)) := by
    funext k
    refine (LinearEquiv.symm_apply_eq _).2 ((A.real μ hμ j x _).trans ?_)
    rw [inv_mul_cancel_left]
  refine (congrArg (X.R.cV j).ext e).trans ?_
  generalize X.fn hμ j x = φ at hz' ⊢
  subst hz'
  exact ext_pre _ (hV j).1 _ _

theorem ext_real_cast (hV : X.R.models_cV) (A : GlobalTheory.NJoin.Agree X M rep) {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m)
    (k : ℕ) (hk : j.1 + 1 = k) (p1 : 1 ≤ k) (p2 : k ≤ D.R.m) (x : D.what₂.Mt μ k) :
    (X.R.cV j).ext (fun q => (Eq.ndrec (motive := fun k => (p1 : 1 ≤ k) → (p2 : k ≤ D.R.m) →
        (X.R.cV j).W ≃ₗ[ℂ] (M μ k p1 p2).wt.W) (fun _ _ => A.eW μ hμ j) hk p1 p2).symm
        ((M μ k p1 p2).real x (A.a j * preF (A.PV j) q))) =
      X.fn hμ j (hk.symm ▸ x) := by
  subst hk
  exact ext_real hV A hμ j x

end Forms

section Canon

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {P : Pin hL D} (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp)


end Canon

end GlobalTheory.ThetaRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftEquivariance
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ThetaTri
open scoped TensorProduct
open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ThetaLoc Formalism.L2.Theta

theorem thetaKO_act {D : D7} {V W : Formalism.BasicNotions.TH.HSp D}
    (om : Formalism.L2.Theta.GA D V × Formalism.L2.Theta.GA D W →* Module.End ℂ (WO V W → ℂ))
    (h' : Formalism.L2.Theta.GA D V) (g' : Formalism.L2.Theta.GA D W) (p : Formalism.L2.Theta.GA D V × Formalism.L2.Theta.GA D W)
    (f : WO V W → ℂ) : thetaKO om h' g' (om p f) = thetaKO om (h' * p.1) (g' * p.2) f := by
  simp only [thetaKO]
  rw [← Module.End.mul_apply, ← map_mul]
  rfl

theorem fin_frame_surj {D : D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n)
    (k : ↥(Formalism.IndefR.Bridge.Gf V)) : ∃ y, (Formalism.L2.Theta.finHom V).rangeRestrict (PV.ψ y) = k := by
  obtain ⟨g, hg, rfl⟩ := GlobalTheory.SplitHeckeAdj.fin_lift V k
  obtain ⟨y, rfl⟩ := PV.onto g hg
  exact ⟨y, rfl⟩

theorem preF_frame {D : D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n)
    (y : Formalism.AUTREP.GAf D.host.E n) : preF PV ((Formalism.L2.Theta.finHom V).rangeRestrict (PV.ψ y)) = y := by
  classical
  have h : ∃ x, (Formalism.L2.Theta.finHom V).rangeRestrict (PV.ψ x) = (Formalism.L2.Theta.finHom V).rangeRestrict (PV.ψ y) :=
    ⟨y, rfl⟩
  unfold preF
  rw [dite_eq_left h]
  exact PV.inj (GlobalTheory.SplitHeckeAdj.fin_inj V (PV.into _) (PV.into _) h.choose_spec)

theorem preF_mul {D : D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n)
    (k : ↥(Formalism.IndefR.Bridge.Gf V)) (y : Formalism.AUTREP.GAf D.host.E n) :
    preF PV (k * (Formalism.L2.Theta.finHom V).rangeRestrict (PV.ψ y)) = preF PV k * y := by
  obtain ⟨z, rfl⟩ := fin_frame_surj PV k
  rw [← map_mul, ← map_mul, preF_frame, preF_frame]

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {P : Pin hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}

theorem eW_cast_symm_wt (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (h' : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) (γ : GA D (Vc D j))
    (hγ : γ ∈ GQ (Vc D j)) (he : finHom (Vc D j) γ = finHom (Vc D j) ((A.PV j).ψ ((A.a j)⁻¹ * h' * A.a j)))
    (k : ℕ) (hk : j.1 + 1 = k) (p1 : 1 ≤ k) (p2 : k ≤ D.R.m) (w : (P.M (D.nd.mu i) k p1 p2).wt.W) :
    (Eq.ndrec (motive := fun k => (p1 : 1 ≤ k) → (p2 : k ≤ D.R.m) →
        (X.R.cV j).W ≃ₗ[ℂ] (P.M (D.nd.mu i) k p1 p2).wt.W) (fun _ _ => A.eW (D.nd.mu i) hμ j) hk p1 p2).symm
        ((P.M (D.nd.mu i) k p1 p2).wt.ρ h' w) =
      (X.R.cV j).ρ γ ((Eq.ndrec (motive := fun k => (p1 : 1 ≤ k) → (p2 : k ≤ D.R.m) →
        (X.R.cV j).W ≃ₗ[ℂ] (P.M (D.nd.mu i) k p1 p2).wt.W) (fun _ _ => A.eW (D.nd.mu i) hμ j) hk p1 p2).symm w) := by
  subst hk
  apply (A.eW _ hμ j).injective
  simp only [LinearEquiv.apply_symm_apply]
  rw [A.wt _ hμ j h' γ hγ he]
  simp

theorem eWloc_symm_wt (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (h' : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) (γ : GA D (Vc D j))
    (hγ : γ ∈ GQ (Vc D j)) (he : finHom (Vc D j) γ = finHom (Vc D j) ((A.PV j).ψ ((A.a j)⁻¹ * h' * A.a j)))
    (w : (P.M.loc i).wt.W) :
    (eWloc A i j hj hμ).symm ((P.M.loc i).wt.ρ h' w) = (X.R.cV j).ρ γ ((eWloc A i j hj hμ).symm w) :=
  eW_cast_symm_wt A i j hμ h' γ hγ he (D.nd.j i) hj _ _ w

theorem fV_rt (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (hcv : (X.R.cV j).Is) (h : Formalism.AUTREP.GAf D.host.E D.R.nV)
    (F F' : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ))
    (hF : (F' : Formalism.AUTREP.GAf D.host.E D.R.nV → (P.M.loc i).wt.W) = NG.rt D.host.E D.R.nV h F)
    (x : GA D (Vc D j)) : fV A i j hj hμ F' x = fV A i j hj hμ F (x * (A.PV j).ψ h) := by
  show (X.R.cV j).ext _ x = (X.R.cV j).ext _ (x * (A.PV j).ψ h)
  rw [GlobalTheory.DefLiftHecke.ext_mul _ hcv _ ((A.PV j).into h) x]
  show (X.R.cV j).ρ x⁻¹ _ = _
  simp only [LinearMap.coe_mk, AddHom.coe_mk, preF_mul, hF, NG.rt, mul_assoc]

theorem fV_rat (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ))
    (γ : GA D (Vc D j)) (hγ : γ ∈ GQ (Vc D j)) (x : GA D (Vc D j)) :
    fV A i j hj hμ F (γ * x) = fV A i j hj hμ F x := by
  obtain ⟨y, hy⟩ := fin_frame_surj (A.PV j) ((finHom (Vc D j)).rangeRestrict γ)
  obtain ⟨z, hz⟩ := fin_frame_surj (A.PV j) ((finHom (Vc D j)).rangeRestrict x)
  have hh' : A.a j * y * (A.a j)⁻¹ ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV := by
    refine (A.rat j _).2 ⟨γ, hγ, ?_⟩
    have : (A.a j)⁻¹ * (A.a j * y * (A.a j)⁻¹) * A.a j = y := by group
    rw [this]
    exact (congrArg Subtype.val hy).symm
  have he : finHom (Vc D j) γ = finHom (Vc D j) ((A.PV j).ψ ((A.a j)⁻¹ *
      ((⟨_, hh'⟩ : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) : Formalism.AUTREP.GAf D.host.E D.R.nV) * A.a j)) := by
    have : (A.a j)⁻¹ * (A.a j * y * (A.a j)⁻¹) * A.a j = y := by group
    simp only [this]
    exact (congrArg Subtype.val hy).symm
  show (X.R.cV j).ρ (γ * x)⁻¹ ((eWloc A i j hj hμ).symm ((F : Formalism.AUTREP.GAf D.host.E D.R.nV → (P.M.loc i).wt.W)
      (A.a j * preF (A.PV j) ((finHom (Vc D j)).rangeRestrict (γ * x))))) =
    (X.R.cV j).ρ x⁻¹ ((eWloc A i j hj hμ).symm ((F : Formalism.AUTREP.GAf D.host.E D.R.nV → (P.M.loc i).wt.W)
      (A.a j * preF (A.PV j) ((finHom (Vc D j)).rangeRestrict x))))
  have hprod : (finHom (Vc D j)).rangeRestrict γ * (finHom (Vc D j)).rangeRestrict x =
      (finHom (Vc D j)).rangeRestrict ((A.PV j).ψ (y * z)) :=
    (congrArg₂ (· * ·) hy.symm hz.symm).trans
      ((map_mul (finHom (Vc D j)).rangeRestrict _ _).symm.trans
        (congrArg (finHom (Vc D j)).rangeRestrict (map_mul (A.PV j).ψ y z).symm))
  have key : preF (A.PV j) ((finHom (Vc D j)).rangeRestrict (γ * x)) = y * z :=
    (congrArg (preF (A.PV j)) ((map_mul (finHom (Vc D j)).rangeRestrict γ x).trans hprod)).trans (preF_frame _ _)
  have hz' : preF (A.PV j) ((finHom (Vc D j)).rangeRestrict x) = z :=
    (congrArg (preF (A.PV j)) hz.symm).trans (preF_frame _ _)
  rw [key, hz']
  have e1 : A.a j * (y * z) = (A.a j * y * (A.a j)⁻¹) * (A.a j * z) := by group
  rw [e1, F.2.1 ⟨_, hh'⟩ (A.a j * z), eWloc_symm_wt A i j hj hμ ⟨_, hh'⟩ γ hγ he, _root_.mul_inv_rev,
    map_mul, Module.End.mul_apply, ← Module.End.mul_apply ((X.R.cV j).ρ γ⁻¹), ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply]

theorem lift_actM {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} {Sp : D.what₂.Tau → Formalism.BasicNotions.TH.SPar}
    (PW : Formalism.IndefR.principalLevelFrame.RowPsi V n) (M : Formalism.IndefR.Mult.DSModel V Sp) (g : Formalism.AUTREP.GAf D.host.E n)
    (T : Formalism.IndefR.Mult.MMap M) (u : PiTensorProduct ℂ fun τ => ↥(M.sm τ)) (x : GA D V) :
    PiTensorProduct.lift (Formalism.IndefR.principalLevelFrame.actM PW M g T) u x = PiTensorProduct.lift T u (x * PW.ψ g) := by
  induction u using PiTensorProduct.induction_on with
  | smul_tprod r f => simp [PiTensorProduct.lift.tprod, Formalism.IndefR.principalLevelFrame.actM_apply]
  | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb]

theorem lift_left {V : Formalism.BasicNotions.TH.HSp D} {Sp : D.what₂.Tau → Formalism.BasicNotions.TH.SPar}
    (M : Formalism.IndefR.Mult.DSModel V Sp) (T : Formalism.IndefR.Mult.MMap M)
    (hT : ∀ v, ∀ γ ∈ GQ V, ∀ x, T v (γ * x) = T v x) (u : PiTensorProduct ℂ fun τ => ↥(M.sm τ))
    (γ : GA D V) (hγ : γ ∈ GQ V) (x : GA D V) :
    PiTensorProduct.lift T u (γ * x) = PiTensorProduct.lift T u x := by
  induction u using PiTensorProduct.induction_on with
  | smul_tprod r f => simp [PiTensorProduct.lift.tprod, hT f γ hγ x]
  | add a b ha hb => simp only [map_add (f := _), Pi.add_apply, ha, hb]

def LeftInvM {V : Formalism.BasicNotions.TH.HSp D} {Sp : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} (M : Formalism.IndefR.Mult.DSModel V Sp) :
    Submodule ℂ (Formalism.IndefR.Mult.MMap M) where
  carrier := {T | ∀ v, ∀ γ ∈ GQ V, ∀ x, T v (γ * x) = T v x}
  add_mem' := by
    intro T T' hT hT' v γ hγ x
    simp only [MultilinearMap.add_apply, Pi.add_apply, hT v γ hγ x, hT' v γ hγ x]
  zero_mem' := by intro v γ hγ x; rfl
  smul_mem' := by
    intro c T hT v γ hγ x
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, hT v γ hγ x]

theorem minf_le_leftInv {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} {Sp : D.what₂.Tau → Formalism.BasicNotions.TH.SPar}
    (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (PW : Formalism.IndefR.principalLevelFrame.RowPsi V n) (M : Formalism.IndefR.Mult.DSModel V Sp) :
    Formalism.IndefR.principalLevelFrame.Minf θ PW M ≤ LeftInvM M := by
  refine iSup_le fun N => Submodule.span_le.2 fun T hT v γ hγ x => ?_
  exact (hT.aut v).left γ hγ x

theorem yv_apply {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y)
    (y : ↥Y.C) (x : GA D (Wc D j)) :
    yv hc y x = PiTensorProduct.lift (eC hc (y : Y.A)) (PiTensorProduct.map
      (fun τ => (lowT (X.R.MW j (sg0 D X.A)) τ).subtype) (kUnit (X.R.MW j (sg0 D X.A)))) x := rfl

theorem yv_rt {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y)
    (g : Formalism.AUTREP.GAf D.host.E D.R.r) (y y' : ↥Y.C) (hy : (y' : Y.A) = Y.ρ g y) (x : GA D (Wc D j)) :
    yv hc y' x = yv hc y (x * (X.PW j).ψ g) := by
  have he : eC hc (y' : Y.A) = Formalism.IndefR.principalLevelFrame.actM (X.PW j) (X.R.MW j (sg0 D X.A)) g (eC hc (y : Y.A)) := by
    rw [hy]; exact (Classical.choose_spec (Classical.choose_spec hc)).2.2.2.1 g y
  rw [yv_apply, yv_apply, he, lift_actM]

theorem yv_rat {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y)
    (y : ↥Y.C) (γ : GA D (Wc D j)) (hγ : γ ∈ GQ (Wc D j)) (x : GA D (Wc D j)) :
    yv hc y (γ * x) = yv hc y x := by
  have hm : eC hc (y : Y.A) ∈ LeftInvM (X.R.MW j (sg0 D X.A)) := by
    apply minf_le_leftInv X.R.θ (X.PW j)
    rw [← (Classical.choose_spec (Classical.choose_spec hc)).2.2.1]
    exact Submodule.mem_map_of_mem y.2
  rw [yv_apply, yv_apply]
  exact lift_left _ _ hm _ γ hγ x

end GlobalTheory.ThetaTri

end
end

