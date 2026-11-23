module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsWeilDatumGeneratorRealOneParamGroup
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0209

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilGeneratorQuadraticOneParameterAtPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped Classical

namespace GlobalTheory.ArchRec.Gen

theorem xOp_dOp {ι : Type} [Fintype ι] [DecidableEq ι] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    (ρ : (ι → ℂ) → B →L[ℂ] B) (H : Matrix ι ι ℂ) (k l : ι) {f : B} (hd : ∀ v, GlobalTheory.RealWeil.Sm ρ (dH ρ v f)) :
    xOp ρ k (dOp ρ H l f) = ∑ b : Bool × Bool,
      (-(1 / (4 * Real.pi)) * (if b.1 then -Complex.I else 1) * (if b.2 then Complex.I else 1) : ℂ) •
        dH ρ ((if b.1 then Complex.I else 1) • Pi.single k 1)
          (dH ρ ((if b.2 then Complex.I else 1) • H⁻¹ *ᵥ Pi.single l 1) f) := by
  have hs : ∀ (a : ℂ) v, GlobalTheory.RealWeil.Sm ρ (a • dH ρ v f) := fun a v => (smS ρ).smul_mem a (hd v)
  have ha : ∀ (a : ℂ) u v, GlobalTheory.RealWeil.Sm ρ (dH ρ u f + a • dH ρ v f) := fun a u v => (smS ρ).add_mem (hd u) (hs a v)
  simp only [xOp, dOp, dH_smul _ _ (ha _ _ _), dH_add _ (hd _) (hs _ _), dH_smul _ _ (hd _), Fintype.sum_prod_type,
    Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, one_smul]
  module

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D} {ψ : AddChar (AF D.host.F) ℂ}
  {S T : HSp D}

theorem coe_dH_at (h : GlobalTheory.FockCompare.Chart θ σ) (hψ : IsStdChar D ψ (-1)) (F : BB ψ S T)
    (hF : IsThetaFunO ψ S T F.1) (τ : D.what₂.Tau) (v : GlobalTheory.RealWeil.Ix S T → ℂ) (hv : ∀ k, k.2 ≠ τ → v k = 0) :
    ((dH (rhoV hψ σ S T) v F).1 : WO S T → ℂ) = Datum.dRho (heisO ψ S T) θ τ (cpt v τ) F.1 := by
  have e : v = vecL (Pi.single τ (cpt v τ) : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) := by
    funext ⟨⟨a, a'⟩, t⟩
    change _ = (Pi.single τ (cpt v τ) : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) t a a'
    by_cases ht : t = τ
    · subst ht
      rw [Pi.single_eq_same]
      rfl
    · rw [Pi.single_eq_of_ne ht]
      exact hv _ ht
  rw [← GlobalTheory.DefLift.Gen.coe_dH h hψ F hF, ← e]


open scoped ComplexOrder in
theorem HM_inv_apply (k l : GlobalTheory.RealWeil.Ix S T) (hkl : k.2 ≠ l.2) : (HM S T)⁻¹ k l = 0 := by
  have : HM S T * blk (fun τ => ((2 * (tauE D τ D.host.xi0).im : ℝ) : ℂ)⁻¹ • (gramAt D T τ)⁻¹) (gramAt D S) = 1 := by
    unfold HM
    rw [blk_mul, ← blk_one]
    congr 1 <;> funext τ
    · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ (two_im_pos τ).ne', one_smul,
        mul_nonsing_inv _ (GlobalTheory.SmoothForms.RealPts.gramAt_unit T τ)]
    · rw [mul_nonsing_inv _ (GlobalTheory.SmoothForms.RealPts.gramAt_unit S τ)]
  rw [inv_eq_right_inv this, WeylAction.blk_apply, if_neg hkl]

theorem nOp_at (h : GlobalTheory.FockCompare.Chart θ σ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau)
    (X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ) (hX : ∀ k l, k.2 ≠ τ ∨ l.2 ≠ τ → X k l = 0) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (z z' : Fin n → Matrix (Fin T.rank) (Fin S.rank) ℂ), ∀ F : BB ψ S T,
      IsThetaFunO ψ S T F.1 → ((nOp (rhoV hψ σ S T) (HM S T) X F).1 : WO S T → ℂ) =
        ∑ i, c i • Datum.dRho (heisO ψ S T) θ τ (z i) (Datum.dRho (heisO ψ S T) θ τ (z' i) F.1) := by
  let e := (Fintype.equivFin (GlobalTheory.RealWeil.Ix S T × GlobalTheory.RealWeil.Ix S T × Bool × Bool)).symm
  let c : GlobalTheory.RealWeil.Ix S T × GlobalTheory.RealWeil.Ix S T × Bool × Bool → ℂ := fun a => X a.1 a.2.1 *
    (-(1 / (4 * Real.pi)) * (if a.2.2.1 then -Complex.I else 1) * (if a.2.2.2 then Complex.I else 1))
  let u : GlobalTheory.RealWeil.Ix S T × GlobalTheory.RealWeil.Ix S T × Bool × Bool → GlobalTheory.RealWeil.Ix S T → ℂ := fun a =>
    (if a.2.2.1 then Complex.I else 1) • Pi.single a.1 1
  let u' : GlobalTheory.RealWeil.Ix S T × GlobalTheory.RealWeil.Ix S T × Bool × Bool → GlobalTheory.RealWeil.Ix S T → ℂ := fun a =>
    (if a.2.2.2 then Complex.I else 1) • (HM S T)⁻¹ *ᵥ Pi.single a.2.1 1
  refine ⟨_, c ∘ e, fun i => cpt (u (e i)) τ, fun i => cpt (u' (e i)) τ, fun F hF => ?_⟩
  have th := GlobalTheory.DefLift.Gen.theta_dH h hψ F hF
  have e1 : nOp (rhoV hψ σ S T) (HM S T) X F =
      ∑ a, c a • dH (rhoV hψ σ S T) (u a) (dH (rhoV hψ σ S T) (u' a) F) := by
    rw [nOp, Fintype.sum_prod_type (f := fun a => c a • dH (rhoV hψ σ S T) (u a) (dH (rhoV hψ σ S T) (u' a) F))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fintype.sum_prod_type (f := fun a => c (k, a) • dH (rhoV hψ σ S T) (u (k, a))
      (dH (rhoV hψ σ S T) (u' (k, a)) F))]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [xOp_dOp _ _ _ _ fun v => sm_of_theta h hψ _ (th v), Finset.smul_sum]
    exact Finset.sum_congr rfl fun b _ => smul_smul _ _ _
  let j : BB ψ S T →ₗ[ℂ] (WO S T → ℂ) := ⟨⟨fun G => G.1, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  change j _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e1, map_sum, ← e.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Function.comp_apply]
  beta_reduce
  generalize e i = a
  by_cases ha : a.1.2 ≠ τ ∨ a.2.1.2 ≠ τ
  · have : c a = 0 := by simp only [c, hX _ _ ha, zero_mul]
    rw [this, zero_smul, zero_smul]
  · push Not at ha
    have h1 : ∀ k, k.2 ≠ τ → u a k = 0 := fun k hk => by
      have : k ≠ a.1 := fun e => hk (e ▸ ha.1)
      simp only [u, Pi.smul_apply, Pi.single_eq_of_ne this, smul_zero]
    have h2 : ∀ k, k.2 ≠ τ → u' a k = 0 := fun k hk => by
      simp only [u', Pi.smul_apply, mulVec_single_one, col_apply, HM_inv_apply k a.2.1 (ha.2 ▸ hk), smul_zero]
    rw [← coe_dH_at h hψ F hF τ _ h2, ← coe_dH_at h hψ _ (th _) τ _ h1]
    rfl

variable {χS χT : (AE D)ˣ →* Circle} {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem quadGen_of_supp (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ S T χS χT ω) (τ : D.what₂.Tau)
    (γ : ℝ → GA D S × GA D T) (h1 : Continuous γ) (h2 : ∀ s t, γ (s + t) = γ s * γ t)
    (h3 : ∀ t, (γ t).1 ∈ GinfC S ∧ (γ t).2 ∈ GinfC T) (X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ)
    (h4 : ∀ k l, HasDerivAt (fun t => mM θ S T (γ t) k l) (X k l) 0) (hX : ∀ k l, k.2 ≠ τ ∨ l.2 ≠ τ → X k l = 0) :
    QuadGen ψ θ τ ω γ := by
  have hψ := hω.std
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hW := GlobalTheory.Ker.isWeak_of_datum hω
  obtain ⟨lam, hl⟩ := GenZero.exists_generator D θ σ h ψ hψ S T ω hW hω.om_cont γ h1 h2 h3 X h4
  obtain ⟨lam', hl'⟩ := GlobalTheory.Mem.LiftGen.hasDerivAt_om D θ σ h ψ hψ S T ω hW hω.om_cont γ h1 h2 h3 X h4
  obtain ⟨n, c, z, z', hq⟩ := nOp_at h hψ τ X hX
  refine ⟨n, c, z, z', lam, fun f hf => ?_⟩
  obtain ⟨F, rfl⟩ : ∃ F : BB ψ S T, (F.1 : WO S T → ℂ) = f := ⟨toB hψ f hf, coe_toB hψ f hf⟩
  obtain ⟨u, hu, hud⟩ := hl F hf
  rw [← hq F hf, GlobalTheory.DefLift.Gen.coe_add_smul]
  have hl2 := hl' F hf
  generalize nOp (rhoV hψ σ S T) (HM S T) X F + lam • F = G at hud ⊢
  generalize nOp (rhoV hψ σ S T) (HM S T) X F + lam' • F = G' at hl2
  have e : (G.1 : WO S T → ℂ) = G'.1 := funext fun w => by
    have a1 := ((ev _ _ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hud
    have a2 := hl2 1 w
    simp only [one_mul, map_one, Module.End.one_apply] at a2
    refine HasDerivAt.unique ?_ a2
    exact a1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (congrFun (hu t) w).symm)
  refine ⟨fun g w => by rw [e]; exact hl2 g w, fun μ 𝓕 hμ h𝓕 E hE => ?_⟩
  obtain ⟨E, rfl⟩ : ∃ F : BB ψ S T, (F.1 : WO S T → ℂ) = E := ⟨toB hψ E hE, coe_toB hψ E hE⟩
  obtain ⟨i1, i2, i3, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have i6 : BorelSpace (WO S T) := ⟨rfl⟩
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (GlobalTheory.Size.measure_dom hμ h𝓕).2
  let Φ : BB ψ S T →L[ℂ] ℂ := (innerSL ℂ (toL2 _ _ (μ.restrict 𝓕) E)).comp (toL2 _ _ (μ.restrict 𝓕))
  have hΦ : ∀ A : BB ψ S T, ipTh μ 𝓕 A.1 E.1 = Φ A := fun A =>
    (BoundedContinuousFunction.inner_toLp (μ.restrict 𝓕) E.1 A.1).symm
  simp only [← hu, hΦ]
  exact (Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hud

theorem quadGen_oneP : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ S T χS χT ω → (∀ X ∈ lieAt S τ, QuadGen ψ θ τ ω fun t => (oneP θ S τ X t, 1)) ∧ ∀ Y ∈ lieAt T τ, QuadGen ψ θ τ ω fun t => (1, oneP θ T τ Y t) := by
  intro D ψ θ S T χS χT ω τ hθ hω
  have supp : ∀ (b : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
      (a : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ), (∀ t, t ≠ τ → b t = 0 ∨ a t = 0) →
      ∀ k l : GlobalTheory.RealWeil.Ix S T, k.2 ≠ τ ∨ l.2 ≠ τ → blk b a k l = 0 := by
    intro b a hab k l hkl
    rw [WeylAction.blk_apply]
    split_ifs with e
    · rcases hab k.2 (hkl.elim id fun h => e ▸ h) with h | h <;> simp [h]
    · rfl
  refine ⟨fun X hX => ?_, fun Y hY => ?_⟩
  · refine quadGen_of_supp hθ hω τ _ ((continuous_oneP hθ hX).prodMk continuous_const)
      (fun s t => by rw [oneP_add hθ hX, Prod.mk_mul_mk, one_mul])
      (fun t => ⟨(isAtTau_oneP hθ hX t).1, one_mem _⟩) (blk (fun _ => 1) (Pi.single τ (-X))) (fun k l => ?_)
      (supp _ _ fun t ht => Or.inr (Pi.single_eq_of_ne ht _))
    simp only [mM_apply, WeylAction.oneP_inv hθ hX, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one,
      WeylAction.blk_apply]
    split_ifs
    · exact (WeylAction.hasDerivAt_comp hθ (WeylAction.neg_mem_lieAt hX) _ _ _).const_mul _
    · exact hasDerivAt_const _ _
  · refine quadGen_of_supp hθ hω τ _ (continuous_const.prodMk (continuous_oneP hθ hY))
      (fun s t => by rw [oneP_add hθ hY, Prod.mk_mul_mk, one_mul])
      (fun t => ⟨one_mem _, (isAtTau_oneP hθ hY t).1⟩) (blk (Pi.single τ Y) fun _ => 1) (fun k l => ?_)
      (supp _ _ fun t ht => Or.inl (Pi.single_eq_of_ne ht _))
    simp only [mM_apply, inv_one, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one, WeylAction.blk_apply]
    split_ifs
    · exact (WeylAction.hasDerivAt_comp hθ hY _ _ _).mul_const _
    · exact hasDerivAt_const _ _

end GlobalTheory.ArchRec.Gen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOneParamMovesFockVacuumSmoothly
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

noncomputable section

theorem GlobalTheory.WeilVacuum.smooth_flow : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ q, (∀ x, β x q = 0) → q = 0) →
    ∀ T : ℝ → SchwartzMap V ℂ →ₗ[ℂ] SchwartzMap V ℂ, (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) →
    (∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    ∀ A : ℝ → (V × V) →ₗ[ℝ] (V × V), (∀ w, Continuous fun t => A t w) → (∀ s t, A (s + t) = (A s).comp (A t)) →
    A 0 = LinearMap.id →
    (∀ (t : ℝ) (p q : V) (f g : SchwartzMap V ℂ), ⇑g = GlobalTheory.GaussLine.heisFun β p q ⇑f →
      ⇑(T t g) = GlobalTheory.GaussLine.heisFun β (A t (p, q)).1 (A t (p, q)).2 ⇑(T t f)) →
    (∀ f x, Continuous fun t => T t f x) →
    ∀ J₀ : (V × V) →ₗ[ℝ] (V × V), (∀ w, J₀ (J₀ w) = -w) →
    ∀ f₀ : SchwartzMap V ℂ, (∀ w x, GlobalTheory.GaussLine.dHeis β (J₀ w) ⇑f₀ x = Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑f₀ x) →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => T p.1 f₀ p.2) ∧
    ∃ (n : ℕ) (qs qs' : Fin n → V) (cs : Fin n → ℂ) (c : ℂ), ∀ x,
      HasDerivAt (fun t => T t f₀ x) (∑ i, cs i * (β x (qs i) : ℂ) * (β x (qs' i) : ℂ) * f₀ x + c * f₀ x) 0 := by
  intro V _ _ _ _ _ μ _ β hβ T hadd h0 hunit A hAc hAadd hA0 hint hcont J₀ hJ₀ f₀ hf₀
  by_cases hz : f₀ = 0
  · subst hz
    have hT0 : ∀ t, T t 0 = 0 := fun t => map_zero _
    refine ⟨?_, 0, Fin.elim0, Fin.elim0, Fin.elim0, 0, fun x => ?_⟩
    · simp only [hT0, SchwartzMap.zero_apply]; exact contDiff_const
    · simp only [hT0, SchwartzMap.zero_apply, Finset.univ_eq_empty, Finset.sum_empty, zero_mul, add_zero]
      exact hasDerivAt_const _ _
  have hAsm := GlobalTheory.T.contDiff_continuous_oneParameter_finiteDimensional_linear A hAc hAadd hA0
  have hinv : ∀ t w, A t (A (-t) w) = w := by
    intro t w
    have := congrArg (fun L => L w) (hAadd t (-t))
    simp only [add_neg_cancel, hA0, LinearMap.id_apply, LinearMap.comp_apply] at this
    exact this.symm
  have hinv' : ∀ t w, A (-t) (A t w) = w := by
    intro t w
    have := congrArg (fun L => L w) (hAadd (-t) t)
    simp only [neg_add_cancel, hA0, LinearMap.id_apply, LinearMap.comp_apply] at this
    exact this.symm
  set J : ℝ → (V × V) →ₗ[ℝ] (V × V) := fun t => (A t).comp (J₀.comp (A (-t))) with hJdef
  have hJapp : ∀ t w, J t w = A t (J₀ (A (-t) w)) := fun t w => rfl
  have hJsm : ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => J t w := by
    intro w
    have e : (fun t => J t w) = fun t => (LinearMap.toContinuousLinearMap (A t))
        ((LinearMap.toContinuousLinearMap J₀) ((LinearMap.toContinuousLinearMap (A (-t))) w)) := by
      funext t; simp [hJapp]
    rw [e]
    exact hAsm.clm_apply ((LinearMap.toContinuousLinearMap J₀).contDiff.comp
      ((hAsm.comp contDiff_neg).clm_apply contDiff_const))
  have hJsq : ∀ t w, J t (J t w) = -w := by
    intro t w; simp only [hJapp, hinv', hJ₀, map_neg, hinv]
  have hFock : ∀ t w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑(T t f₀) x =
      Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑(T t f₀) x := by
    intro t w x
    set u := A (-t) w
    obtain ⟨g1, hg1⟩ := _root_.GlobalTheory.dHeis_schwartz β (J₀ u) f₀
    obtain ⟨g2, hg2⟩ := _root_.GlobalTheory.dHeis_schwartz β u f₀
    have hg12 : g1 = Complex.I • g2 := by
      ext y; rw [SchwartzMap.smul_apply, hg1, hg2, hf₀, smul_eq_mul]
    have hI : ∀ w₁ : V × V, ∀ (s : ℝ) (f g : SchwartzMap V ℂ),
        ⇑g = GlobalTheory.GaussLine.heisFun β (s • w₁).1 (s • w₁).2 ⇑f →
        ⇑(T t g) = GlobalTheory.GaussLine.heisFun β (s • A t w₁).1 (s • A t w₁).2 ⇑(T t f) := by
      intro w₁ s f g h
      have := hint t (s • w₁).1 (s • w₁).2 f g h
      rwa [Prod.mk.eta, map_smul] at this
    have h1 := _root_.GlobalTheory.HeisenbergL2.map_dHeis_of_isometry μ β (T t) (hunit t) (J₀ u) (A t (J₀ u)) (hI _) f₀ g1 hg1 x
    have h2 := _root_.GlobalTheory.HeisenbergL2.map_dHeis_of_isometry μ β (T t) (hunit t) u (A t u) (hI _) f₀ g2 hg2 x
    have hu : A t u = w := hinv t w
    rw [hu] at h2
    rw [hJapp, ← h1, ← h2, hg12, map_smul, SchwartzMap.smul_apply, smul_eq_mul]
  have hne : ∀ t, T t f₀ ≠ 0 := by
    intro t h
    apply hz
    have := hadd (-t) t f₀
    rw [neg_add_cancel, h0, h, map_zero] at this
    exact this
  obtain ⟨M, hMs, hMj, hMdec, hMuniq, n, qs, qs', cs, hMder⟩ :=
    _root_.GlobalTheory.FockFamily.fock_vacua_family β hβ J hJsm hJsq (fun t => ⟨T t f₀, hne t, hFock t⟩)
  set cc : ℝ → ℂ := fun t => T t f₀ 0 with hccdef
  have hrep : ∀ t x, T t f₀ x = cc t * Complex.exp (M t x x) := fun t x => hMuniq t (T t f₀) (hFock t) x
  obtain ⟨hK, hKne⟩ := GlobalTheory.T.gaussianPairingIntegral_contDiff_ne_zero_diag μ M hMs hMdec
  set K : ℝ → ℝ → ℂ := fun u v => ∫ x, Complex.exp (M u x x) * starRingEnd ℂ (Complex.exp (M v x x)) ∂μ with hKdef
  have hexp : ∀ u v, ∫ x, T u f₀ x * starRingEnd ℂ (T v f₀ x) ∂μ = cc u * starRingEnd ℂ (cc v) * K u v := by
    intro u v
    simp_rw [hrep, map_mul]
    rw [hKdef, ← integral_const_mul]
    congr 1; funext x; ring
  have hpol := fun s => _root_.GlobalTheory.schwartz_L2_isometry_preserves_inner μ (T s) (hunit s)
  have eq1 : ∀ s t, cc (s + t) * starRingEnd ℂ (cc s) * K (s + t) s = cc t * starRingEnd ℂ (cc 0) * K t 0 := by
    intro s t
    have := hpol s (T t f₀) (T 0 f₀)
    rw [← hadd, ← hadd, add_zero] at this
    rw [← hexp, ← hexp, this]
  have eq2 : ∀ s, cc s * starRingEnd ℂ (cc s) * K s s = cc 0 * starRingEnd ℂ (cc 0) * K 0 0 := by
    intro s
    have := hpol s f₀ f₀
    rw [← hexp, ← hexp, this, h0]
  have hc0 : cc 0 ≠ 0 := by
    intro h; apply hz; ext x
    rw [← h0 f₀, hrep, h, zero_mul, SchwartzMap.zero_apply]
  have hcs : ∀ s, cc s ≠ 0 := by
    intro s h
    have := eq2 s
    rw [h, zero_mul, zero_mul] at this
    exact mul_ne_zero (mul_ne_zero hc0 ((map_ne_zero _).2 hc0)) (hKne 0) this.symm
  have hKc : Continuous fun p : ℝ × ℝ => K p.1 p.2 := hK.continuous
  set U : Set (ℝ × ℝ) := {p | K (p.1 + p.2) p.1 ≠ 0} with hUdef
  have hUo : IsOpen U := isOpen_ne_fun (hKc.comp ((continuous_fst.add continuous_snd).prodMk continuous_fst)) continuous_const
  have hU0 : ∀ s, (s, 0) ∈ U := by intro s; simp only [hUdef, Set.mem_setOf_eq, add_zero]; exact hKne s
  set E : ℝ → ℝ → ℂ := fun s t => K s s * K t 0 / (cc 0 * K 0 0 * K (s + t) s) with hEdef
  have hEsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => E p.1 p.2) U := by
    have k1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => K p.1 p.1) := hK.comp (contDiff_fst.prodMk contDiff_fst)
    have k2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => K p.2 0) := hK.comp (contDiff_snd.prodMk contDiff_const)
    have k3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => K (p.1 + p.2) p.1) :=
      hK.comp ((contDiff_fst.add contDiff_snd).prodMk contDiff_fst)
    have hinvd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => (cc 0 * K 0 0 * K (p.1 + p.2) p.1)⁻¹) U :=
      ((contDiff_const.mul k3).contDiffOn).inv (fun p hp => mul_ne_zero (mul_ne_zero hc0 (hKne 0)) hp)
    have := (k1.mul k2).contDiffOn.mul hinvd
    simpa only [hEdef, div_eq_mul_inv] using this
  have hfe : ∀ p ∈ U, cc (p.1 + p.2) = cc p.1 * cc p.2 * E p.1 p.2 := by
    rintro ⟨s, t⟩ hp
    simp only [hUdef, Set.mem_setOf_eq] at hp
    simp only [hEdef]
    have hd : starRingEnd ℂ (cc 0) ≠ 0 := (map_ne_zero _).2 hc0
    rw [mul_div_assoc', eq_div_iff (mul_ne_zero (mul_ne_zero hc0 (hKne 0)) hp)]
    apply mul_left_cancel₀ hd
    linear_combination (-(cc (s + t) * K (s + t) s)) * eq2 s + (cc s * K s s) * eq1 s t
  have hccc : Continuous cc := by
    have := hcont f₀ 0
    exact this
  have hcsm := GlobalTheory.T.contDiff_of_continuous_quasiMultiplicative_smoothDefect cc E U hccc hc0 hUo hU0 hEsm hfe
  have hfun : (fun p : ℝ × V => T p.1 f₀ p.2) = fun p => cc p.1 * Complex.exp (M p.1 p.2 p.2) := by
    funext p; exact hrep p.1 p.2
  refine ⟨?_, n, qs, qs', cs, deriv cc 0 / cc 0, fun x => ?_⟩
  · rw [hfun]; exact (hcsm.comp contDiff_fst).mul hMj.cexp
  · have hft : (fun t => T t f₀ x) = fun t => cc t * Complex.exp (M t x x) := by funext t; exact hrep t x
    rw [hft]
    have hdc : HasDerivAt cc (deriv cc 0) 0 := ((hcsm.differentiable (by simp)) 0).hasDerivAt
    refine (hdc.mul (hMder x).cexp).congr_deriv ?_
    have hf0x : f₀ x = cc 0 * Complex.exp (M 0 x x) := by rw [← hrep 0 x, h0]
    rw [hf0x, ← Finset.sum_mul]
    field_simp
    ring

end
end

