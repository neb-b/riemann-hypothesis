module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.WeilRepresentationThetaEquivariance
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.HeisenbergCommutingOperatorScalar
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.AdelicCharacterRationalDual
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaSumAdmissibility
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle0001
public import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle0004
public import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowHt
public import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle0003

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.EqZeroOfTheta
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace PositivityTheory.ThKF0

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}

theorem isStd_ne_one (hψ : IsStd ψ) : ψ ≠ 1 := by
  intro h1
  have hn : (Module.finrank ℚ F : ℚ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := F)).ne'
  have e := GlobalTheory.PsiNontriv.isStd_fin_rat hψ (algebraMap ℚ F (1 / (2 * Module.finrank ℚ F)))
  rw [h1, AddChar.one_apply, Algebra.trace_algebraMap] at e
  have e2 : (Module.finrank ℚ F • (1 / (2 * (Module.finrank ℚ F : ℚ))) : ℚ) = 1 / 2 := by
    rw [nsmul_eq_mul]
    field_simp
  rw [e2] at e
  have e3 : 2 * (Real.pi : ℂ) * Complex.I * (((1 / 2 : ℚ)) : ℂ) = Real.pi * Complex.I := by
    push_cast
    ring
  rw [e3, Complex.exp_pi_mul_I] at e
  norm_num at e


variable (F) in
def ratPt (y z : κ → F) : (κ → AF F) × (κ → AF F) :=
  (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))

section One

variable {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F}

structure Tw (ψ : AddChar (AF F) ℂ) (d d₁ : Darboux B κ) (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) : Prop where
  maps : ∀ Φ ∈ schA F κ, e Φ ∈ schA F κ
  Heisenberg₂ : ∀ w, ∀ Φ ∈ schA F κ, e (d.rho ψ w Φ) = d₁.rho ψ w (e Φ)
  adm : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ e ∈ (adeleClass F).adm κ
  ne : ∃ Φ ∈ schA F κ, e Φ ≠ 0

def RatRel (d d₁ : Darboux B κ) : Prop := ∀ y z : κ → F, ∃ w y' z', d.e w = ratPt F y z ∧ d₁.e w = ratPt F y' z'

variable {d d₁ d₂ : Darboux B κ} {e e' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)}

theorem rho_mem (hψ : IsStd ψ) (d : Darboux B κ) (w : W) {Φ} (hΦ : Φ ∈ schA F κ) : d.rho ψ w Φ ∈ schA F κ :=
  (_root_.GlobalTheory.CompanionTheory.AdelicHeis.schr_mem_and_thetaSum F κ ψ hψ.1 (isStd_ne_one hψ) hψ.2.1).1 _ Φ hΦ

theorem eq_zero_of_theta (hψ : IsStd ψ) (d : Darboux B κ) {Φ} (hΦ : Φ ∈ schA F κ) (h : ∀ w, thetaSum F (d.rho ψ w Φ) = 0) :
    Φ = 0 :=
  _root_.GlobalTheory.CompanionTheory.ThetaInj.theta_inj F κ ψ hψ.1 (isStd_ne_one hψ) hψ.2.1 Φ hΦ fun w => by
    obtain ⟨w', rfl⟩ := d.e.surjective w
    exact h w'

theorem rho_smul (d : Darboux B κ) (w : W) (c : ℂ) (Φ : (κ → AF F) → ℂ) : d.rho ψ w (c • Φ) = c • d.rho ψ w Φ := by
  funext x
  simp only [Darboux.rho, schr, Pi.smul_apply, smul_eq_mul]
  ring

theorem thetaSum_smul (c : ℂ) (Φ : (κ → AF F) → ℂ) : thetaSum F (c • Φ) = c * thetaSum F Φ := by
  simp only [thetaSum, Pi.smul_apply, smul_eq_mul, tsum_mul_left]

theorem Tw.theta (hψ : IsStd ψ) (h : Tw ψ d d₁ e) (hr : RatRel d d₁) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ schA F κ, thetaSum F (e Φ) = c * thetaSum F Φ := by
  obtain ⟨-, ⟨l, hl0, hl⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.ThetaAdm.theta_adm F κ
  have hinv := (_root_.GlobalTheory.CompanionTheory.AdelicHeis.schr_mem_and_thetaSum F κ ψ hψ.1 (isStd_ne_one hψ) hψ.2.1).2
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.CompanionTheory.ThetaUniq.theta_unique F κ ψ hψ.1 (isStd_ne_one hψ) hψ.2.1 (l ∘ₗ e) (h.adm l hl0) fun w Φ hΦ => by
    obtain ⟨u, y', z', h1, h2⟩ := hr w.1 w.2
    have e1 := h.Heisenberg₂ u Φ hΦ
    rw [Darboux.rho, Darboux.rho, h1, h2] at e1
    have e2 := rho_mem hψ d₁ u (h.maps Φ hΦ)
    rw [Darboux.rho, h2] at e2
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    refine (congrArg l e1).trans ?_
    rw [hl _ e2, hl _ (h.maps Φ hΦ)]
    exact hinv (y', z') _
  have ha' : ∀ Φ ∈ schA F κ, thetaSum F (e Φ) = a * thetaSum F Φ := fun Φ hΦ => by
    rw [← ha Φ hΦ, LinearMap.comp_apply, hl _ (h.maps Φ hΦ)]
  refine ⟨a, fun a0 => ?_, ha'⟩
  obtain ⟨Φ, hΦ, hne⟩ := h.ne
  refine hne (eq_zero_of_theta hψ d₁ (h.maps Φ hΦ) fun w => ?_)
  rw [← h.Heisenberg₂ w Φ hΦ, ha' _ (rho_mem hψ d w hΦ), a0, zero_mul]

theorem Tw.inj (hψ : IsStd ψ) (h : Tw ψ d d₁ e) (hr : RatRel d d₁) {Φ} (hΦ : Φ ∈ schA F κ) (h0 : e Φ = 0) : Φ = 0 := by
  obtain ⟨c, hc, H⟩ := h.theta hψ hr
  refine eq_zero_of_theta hψ d hΦ fun w => ?_
  have := H _ (rho_mem hψ d w hΦ)
  rw [h.Heisenberg₂ w Φ hΦ, h0, ← zero_smul ℂ (0 : (κ → AF F) → ℂ), rho_smul, thetaSum_smul, zero_mul] at this
  exact (mul_eq_zero.1 this.symm).resolve_left hc

theorem schur (hψ : IsStd ψ) (d : Darboux B κ) (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ))
    (h1 : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) (h2 : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ T ∈ (adeleClass F).adm κ)
    (h3 : ∀ w, ∀ Φ ∈ schA F κ, T (d.rho ψ w Φ) = d.rho ψ w (T Φ)) : ∃ a : ℂ, ∀ Φ ∈ schA F κ, T Φ = a • Φ :=
  _root_.GlobalTheory.CompanionTheory.AdelicSchur.schur F κ ψ hψ.1 (isStd_ne_one hψ) hψ.2.1 T h1 h2 fun w Φ hΦ => by
    obtain ⟨w', rfl⟩ := d.e.surjective w
    exact h3 w' Φ hΦ

theorem Tw.smul (h : Tw ψ d d₁ e) {c : ℂ} (hc : c ≠ 0) : Tw ψ d d₁ (c • e) := by
  refine
    { maps := fun Φ hΦ => Submodule.smul_mem _ c (h.maps Φ hΦ)
      Heisenberg₂ := ?_
      adm := ?_
      ne := ?_ }
  · intro w Φ hΦ
    rw [LinearMap.smul_apply, LinearMap.smul_apply, h.Heisenberg₂ w Φ hΦ, rho_smul]
  · intro l hl g hg
    obtain ⟨T, hT⟩ := h.adm l hl g hg
    refine ⟨c • T, fun f => ?_⟩
    rw [LinearMap.comp_smul, LinearMap.smul_apply, hT, ContinuousLinearMap.smul_apply]
  ·
    obtain ⟨Φ, hΦ, h0⟩ := h.ne
    exact ⟨Φ, hΦ, smul_ne_zero hc h0⟩

theorem Tw.exists_inv (hψ : IsStd ψ) (h : Tw ψ d d₁ e) (h' : Tw ψ d₁ d e') (hr : RatRel d d₁) (hr' : RatRel d₁ d) :
    ∃ e'', Tw ψ d₁ d e'' ∧ (∀ Φ ∈ schA F κ, e'' (e Φ) = Φ) ∧ ∀ Φ ∈ schA F κ, e (e'' Φ) = Φ := by
  obtain ⟨a, ha⟩ := schur hψ d (e' ∘ₗ e) (fun Φ hΦ => h'.maps _ (h.maps Φ hΦ))
    (fun l hl => h.adm _ (h'.adm l hl)) fun w Φ hΦ => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, h.Heisenberg₂ w Φ hΦ, h'.Heisenberg₂ w _ (h.maps Φ hΦ)]
  have a0 : a ≠ 0 := fun a0 => by
    obtain ⟨Φ, hΦ, hne⟩ := h.ne
    exact hne (h'.inj hψ hr' (h.maps Φ hΦ) ((ha Φ hΦ).trans (by rw [a0, zero_smul])))
  have h1 : ∀ Φ ∈ schA F κ, (a⁻¹ • e') (e Φ) = Φ := fun Φ hΦ => by
    rw [LinearMap.smul_apply, show e' (e Φ) = a • Φ from ha Φ hΦ, smul_smul, inv_mul_cancel₀ a0, one_smul]
  have h'' := h'.smul (inv_ne_zero a0)
  refine ⟨_, h'', h1, fun Φ hΦ => sub_eq_zero.1 (h''.inj hψ hr' (sub_mem (h.maps _ (h''.maps Φ hΦ)) hΦ) ?_)⟩
  rw [map_sub, h1 _ (h''.maps Φ hΦ), sub_self]

end One

def TwEx : Prop := ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
  (W : Type) [AddCommGroup W] [Module (AF F) W] (B : W → W → AF F) (d d₁ : Darboux B κ), ∃ e, Tw ψ d d₁ e

theorem schr_box {κ' : Type} [Fintype κ'] (a b : κ → AF F) (a' b' : κ' → AF F) (φ : (κ → AF F) → ℂ) (φ' : (κ' → AF F) → ℂ) :
    schr ψ (Sum.elim a a', Sum.elim b b') (boxFun φ φ') = boxFun (schr ψ (a, b) φ) (schr ψ (a', b') φ') := by
  funext x
  have e1 : (x + Sum.elim a a') ∘ Sum.inl = x ∘ Sum.inl + a := rfl
  have e2 : (x + Sum.elim a a') ∘ Sum.inr = x ∘ Sum.inr + a' := rfl
  have e3 : x ⬝ᵥ Sum.elim b b' + ⅟(2 : AF F) * (Sum.elim a a' ⬝ᵥ Sum.elim b b') =
      (x ∘ Sum.inl ⬝ᵥ b + ⅟(2 : AF F) * (a ⬝ᵥ b)) + (x ∘ Sum.inr ⬝ᵥ b' + ⅟(2 : AF F) * (a' ⬝ᵥ b')) := by
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
    ring
  simp only [schr, boxFun, e1, e2, e3, AddChar.map_add_eq_mul]
  ring

section Dbl

variable {E : Type} [CommRing E] [Algebra (AF F) E] {c : E →ₐ[AF F] E} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β]
  [DecidableEq β] {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {d d₁ : Darboux (symp c ξ JA JB) κ}
  {dd dd₁ : Darboux (symp c ξ JA (dbl JB)) (κ ⊕ κ)}

end Dbl

end PositivityTheory.ThKF0

end
end

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.EvChange
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0.Change

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def finPr {κ : Type} (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) : (κ → Af F) → ℂ :=
  fun y => ∏ᶠ v, φ v fun i => evalV F v (y i)

theorem pure_eq {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ = pureA F f (finPr φ) := rfl

theorem finPr_mem {κ : Type} [Fintype κ] (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB _)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) : finPr φ ∈ SB _ :=
  ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hSB hstd, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hSB hstd⟩

theorem exists_finPr_ne {κ : Type} [Fintype κ] (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (h0 : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) : ∃ y, finPr φ y ≠ 0 := by
  have key : ∀ v : Pl (F := F), ∃ p : κ → Fv F v, φ v p ≠ 0 ∧
      (φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 → ∀ i, p i ∈ v.adicCompletionIntegers F) := by
    intro v
    obtain ⟨p, hp⟩ := Function.ne_iff.1 (h0 v)
    refine ⟨p, hp, fun h => ?_⟩
    rw [h] at hp
    exact Set.mem_of_indicator_ne_zero hp
  choose p hp hp' using key
  refine ⟨fun i => ⟨fun v => p v i, ?_⟩, ?_⟩
  · filter_upwards [hstd] with v hv using hp' v hv i
  · exact finprod_induction (fun z : ℂ => z ≠ 0) one_ne_zero (fun a b ha hb => mul_ne_zero ha hb) fun v => hp v

def pt {κ : Type} (x : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i)

theorem pureA_pt {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) : pureA F f g (pt x y) = f x * g y := by
  simp only [pureA, pt, RingEquiv.apply_symm_apply]

theorem mem_span_finPr {κ : Type} [Fintype κ] (g) (hg : g ∈ SB (κ → Af F)) :
    g ∈ Submodule.span ℂ {p : (κ → Af F) → ℂ | ∃ φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ, (∀ v, φ v ∈ SB (κ → Fv F v)) ∧
      (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
      p = fun y => ∏ᶠ v, φ v fun i => evalV F v (y i)} := by
  obtain ⟨m, c, φ, h1, h2, rfl⟩ := Span.exists_sum_finprod hg
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨φ k, h1 k, h2 k, rfl⟩)

section

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem pol_map (M M' : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (D D' : Matrix (Fin n) (Fin d) (AE F E) → SInf F (Fin n × Fin d) → SInf F (Fin n × Fin d))
    (hD : ∀ u, At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ ↔ f₁ = D u f)
    (hD' : ∀ u, At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M'.heisLine ψ u) f f₁ ↔ f₁ = D' u f)
    (ei : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)) (hb : Function.Bijective ei)
    (hi : ∀ u, At (evI F) u → ∀ f, ei (D u f) = D' u (ei f)) : (M.Pol ψ τ).map ei = M'.Pol ψ τ := by
  have hG : ∀ f, M.IsGauss ψ τ f ↔ M'.IsGauss ψ τ (ei f) := fun f => by
    refine exists_congr fun ε => forall₂_congr fun u u' => forall₃_congr fun hu hu' _ => ⟨fun h g g' hg hg' => ?_, fun h g g' hg hg' => ?_⟩
    · rw [(hD' u hu _ _).1 hg, (hD' u' hu' _ _).1 hg', ← hi u hu, ← hi u' hu',
        h _ _ ((hD u hu _ _).2 rfl) ((hD u' hu' _ _).2 rfl), map_smul]
    · apply hb.1
      rw [(hD u hu _ _).1 hg, (hD u' hu' _ _).1 hg', map_smul, hi u hu, hi u' hu']
      exact h _ _ ((hD' u hu _ _).2 rfl) ((hD' u' hu' _ _).2 rfl)
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    refine sInf_le ⟨fun f hf => ?_, fun u hu f hf f₁ h₁ => ?_⟩
    · exact Submodule.mem_sInf.2 fun N hN => hN.1 _ ((hG f).1 hf)
    · refine Submodule.mem_sInf.2 fun N hN => hN.2 u hu (ei f) (Submodule.mem_sInf.1 hf N hN) _ ?_
      rw [hD' u hu, (hD u hu _ _).1 h₁, hi u hu]
  · refine sInf_le ⟨fun g hg => ?_, ?_⟩
    · obtain ⟨f, rfl⟩ := hb.2 g
      exact Submodule.mem_map_of_mem (Submodule.mem_sInf.2 fun N hN => hN.1 _ ((hG f).2 hg))
    · rintro u hu _ ⟨f, hf, rfl⟩ g₁ h₁
      rw [(hD' u hu _ _).1 h₁, ← hi u hu]
      exact Submodule.mem_map_of_mem (Submodule.mem_sInf.2 fun N hN =>
        hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) _ ((hD u hu _ _).2 rfl))


open PositivityTheory.ThKF0.Lib (dop aOf lOf hl) in
open scoped Classical in
theorem inter (hDq : SchwartzDq) (M M' : Model σ X W) (A : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
    (hA : ∀ u, At (evI F) u → ∀ (f G : SInf F (Fin n × Fin d)) (t : ℝ), (∀ x, G x = hl (aOf M u) (lOf M u) t f x) →
      ∀ x, A G x = hl (aOf M' u) (lOf M' u) t (A f) x) {u} (hu : At (evI F) u) (f) :
    A (dop (aOf M u) (lOf M u) f) = dop (aOf M' u) (lOf M' u) (A f) := by
  choose G hG using Line.hl_schwartz (aOf M u) (lOf M u) f
  ext x
  have h1 := hDq _ _ _ f G hG ((BoundedContinuousFunction.evalCLM ℂ x ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ) ∘L A)
  have e : (fun t => ((BoundedContinuousFunction.evalCLM ℂ x ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ) ∘L A) (G t)) =
      fun t => hl (aOf M' u) (lOf M' u) t (A f) x := funext fun t => hA u hu f (G t) t (hG t) x
  rw [e] at h1
  exact h1.unique (Lib.hasDerivAt_hl _ _ (A f) x)

end

theorem change_core {B : Base F E} (hψ : IsStd B.ψ) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M M' : Model σ X W}
    (hM : M.IsGood B.ψ) (hM' : M'.IsGood B.ψ) {e : Fn F n d →ₗ[ℂ] Fn F n d} (hE : IsEv B M M' 1 1 ∅ e)
    (hbij : Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _)) :
      ∃ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
        (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ), Function.Surjective ei ∧
        (SchwartzDq → (M.Pol B.ψ B.emb).map (ei : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)) = M'.Pol B.ψ B.emb) ∧
        (∀ v, ev v (M.vac v) = M'.vac v ∧ (SB _).map (ev v) = SB _) ∧
        ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) →
          e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v) := by
  classical
  obtain ⟨ei, ev, -, hv, hl⟩ := hE.loc
  have hg : finPr M.vac ∈ SB _ := finPr_mem _ (fun v => (hM.vac v).1) hM.std
  have hg' : finPr M'.vac ∈ SB _ := finPr_mem _ (fun v => (hM'.vac v).1) hM'.std
  obtain ⟨y, hy⟩ := exists_finPr_ne M.vac (fun v => (hM.vac v).2.1) hM.std
  obtain ⟨y', hy'⟩ := exists_finPr_ne M'.vac (fun v => (hM'.vac v).2.1) hM'.std
  have mem : ∀ (f : SInf F (Fin n × Fin d)) g, g ∈ SB (Fin n × Fin d → Af F) → pureA F f g ∈ schA F (Fin n × Fin d) :=
    fun f g h => Submodule.subset_span ⟨f, g, h, rfl⟩
  have hvac : ∀ f : SInf F (Fin n × Fin d), e (pureA F f (finPr M.vac)) = pureA F (ei f) (finPr M'.vac) := fun f => by
    have := hl f M.vac (fun v => (hM.vac v).1) (Eventually.of_forall fun _ => rfl)
    simp only [fun v => (hv v).1] at this
    exact this
  have hinj : Function.Injective ei := (injective_iff_map_eq_zero ei).2 fun f hf => by
    have h1 : e (pureA F f (finPr M.vac)) = e 0 := by
      rw [hvac, hf, map_zero]; funext x; simp [pureA]
    have h2 := hbij.injOn (mem f _ hg) (zero_mem _) h1
    refine SchwartzMap.ext fun x => ?_
    have h3 := congrFun h2 (pt x y)
    rw [pureA_pt] at h3
    exact (mul_eq_zero.1 h3).resolve_right hy
  have hsl : ∀ Φ ∈ schA F (Fin n × Fin d), ∃ f, ∀ x, e Φ (pt x y') = ei f x := by
    intro Φ hΦ
    induction hΦ using Submodule.span_induction with
    | zero => exact ⟨0, fun x => by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨f, hf⟩ := ha
      obtain ⟨g, hg⟩ := hb
      exact ⟨f + g, fun x => by simp [hf, hg]⟩
    | smul c a _ ha =>
      obtain ⟨f, hf⟩ := ha
      exact ⟨c • f, fun x => by simp [hf]⟩
    | mem Φ hΦ =>
      obtain ⟨f, g, hg, rfl⟩ := hΦ
      replace hg := mem_span_finPr g hg
      induction hg using Submodule.span_induction with
      | zero => exact ⟨0, fun x => by
          rw [show pureA F f 0 = 0 from funext fun _ => mul_zero _]; simp⟩
      | add a b _ _ ha hb =>
        obtain ⟨f₁, hf⟩ := ha
        obtain ⟨f₂, hg⟩ := hb
        exact ⟨f₁ + f₂, fun x => by
          rw [show pureA F f (a + b) = pureA F f a + pureA F f b from funext fun _ => mul_add _ _ _]; simp [hf, hg]⟩
      | smul c a _ ha =>
        obtain ⟨f₁, hf⟩ := ha
        exact ⟨c • f₁, fun x => by
          rw [show pureA F f (c • a) = c • pureA F f a from funext fun _ => mul_left_comm _ _ _]; simp [hf]⟩
      | mem p hp =>
        obtain ⟨φ, hφ, hs, rfl⟩ := hp
        have h1 := hl f φ hφ (by filter_upwards [hs, hM.std] with v h1 h2 using h1.trans h2.symm)
        refine ⟨finPr (fun v => ev v (φ v)) y' • f, fun x => ?_⟩
        rw [pure_eq, pure_eq] at h1
        refine (congrFun h1 _).trans ?_
        rw [pureA_pt]
        simp [mul_comm]
  have hsurj : Function.Surjective ei := fun g => by
    obtain ⟨Φ, hΦ, h1⟩ := hbij.surjOn (mem g _ hg')
    obtain ⟨f, hf⟩ := hsl Φ hΦ
    refine ⟨(finPr M'.vac y')⁻¹ • f, ?_⟩
    refine SchwartzMap.ext fun x => ?_
    have h2 := hf x
    rw [h1, pureA_pt] at h2
    rw [map_smul, smul_apply, ← h2, smul_eq_mul]
    field_simp
  have Heisenberg₂ : ∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ u Φ) = M'.co.rho B.ψ u (e Φ) := by
    intro u Φ hΦ
    have h1 : ∀ m : ℕ, incM F (1 : Matrix (Fin m) (Fin m) E) = 1 := fun m => Matrix.map_one _ (map_zero _) (map_one _)
    have := hE.Heisenberg₂ u Φ hΦ
    rwa [h1, h1, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at this
  refine ⟨ei, ev, hsurj, fun hDq => ?_, hv, hl⟩
  have key : ∀ (N : Model σ X W) u, At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (N.heisLine B.ψ u) f f₁ ↔
      f₁ = Lib.dop (Lib.aOf N u) (Lib.lOf N u) f := fun N u hu f f₁ =>
    ⟨Lib.actsD_unique N hψ hu, fun h => h ▸ Lib.actsD_dop N hψ hu f⟩
  refine pol_map M M' B.ψ B.emb _ _ (key M) (key M') _ ⟨hinj, hsurj⟩ fun u hu f => inter hDq M M' ei (fun u hu f G t hG x => ?_) hu f
  have e1 : M.heisLine B.ψ u t (pureA F f (finPr M.vac)) = pureA F G (finPr M.vac) := by
    rw [← Lib.tens_rOf, Lib.heisLine_tens M hψ hu f (Lib.rOf_add _) t,
      Lib.tens_rOf]
    congr 1
    exact funext fun x => (hG x).symm
  have e2 : e (M.heisLine B.ψ u t (pureA F f (finPr M.vac))) = M'.heisLine B.ψ u t (e (pureA F f (finPr M.vac))) :=
    Heisenberg₂ _ _ (mem f _ hg)
  rw [e1, hvac, hvac, ← Lib.tens_rOf (ei f),
    Lib.heisLine_tens M' hψ hu (ei f) (Lib.rOf_add _) t, Lib.tens_rOf] at e2
  have := congrFun e2 (pt x y')
  rw [pureA_pt, pureA_pt] at this
  exact mul_right_cancel₀ hy' this

end PositivityTheory.ThKF0.Change
end
end

-- bundled from Development.WeilBound.ThetaLifts.LeviDeterminants.WeilRepRationalSupportCommonDenominator
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical

namespace PositivityTheory.ThKF0

open Grow

theorem exists_dual_den (F : Type) [Field F] [NumberField F] : ∃ D : ℕ, 1 ≤ D ∧ ∀ ξ : F,
    (∀ y : 𝓞 F, ∃ z : ℤ, Algebra.trace ℚ F (ξ * y) = z) → IsIntegral ℤ ((D : F) * ξ) := by
  refine ⟨(NumberField.discr F).natAbs,
    Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero F)), ?_⟩
  intro ξ hξ
  have h10 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 := by
    rw [← FractionalIdeal.coeIdeal_top]
    exact FractionalIdeal.coeIdeal_ne_zero.mpr top_ne_bot
  have hdual : ξ ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    rw [FractionalIdeal.mem_dual h10]
    intro a ha
    obtain ⟨y, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    obtain ⟨z, hz⟩ := hξ y
    refine ⟨z, ?_⟩
    rw [Algebra.traceForm_apply, hz]
    simp
  have hD : ((NumberField.discr F).natAbs : 𝓞 F) ∈ differentIdeal ℤ (𝓞 F) := by
    rw [← NumberField.absNorm_differentIdeal F (𝓞 F)]
    exact Ideal.absNorm_mem _
  have hD' : ((NumberField.discr F).natAbs : F) ∈
      ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    rw [FractionalIdeal.mem_coeIdeal]
    exact ⟨_, hD, by simp⟩
  rw [coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)] at hD'
  have hmem := FractionalIdeal.mul_mem_mul hD' hdual
  rw [inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ h10)] at hmem
  obtain ⟨y, hy⟩ := (FractionalIdeal.mem_one_iff _).mp hmem
  rw [← hy]
  exact NumberField.RingOfIntegers.isIntegral_coe y

theorem trace_int {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (a : F)
    (h : ψ (0, (algebraMap F (AF F) a).2) = 1) : ∃ z : ℤ, Algebra.trace ℚ F a = z := by
  have e := GlobalTheory.PsiNontriv.isStd_fin_rat hψ a
  have e2 : ψ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA F 0 ((algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)) a)) = 1 := h
  rw [e2] at e
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp e.symm
  refine ⟨n, ?_⟩
  have hpi : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hq : ((Algebra.trace ℚ F a : ℚ) : ℂ) = ((n : ℚ) : ℂ) := by
    apply mul_left_cancel₀ hpi
    rw [hn]
    push_cast
    ring
  exact_mod_cast hq

theorem weil_rep_bounded_denominator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ^ k ∧
    ∀ ξ : Fin n × Fin d → F, om (g, h) Φ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  obtain ⟨C, -, hC⟩ := htBd F E σ n d X W M
  obtain ⟨m₀, hm₀, h₀⟩ := finInv F _ B.ψ hP.base.std Φ hΦ
  obtain ⟨D, hD, hDD⟩ := exists_dual_den F
  refine ⟨D * m₀ * C, 1, fun g h => ?_⟩
  obtain ⟨m, hm, hmC, hb⟩ := hC g h
  refine ⟨D * (m₀ * m), Nat.mul_pos hD (Nat.mul_pos hm₀ hm), ?_, fun ξ hξ i => ?_⟩
  · push_cast
    rw [pow_one, mul_assoc, mul_assoc]
    gcongr
  · rw [Nat.cast_mul D, mul_assoc]
    refine hDD _ fun y => trace_int hP.base.std _ ?_
    let u : AF F := (0, (algebraMap F (AF F) (y : F)).2)
    have hu : IntF u := ⟨rfl, fun v => HeightOneSpectrum.coe_mem_adicCompletionIntegers v y⟩
    have h0 : IntF (0 : AF F) := ⟨rfl, fun v => by rw [map_zero]; exact zero_mem _⟩
    have key := congrFun (h₀ _ _ _ _ (impl_sOf hP.weil g h) hb (0, Pi.single i u) ⟨fun _ => h0, fun j => by
      by_cases e : j = i
      · subst e; simpa using hu
      · simpa [e] using h0⟩) fun i => algebraMap F (AF F) (ξ i)
    simp only [schr, Prod.smul_mk, smul_zero, add_zero, Pi.zero_apply, zero_mul, mul_zero, dotProduct_smul,
      dotProduct_single] at key
    rw [← mul_right_cancel₀ hξ (key.trans (one_mul _).symm)]
    refine congrArg B.ψ (Prod.ext ?_ ?_)
    · change (0 : Ainf F) = ((m₀ * m : ℕ) : AF F).1 * ((algebraMap F (AF F) (ξ i)).1 * 0)
      rw [mul_zero, mul_zero]
    · rw [map_mul, map_mul, map_natCast, mul_assoc]
      rfl

end PositivityTheory.ThKF0
end

