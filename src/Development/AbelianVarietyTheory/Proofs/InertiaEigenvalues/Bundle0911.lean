module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0784
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0673
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesSecond
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MovedFiniteDatumFourierExpansionChainless
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0811
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0906
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0903
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0864
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0798
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0819
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0765

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniformisedCoverInvPhaseConstantsNormalisedDomin
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

namespace GlobalTheory.CoverPinDom


set_option maxHeartbeats 2000000 in
theorem pin_at {D : D7} (T : CoreJ D) (hL : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ) (hσ : GoodEmb T.Q.c σ)
    (C : Cover T j σ) (hC : C.IsUnif) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} (hV : T.V j σ = W)
    (hr : W.rank = D.R.r) {χV χW : (AE D)ˣ →* Circle} {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
    (hP : IsPair ψ θ V W χV χW om) (hM : ∀ k, IsMod W hr ((T.U j σ).X k)) {f₀ : WO V W → ℂ}
    (hf₀ : IsThetaFunO ψ V W f₀) {mu : GA D (T.V j σ) → ℂ} (hmu0 : ∀ g, mu g ≠ 0)
    (hunit : ∀ h, IsUnitFr ((T.U j σ).X (T.dict j σ h).1) (T.dict j σ h).2)
    {c₁ : C.U₂.Comp → ℂ} {c₂ : (T.U j σ).Comp → ℂ}
    (h₁ : CcIs θ V W hr C.U₂ (castDict hV C.dict₂) (castDict hV mu) (T.x₀ j σ) om f₀ c₁)
    (h₂ : CcIs θ V W hr (T.U j σ) (castDict hV (T.dict j σ)) (castDict hV mu) (T.x₀ j σ) om f₀ c₂)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) (hf : f ∈ sec (T.Q.Xo j) T.Q.c a V.rank)
    (f₂ : Rul C.d.Xo₂ C.d.c₂) (hf₂ : f₂ ∈ sec C.d.Xo₂ C.d.c₂ a V.rank) (hp : C.IsPull f f₂) (g : GA D (T.V j σ)) :
    c₁ (C.dict₂ g).1 * rdU C.U₂ f₂ (C.dict₂ g).1 (C.dict₂ g).2 =
      c₂ (T.dict j σ g).1 * rdU (T.U j σ) f (T.dict j σ g).1 (T.dict j σ g).2 := by
  subst hV
  change CcIs θ V (T.V j σ) hr C.U₂ C.dict₂ mu (T.x₀ j σ) om f₀ c₁ at h₁
  change CcIs θ V (T.V j σ) hr (T.U j σ) (T.dict j σ) mu (T.x₀ j σ) om f₀ c₂ at h₂

  have hθ := hP.inf
  have hC₀ := hC
  have hU₁ := hL.unf j hj σ hσ
  have hU₂ : IsUnf C.U₂ := hC.2.2.2.1
  obtain ⟨_, _, -, hd⟩ := hL.dictU j hj σ hσ
  have hdom₁ : ∀ h, (T.dict j σ h).2 ∈ ((T.U j σ).X (T.dict j σ h).1).dom := hd.2.2.2.1
  obtain ⟨hr₁, g₁, e₁, F₁, ik₁, φ₁, th₁, -, -, hth₁, -, hd₁⟩ := hL.adPin j hj σ hσ
  obtain ⟨-, -, -, -, hdom₂, hr₂, g₂, e₂, F₂, ik₂, φ₂, th₂, hW₂, hth₂, -, hd₂⟩ := hC
  obtain ⟨hr₀, hW₁⟩ := hL.modelW j hj σ hσ
  obtain ⟨γ₁, hγ₁, hL₁, -, hq₁⟩ := hd₁ g
  obtain ⟨γ₂, hγ₂, hL₂, -, hq₂⟩ := hd₂ g
  obtain ⟨δ, hl, hi, hfδ⟩ := GlobalTheory.CoverFrameMove.move (T.V j σ) hr₁ g γ₁ γ₂ hγ₁ hγ₂ _ _ _ _ (hW₁ (T.dict j σ g).1).1 (hW₂ (C.dict₂ g).1).1 hL₁ hL₂
  have hfr : ∀ (τ : D.host.E →+* ℂ) (t₂ : τ ∈ (C.U₂.X (C.dict₂ g).1).Ψ) (t₁ : τ ∈ ((T.U j σ).X (T.dict j σ g).1).Ψ),
      mat (T.dict j σ g).2 ⟨τ, t₁⟩ = (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ g).2 ⟨τ, t₂⟩ := by
    intro τ t₂ t₁
    have e₂' := hq₂ ⟨τ, t₂⟩
    have e₁' := hq₁ ⟨τ, t₁⟩
    rw [GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (hth₂ _ ⟨τ, t₂⟩) (hth₁ _ ⟨τ, t₁⟩)] at e₂'
    rw [e₁', e₂']
    exact hfδ τ _ (hth₁ _ ⟨τ, t₁⟩) _
  have hΨ₁ : ∀ k, ∀ τ ∈ ((T.U j σ).X k).Ψ, ∃ ρ, τ = tauE D ρ := fun k τ hτ => ((hM k).psi τ).1 hτ
  have hΨ₂ : ∀ k, ∀ τ ∈ (C.U₂.X k).Ψ, ∃ ρ, τ = tauE D ρ := fun k τ hτ =>
    hΨ₁ (T.dict j σ g).1 τ (((hU₁.2.1 _).2 τ).2 (((hU₂.2.1 k).2 τ).1 hτ))
  have hat₁ : AtComp θ (T.V j σ) hr (T.U j σ).X (T.dict j σ) (T.x₀ j σ) g γ₁ := by
    refine ⟨hγ₁, ?_, ?_⟩
    · apply SetLike.coe_injective
      rw [hL₁, latR, Submodule.map_coe]
      rfl
    · funext τ
      have := hq₁ τ
      rw [← GlobalTheory.AdTh.CcModel.realM_mt hθ _ (γ₁ * g) τ.1 (hΨ₁ _ _ τ.2) _ (hth₁ _ τ)] at this
      exact this
  have hat₂ : AtComp θ (T.V j σ) hr C.U₂.X C.dict₂ (T.x₀ j σ) g γ₂ := by
    refine ⟨hγ₂, ?_, ?_⟩
    · apply SetLike.coe_injective
      rw [hL₂, latR, Submodule.map_coe]
      rfl
    · funext τ
      have := hq₂ τ
      rw [← GlobalTheory.AdTh.CcModel.realM_mt hθ _ (γ₂ * g) τ.1 (hΨ₂ _ _ τ.2) _ (hth₂ _ τ)] at this
      exact this
  have hrm : ∀ τ ∈ ((T.U j σ).X (T.dict j σ g).1).Ψ, Matrix.reindex (finCongr hr) (finCongr hr)
      (realM θ (Formalism.L2.Theta.mt (T.V j σ) (γ₁ * γ₂⁻¹)) τ) = (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ := by
    intro τ t₁
    have hth := hth₁ _ ⟨τ, t₁⟩
    rw [GlobalTheory.AdTh.CcModel.realM_mt hθ _ _ τ (hΨ₁ _ _ t₁) _ hth]
    generalize th₁ (T.dict j σ g).1 ⟨τ, t₁⟩ = th at hth ⊢
    have hmul : ∀ a b : GA D (T.V j σ), archM (T.V j σ) th (a * b) = archM _ th a * archM _ th b := fun a b => by
      rw [archM, archM, archM, map_mul, Units.val_mul, Matrix.map_mul]
    have hone : archM (T.V j σ) th 1 = 1 := by
      rw [archM, map_one, Units.val_one, Matrix.map_one] <;> simp
    have hre : ∀ A B : Matrix (Fin (T.V j σ).rank) (Fin (T.V j σ).rank) ℂ,
        Matrix.reindex (finCongr hr) (finCongr hr) (A * B) =
          Matrix.reindex (finCongr hr) (finCongr hr) A * Matrix.reindex (finCongr hr) (finCongr hr) B := fun A B => by
      simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    have e1 := hfδ τ th hth 1
    rw [Matrix.mul_one, Matrix.mul_one] at e1
    rw [show γ₁ * g = γ₁ * γ₂⁻¹ * (γ₂ * g) by group, hmul, hre] at e1
    have e3 : Matrix.reindex (finCongr hr) (finCongr hr) (archM (T.V j σ) th (γ₂ * g)) *
        Matrix.reindex (finCongr hr) (finCongr hr) (archM (T.V j σ) th (γ₂ * g)⁻¹) = 1 := by
      rw [← hre, ← hmul, mul_inv_cancel, hone]
      simp
    calc _ = Matrix.reindex (finCongr hr) (finCongr hr) (archM (T.V j σ) th (γ₁ * γ₂⁻¹)) *
          (Matrix.reindex (finCongr hr) (finCongr hr) (archM (T.V j σ) th (γ₂ * g)) *
            Matrix.reindex (finCongr hr) (finCongr hr) (archM (T.V j σ) th (γ₂ * g)⁻¹)) := by rw [e3, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, e1, Matrix.mul_assoc, e3, Matrix.mul_one]
  have hm2 : ∀ a b : GA D (T.V j σ), om (1, a * b) = om (1, a) * om (1, b) := fun a b => by
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  have hF : ∀ w, om (1, γ₁ * g) f₀ (actO V (T.V j σ) 1 (γ₁ * γ₂⁻¹) w) = om (1, γ₂ * g) f₀ w := fun w => by
    rw [show γ₁ * g = γ₁ * γ₂⁻¹ * (γ₂ * g) by group, hm2, Module.End.mul_apply]
    exact GlobalTheory.WeilRat.om_rat_actO D ψ hP.weil.std V (T.V j σ) χV χW om hP.weil 1 (one_mem _) _
      (mul_mem hγ₁ (inv_mem hγ₂)) _ (hP.weil.om_pres _ _ hf₀) w
  have key := _root_.GlobalTheory.CoverConstMove.const_cover D T hL j hj σ hσ C hC₀ ψ θ V χV χW om hP hr hM g δ hl hi hfr (γ₁ * γ₂⁻¹) hrm (hdom₁ g) (hdom₂ g)
    (hunit g) (om (1, γ₂ * g) f₀) (om (1, γ₁ * g) f₀) (c₁ (C.dict₂ g).1 * mu g) (c₂ (T.dict j σ g).1 * mu g)
    (h₁.2 g γ₂ hat₂ (hdom₂ g)) (h₂.2 g γ₁ hat₁ (hdom₁ g)) hF a f hf f₂ hf₂ hp
  apply mul_left_cancel₀ (hmu0 g)
  linear_combination key


set_option maxHeartbeats 2000000 in
theorem isPinned_inv_mul : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, ∀ ph : ℂ, ‖ph‖ = 1 → BaseCc T R i hV ph → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, C.IsUnif → ∀ cc : C.U₂.Comp → ℂ, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) C.U₂ (castDict hV C.dict₂) (castDict hV (T.mu ((i : ℕ) + 1) T.σ₀)) (T.x₀ ((i : ℕ) + 1) T.σ₀) (R.ωP i A.μ0) (R.vacP i) cc → ∀ a, Dom a (κ i).n → ({ C with cc₂ := fun k => ph⁻¹ * cc k } : Cover T ((i : ℕ) + 1) T.σ₀).IsPinned a (κ i).n := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL hlev hgrp hfam hmods hthP ht i hS hV ph hph hbase C hC cc hcc a ha
  have hC3 : GlobalTheory.Hk3.CoreNoChain R F := ⟨hlev, hgrp, hfam, hmods, hthP⟩
  have hj : InR D ((i : ℕ) + 1) := inR i
  have hσ : GoodEmb T.Q.c T.σ₀ := T.good_σ₀
  have hmod := GlobalTheory.AdTh.models_at_record_core_nc D G Pl0 T0 A T R F κ v₀ hC3 ht i T.σ₀ rfl
  have hP := (GlobalTheory.AdTh.RecPairCore.isPair_record_core_nc D G Pl0 T0 A T.Q.c.F R F hC3 i A.μ0 hS).1
  have hf₀ := (hthP.vP i A.μ0).1.2.theta
  have hmu0 : ∀ g, T.mu ((i : ℕ) + 1) T.σ₀ g ≠ 0 := fun g =>
    norm_ne_zero_iff.1 (((hL.muVal _ hj _ hσ).norm g).trans_ne one_ne_zero)
  have hunit := (hL.muUnit _ hj _ hσ).2.2.2
  have hph0 : ph ≠ 0 := norm_ne_zero_iff.1 (by rw [hph]; exact one_ne_zero)
  refine ⟨fun k => ?_, fun f hf f₂ hf₂ hp => ?_⟩
  · show ‖ph⁻¹ * cc k‖ = 1
    rw [norm_mul, norm_inv, hph, hcc.norm k, inv_one, one_mul]
  · funext g
    have hn : (κ i).n = (Vc D i).rank := (hmod (T.dict _ _ g).1).2.2.2.2.2.2.2.2.2.2.2.1
    rw [hn] at hf hf₂
    have key := GlobalTheory.CoverPinDom.pin_at T hL _ hj _ hσ C hC hV (rank_Wc i) hP (fun k => (hmod k).1) hf₀ hmu0 hunit hcc
      hbase a f hf f₂ hf₂ hp g
    show Cover.rd _ a f₂ g = T.phiJ _ _ a f g
    simp only [Cover.rd, CoreJ.phiJ, Pi.smul_apply, smul_eq_mul, adel_muPin] at key ⊢
    have hinv : ph⁻¹ * ph = 1 := inv_mul_cancel₀ hph0
    linear_combination (↑(lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a) * ph⁻¹ * T.mu ((i : ℕ) + 1) T.σ₀ g) * key +
      (↑(lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a) * T.cE ((i : ℕ) + 1) T.σ₀ (T.dict ((i : ℕ) + 1) T.σ₀ g).1 *
        T.mu ((i : ℕ) + 1) T.σ₀ g * rdU (T.U ((i : ℕ) + 1) T.σ₀) f (T.dict ((i : ℕ) + 1) T.σ₀ g).1
          (T.dict ((i : ℕ) + 1) T.σ₀ g).2) * hinv

end GlobalTheory.CoverPinDom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniformisedLevelCoverExistsConstantsDominantWeig
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.Member GlobalTheory.CompRat GlobalTheory.FinalJoin
open scoped TensorProduct Matrix

namespace GlobalTheory.CoverRead.Cover

theorem exists_pinned_dom : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j, Formalism.L2.Pj.InR D j → ∀ σ : T.Q.c.F →+* ℂ,
    GoodEmb T.Q.c σ → ∀ C : Cover T j σ, C.IsUnif → ∀ n : ℕ, ∃ cc₂ : C.U₂.Comp → ℂ,
      ∀ a : (D.host.E →+* ℂ) × ℕ → ℕ, Dom a n → ({ C with cc₂ := cc₂ } : Cover T j σ).IsPinned a n := by
  intro D T hT j hj σ hσ C hC n
  obtain ⟨u, hu1, hu⟩ := _root_.GlobalTheory.CoverConstAt.cover_read_const D T hT j hj σ hσ C hC n
  choose k γ hk using fun k₂ => _root_.GlobalTheory.CoverFrame.comp_over_comp D T hT j hj σ hσ C hC k₂
  have hu0 : ∀ k₂, u k₂ ≠ 0 := fun k₂ h => by simpa [h] using hu1 k₂
  refine ⟨fun k₂ => T.cE j σ (k k₂) / u k₂, fun a ha => ⟨?_, ?_⟩⟩
  · intro k₂
    show ‖T.cE j σ (k k₂) / u k₂‖ = 1
    rw [norm_div, hu1, hT.cUnit j hj σ hσ, div_one]
  · intro f hf f₂ hf₂ hp
    funext g
    have hp' : C.IsPull f f₂ := hp
    have h3 : (T.dict j σ g).1 = k (C.dict₂ g).1 := (hk (C.dict₂ g).1).2.2.1 g rfl
    show (lieFac (T.Q.Dw j) (xiR D) a : ℂ) *
        (T.cE j σ (k (C.dict₂ g).1) / u (C.dict₂ g).1 * T.mu j σ g * rdU C.U₂ f₂ (C.dict₂ g).1 (C.dict₂ g).2) =
      (lieFac (T.Q.Dw j) (xiR D) a : ℂ) *
        (T.cE j σ (T.dict j σ g).1 * T.mu j σ g * rdU (T.U j σ) f (T.dict j σ g).1 (T.dict j σ g).2)
    rw [hu a ha f hf f₂ hf₂ hp' g, ← h3]
    field_simp [hu0 (C.dict₂ g).1]

end GlobalTheory.CoverRead.Cover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumTranslateSumConjugateHalfNeZero
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
namespace GlobalTheory.VacTransNe

theorem sum_heisO_conjHalf_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D), IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ Y : Finset (WO V W), (∀ y ∈ Y, IsHalf (cA D eT) y ∧ m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) → (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → y = y') → (∀ y : WO V W, IsHalf (cA D eT) y → m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → ∃ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) → ∑ y ∈ Y, heisO ψ V W y f₀ ≠ 0 := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT hT _ _ _ Y hY hYd hYc h0
  obtain ⟨y₀, hy₀, -⟩ := hYc 0 (fun i j => mul_zero _) (by rw [nsmul_zero]; exact zero_mem _)
  obtain ⟨p, hp⟩ := hP.2.2.2.2.2.2.2.2.2.norm.1
  have h := GlobalTheory.VacTransOrth.vacuumTranslates_conjHalf_sq_norm_eq_card_alt D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T eT hT Y
    (fun y hy => (hY y hy).1) hYd p.1 p.2 hp
  rw [h0] at h
  have hz : nrm2 p.1 p.2 (0 : WO V W → ℂ) = 0 := by
    unfold nrm2
    simp
  rw [hz] at h
  have hc : Y.card = 0 := by exact_mod_cast h.symm
  exact Finset.card_ne_zero_of_mem hy₀ hc

end GlobalTheory.VacTransNe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumTranslateSumFixedByFlippedLattice
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

namespace GlobalTheory.FlipFixSum

open GlobalTheory.PlaceModel GlobalTheory.PlaceModelSum

variable {D : D7} {S T : HSp D}

theorem smul_half_zero {e c : AE D} (h : e * c = 0) {y : WO S T} (hy : c • y = y) : e • y = 0 := by
  rw [← hy, smul_smul, h, zero_smul]

theorem half_two : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
  rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
  norm_num

theorem natCast_mul_inv {m : ℕ} (hm : m ≠ 0) : (m : AE D) * incA D ((m : D.host.E)⁻¹) = 1 := by
  rw [show (m : AE D) = incA D (m : D.host.E) by simp, ← map_mul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.2 hm), map_one]

theorem sum_reindex {X M : Type} [AddCommMonoid M] (Y : Finset X) (G g : X → M) (R : X → X → Prop)
    (hR : ∀ y ∈ Y, ∃ y' ∈ Y, R y y' ∧ G y = g y')
    (hinj : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, ∀ z ∈ Y, R y₁ z → R y₂ z → y₁ = y₂) :
    ∑ y ∈ Y, G y = ∑ y ∈ Y, g y := by
  classical
  choose! φ hφY hφR hφG using hR
  have hinjOn : Set.InjOn φ Y := fun y₁ h₁ y₂ h₂ he =>
    hinj y₁ h₁ y₂ h₂ (φ y₁) (hφY y₁ h₁) (hφR y₁ h₁) (he ▸ hφR y₂ h₂)
  have himg : Y.image φ = Y := Finset.eq_of_subset_of_card_le
    (Finset.image_subset_iff.2 hφY) (Finset.card_image_of_injOn hinjOn).ge
  calc ∑ y ∈ Y, G y = ∑ y ∈ Y, g (φ y) := Finset.sum_congr rfl hφG
    _ = ∑ z ∈ Y.image φ, g z := (Finset.sum_image hinjOn).symm
    _ = ∑ y ∈ Y, g y := by rw [himg]

end GlobalTheory.FlipFixSum

namespace GlobalTheory.FlipFixSum

open GlobalTheory.PlaceModel GlobalTheory.PlaceModelSum GlobalTheory.LevelSeries

variable {D : D7} {S T : HSp D}

theorem flipElt_eq (e : AE D) (m : ℕ) :
    flipElt e m = (e * (m : AE D) + (1 - e - cA D e)) + cA D e * incA D ((m : D.host.E)⁻¹) := by
  unfold flipElt; ring

theorem cA_intPart (e : AE D) (m : ℕ) :
    cA D (e * (m : AE D) + (1 - e - cA D e)) = cA D e * (m : AE D) + (1 - cA D e - e) := by
  simp only [map_add (f := _), map_mul, map_sub, map_one, cA_cA, map_natCast]


set_option maxHeartbeats 1000000 in
theorem phase_eq {ψ : AddChar (AF D.host.F) ℂ} {e c b k : AE D} {m : ℕ} (hc : cA D e = c) (hcc : c * c = c)
    (hec : e * c = 0) (hcb : cA D b = c * (m : AE D) + (1 - c - e)) (hmk : (m : AE D) * k = 1)
    {x y : WO S T} (hy : c • y = y) (hwy : ψ (symplO S T (e • x) ((m : AE D) • y)) = 1)
    (hxx : ψ (symplOH S T x (c • x)) = 1) :
    ψ (symplOH S T ((b + c * k) • x) y) = ψ (symplOH S T (y + (c * k) • x) (b • x)) := by
  have hce : c * e = 0 := by rw [mul_comm, hec]
  have hcA : cA D c = e := by rw [← hc, cA_cA]
  have hqy : symplO S T ((c * k) • x) y = 0 := by
    rw [← smul_smul, symplO_smul, hcA, smul_half_zero hec hy, symplO_zero_right]
  have hby : cA D b • y = c • ((m : AE D) • y) := by
    conv_lhs => rw [← hy]
    rw [smul_smul, smul_smul, hcb]
    congr 1
    linear_combination (m : AE D) * hcc - hcc - hce
  have hwy' : symplO S T (b • x) y = symplO S T (e • x) ((m : AE D) • y) := by
    rw [symplO_smul, hby, symplO_smul S T e, hc]
  have hbq : cA D b • ((c * k) • x) = c • x := by
    rw [smul_smul, hcb]
    congr 1
    linear_combination k * (m : AE D) * hcc - k * hcc - k * hce + c * hmk
  have hqw : symplO S T ((c * k) • x) (b • x) = -symplO S T x (c • x) := by
    rw [symplO_skew S T (b • x) ((c * k) • x), symplO_smul, hbq]
  have key : symplOH S T ((b + c * k) • x) y =
      symplOH S T (y + (c * k) • x) (b • x) + symplO S T (b • x) y + symplOH S T x (c • x) := by
    simp only [symplOH]
    rw [add_smul, symplO_add_left S T (b • x), symplO_add_left S T y, hqy, hqw, symplO_skew S T (b • x) y]
    linear_combination (symplO S T (b • x) y) * half_two (D := D)
  rw [key, AddChar.map_add_eq_mul ψ (symplOH S T (y + (c * k) • x) (b • x) + symplO S T (b • x) y) (symplOH S T x (c • x)),
    AddChar.map_add_eq_mul ψ (symplOH S T (y + (c * k) • x) (b • x)) (symplO S T (b • x) y), hwy', hwy, hxx, mul_one, mul_one]


set_option maxHeartbeats 1000000 in
theorem heisO_translate {ψ : AddChar (AF D.host.F) ℂ} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {f₀ : WO S T → ℂ}
    (hlat : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f₀)
    {e c b k : AE D} {m : ℕ} (hO : IsOrthSum e) (hc : cA D e = c) (hcc : c * c = c)
    (hec : e * c = 0) (hcb : cA D b = c * (m : AE D) + (1 - c - e)) (hmk : (m : AE D) * k = 1)
    {x y y' : WO S T} (hw : heisO ψ S T (b • x) f₀ = f₀) (hy : c • y = y)
    (hwy : ψ (symplO S T (e • x) ((m : AE D) • y)) = 1) (hxx : ψ (symplOH S T x (c • x)) = 1)
    (hy' : c • y' = y')
    (hl : y + (c * k) • x - y' ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) :
    heisO ψ S T ((b + c * k) • x) (heisO ψ S T y f₀) = heisO ψ S T y' f₀ := by
  have h1 := GlobalTheory.LatVac.heisO_heisO ψ ((b + c * k) • x) y f₀
  have h2 := GlobalTheory.LatVac.heisO_heisO ψ (y + (c * k) • x) (b • x) f₀
  rw [hw] at h2
  have hsum : (b + c * k) • x + y = y + (c * k) • x + b • x := by rw [add_smul]; abel
  rw [h1, phase_eq hc hcc hec hcb hmk hy hwy hxx, hsum, ← h2]
  have hcq : c • ((c * k) • x) = (c * k) • x := by rw [smul_smul, ← mul_assoc, hcc]
  have hlc : c • (y + (c * k) • x - y') = y + (c * k) • x - y' := by rw [smul_sub, smul_add, hy, hcq, hy']
  have hlc' : cA D e • (y + (c * k) • x - y') = y + (c * k) • x - y' := by rw [hc]; exact hlc
  have hl0 : heisO ψ S T (y + (c * k) • x - y') f₀ = f₀ :=
    hO.conj.heisO_eq (by rw [cA_cA, hc, hec]) hlat _ (AddSubgroup.mem_inf.2 ⟨hl, (mem_half S T).2 hlc'⟩)
  have hcA : cA D c = e := by rw [← hc, cA_cA]
  have hp : symplO S T y' (y + (c * k) • x - y') = 0 := by
    have h' : symplO S T y' (y + (c * k) • x - y') = symplO S T (c • y') (y + (c * k) • x - y') := by rw [hy']
    rw [h', symplO_smul, hcA, smul_half_zero hec hlc, symplO_zero_right]
  have h3 := GlobalTheory.LatVac.heisO_heisO ψ y' (y + (c * k) • x - y') f₀
  rw [hl0, symplOH, hp, mul_zero, AddChar.map_zero_eq_one, one_smul] at h3
  rw [h3, add_sub_cancel]

end GlobalTheory.FlipFixSum

namespace GlobalTheory.FlipFixSum

open GlobalTheory.PlaceModel GlobalTheory.PlaceModelSum GlobalTheory.LevelSeries


set_option maxHeartbeats 2000000 in
theorem flip_fix : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D), IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ Y : Finset (WO V W), (∀ y ∈ Y, IsHalf (cA D eT) y ∧ m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) → (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → y = y') → (∀ y : WO V W, IsHalf (cA D eT) y → m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → ∃ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) → (∀ u ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True), heisO ψ V W (flipElt eT m • (2 • u)) (∑ y ∈ Y, heisO ψ V W y f₀) = ∑ y ∈ Y, heisO ψ V W y f₀) ∧ ∀ e : AE D, IsSplitIdem D e → ∀ u ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True), IsHalf e u → heisO ψ V W (flipElt eT m • u) (∑ y ∈ Y, heisO ψ V W y f₀) = ∑ y ∈ Y, heisO ψ V W y f₀ := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT hT hm _ _ Y hY hdist hcompl
  obtain ⟨-, -, -, -, hSV, hSW, -, -, hvac⟩ := hP
  obtain ⟨hψ, hv⟩ := hvac
  have hlat := hv.lat
  have hO := isOrthSum_of_isIdemSum hT
  have hec : eT * cA D eT = 0 := hT.2
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hmk := natCast_mul_inv (D := D) hm0
  have hcc : cA D eT * cA D eT = cA D eT := by rw [← map_mul, hO.idem]
  have hee : eT * eT = eT := hO.idem
  have hbu : ∀ u ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True),
      (eT * (m : AE D) + (1 - eT - cA D eT)) • u ∈
        latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) := by
    intro u hu
    have e1 : (eT * (m : AE D) + (1 - eT - cA D eT)) • u = m • (eT • u) + (u - eT • u - cA D eT • u) := by
      rw [add_smul, sub_smul, sub_smul, one_smul, mul_comm, ← smul_smul, Nat.cast_smul_eq_nsmul]
    rw [e1]
    exact add_mem (nsmul_mem (idem_smul_latO hee hu) m)
      (sub_mem (sub_mem hu (idem_smul_latO hee hu)) (idem_smul_latO hcc hu))
  have gen : ∀ x ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True),
      heisO ψ V W ((eT * (m : AE D) + (1 - eT - cA D eT)) • x) f₀ = f₀ →
      ψ (symplOH V W x (cA D eT • x)) = 1 →
      heisO ψ V W (flipElt eT m • x) (∑ y ∈ Y, heisO ψ V W y f₀) = ∑ y ∈ Y, heisO ψ V W y f₀ := by
    intro x hx hw hxx
    rw [flipElt_eq]
    change heisL V W ψ _ (∑ y ∈ Y, heisO ψ V W y f₀) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine sum_reindex Y _ _ (fun y y' => y + (cA D eT * incA D ((m : D.host.E)⁻¹)) • x - y' ∈
        latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True))
      (fun y hy => ?_) (fun y₁ h₁ y₂ h₂ z _ r₁ r₂ => ?_)
    · have hyc : cA D eT • y = y := (mem_half V W).1 ((isHalf_iff V W).1 (hY y hy).1)
      have hhalf : IsHalf (cA D eT) (y + (cA D eT * incA D ((m : D.host.E)⁻¹)) • x) :=
        (isHalf_iff V W).2 ((mem_half V W).2 (by rw [smul_add, hyc, smul_smul, ← mul_assoc, hcc]))
      have hmq : m • (y + (cA D eT * incA D ((m : D.host.E)⁻¹)) • x) ∈
          latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) := by
        rw [nsmul_add]
        refine add_mem (hY y hy).2 ?_
        rw [← Nat.cast_smul_eq_nsmul (AE D), smul_smul,
          show (m : AE D) * (cA D eT * incA D ((m : D.host.E)⁻¹)) = cA D eT by
            linear_combination cA D eT * hmk]
        exact idem_smul_latO hcc hx
      obtain ⟨y', hy'Y, hd⟩ := hcompl _ hhalf hmq
      have hy'c : cA D eT • y' = y' := (mem_half V W).1 ((isHalf_iff V W).1 (hY y' hy'Y).1)
      have hwy : ψ (symplO V W (eT • x) ((m : AE D) • y)) = 1 := by
        rw [Nat.cast_smul_eq_nsmul]
        exact GlobalTheory.LatVac.char_sympl_eq_one hψ hSV hSW (idem_smul_latO hee hx) (hY y hy).2
      refine ⟨y', hy'Y, hd, ?_⟩
      exact heisO_translate hlat hO rfl hcc hec (cA_intPart eT m) hmk hw hyc hwy hxx hy'c hd
    · refine hdist y₁ h₁ y₂ h₂ ?_
      have := sub_mem r₁ r₂
      convert this using 1
      abel
  refine ⟨fun u hu => ?_, fun e he u hu hhu => ?_⟩
  · refine gen (2 • u) (nsmul_mem hu 2) ?_ ?_
    · rw [smul_comm]
      exact hlat.1 _ (hbu u hu)
    · have hS := GlobalTheory.LatVac.char_sympl_eq_one hψ hSV hSW hu (idem_smul_latO hcc hu)
      rw [two_nsmul, smul_add, symplOH, symplO_add_left, symplO_add_right]
      have e2 : algebraMap D.host.F (AF D.host.F) (1 / 2) *
          (symplO V W u (cA D eT • u) + symplO V W u (cA D eT • u) +
            (symplO V W u (cA D eT • u) + symplO V W u (cA D eT • u))) =
          symplO V W u (cA D eT • u) + symplO V W u (cA D eT • u) := by
        linear_combination (2 * symplO V W u (cA D eT • u)) * half_two (D := D)
      rw [e2, AddChar.map_add_eq_mul ψ (symplO V W u (cA D eT • u)) (symplO V W u (cA D eT • u)), hS, one_mul]
  · have hue : e • u = u := (mem_half V W).1 ((isHalf_iff V W).1 hhu)
    refine gen u hu ?_ ?_
    · have hb : e • ((eT * (m : AE D) + (1 - eT - cA D eT)) • u) = (eT * (m : AE D) + (1 - eT - cA D eT)) • u := by
        rw [smul_smul, mul_comm, ← smul_smul, hue]
      exact hlat.2 e he _ (hbu u hu) ((isHalf_iff V W).2 ((mem_half V W).2 hb))
    · have h0 : symplO V W u (cA D eT • u) = 0 := by
        have h' : symplO V W u (cA D eT • u) = symplO V W (e • u) (cA D eT • (e • u)) := by rw [hue]
        rw [h', symplO_smul, smul_smul, smul_smul, mul_right_comm (cA D e) (cA D eT) e, mul_comm (cA D e) e, he.2.1, zero_mul,
          zero_smul, symplO_zero_right]
      rw [symplOH, h0, mul_zero, AddChar.map_zero_eq_one]

end GlobalTheory.FlipFixSum
end
end

