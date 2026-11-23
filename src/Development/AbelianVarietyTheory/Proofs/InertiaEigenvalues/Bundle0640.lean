module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothVecLowKSub
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0856

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalHeckeSumPreservesPrincipalLevelForms
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.LocalHeckeLevel

theorem sum_mul_left_eq {Gp M : Type} [Group Gp] [AddCommMonoid M] (K : Subgroup Gp) (α : Gp) (C : Finset Gp)
    (h1 : ∀ γ ∈ C, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * α * k₂)
    (h2 : ∀ x : Gp, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * α * k₂) → ∃! γ, γ ∈ C ∧ γ⁻¹ * x ∈ K)
    (F : Gp → M) (hF : ∀ x, ∀ κ ∈ K, F (x * κ) = F x) {k₀ : Gp} (hk₀ : k₀ ∈ K) :
    ∑ δ ∈ C, F (k₀ * δ) = ∑ δ ∈ C, F δ := by
  classical
  have hmem : ∀ k ∈ K, ∀ δ ∈ C, ∃ k₁ ∈ K, ∃ k₂ ∈ K, k * δ = k₁ * α * k₂ := by
    intro k hk δ hδ
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := h1 δ hδ
    exact ⟨k * k₁, K.mul_mem hk hk₁, k₂, hk₂, by simp only [mul_assoc]⟩
  let s : Gp → Gp → Gp := fun k δ =>
    if h : ∃ k₁ ∈ K, ∃ k₂ ∈ K, k * δ = k₁ * α * k₂ then (h2 _ h).exists.choose else δ
  have hs : ∀ k ∈ K, ∀ δ ∈ C, s k δ ∈ C ∧ (s k δ)⁻¹ * (k * δ) ∈ K := by
    intro k hk δ hδ
    have h := hmem k hk δ hδ
    have e : s k δ = (h2 _ h).exists.choose := dif_pos h
    rw [e]
    exact (h2 _ h).exists.choose_spec
  have huniq : ∀ k ∈ K, ∀ δ ∈ C, ∀ γ ∈ C, γ⁻¹ * (k * δ) ∈ K → s k δ = γ := by
    intro k hk δ hδ γ hγ hγK
    exact (h2 _ (hmem k hk δ hδ)).unique (hs k hk δ hδ) ⟨hγ, hγK⟩
  have hinv : ∀ δ ∈ C, s k₀⁻¹ (s k₀ δ) = δ := by
    intro δ hδ
    obtain ⟨hm, hK⟩ := hs k₀ hk₀ δ hδ
    apply huniq _ (K.inv_mem hk₀) _ hm _ hδ
    have e : δ⁻¹ * (k₀⁻¹ * s k₀ δ) = ((s k₀ δ)⁻¹ * (k₀ * δ))⁻¹ := by group
    rw [e]
    exact K.inv_mem hK
  have hinv' : ∀ δ ∈ C, s k₀ (s k₀⁻¹ δ) = δ := by
    intro δ hδ
    obtain ⟨hm, hK⟩ := hs k₀⁻¹ (K.inv_mem hk₀) δ hδ
    apply huniq _ hk₀ _ hm _ hδ
    have e : δ⁻¹ * (k₀ * s k₀⁻¹ δ) = ((s k₀⁻¹ δ)⁻¹ * (k₀⁻¹ * δ))⁻¹ := by group
    rw [e]
    exact K.inv_mem hK
  refine Finset.sum_nbij' (s k₀) (s k₀⁻¹) (fun δ hδ => (hs k₀ hk₀ δ hδ).1)
    (fun δ hδ => (hs _ (K.inv_mem hk₀) δ hδ).1) hinv hinv' ?_
  intro δ hδ
  obtain ⟨_, hK⟩ := hs k₀ hk₀ δ hδ
  calc F (k₀ * δ) = F (s k₀ δ * ((s k₀ δ)⁻¹ * (k₀ * δ))) := by rw [mul_inv_cancel_left]
    _ = F (s k₀ δ) := hF _ _ hK

variable {D : D7}

theorem mt_mul (V : HSp D) (a b : GA D V) : mt V (a * b) = mt V a * mt V b := by
  unfold Formalism.L2.Theta.mt
  rw [map_mul, Units.val_mul]

theorem mt_one (V : HSp D) : mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [map_one, Units.val_one]

theorem mt_injective (V : HSp D) {a b : GA D V} (h : mt V a = mt V b) : a = b :=
  Subtype.val_injective (Units.ext h)

theorem suppF_mul {V : HSp D} {f : AE D} {a b : GA D V} (ha : SuppF V f a) (hb : SuppF V f b) :
    SuppF V f (a * b) := by
  intro i j
  have e : mt V (a * b) - 1 = (mt V a - 1) * mt V b + (mt V b - 1) := by
    rw [mt_mul, sub_mul, one_mul]; abel
  rw [e, Matrix.add_apply, Matrix.mul_apply, mul_add, Finset.mul_sum, hb i j]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← mul_assoc, ha i l]

theorem suppF_inv {V : HSp D} {f : AE D} {a : GA D V} (ha : SuppF V f a) : SuppF V f a⁻¹ := by
  intro i j
  have e : mt V a⁻¹ - 1 = -(mt V a⁻¹ * (mt V a - 1)) := by
    rw [mul_sub, ← mt_mul, inv_mul_cancel, mt_one, mul_one]; abel
  rw [e, Matrix.neg_apply, Matrix.mul_apply, mul_neg, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_left_comm, ha l j]

theorem suppF_one (V : HSp D) (f : AE D) : SuppF V f (1 : GA D V) := by
  intro i j
  simp [mt_one]

def suppSub (V : HSp D) (f : AE D) : Subgroup (GA D V) where
  carrier := {g | SuppF V f g}
  mul_mem' := suppF_mul
  one_mem' := suppF_one V f
  inv_mem' := suppF_inv

theorem comm_of_suppF_trivAt {V : HSp D} {f : AE D} {a b : GA D V} (ha : SuppF V f a) (hb : TrivAt V f b) :
    a * b = b * a := by
  apply mt_injective
  have hAB : (mt V a - 1) * (mt V b - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← ha i l, mul_assoc, mul_left_comm, hb l j, mul_zero]
  have hBA : (mt V b - 1) * (mt V a - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← ha l j, mul_left_comm, ← mul_assoc, hb i l, zero_mul]
  have e1 : mt V a * mt V b = (mt V a - 1) * (mt V b - 1) + mt V a + mt V b - 1 := by noncomm_ring
  have e2 : mt V b * mt V a = (mt V b - 1) * (mt V a - 1) + mt V b + mt V a - 1 := by noncomm_ring
  rw [mt_mul, mt_mul, e1, e2, hAB, hBA, zero_add, zero_add, add_comm (mt V a)]

theorem heckeOn_mem_wall : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m}, LevProd R i → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → ∀ (α : GA D (Wc D i)), SuppF (Wc D i) f α → ∀ (C : Finset (GA D (Wc D i))), (∀ γ ∈ C, SuppF (Wc D i) f γ) → IsCosetRep (Wc D i) {k | k ∈ levW R i ∧ SuppF (Wc D i) f k} α C → ∀ T ∈ R.Wall i (sg0 D A), heckeOn (R.MW i (sg0 D A)) C T ∈ R.Wall i (sg0 D A) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i hLP v f hf α _ C hC hrep Tm hT
  obtain ⟨hle, hchi, cmp, hcmp1, hcmp2⟩ := hLP
  have hT' : IsMultMap R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv))
      (levChi _ (R.βW i) (R.datWp i R.triv)) Tm := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hT
  refine (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).2
    (GlobalTheory.HeckeParts.isMultMap_heckeOn hT' (fun γ hγ => (hrep.1 γ hγ).1) ?_)
  intro w κ hκ g
  have hκ' : κ ∈ levW R i := hκ
  rw [hchi κ hκ', one_mul]
  show ∑ δ ∈ C, Tm w (g * κ * δ) = ∑ δ ∈ C, Tm w (g * δ)
  have hF : ∀ x, ∀ c ∈ levW R i, Tm w (x * c) = Tm w x := fun x c hc => by
    rw [hT'.lev w c hc x, hchi c hc, one_mul]
  obtain ⟨hs, ht⟩ := hcmp1 v f hf κ
  have hkv : cmp v κ ∈ levW R i := ((hcmp2 κ (hle hκ')).1.1 hκ') v
  have hk' : κ * (cmp v κ)⁻¹ ∈ levW R i := mul_mem hκ' (inv_mem hkv)
  calc ∑ δ ∈ C, Tm w (g * κ * δ) = ∑ δ ∈ C, Tm w (g * (κ * (cmp v κ)⁻¹) * (cmp v κ * δ)) :=
        Finset.sum_congr rfl fun δ _ => by group
    _ = ∑ δ ∈ C, Tm w (g * (κ * (cmp v κ)⁻¹) * δ) :=
        sum_mul_left_eq (levW R i ⊓ suppSub (Wc D i) f) α C (fun γ hγ => (hrep.1 γ hγ).2)
          (fun x hx => hrep.2 x hx) (fun x => Tm w (g * (κ * (cmp v κ)⁻¹) * x))
          (fun x c hc => by simp only [← mul_assoc]; exact hF _ c hc.1) (k₀ := cmp v κ) ⟨hkv, hs⟩
    _ = ∑ δ ∈ C, Tm w (g * δ) := Finset.sum_congr rfl fun δ hδ => by
        rw [mul_assoc, ← comm_of_suppF_trivAt (hC δ hδ) ht, ← mul_assoc, hF _ _ hk']

end GlobalTheory.LocalHeckeLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RallisInnerProductKernelIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.RawLift

theorem rallis_kernel_step : ∀ D : D7, KerAbs D → SWPair D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (θ : InfFam D), IsInfFam θ → ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ → (∀ h, IntegrableOn (fun g => star (thetaKO om h g f₁) * φ₁ g) 𝓖 νW) ∧ IntegrableOn (fun h => star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h) 𝓗 νV ∧ ∫ h in 𝓗, star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h ∂νV = ((νV 𝓗).toReal : ℂ) * ∫ p in 𝓖 ×ˢ 𝓖, star (φ₁ p.1) * φ₂ p.2 * ∑' Y : Lag W, lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂) ∂(νW.prod νW) := by
  intro D hKer hSW ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ hφ₁ hc₁ hφ₂ hc₂
  obtain ⟨lcV, scV, t2V⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V
  obtain ⟨lcW, scW, t2W⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D W
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : BorelSpace (GA D W) := ⟨rfl⟩
  haveI := hS.haarV
  haveI := hS.haarW
  obtain ⟨hfin, hK⟩ := hKer ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS θ hθ
  obtain ⟨B₁, hB₁⟩ := hK f₁ hf₁ φ₁ hφ₁ hc₁
  obtain ⟨B₂, hB₂⟩ := hK f₂ hf₂ φ₂ hφ₂ hc₂
  haveI : IsFiniteMeasure (νV.restrict 𝓗) := isFiniteMeasure_restrict.2 hfin
  have hk : ∀ f, IsThetaFunO ψ V W f → Continuous fun p : GA D V × GA D W => thetaKO om p.1 p.2 f :=
    fun f hf => hS.weil.om_cont f hf 0
  set μG := νW.restrict 𝓖 with hμG
  set μH := νV.restrict 𝓗 with hμH
  set F : GA D V → GA D W × GA D W → ℂ := fun h p =>
    thetaKO om h p.1 f₁ * star (φ₁ p.1) * (star (thetaKO om h p.2 f₂) * φ₂ p.2) with hF
  have hFc : Continuous (Function.uncurry F) := by
    have a1 : Continuous fun q : GA D V × (GA D W × GA D W) => thetaKO om q.1 q.2.1 f₁ :=
      (hk f₁ hf₁).comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    have a2 : Continuous fun q : GA D V × (GA D W × GA D W) => thetaKO om q.1 q.2.2 f₂ :=
      (hk f₂ hf₂).comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
    have b1 : Continuous fun q : GA D V × (GA D W × GA D W) => φ₁ q.2.1 :=
      hφ₁.cont.comp (continuous_fst.comp continuous_snd)
    have b2 : Continuous fun q : GA D V × (GA D W × GA D W) => φ₂ q.2.2 :=
      hφ₂.cont.comp (continuous_snd.comp continuous_snd)
    exact (a1.mul b1.star).mul (a2.star.mul b2)
  have hFm : AEStronglyMeasurable (Function.uncurry F) (μH.prod (μG.prod μG)) := hFc.aestronglyMeasurable
  have hI1 : ∀ h, Integrable (fun g => thetaKO om h g f₁ * star (φ₁ g)) μG := by
    intro h
    refine ((hB₁ h).1.norm).mono' (((hk f₁ hf₁).comp (continuous_const.prodMk continuous_id)).mul
      hφ₁.cont.star).aestronglyMeasurable (ae_of_all _ fun g => ?_)
    simp [norm_mul]
  have hI2 : ∀ h, Integrable (fun g => star (thetaKO om h g f₂) * φ₂ g) μG := fun h => (hB₂ h).1
  have hFh : ∀ h, star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h = ∫ p, F h p ∂(μG.prod μG) := by
    intro h
    rw [integral_prod_mul (fun g => thetaKO om h g f₁ * star (φ₁ g)) (fun g => star (thetaKO om h g f₂) * φ₂ g)]
    unfold upLift
    congr 1
    rw [← hμG]
    show (starRingEnd ℂ) _ = _
    rw [← integral_conj]
    congr 1
    funext g
    simp [Complex.star_def]
  have hB₁0 : 0 ≤ B₁ := le_trans (integral_nonneg fun g => by positivity) ((hB₁ 1).2)
  have hB₂0 : 0 ≤ B₂ := le_trans (integral_nonneg fun g => by positivity) ((hB₂ 1).2)
  have hnorm : ∀ h, ∫ p, ‖F h p‖ ∂(μG.prod μG) =
      (∫ g, ‖thetaKO om h g f₁‖ * ‖φ₁ g‖ ∂μG) * ∫ g, ‖thetaKO om h g f₂‖ * ‖φ₂ g‖ ∂μG := by
    intro h
    rw [← integral_prod_mul (fun g => ‖thetaKO om h g f₁‖ * ‖φ₁ g‖) (fun g => ‖thetaKO om h g f₂‖ * ‖φ₂ g‖)]
    congr 1
    funext p
    simp [hF, norm_mul]
  have hInt : Integrable (Function.uncurry F) (μH.prod (μG.prod μG)) := by
    rw [integrable_prod_iff hFm]
    refine ⟨ae_of_all _ fun h => (hI1 h).mul_prod (hI2 h), ?_⟩
    refine (integrable_const (B₁ * B₂)).mono' hFm.norm.integral_prod_right' (ae_of_all _ fun h => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [hnorm h, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul (hB₁ h).2 (hB₂ h).2 (integral_nonneg fun g => by positivity) hB₁0
  have hsplit : ∀ (h : GA D V) (g : GA D W) (f : WO V W → ℂ), thetaKO om h g f = thetaKO om h 1 (om (1, g) f) := by
    intro h g f
    unfold thetaKO
    rw [show ((h, g) : GA D V × GA D W) = (h, 1) * (1, g) by simp, map_mul, Module.End.mul_apply]
  have hup : (fun h => star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h) =
      fun h => ∫ p, F h p ∂(μG.prod μG) := funext hFh
  refine ⟨fun h => (hB₁ h).1, ?_, ?_⟩
  · show Integrable _ μH
    rw [hup]
    exact hInt.integral_prod_left
  · have hpt : ∀ p : GA D W × GA D W, ∫ h, F h p ∂μH = ((νV 𝓗).toReal : ℂ) * (star (φ₁ p.1) * φ₂ p.2 *
        ∑' Y : Lag W, lagTerm μ 𝓕 (fr Y) (om (1, p.1) f₁) (om (1, p.2) f₂)) := by
      intro p
      have hsw := hSW ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr hS (om (1, p.1) f₁) (om (1, p.2) f₂)
        (hS.weil.om_pres _ _ hf₁) (hS.weil.om_pres _ _ hf₂)
      have he := hsw.tsum_eq
      rw [← hμH, tsum_mul_left] at he
      have hfun : (fun h => F h p) = fun h => (star (φ₁ p.1) * φ₂ p.2) *
          (thetaKO om h 1 (om (1, p.1) f₁) * star (thetaKO om h 1 (om (1, p.2) f₂))) := by
        funext h
        simp only [hF]
        rw [hsplit h p.1 f₁, hsplit h p.2 f₂]
        ring
      rw [hfun, integral_const_mul, ← he]
      ring
    show ∫ h, star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h ∂μH = _
    rw [hup, integral_integral_swap hInt, ← Measure.prod_restrict, ← hμG, ← integral_const_mul]
    congr 1
    funext p
    rw [hpt p]

end GlobalTheory.RawLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermStronglyMeasurable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

open scoped GlobalTheory.GaugeEx

namespace GlobalTheory.RallisMeas

variable {D : D7}

theorem borelSpace_WO (V W : HSp D) : BorelSpace (WO V W) := ⟨rfl⟩

theorem secondCountable_WO (V W : HSp D) : SecondCountableTopology (WO V W) :=
  inferInstanceAs (SecondCountableTopology (Fin W.rank → Fin V.rank → AE D))

theorem measurable_om_uncurry {ψ : AddChar (AF D.host.F) ℂ} {V W : HSp D} {χV χW : (AE D)ˣ →* Circle}
    {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} (hw : IsWeilDatumO ψ V W χV χW om)
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    Measurable (fun q : GA D W × WO V W => om (1, q.1) f q.2) := by
  have := borelSpace_WO V W
  have := secondCountable_WO V W
  have h := measurable_uncurry_of_continuous_of_measurable (ι := GA D W) (α := WO V W) (β := ℂ)
    (u := fun g w => om (1, g) f w)
    (fun w => (hw.om_cont f hf w).comp (Continuous.prodMk continuous_const continuous_id))
    (fun g => (hw.om_pres (1, g) f hf).cont.measurable)
  exact h

theorem lagTerm_stronglyMeasurable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsWeilDatumO ψ V W χV χW om → IsCovolOne (ratL W V) μ 𝓕 → ∀ (f₁ f₂ : WO V W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E, StronglyMeasurable (fun p : GA D W × GA D W => lagTerm μ 𝓕 C (om (1, p.1) f₁) (om (1, p.2) f₂)) := by
  intro D ψ V W χV χW om μ 𝓕 hw hμ f₁ f₂ hf₁ hf₂ C
  have := borelSpace_WO V W
  have := secondCountable_WO V W
  have hfin : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 (by rw [hμ.2.2]; simp)
  have hsf : SFinite (μ.restrict 𝓕) := @instSFiniteOfSigmaFinite _ _ _ (@IsFiniteMeasure.toSigmaFinite _ _ _ hfin)
  have c1 : Continuous (fun u : WO V W => ratMul C.1 u) := by unfold ratMul; fun_prop
  have c2 : Continuous (fun u : WO V W => ratMul C.2 u) := by unfold ratMul; fun_prop
  have m1 : Measurable (fun x : (GA D W × GA D W) × WO V W => om (1, x.1.1) f₁ (ratMul C.1 x.2)) :=
    (measurable_om_uncurry hw hf₁).comp (measurable_fst.fst.prodMk (c1.measurable.comp measurable_snd))
  have m2 : Measurable (fun x : (GA D W × GA D W) × WO V W => om (1, x.1.2) f₂ (ratMul C.2 x.2)) :=
    (measurable_om_uncurry hw hf₂).comp (measurable_fst.snd.prodMk (c2.measurable.comp measurable_snd))
  have hG : Measurable (fun x : (GA D W × GA D W) × WO V W =>
      om (1, x.1.1) f₁ (ratMul C.1 x.2) * star (om (1, x.1.2) f₂ (ratMul C.2 x.2))) :=
    m1.mul (continuous_star.measurable.comp m2)
  exact hG.stronglyMeasurable.integral_prod_right' (ν := μ.restrict 𝓕)

end GlobalTheory.RallisMeas

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanPOfGiven
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.LiftRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem lowTNZ_holds {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) :
    Formalism.IndefR.Eqv.KerDiag.LowTNZ R := by
  intro i τ
  obtain ⟨w, hw, h0⟩ := (Submodule.ne_bot_iff _).1 (GlobalTheory.LowTypeRestriction.lowT_ne_bot (R.MW i (sg0 D A)) τ)
  exact ⟨⟨w, hw⟩, fun h => h0 (Subtype.ext h)⟩

theorem spanP_of_given : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    GlobalTheory.LiftRows.Given R F → Formalism.IndefR.Eqv.Act.SpanP R :=
  fun R _ _ => Formalism.IndefR.Eqv.KerDiag.spanP_of_lowTNZ R (lowTNZ_holds R)

end GlobalTheory.LiftRows

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumSegmentsLanglands
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

noncomputable section

namespace GlobalTheory.NuShift

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem lpChar_lpTw (x y : WD h) (s : ℝ) : (x.lpTw s).lpChar y = (x.lpChar y).lpTw s := by
  induction x using WD.ind with
  | hP n a =>
  induction y using WD.ind with
  | hP m b =>
  rw [WD.lpTw_mk, WD.lpChar_mk, WD.lpChar_mk, WD.lpTw_mk]
  refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => ?_⟩
  · simp only [WDRep.tensor_ρ, WDRep.tw_ρ, LinearEquiv.refl_apply, TensorProduct.map_smul_left]
  · rfl

theorem lpTw_lpZero (s : ℝ) : (WD.lpZero (h := h)).lpTw s = WD.lpZero (h := h) := by
  rw [WD.lpZero, WD.lpTw_mk]
  exact WD.sound ⟨.refl _ _, fun σ v => Subsingleton.elim _ _, fun v => Subsingleton.elim _ _⟩

theorem sumList_lpTw (l : List (WD h)) (s : ℝ) :
    sumList (l.map fun x => x.lpTw s) = (sumList l).lpTw s := by
  induction l with
  | nil => exact (lpTw_lpZero s).symm
  | cons x l ih =>
    show WD.lpSum _ (sumList _) = (WD.lpSum x (sumList l)).lpTw s
    rw [ih, WD.lpTw_sum]

end GlobalTheory.NuShift

namespace GlobalTheory

open GlobalTheory.NuShift

theorem lpSum_segments_nu : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)),
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    ∀ (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRec h rc →
    ∀ (l : List (Segment (w.adicCompletion E))) (c : ℝ),
      sumList ((l.map fun Γ => Γ.nu (c : ℂ)).map fun Δ =>
          ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len)) =
        (sumList (l.map fun Δ =>
          ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len))).lpTw c := by
  intro E Ω _ _ _ _ _ A w
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  intro h rc hrc l c
  obtain ⟨a, ha, ε, -, L⟩ := hrc
  rw [← sumList_lpTw, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun Γ _ => ?_
  show ((rc (Γ.first.nu (c : ℂ))).lpTw _).lpChar _ = _
  rw [L.nu_eq, WD.lpTw_add, add_comm, ← WD.lpTw_add, lpChar_lpTw]
  rfl

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaPairingInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.WeilPairing


set_option maxHeartbeats 1000000 in
theorem thetaInner_weilRep : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsWeilDatumO ψ V W χV χW om → IsCovolOne (ratL W V) μ 𝓕 → ∀ (p : GA D V × GA D W) (a b : WO V W → ℂ), IsThetaFunO ψ V W a → IsThetaFunO ψ V W b → thetaIP μ 𝓕 (om p a) (om p b) = thetaIP μ 𝓕 a b := by
  intro D ψ V W χV χW om μ 𝓕 hom hc p a b ha hb
  have h := GlobalTheory.WeilInner.om_inner D ψ V W χV χW om hom μ 𝓕 hc p b a hb ha
  have e : ∀ (f g : WO V W → ℂ), thetaIP μ 𝓕 f g = ∫ w in 𝓕, g w * (starRingEnd ℂ) (f w) ∂μ := fun f g => by
    unfold thetaIP
    congr 1
    funext w
    exact mul_comm _ _
  rw [e, e]
  exact h

end GlobalTheory.WeilPairing
end

