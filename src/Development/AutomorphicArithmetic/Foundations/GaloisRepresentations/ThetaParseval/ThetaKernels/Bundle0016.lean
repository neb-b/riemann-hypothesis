module

public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0008
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0006
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SmulMemConjHalf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0007
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1439
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0009
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0008
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1396
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1247

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ParsevalRationalPairing
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.ParsevalPolarization
open GlobalTheory.ThetaTransform
theorem parseval_rational_pairing : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E}, _root_.UpperTheory.TP.W.GoodK σ B → ∀ (N : ℕ),
    letI : MeasurableSpace (Fin N → AF F) := borel _
    letI : MeasurableSpace (VA F N) := borel _
    ∀ (ν : Measure (VA F N)), ν.IsAddHaarMeasure → ∀ 𝓕 : Set (VA F N),
      IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N)) 𝓕 ν →
      ∃ (μ : Measure (Fin N → AF F)) (c : ℝ), μ.IsAddHaarMeasure ∧ 0 < c ∧
        ∀ Φ₁ ∈ schA F (Fin N), ∀ Φ₂ ∈ schA F (Fin N),
          ∫ w in 𝓕, thV B.ψ Φ₁ w * starRingEnd ℂ (thV B.ψ Φ₂ w) ∂ν =
            (c : ℂ) * ∫ x, Φ₁ x * starRingEnd ℂ (Φ₂ x) ∂μ := by
  intro F E _ _ _ _ _ σ B hB N
  letI mA : MeasurableSpace (Fin N → AF F) := borel _
  letI mV : MeasurableSpace (VA F N) := borel _
  intro ν hν 𝓕 h𝓕
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : BorelSpace (Fin N → AF F) := ⟨rfl⟩
  have hR : IsTotallyReal F := hB.cm.1
  have hψ : IsCharAF F B.ψ := (_root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B hB).1
  let μ : Measure (Fin N → AF F) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  obtain ⟨𝓕₁, h𝓕₁, h0, htop⟩ := _root_.GlobalTheory.RatVecDomain.exists_fundamentalDomain F (Fin N) μ hμ
  obtain ⟨c₁, hc0, hctop, hc⟩ := _root_.GlobalTheory.PeriodicIterated.lintegral_ratPair_fundamentalDomain_eq_iterated F (Fin N) μ hμ ν hν 𝓕 h𝓕 𝓕₁ h𝓕₁
  set K : ENNReal := c₁ * μ 𝓕₁ with hK
  have hK0 : K ≠ 0 := mul_ne_zero hc0 h0
  have hKt : K ≠ ⊤ := ENNReal.mul_ne_top hctop htop
  have hpar : ∀ Φ ∈ schA F (Fin N), ∫⁻ w in 𝓕, ‖thV B.ψ Φ w‖ₑ ^ 2 ∂ν = K * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
    intro Φ hΦ
    have hm := _root_.GlobalTheory.ThetaTransformMeas.main F B.ψ hψ (Fin N) Φ hΦ
    have hG : @Measurable _ _ (borel _) _ (fun w : (Fin N → AF F) × (Fin N → AF F) =>
        ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr B.ψ w Φ)‖ₑ ^ 2) := Measurable.pow_const (measurable_enorm.comp hm) 2
    show ∫⁻ w in 𝓕, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr B.ψ w Φ)‖ₑ ^ 2 ∂ν = _
    rw [hc _ hG (fun γ hγ w => by
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, _root_.GlobalTheory.ThetaRatInv.norm_thetaSum_schr_ratPair_add F B.ψ hψ (Fin N) Φ γ hγ w])]
    simp_rw [_root_.GlobalTheory.ThetaParsevalInner.lintegral_thetaSum_schr_sq F B.ψ hψ (Fin N) μ hμ 𝓕₁ h𝓕₁ htop Φ hΦ]
    rw [lintegral_const_mul' _ _ htop, _root_.GlobalTheory.ThetaUnfold.unfold F (Fin N) μ hμ 𝓕₁ h𝓕₁ Φ hΦ, hK, mul_assoc]
  have henorm : ∀ z : ℂ, ‖‖z‖ ^ 2‖ₑ = ‖z‖ₑ ^ 2 := fun z => by
    rw [Real.enorm_eq_ofReal (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have hΦint : ∀ Φ ∈ schA F (Fin N), Integrable (fun x => ‖Φ x‖ ^ 2) μ := fun Φ hΦ =>
    (GlobalTheory.WeilM.schA_memLp_two F (Fin N) μ hμ Φ hΦ).integrable_norm_pow two_ne_zero
  have hthint : ∀ Φ ∈ schA F (Fin N), Integrable (fun w => ‖thV B.ψ Φ w‖ ^ 2) (ν.restrict 𝓕) := by
    intro Φ hΦ
    have hm := _root_.GlobalTheory.ThetaTransformMeas.main F B.ψ hψ (Fin N) Φ hΦ
    refine ⟨((hm.norm.pow_const 2).aestronglyMeasurable), ?_⟩
    show ∫⁻ w in 𝓕, ‖‖thV B.ψ Φ w‖ ^ 2‖ₑ ∂ν < ⊤
    simp_rw [henorm]
    rw [hpar Φ hΦ]
    refine ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hKt) ?_
    have := (hΦint Φ hΦ).2
    unfold HasFiniteIntegral at this
    simp_rw [henorm] at this
    exact this
  have hreal : ∀ Φ ∈ schA F (Fin N), ∫ w in 𝓕, ‖thV B.ψ Φ w‖ ^ 2 ∂ν = K.toReal * ∫ x, ‖Φ x‖ ^ 2 ∂μ := by
    intro Φ hΦ
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _)
        (hthint Φ hΦ).aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _) (hΦint Φ hΦ).aestronglyMeasurable]
    have e1 : ∀ z : ℂ, ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ 2 := fun z => by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    simp_rw [e1]
    rw [hpar Φ hΦ, ENNReal.toReal_mul]
  refine ⟨μ, K.toReal, hμ, ENNReal.toReal_pos hK0 hKt, fun Φ₁ hΦ₁ Φ₂ hΦ₂ => ?_⟩
  have hmem : ∀ a : ℂ, Φ₁ + a • Φ₂ ∈ schA F (Fin N) := fun a => add_mem hΦ₁ (Submodule.smul_mem _ a hΦ₂)
  have hth : ∀ a : ℂ, thV B.ψ (Φ₁ + a • Φ₂) = fun w => thV B.ψ Φ₁ w + a * thV B.ψ Φ₂ w := by
    intro a
    rw [thV_add hR hψ (_root_.GlobalTheory.SchwartzDecay.decay_of_mem_schA F N Φ₁ hΦ₁) (GlobalTheory.SchwartzDecay.decay_smul a (_root_.GlobalTheory.SchwartzDecay.decay_of_mem_schA F N Φ₂ hΦ₂)),
      thV_smul]
    rfl
  have hfn : ∀ a : ℂ, (Φ₁ + a • Φ₂) = fun x => Φ₁ x + a * Φ₂ x := fun a => rfl
  refine polar μ (ν.restrict 𝓕) Φ₁ Φ₂ (thV B.ψ Φ₁) (thV B.ψ Φ₂) K.toReal (fun a => ?_) (fun a => ?_) (fun a => ?_)
  · have := hΦint _ (hmem a)
    rwa [hfn a] at this
  · have := hthint _ (hmem a)
    rwa [hth a] at this
  · have := hreal _ (hmem a)
    rwa [hth a, hfn a] at this
end PositivityTheory.ThKW.ParsevalPolarization
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ProfHeisLiftK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace GlobalTheory.SplitLagrF
open GlobalTheory.SplitInvFormF GlobalTheory.WeilSchrodinger.DblTargetF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
  {ψ : AddChar (AF F) ℂ}
variable {B : Base F E}
theorem prof_add_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) {ν : Measure (WOF F E nS nT)} {𝓕 : Set (WOF F E nS nT)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) {f g : WOF F E nS (nT + nT) → ℂ}
    (hf : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f) (hg : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ g) (y : WOF F E nS nT) :
    prof σ JS JT ξ₀ B.ψ ν 𝓕 (f + g) y = prof σ JS JT ξ₀ B.ψ ν 𝓕 f y + prof σ JS JT ξ₀ B.ψ ν 𝓕 g y := by
  unfold prof
  rw [GlobalTheory.WeilPartsF.heisOF_add]
  exact integral_add
    (integrableOn_dC hν h𝓕 (_root_.GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB _ _ JS _ ξ₀ (aC F E nT * y) f hf))
    (integrableOn_dC hν h𝓕 (_root_.GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB _ _ JS _ ξ₀ (aC F E nT * y) g hg))
theorem prof_heis_dC_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : ξ₀ ≠ 0) (hσξ : σ ξ₀ = -ξ₀)
    {ν : Measure (WOF F E nS nT)} {𝓕 : Set (WOF F E nS nT)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) {f : WOF F E nS (nT + nT) → ℂ}
    (hf : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f) (a y : WOF F E nS nT) :
    prof σ JS JT ξ₀ B.ψ ν 𝓕 (heisOF σ JS (dblG JT) ξ₀ B.ψ (dC F E nT * a) f) y =
      commF σ JS JT ξ₀ B.ψ y (a + a) * prof σ JS JT ξ₀ B.ψ ν 𝓕 f y := by
  unfold prof
  rw [heisOF_comm, lagrInt_smul, commF_aC_dC, _root_.GlobalTheory.SplitLagrF.lagrInt_heis_dC_k F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ ν 𝓕 hν h𝓕 _
    (_root_.GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB _ _ JS _ ξ₀ (aC F E nT * y) f hf)]
theorem prof_heis_lift_k (hB : _root_.UpperTheory.TP.W.GoodK σ B) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : ξ₀ ≠ 0) (hσξ : σ ξ₀ = -ξ₀)
    {ν : Measure (WOF F E nS nT)} {𝓕 : Set (WOF F E nS nT)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) {f : WOF F E nS (nT + nT) → ℂ}
    (hf : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f) (g y : WOF F E nS nT) :
    prof σ JS JT ξ₀ B.ψ ν 𝓕 (heisOF σ JS (dblG JT) ξ₀ B.ψ (dC F E nT * ((-hlf F E) • g : WOF F E nS nT)) f) y =
      commF σ JS JT ξ₀ B.ψ g y * prof σ JS JT ξ₀ B.ψ ν 𝓕 f y := by
  rw [_root_.GlobalTheory.SplitLagrF.prof_heis_dC_k hB hS hT hξ hσξ hν h𝓕 hf, neg_hlf_add, GlobalTheory.SplitVacF.commF_swap]
end GlobalTheory.SplitLagrF
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PsiHalfSympAddK
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny
noncomputable section
namespace Tw.VacCocycle
open _root_.GlobalTheory
section General
variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
end General
theorem psi_half_symp_add_k : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v, ∀ γ' ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v,
      B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
          (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) (γ + γ') (γ + γ')) =
        B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ) *
          B.ψ (⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ' γ') *
          B.ψ (-(⅟(2 : AF F) * GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1)
            (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ')) := by
  intro F E _ _ _ _ _ σ B hB n d X Y r s r' s' hX hY θ hθ v γ hγ γ' hγ'
  have hσ : ∀ x : E, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hc : ∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ z) = z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, hσ]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hi : ∀ e : E, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  have hsw := symp_swap (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) hc (JA := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (JB := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)
    (fun i j => by simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, hi, hX.herm])
    (fun i j => by simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.map_apply, hi, hY.skew, map_neg])
    (ξ := inclR (F := F) (AF F) (θ : E)) (by rw [hi, ← map_add (f := _), hθ, map_one]) γ γ'
  have h1 := _root_.Tw.LatVacArith.psi_symp_latAtV_k σ B X Y r s r' s' hB hX hY v θ 1
    (by rw [map_one]; exact one_mem _) γ hγ γ' hγ'
  have h2 := _root_.Tw.LatVacArith.psi_symp_latAtV_k σ B X Y r s r' s' hB hX hY v (-1) 1
    (by rw [map_one]; exact one_mem _) γ hγ γ' hγ'
  have hm : inclR (F := F) (AF F) ((-1 : 𝓞 E) : E) = -1 := by
    rw [show ((-1 : 𝓞 E) : E) = -1 by simp, map_neg, map_one]
  rw [hm] at h2
  rw [Tw.LatVacArith.symp_add_left, Tw.LatVacArith.symp_add_right, Tw.LatVacArith.symp_add_right, hsw,
    ← mul_one (_ * _ * _), ← h1, ← mul_one (_ * _ * _ * _), ← h2]
  simp only [← AddChar.map_add_eq_mul]
  congr 1
  have h : (⅟(2 : AF F)) * 2 = 1 := invOf_mul_self _
  generalize (⅟(2 : AF F)) = t at h ⊢
  linear_combination (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (inclR (F := F) (AF F) (θ : E))
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ' +
    GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J) γ γ') * h
end Tw.VacCocycle
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.PsiSymplOHFIotaVFK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
noncomputable section
namespace GlobalTheory.RealCharF
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem psi_symplOHF_iotaVF_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ u v : IxF F nS nT → ℂ, B.ψ (symplOHF σ JS JT ξ₀ (iotaVF ι u) (iotaVF ι v)) =
        Complex.exp (Real.pi * Complex.I * ((star v ⬝ᵥ HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) *ᵥ u).im : ℂ)) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ θ hθ ι hι u v
  have hσ := hB.cm
  haveI : IsTotallyReal F := hσ.1
  have hψ := _root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood_k F E σ B hB
  have hw : ∀ w : InfinitePlace F, w.embedding = (B.emb w).1.comp (algebraMap F E) := fun w => (B.emb w).2.symm
  set s := symplOHF σ JS JT ξ₀ (iotaVF ι u) (iotaVF ι v) with hs
  have hsnd : sndA F s = 0 :=
    GlobalTheory.HeisDerivCM.map_symplOHF_eq_zero (sndA F) σ JS JT ξ₀ _ _ (Or.inr (real_iotaVF hι v))
  have e1 : B.ψ s = psiInf F B.ψ (fstA F s) := by
    have hsplit : s = pairA F (fstA F s) 0 := Prod.ext rfl hsnd
    conv_lhs => rw [hsplit]
    rfl
  have hre : ∀ w : InfinitePlace F, ((B.emb w).1 ξ₀).re = 0 := by
    intro w
    have h1 := hσ.2.2.2 (B.emb w).1 ξ₀
    rw [hσξ, map_neg] at h1
    have h2 := congrArg Complex.re h1
    rw [Complex.neg_re, Complex.star_def, Complex.conj_re] at h2
    linarith
  rw [e1, hψ.2.2 θ hθ, trace_HMF]
  have e2 : ∑ w, θ w (fstA F s ⊗ₜ[F] (1 : E)) = ∑ w, ((((B.emb w).1 ξ₀) *
      ((JS.map (B.emb w).1)⁻¹ * (cpt v w)ᴴ * JT.map (B.emb w).1 * cpt u w).trace).re : ℂ) :=
    Finset.sum_congr rfl fun w _ => by
      rw [hs, theta_fstA_symplOHF hσ (hw w) (hθ w) JS JT ξ₀ (iotaVF ι u) (iotaVF ι v),
        theta_hOF hσ hw hθ hι JT hJS.2 u v]
  rw [e2]
  congr 1
  rw [Complex.im_sum]
  simp only [Complex.mul_re, hre, Complex.im_ofReal_mul, zero_mul, zero_sub]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring
end GlobalTheory.RealCharF
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RatK
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.PhaseFourierInjectivity
open PositivityTheory.ThKW.ModulusFactorDefinition
theorem rat_k : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ (χS : (AF F ⊗[F] E)ˣ →* Circle) (ωd : GAF σ JS × GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) →*
            Module.End ℂ (WOF F E nS (nT + nT) → ℂ)),
        IsWeilDatumOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)
            (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS 1 ωd →
      ∀ γ ∈ GQF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT), ∀ t : GL (Fin nT) (AF F ⊗[F] E),
        mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) γ * dC (AF F ⊗[F] E) nT = dC (AF F ⊗[F] E) nT * t.1 →
      ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
        GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) (ωd (1, γ) f) =
          GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT) f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ ν 𝓕 hν h𝓕 χS ωd hω γ hγ t ht f hf
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := _root_.GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  have : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  have : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have h0 : ∀ y : WOF F E nS (nT + nT), symplOHF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ 0 y = 0 := fun y => by
    simp [symplOHF, symplOF, hOF]
  have h1 : ∀ w : WOF F E nS nT, ωd (1, γ) f (dC (AF F ⊗[F] E) nT * w) = f (dC (AF F ⊗[F] E) nT * ((t⁻¹).1 * w)) := by
    intro w
    have hact : actOF σ JS _ 1 γ (dC (AF F ⊗[F] E) nT * ((t⁻¹).1 * w)) = dC (AF F ⊗[F] E) nT * w := by
      unfold actOF
      rw [inv_one, show mtF σ JS 1 = 1 from rfl, Matrix.mul_one, ← Matrix.mul_assoc, ht, Matrix.mul_assoc,
        ← Matrix.mul_assoc t.1, Units.mul_inv, Matrix.one_mul]
    have h2 := congrFun (hω.om_heis 1 γ (dC (AF F ⊗[F] E) nT * ((t⁻¹).1 * w)) f hf) 0
    rw [hω.om_aut 1 (one_mem _) γ hγ _ (_root_.GlobalTheory.HeisThetaF.isThetaFunOF_heisOF_k F E σ B hB _ _ JS _ ξ₀ _ f hf), hact] at h2
    simp only [heisOF, h0, AddChar.map_zero_eq_one, one_mul, zero_add] at h2
    exact h2.symm
  obtain ⟨g₀, -, hg⟩ := hγ
  have hg' : mtF σ _ γ = g₀.1.map (incAF F E) := (congrArg Units.val hg).symm
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : Matrix (Fin nT) (Fin nT) E, t.1 = incM F s₀ := by
    refine ⟨(g₀.1 * GlobalTheory.LagrThetaInv.dC E nT).submatrix (fun p => finSumFinEquiv (Sum.inl p)) id, ?_⟩
    have e : (g₀.1 * GlobalTheory.LagrThetaInv.dC E nT).map (incAF F E) = dC (AF F ⊗[F] E) nT * t.1 := by
      rw [Matrix.map_mul, ← hg', ← ht]
      congr 1
      have := GlobalTheory.LagrThetaInv.dC_mul_rat (F := F) (1 : Matrix (Fin nT) (Fin nT) E)
      rw [Matrix.mul_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at this
      exact this.symm
    ext i j
    rw [← GlobalTheory.LagrThetaInv.dC_mul_inl t.1, ← e]
    rfl
  have hd := GlobalTheory.DiagThetaRatF.det_ne_zero_of_unit t s₀ hs₀
  have hs₁ : (t⁻¹).1 = incM F s₀⁻¹ := by
    rw [Matrix.coe_units_inv]
    refine Matrix.inv_eq_right_inv ?_
    rw [hs₀]
    show s₀.map (inclR (F := F) (AF F)) * s₀⁻¹.map (inclR (F := F) (AF F)) = 1
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hd),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hm : ∀ (s : Matrix (Fin nT) (Fin nT) E) (x : WOF F E nS nT), x ∈ ratLF F E nS nT →
      (incM F s * x : Matrix (Fin nT) (Fin nS) (AF F ⊗[F] E)) ∈ ratLF F E nS nT := by
    rintro s _ ⟨y, rfl⟩
    refine ⟨s * y, ?_⟩
    show (s * y).map (incAF F E) = s.map (incAF F E) * y.map (incAF F E)
    exact Matrix.map_mul
  let e : WOF F E nS nT ≃+ WOF F E nS nT :=
    { toFun := fun w => (t⁻¹).1 * w
      invFun := fun w => t.1 * w
      left_inv := fun w => by simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
      right_inv := fun w => by simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
      map_add' := fun v w => Matrix.mul_add _ v w }
  unfold GlobalTheory.LagrTheta.lagrInt
  simp only [h1]
  exact GlobalTheory.DiagThetaRatF.setIntegral_comp_aut (ratLF F E nS nT) hK hKc ν h𝓕 e
    (continuous_const.matrix_mul continuous_id) (continuous_const.matrix_mul continuous_id)
    (fun x hx => by
      show (t⁻¹).1 * x ∈ _
      rw [hs₁]
      exact hm _ x hx)
    (fun x hx => by
      show t.1 * x ∈ _
      rw [hs₀]
      exact hm _ x hx)
    (fun w => f (dC (AF F ⊗[F] E) nT * w)) (periodic hf)
end PositivityTheory.ThKW.PhaseFourierInjectivity
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.RedWpAutRealB
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF
namespace PositivityTheory.ThKW
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
theorem det_mMF_B_k (C : _root_.PositivityTheory.ThKW.Ctx_k σ B JS JT ξ₀ θ ι) {g : GAF σ JS} {h : GAF σ JT} {a b}
    (ha : IsRatF σ JS g a) (hb : IsRatF σ JT h⁻¹ b) :
    (mMF σ JS JT θ (g⁻¹, h⁻¹)).det = ∏ v, tauB B v (b ⊗ₖ aᵀ).det ∧
      (mMF σ JS JT θ (g⁻¹, h⁻¹) - 1).det = ∏ v, tauB B v (b ⊗ₖ aᵀ - 1).det := by
  have e1 : ∀ w, compAtF θ w (mtF σ JT h⁻¹) = b.map (tauB B w) := fun w => by
    rw [show mtF σ JT h⁻¹ = b.map (incAF F E) from hb]
    ext i j
    exact PositivityTheory.ThKW.RealC.theta_inc (C.inf w) _
  have e2 : ∀ w, compAtF θ w (mtF σ JS g⁻¹⁻¹) = a.map (tauB B w) := fun w => by
    rw [inv_inv, show mtF σ JS g = a.map (incAF F E) from ha]
    ext i j
    exact PositivityTheory.ThKW.RealC.theta_inc (C.inf w) _
  have e3 : ∀ w, (b.map (tauB B w) ⊗ₖ (a.map (tauB B w))ᵀ) = (b ⊗ₖ aᵀ).map (tauB B w) := fun w => by
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Matrix.kroneckerMap_apply, Matrix.map_apply, Matrix.transpose_apply, map_mul]
  rw [mMF_apply]
  simp only [e1, e2]
  refine ⟨?_, ?_⟩
  · rw [GlobalTheory.RatAut.RealInt.det_blk]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [e3]
    exact (RingHom.map_det _ _).symm
  · rw [GlobalTheory.RatAut.RealInt.det_blk_sub_one]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [e3, RingHom.map_det, map_sub, map_one]
    rfl
end PositivityTheory.ThKW
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SchrodingerModelIsomorphism
section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodinger_model_isomorphism : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (N : ℕ) (e : Formalism.IndefR.DatumF.WOF F E nS nT ≃ₗ[AF F] GlobalTheory.ThetaTransform.VA F N),
        (∀ w w', Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ w w' = GlobalTheory.ThetaTransform.symV (e w) (e w')) →
        (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin N → F,
          e (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N),
          Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ (GlobalTheory.ThetaTransform.thV B.ψ Φ ∘ e) := by
  first | exact @_root_.GlobalTheory.ThetaTransformF.isThetaFunOF_thV_k | exact _root_.GlobalTheory.ThetaTransformF.isThetaFunOF_thV_k | (intros; apply _root_.GlobalTheory.ThetaTransformF.isThetaFunOF_thV_k <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SplitOrInertKStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
theorem _root_.GlobalTheory.T.nonempty_algHom_or_exists_inert_of_goodK : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    _root_.UpperTheory.TP.W.GoodK σ B → ∀ v : Pl F, Nonempty (E →ₐ[F] Fv F v) ∨ ∃ w : HeightOneSpectrum (𝓞 E), Formalism.UG.IsInertAt F E v w := by
  first | exact @_root_.GlobalTheory.KFinLoc.split_or_inert_k | exact _root_.GlobalTheory.KFinLoc.split_or_inert_k | (intros; apply _root_.GlobalTheory.KFinLoc.split_or_inert_k <;> assumption)
end
end

