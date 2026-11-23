module

public import Mathlib
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0004
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0008
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ProjFacts
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0005
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0006
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0015
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1455
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.Bundle0003

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.DiagonalLagrangianIntegralSiegelParabolicTransfoAlt
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.PhaseFourierInjectivity

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation PositivityTheory.ThKW.LagrangianIntegralFactorisation GlobalTheory.ThetaTransform

theorem coef : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
    ∃ (μW : Measure (WOF F E nS (nT + nT))) (𝓕W : Set (WOF F E nS (nT + nT))) (κ : ℝ), μW.IsAddHaarMeasure ∧
      IsAddFundamentalDomain (ratLF F E nS (nT + nT)) 𝓕W μW ∧ 0 < κ ∧
      ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
        Continuous (nrm σ JS JT ξ₀ B.ψ ν 𝓕 f) ∧ Integrable (nrm σ JS JT ξ₀ B.ψ ν 𝓕 f) ν ∧
        ∀ y : WOF F E nS nT,
          ∫ w in 𝓕W, heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (dC (AF F ⊗[F] E) nT * y) f w * starRingEnd ℂ (f w) ∂μW =
            (κ : ℂ) * ∫ v, phase σ JS JT ξ₀ B.ψ y v * nrm σ JS JT ξ₀ B.ψ ν 𝓕 f v ∂ν := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσ ν 𝓕 hν h𝓕
  have hT' := GlobalTheory.WeilSchrodinger.DblTargetF.isHermND_dblG hT
  have hstd := GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB
  obtain ⟨N, α, β, e, hCe, he, hrat, hrat', hec, hes, hαc, hαs, hβc, hβs, hr1, hr2⟩ := PositivityTheory.ThKW.AdelicSchwartzProperties.coords hB hS hT hξ hσ
  obtain ⟨μN, μW, 𝓕W, c₁, hμN, hμW, h𝓕W, hc₁, hpar⟩ := PositivityTheory.ThKW.AdelicSchwartzProperties.parseval_pol hB N e hec hes hrat hrat'
  obtain ⟨c₀, hc₀, hlam⟩ := PositivityTheory.ThKW.AdelicSchwartzProperties.lam_formula hB JS JT ξ₀ ν 𝓕 hν h𝓕 N α β e hCe he hβc hβs hr1 hr2
  obtain ⟨c₂, hc₂, hmap, hint⟩ := PositivityTheory.ThKW.AdelicSchwartzProperties.map_haar α hαc hαs ν hν μN hμN
  have hn0 : 0 < ‖c₀‖ := norm_pos_iff.2 hc₀
  refine ⟨μW, 𝓕W, c₁ / (c₂ * ‖c₀‖ ^ 2), hμW, h𝓕W, by positivity, fun f hf => ?_⟩
  obtain ⟨Φ, hΦ, rfl⟩ := GlobalTheory.ThetaOntoF.exists_thV_eqF F E σ B hB nS (nT + nT) JS _ hS hT' ξ₀ hξ hσ hstd N e he hrat f hf
  obtain ⟨hΦc, hΦi, hΦm⟩ := PositivityTheory.ThKW.AdelicSchwartzProperties.schA_facts hB N μN hμN Φ hΦ
  have hnrm : nrm σ JS JT ξ₀ B.ψ ν 𝓕 (thV B.ψ Φ ∘ e) =
      fun v => ((‖c₀‖ ^ 2 : ℝ) : ℂ) * (Φ (α v) * starRingEnd ℂ (Φ (α v))) := by
    funext v
    unfold nrm
    rw [hlam Φ hΦ v, map_mul, Complex.ofReal_pow, ← Complex.mul_conj' c₀]
    ring
  have hph : ∀ y v, phase σ JS JT ξ₀ B.ψ y v = B.ψ (α v ⬝ᵥ β y) := by
    intro y v
    unfold phase
    rw [he]
    have h1 : e (dCd F JT * v) = (α v, 0) := by
      have := hCe 0 v
      rwa [Matrix.mul_zero, zero_add, map_zero] at this
    have h2 : e (dC (AF F ⊗[F] E) nT * y) = (0, β y) := by
      have := hCe y 0
      rwa [Matrix.mul_zero, add_zero, map_zero] at this
    rw [h1, h2]
    simp [symV]
  refine ⟨?_, ?_, fun y => ?_⟩
  · rw [hnrm]
    exact continuous_const.mul ((hΦc.comp hαc).mul (Complex.continuous_conj.comp (hΦc.comp hαc)))
  · rw [hnrm]
    exact ((hint _).2 hΦi).const_mul _
  · rw [PositivityTheory.ThKW.AdelicSchwartzProperties.heis_C hB JS JT ξ₀ N α β e hCe he Φ y]
    have hl : ∫ w in 𝓕W, (thV B.ψ (fun x => B.ψ (x ⬝ᵥ β y) * Φ x) ∘ e) w * starRingEnd ℂ ((thV B.ψ Φ ∘ e) w) ∂μW =
        (c₁ : ℂ) * ∫ x, B.ψ (x ⬝ᵥ β y) * Φ x * starRingEnd ℂ (Φ x) ∂μN :=
      hpar _ (hΦm (β y)) Φ hΦ
    rw [hl, hnrm]
    simp_rw [hph]
    have hr : ∫ v, B.ψ (α v ⬝ᵥ β y) * (((‖c₀‖ ^ 2 : ℝ) : ℂ) * (Φ (α v) * starRingEnd ℂ (Φ (α v)))) ∂ν =
        ((‖c₀‖ ^ 2 : ℝ) : ℂ) * ((c₂ : ℂ) * ∫ x, B.ψ (x ⬝ᵥ β y) * Φ x * starRingEnd ℂ (Φ x) ∂μN) := by
      rw [← hmap (fun x => B.ψ (x ⬝ᵥ β y) * Φ x * starRingEnd ℂ (Φ x)), ← integral_const_mul]
      congr 1
      funext v
      ring
    rw [hr]
    have hc2 : (c₂ : ℂ) ≠ 0 := by exact_mod_cast hc₂.ne'
    have hc0 : ((‖c₀‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hn0 2).ne'
    have hn' : ((‖c₀‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    push_cast
    field_simp

end PositivityTheory.ThKW.PhaseFourierInjectivity

end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ExistsForm
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.SplitLagrF

theorem exists_form : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)), ν.IsAddHaarMeasure →
        IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν →
      ∀ e, IsSplitIdemF σ e →
      ∀ f₀, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f₀ →
        GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC F E nT) f₀ ≠ 0 →
      ∃ ℓ : (WOF F E nS (nT + nT) → ℂ) →ₗ[ℂ] ℂ,
        (∀ u : WOF F E nS (nT + nT), (∀ i j, cAF σ e * u i j = u i j) →
          ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
            ℓ (heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ u f) = ℓ f) ∧
        (∃ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f ∧ ℓ f ≠ 0) ∧
        ∀ M : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E), IsUnit M.det → ∃ R : ℝ, 0 < R ∧
          ∀ (f f' : WOF F E nS (nT + nT) → ℂ) (k : ℂ),
            IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
            IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f' →
            (∀ y : WOF F E nS nT, (∀ i j, cAF σ e * y i j = y i j) →
              prof σ JS JT ξ₀ B.ψ ν 𝓕 f' y = k * prof σ JS JT ξ₀ B.ψ ν 𝓕 f (M * y)) →
            ℓ f' = (R : ℂ) * k * ℓ f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ ν 𝓕 hν h𝓕 e he f₀ hf₀ hne
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  letI : MeasurableSpace (GlobalTheory.SplitInvFormF.conjHalf σ e nS nT) := borel _
  haveI : BorelSpace (GlobalTheory.SplitInvFormF.conjHalf σ e nS nT) := ⟨rfl⟩
  haveI : LocallyCompactSpace (GlobalTheory.SplitInvFormF.conjHalf σ e nS nT) :=
    (isClosed_conjHalf e).isClosedEmbedding_subtypeVal.locallyCompactSpace
  let μ : Measure (GlobalTheory.SplitInvFormF.conjHalf σ e nS nT) := Measure.addHaar
  haveI : μ.IsAddHaarMeasure := inferInstanceAs (Measure.addHaar (G := GlobalTheory.SplitInvFormF.conjHalf σ e nS nT)).IsAddHaarMeasure
  have hth := GlobalTheory.HeisThetaF.isThetaFunOF_heisOF F E σ B hB nS (nT + nT) JS
    (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀
  let L : GlobalTheory.WeilPartsF.thetaSubF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ y : GlobalTheory.SplitInvFormF.conjHalf σ e nS nT, prof σ JS JT ξ₀ B.ψ ν 𝓕 f.1 y.1 ∂μ
      map_add' := fun f g => by
        rw [← integral_add (prof_integrable hB hS hT hξ hσξ hν h𝓕 he μ f.2)
          (prof_integrable hB hS hT hξ hσξ hν h𝓕 he μ g.2)]
        exact integral_congr_ae (Filter.Eventually.of_forall fun y => prof_add hB hν h𝓕 f.2 g.2 y.1)
      map_smul' := fun c f => by
        rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun y => prof_smul ν 𝓕 c f.1 y.1) }
  obtain ⟨ℓ, hℓ0⟩ := LinearMap.exists_extend L
  have hℓ : ∀ f, IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
      ℓ f = ∫ y : GlobalTheory.SplitInvFormF.conjHalf σ e nS nT, prof σ JS JT ξ₀ B.ψ ν 𝓕 f y.1 ∂μ :=
    fun f hf => LinearMap.congr_fun hℓ0 ⟨f, hf⟩
  refine ⟨ℓ, fun u hu f hf => ?_, ?_, fun M hM => ?_⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := exists_decomp (σ := σ) (e := e) hu
    rw [hℓ _ (hth _ _ hf), hℓ f hf,
      GlobalTheory.SplitVacF.heisOF_add_half he (mul_mem_conjHalf _ ha) (mul_mem_conjHalf _ hb),
      ← integral_add_right_eq_self (μ := μ)
        (fun y : GlobalTheory.SplitInvFormF.conjHalf σ e nS nT => prof σ JS JT ξ₀ B.ψ ν 𝓕 f y.1) ⟨b, hb⟩]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show _ = prof σ JS JT ξ₀ B.ψ ν 𝓕 f (y.1 + b)
    simp only
    rw [prof_heis_dC hB hS hT hξ hσξ hν h𝓕 (hth _ _ hf), GlobalTheory.SplitVacF.commF_half he y.2 (add_mem ha ha), one_mul,
      prof_heis_aC ν 𝓕 he f y.2 hb]
  · by_contra hall
    push Not at hall
    exact hne (lagrInt_eq_zero hB hS hT hξ hσξ hν h𝓕 he μ hf₀ fun u => by
      rw [← hℓ _ (hth u _ hf₀)]; exact hall _ (hth u _ hf₀))
  · obtain ⟨r, hr, hm⟩ := integral_mul_left e μ M hM
    refine ⟨r, hr, fun f f' k hf hf' hk => ?_⟩
    rw [hℓ f hf, hℓ f' hf', mul_comm (r : ℂ) k, mul_assoc, ← hm, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hk x.1 x.2)

end GlobalTheory.SplitLagrF

end
end

