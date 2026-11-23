module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0293
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0278
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0169
public import Formalism.LatticeTheta.ThetaShiftInversion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0184
public import Formalism.LatticeTheta.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeFractionalIdealRealLatticeImage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0223
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0294
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0129

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearMapFibreRankSplitCompSurjective
section
open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

namespace GlobalTheory.FibreRanks

theorem fibre_ranks : ∀ (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] (N : Type) [AddCommGroup N] [Module O N] (K : Type) [AddCommGroup K] [Module O K] [Module.Finite O M] [Module.Finite O N] (f : M →ₗ[O] N), (∀ (ρ : N →ₗ[O] M), (∀ m, ρ (f m) = m) → ∀ q, fibreRank f q = fibreDim M q) ∧ (∀ (g : N →ₗ[O] K) (q : PrimeSpectrum O), fibreRank g q = fibreDim N q → fibreRank (g ∘ₗ f) q = fibreRank f q) ∧ ((∀ q, fibreRank f q = fibreDim N q) → Function.Surjective f) ∧ (∀ [Module.Free O M] (q : PrimeSpectrum O), fibreDim M q = Module.finrank O M) := by
  intro O _ M _ _ N _ _ K _ _ _ _ f
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ρ hρ q
    have hinj : Function.Injective (f.baseChange q.asIdeal.ResidueField) := by
      apply Function.LeftInverse.injective (g := ρ.baseChange q.asIdeal.ResidueField)
      intro x
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
      have : ρ ∘ₗ f = LinearMap.id := LinearMap.ext hρ
      rw [this]
      simp
    exact LinearMap.finrank_range_of_inj hinj
  · intro g q hg
    have hker := LinearMap.finrank_range_add_finrank_ker (g.baseChange q.asIdeal.ResidueField)
    have h0 : Module.finrank q.asIdeal.ResidueField
        (LinearMap.ker (g.baseChange q.asIdeal.ResidueField)) = 0 := by
      unfold fibreRank fibreDim at hg
      omega
    have hinj : Function.Injective (g.baseChange q.asIdeal.ResidueField) := by
      rw [← LinearMap.ker_eq_bot]
      exact Submodule.finrank_eq_zero.mp h0
    unfold fibreRank
    rw [LinearMap.baseChange_comp, LinearMap.range_comp]
    exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm
  · intro h
    exact surjective_of_fibre_rank O M N f h
  · intro _ q
    haveI : Nontrivial O := by
      by_contra hn
      rw [not_nontrivial_iff_subsingleton] at hn
      exact q.isPrime.ne_top (Subsingleton.elim _ _)
    exact Module.finrank_baseChange

end GlobalTheory.FibreRanks
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralCutoffGramBoundMixedBlockTwoLtTop
section
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall

theorem lintegral_hB_one_two_lt_top : ∫⁻ w : Low 2 → ℂ, hB 1 w < ⊤ := by
  have hg : ∀ w : Low 2 → ℂ, gB 1 w = 1 := by
    intro w
    simp [gB, colGram, lminor]
  have hset : {w : Low 2 → ℂ | ∀ p : Low 2, (p.1.2 : ℕ) < 1 → 1 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1}
      = Metric.closedBall (0 : Low 2 → ℂ) 1 := by
    ext w
    simp only [Set.mem_setOf_eq, mem_closedBall_zero_iff]
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    constructor
    · intro h p
      have hp := p.2
      have h1 : (p.1.2 : ℕ) < p.1.1 := hp
      have h2 : (p.1.1 : ℕ) < 2 := p.1.1.isLt
      exact h p (by omega) (by omega)
    · intro h p _ _
      exact h p
  have hfun : hB 1 = Set.indicator (Metric.closedBall (0 : Low 2 → ℂ) 1) (fun _ => (1 : ℝ≥0∞)) := by
    funext w
    simp only [hB, hset, hg, ENNReal.ofReal_one]
  rw [hfun, lintegral_indicator Metric.isClosed_closedBall.measurableSet]
  simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, one_mul]
  exact measure_closedBall_lt_top

end GlobalTheory.IntBall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralFourSq
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp.Planch

variable {X : Type} [AddCommGroup X] [TopologicalSpace X]

theorem e_zero {e : X → X → ℂ} (he : IsPair e) (y : X) : e 0 y = 1 := by
  have h := he.add 0 0 y
  rw [add_zero] at h
  have hn : e 0 y ≠ 0 := by
    intro h0
    have := he.norm 0 y
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  exact mul_left_cancel₀ hn (h.symm.trans (mul_one _).symm)

theorem conj_e {e : X → X → ℂ} (he : IsPair e) (x y : X) : starRingEnd ℂ (e x y) = e (-x) y := by
  have hn : e x y ≠ 0 := by
    intro h0
    have := he.norm x y
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have h1 : e (-x) y * e x y = 1 := by rw [← he.add, neg_add_cancel, e_zero he]
  have h2 : starRingEnd ℂ (e x y) * e x y = 1 := by
    rw [Complex.conj_mul', he.norm]; simp
  exact mul_right_cancel₀ hn (h2.trans h1.symm)

theorem integral_four_mul (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (hG : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ) (he : IsPair e) (C : ℝ) (_hC : 0 < C)
    (hinv : ∀ φ ∈ SB X, ∀ x, four μ e (four μ e φ) x = (C : ℂ) * φ (-x)) (φ : X → ℂ) (hφ : φ ∈ SB X) :
    ∫ x, four μ e φ x * starRingEnd ℂ (four μ e φ x) ∂μ = (C : ℂ) * ∫ y, φ y * starRingEnd ℂ (φ y) ∂μ := by
  haveI := hG.grp; haveI := hG.t2; haveI := hG.lc; haveI := hG.sc
  set Φ := four μ e φ with hΦdef
  have hΦ : Φ ∈ SB X := _root_.GlobalTheory.KSp.FourMem.four_mem_SB X hG μ e he φ hφ
  have hec : Continuous (fun p : X × X => e p.1 p.2) := he.lc.continuous
  have hint : Integrable (Function.uncurry fun x y => e x y * φ y * starRingEnd ℂ (Φ x)) (μ.prod μ) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (hec.mul (hφ.1.continuous.comp continuous_snd)).mul
        ((Complex.continuous_conj.comp hΦ.1.continuous).comp continuous_fst)
    · apply HasCompactSupport.intro (hΦ.2.isCompact.prod hφ.2.isCompact)
      rintro ⟨x, y⟩ hxy
      simp only [Set.mem_prod, not_and_or] at hxy
      rcases hxy with h | h
      · simp [image_eq_zero_of_notMem_tsupport h]
      · simp [image_eq_zero_of_notMem_tsupport h]
  have hinner : ∀ y, ∫ x, e x y * starRingEnd ℂ (Φ x) ∂μ = (C : ℂ) * starRingEnd ℂ (φ y) := by
    intro y
    have h1 : ∀ x, e x y * starRingEnd ℂ (Φ x) = starRingEnd ℂ (e (-y) x * Φ x) := by
      intro x
      rw [map_mul, Planch.conj_e he, neg_neg, he.symm]
    simp_rw [h1]
    rw [integral_conj]
    have h2 := hinv φ hφ (-y)
    rw [neg_neg] at h2
    change starRingEnd ℂ (four μ e Φ (-y)) = _
    rw [h2, map_mul, Complex.conj_ofReal]
  calc ∫ x, Φ x * starRingEnd ℂ (Φ x) ∂μ
      = ∫ x, ∫ y, e x y * φ y * starRingEnd ℂ (Φ x) ∂μ ∂μ := by
        congr 1; ext x
        rw [integral_mul_const]
        rfl
    _ = ∫ y, ∫ x, e x y * φ y * starRingEnd ℂ (Φ x) ∂μ ∂μ := integral_integral_swap hint
    _ = ∫ y, φ y * ∫ x, e x y * starRingEnd ℂ (Φ x) ∂μ ∂μ := by
        congr 1; ext y
        rw [← integral_const_mul]
        congr 1; ext x; ring
    _ = (C : ℂ) * ∫ y, φ y * starRingEnd ℂ (φ y) ∂μ := by
        simp_rw [hinner]
        rw [← integral_const_mul]
        congr 1; ext y; ring

theorem lintegral_four_sq : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e → ∀ C : ℝ, 0 < C → (∀ φ ∈ SB X, ∀ x, four μ e (four μ e φ) x = (C : ℂ) * φ (-x)) → ∀ φ ∈ SB X, ∫⁻ x, ‖four μ e φ x‖ₑ ^ 2 ∂μ = ENNReal.ofReal C * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ := by
  intro X _ _ _ _ hG μ _ e he C hC hinv φ hφ
  haveI := hG.grp; haveI := hG.t2; haveI := hG.lc; haveI := hG.sc
  have hΦ : four μ e φ ∈ SB X := _root_.GlobalTheory.KSp.FourMem.four_mem_SB X hG μ e he φ hφ
  have hL : ∀ f ∈ SB X, ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂μ) := by
    intro f hf
    have h1 : Continuous f := hf.1.continuous
    have h2 : HasCompactSupport f := hf.2
    have h3 : HasCompactSupport (fun x => ‖f x‖ ^ 2) := by
      have := h2.norm
      exact this.mul_right (f' := fun x => ‖f x‖) |>.mono (fun x hx => by simpa [sq] using hx)
    have hi : Integrable (fun x => ‖f x‖ ^ 2) μ :=
      (h1.norm.pow 2).integrable_of_hasCompactSupport h3
    rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => by positivity)]
    congr 1; ext x
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  have hC' : ∀ f : X → ℂ, ∫ x, f x * starRingEnd ℂ (f x) ∂μ = ((∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    intro f
    rw [← integral_complex_ofReal]
    congr 1; ext x
    rw [Complex.mul_conj']
    push_cast; rfl
  have hk := integral_four_mul X hG μ e he C hC hinv φ hφ
  rw [hC', hC'] at hk
  have hk' : ∫ x, ‖four μ e φ x‖ ^ 2 ∂μ = C * ∫ x, ‖φ x‖ ^ 2 ∂μ := by exact_mod_cast hk
  rw [hL _ hΦ, hL _ hφ, hk', ENNReal.ofReal_mul hC.le]

end GlobalTheory.KSp.Planch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralUpdateSubShear
section
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory

theorem lintegral_update_sub_shear {ι : Type} [Fintype ι] [DecidableEq ι] (i : ι)
    (g : (ι → ℂ) → ℂ) (hg : Measurable g)
    (hgi : ∀ w v : ι → ℂ, (∀ j, j ≠ i → w j = v j) → g w = g v)
    (F : (ι → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ w, F (Function.update w i (w i - g w)) = ∫⁻ w, F w := by
  classical
  set e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℂ) (fun j => j ≠ i) with he
  have he_mp : MeasurePreserving e := volume_preserving_piEquivPiSubtypeProd (fun _ : ι => ℂ) _

  set c : ({j // j ≠ i} → ℂ) → ℂ := fun x => g (e.symm (x, 0)) with hc
  have hcm : Measurable c :=
    hg.comp (e.symm.measurable.comp (measurable_id.prodMk measurable_const))
  set S : ({j // j ≠ i} → ℂ) × ({j // ¬ j ≠ i} → ℂ) → ({j // j ≠ i} → ℂ) × ({j // ¬ j ≠ i} → ℂ) :=
    fun p => (p.1, p.2 + (fun _ => - c p.1)) with hS
  have hS_mp : MeasurePreserving S (volume.prod volume) (volume.prod volume) := by
    refine MeasurePreserving.skew_product (g := fun x y => y + (fun _ => - c x))
      (MeasurePreserving.id volume) ?_ ?_
    · exact measurable_snd.add (Measurable.of_eval fun _ => (hcm.comp measurable_fst).neg)
    · exact Filter.Eventually.of_forall fun x => map_add_right_eq_self _ _
  have hT : (fun w => Function.update w i (w i - g w)) = e.symm ∘ S ∘ e := by
    funext w
    have hgw : g w = c (e w).1 := by
      apply hgi
      intro j hj
      simp [hc, he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hj]
    ext k
    by_cases hk : k = i
    · subst hk
      simp [hS, he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hgw, sub_eq_add_neg]
    · simp [hS, he, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hk]
  have hmp : MeasurePreserving (e.symm ∘ S ∘ e) :=
    he_mp.symm.comp (hS_mp.comp he_mp)
  have h := hmp.lintegral_comp hF
  rw [← hT] at h
  exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LipschitzFormulaTotallyRealPoisson
section
noncomputable section
open NumberField nonZeroDivisors MeasureTheory
open scoped FourierTransform RealInnerProductSpace

namespace GlobalTheory.LipschitzTR
open GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent

variable {F : Type} [Field F] [NumberField F]

theorem latOf_discrete [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F) :
    DiscreteTopology (latOf N) := _root_.GlobalTheory.LipschitzTR.discrete_latOf F N

theorem latOf_isZLattice [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F) (hN : N ≠ 0)
    [DiscreteTopology (latOf N)] : IsZLattice ℝ (latOf N) := _root_.GlobalTheory.LipschitzTR.isZLattice_latOf F N hN

theorem covolume_latOf [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F) (hN : N ≠ 0)
    [DiscreteTopology (latOf N)] [IsZLattice ℝ (latOf N)] :
    ZLattice.covolume (latOf N) = covol N := _root_.GlobalTheory.LipschitzCovol.covolume_latOf F N hN

theorem dual_latOf [IsTotallyReal F] (N : FractionalIdeal (𝓞 F)⁰ F) (hN : N ≠ 0) :
    Formalism.H.dual (latOf N) = latOf (FractionalIdeal.dual ℤ ℚ N) := GlobalTheory.T.dual_latticeImage_eq_latticeImage_traceDual F N hN

theorem fourier_lipschitzOneVariableKernel (k : ℕ) (hk : 2 ≤ k) (he : Even k) (w : ℂ) (hw : w.im ≠ 0) (x : ℝ) :
    𝓕 (phi1 k w) x = ((k - 1).factorial : ℂ) / (2 * Real.pi * Complex.I) ^ k * (w - x) ^ (-(k : ℤ)) :=
  _root_.GlobalTheory.LipschitzTR.fourier_phi1_eq_factorial_mul_zpow k hk he w hw x

theorem Phi_cont_decay (k : ℕ) (hk : 2 ≤ k) (z : (F →+* ℝ) → ℂ) (hz : ∀ τ, (z τ).im ≠ 0) :
    Continuous (Phi k z) ∧
      ∀ b : ℝ, Phi k z =O[Filter.cocompact (RSp F)] fun v => ‖v‖ ^ (-b) := GlobalTheory.T.continuous_isBigO_rpow_lipschitzProductKernel F k hk z hz

theorem summable_lhsTerm [IsTotallyReal F] (M : FractionalIdeal (𝓞 F)⁰ F) (hM : M ≠ 0) (k : ℕ)
    (hk : 2 ≤ k) (z : (F →+* ℝ) → ℂ) (hz : ∀ τ, (z τ).im ≠ 0) :
    Summable (fun a : (M : Set F) => lhsTerm k z a) := _root_.GlobalTheory.LipschitzTR.summable_lhsTerm_ideal F M hM k hk z hz

theorem fourier_prod_coord (ι : Type) [Fintype ι] (f : ι → ℝ → ℂ) (x : EuclideanSpace ℝ ι) :
    𝓕 (fun ξ : EuclideanSpace ℝ ι => ∏ i, f i (ξ i)) x = ∏ i, 𝓕 (f i) (x i) := by
  simp only [Real.fourier_eq', Real.fourier_real_eq]
  rw [← integral_fintype_prod_volume_eq_prod,
    ← (PiLp.volume_preserving_toLp ι).integral_comp (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [smul_eq_mul]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, PiLp.inner_apply, Finset.mul_sum, Complex.ofReal_sum,
    Finset.sum_mul]

theorem remb_injective [IsTotallyReal F] : Function.Injective (remb F) := by
  intro a b h
  have hne : Nonempty (F →+* ℝ) := by
    rw [← Fintype.card_pos_iff, card_realEmb]
    exact Module.finrank_pos
  have h1 := congrArg (fun v : RSp F => v (Classical.choice hne)) h
  simp only [remb_apply] at h1
  exact (Classical.choice hne).injective h1

theorem Phi_remb (k : ℕ) (z : (F →+* ℝ) → ℂ) (ν : F) :
    Phi k z (remb F ν) =
      if ∀ τ : F →+* ℝ, 0 < (SignType.sign (z τ).im : ℝ) * τ ν then rhsTerm k z ν else 0 := by
  unfold Phi
  by_cases hc : ∀ τ : F →+* ℝ, 0 < (SignType.sign (z τ).im : ℝ) * τ ν
  · rw [if_pos hc, Finset.prod_congr rfl fun τ _ => by rw [remb_apply, phi1, if_pos (hc τ)],
      Finset.prod_mul_distrib, ← Complex.exp_sum, rhsTerm, Finset.abs_prod, ← Finset.prod_pow, Complex.ofReal_prod]
    congr 2
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  · rw [if_neg hc]
    push Not at hc
    obtain ⟨τ, hτ⟩ := hc
    exact Finset.prod_eq_zero (Finset.mem_univ τ) (by rw [remb_apply, phi1, if_neg (not_lt.2 hτ)])

theorem fourier_Phi (k : ℕ) (hk : 2 ≤ k) (he : Even k) (z : (F →+* ℝ) → ℂ) (hz : ∀ τ, (z τ).im ≠ 0)
    (a : F) : 𝓕 (Phi k z) (remb F a) =
      (((k - 1).factorial : ℂ) / (2 * Real.pi * Complex.I) ^ k) ^ Fintype.card (F →+* ℝ) *
        lhsTerm k z (-a) := by
  rw [show Phi k z = fun ξ : RSp F => ∏ τ, phi1 k (z τ) (ξ τ) from rfl, fourier_prod_coord]
  simp only [remb_apply]
  have h := fun τ : F →+* ℝ => fourier_lipschitzOneVariableKernel k hk he (z τ) (hz τ) (τ a)
  simp only [h]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, lhsTerm, Finset.prod_zpow]
  simp [map_neg, sub_eq_add_neg]

theorem lipschitz : Lipschitz := by
  intro F _ _ _ M hM k hk he z hz
  haveI : DiscreteTopology (latOf M) := latOf_discrete M
  haveI : IsZLattice ℝ (latOf M) := latOf_isZLattice M hM
  set L := Formalism.H.dual (latOf M) with hL
  obtain ⟨h1, h2⟩ := Formalism.H.dualIsLattice (RSp F) (latOf M)
  haveI : DiscreteTopology L := h1
  haveI : IsZLattice ℝ L := h2
  have hdd : Formalism.H.dual L = latOf M := Formalism.H.dualDual (RSp F) (latOf M)
  have hcov : ZLattice.covolume L = (covol M)⁻¹ := by
    rw [Formalism.H.covolumeDual (RSp F) (latOf M), covolume_latOf M hM]
  have hLmem : ∀ x, x ∈ L ↔ ∃ ν ∈ FractionalIdeal.dual ℤ ℚ M, remb F ν = x := by
    intro x; rw [hL, dual_latOf M hM]; exact mem_latOf _ x
  have hDmem : ∀ x, x ∈ Formalism.H.dual L ↔ ∃ a ∈ M, remb F a = x := by
    intro x; rw [hdd]; exact mem_latOf _ x
  obtain ⟨hcont, hdec⟩ := Phi_cont_decay k hk z hz
  obtain ⟨hint, hsumx, hGc, hGper⟩ := Formalism.H.poisson_periodization (RSp F) L (Phi k z) hcont
    ((Module.finrank ℝ (RSp F) : ℝ) + 1) (by linarith) (hdec _)
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  have hD := ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ L) (volume : Measure (RSp F))
  set D := ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)
  have hcoef : ∀ μ : Formalism.H.dual L, (∫ y in D, (∑' l : L, Phi k z ((l : RSp F) + y)) *
      Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : RSp F), y⟫ : ℝ)))) = 𝓕 (Phi k z) μ :=
    fun μ => Formalism.H.unfolding_fourier_coefficient (RSp F) L (Phi k z) hint D hD μ μ.2

  let eM : (M : Set F) ≃ Formalism.H.dual L := Equiv.ofBijective
    (fun a => ⟨remb F a, (hDmem _).2 ⟨a, a.2, rfl⟩⟩)
    ⟨fun a b h => Subtype.ext (remb_injective (congrArg Subtype.val h)), fun μ => by
      obtain ⟨a, ha, h⟩ := (hDmem μ).1 μ.2
      exact ⟨⟨a, ha⟩, Subtype.ext h⟩⟩
  let eD : (FractionalIdeal.dual ℤ ℚ M : Set F) ≃ L := Equiv.ofBijective
    (fun a => ⟨remb F a, (hLmem _).2 ⟨a, a.2, rfl⟩⟩)
    ⟨fun a b h => Subtype.ext (remb_injective (congrArg Subtype.val h)), fun μ => by
      obtain ⟨a, ha, h⟩ := (hLmem μ).1 μ.2
      exact ⟨⟨a, ha⟩, Subtype.ext h⟩⟩
  set cst : ℂ := (((k - 1).factorial : ℂ) / (2 * Real.pi * Complex.I) ^ k) ^ Fintype.card (F →+* ℝ)
  have hsL := summable_lhsTerm M hM k hk z hz
  let eN : (M : Set F) ≃ (M : Set F) :=
    ⟨fun a => ⟨-a, (M : Submodule (𝓞 F) F).neg_mem a.2⟩, fun a => ⟨-a, (M : Submodule (𝓞 F) F).neg_mem a.2⟩, fun a => by simp, fun a => by simp⟩
  have hsLn : Summable (fun a : (M : Set F) => lhsTerm k z (-(a : F))) :=
    (eN.summable_iff (f := fun a : (M : Set F) => lhsTerm k z a)).2 hsL
  have hFM : ∀ a : (M : Set F), 𝓕 (Phi k z) (eM a) = cst * lhsTerm k z (-(a : F)) :=
    fun a => fourier_Phi k hk he z hz a
  have hsumc : Summable (fun μ : Formalism.H.dual L => ∫ y in D, (∑' l : L, Phi k z ((l : RSp F) + y)) *
      Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : RSp F), y⟫ : ℝ)))) := by
    simp only [hcoef]
    rw [← eM.summable_iff]
    exact (hsLn.mul_left cst).congr fun a => (hFM a).symm
  have H4 := Formalism.H.lattice_fourier_series (RSp F) L (fun x => ∑' l : L, Phi k z ((l : RSp F) + x))
    hGc hGper D hD hsumc 0
  simp only [hcoef, inner_zero_right, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one,
    add_zero] at H4
  rw [← eM.hasSum_iff] at H4
  have H4' : HasSum (fun a : (M : Set F) => (covol M : ℂ) * cst * lhsTerm k z (-(a : F)))
      (∑' l : L, Phi k z (l : RSp F)) := by
    refine H4.congr_fun fun a => ?_
    simp only [Function.comp_apply, hFM, hcov, Complex.ofReal_inv, inv_inv]
    ring
  have hs0 : Summable (fun l : L => Phi k z (l : RSp F)) := by
    simpa using hsumx 0
  set g : F → ℂ := fun ν =>
    if ∀ τ : F →+* ℝ, 0 < (SignType.sign (z τ).im : ℝ) * τ ν then rhsTerm k z ν else 0 with hg
  have hind : (FractionalIdeal.dual ℤ ℚ M : Set F).indicator g = (dualCone M z).indicator (rhsTerm k z) := by
    funext ν
    by_cases hν : ν ∈ (FractionalIdeal.dual ℤ ℚ M : Set F)
    · have hν' : ν ∈ traceDual M := (mem_traceDual_iff hM ν).2 hν
      by_cases hc : ∀ τ : F →+* ℝ, 0 < (SignType.sign (z τ).im : ℝ) * τ ν
      · rw [Set.indicator_of_mem hν, Set.indicator_of_mem (show ν ∈ dualCone M z from ⟨hν', hc⟩), hg]
        simp [hc]
      · rw [Set.indicator_of_mem hν, Set.indicator_of_notMem (show ν ∉ dualCone M z from fun h => hc h.2), hg]
        simp [hc]
    · have hν' : ν ∉ dualCone M z := fun h => hν ((mem_traceDual_iff hM ν).1 h.1)
      rw [Set.indicator_of_notMem hν, Set.indicator_of_notMem hν']
  have hPg : ∀ ν : (FractionalIdeal.dual ℤ ℚ M : Set F), Phi k z (eD ν) = g ν := fun ν => Phi_remb k z ν
  have hsD : Summable (fun ν : (FractionalIdeal.dual ℤ ℚ M : Set F) => g ν) := by
    rw [← eD.summable_iff] at hs0
    exact hs0.congr fun ν => hPg ν
  have hsR : Summable (fun ν : dualCone M z => rhsTerm k z ν) := by
    have h3 := (summable_subtype_iff_indicator (s := (FractionalIdeal.dual ℤ ℚ M : Set F)) (f := g)).1 hsD
    rw [hind] at h3
    exact (summable_subtype_iff_indicator (s := dualCone M z) (f := rhsTerm k z)).2 h3
  have hR : ∑' l : L, Phi k z (l : RSp F) = ∑' ν : dualCone M z, rhsTerm k z ν := by
    rw [← eD.tsum_eq, tsum_subtype (dualCone M z) (rhsTerm k z), ← hind, ← tsum_subtype]
    exact tsum_congr fun ν => hPg ν
  have hLn : ∑' a : (M : Set F), lhsTerm k z (-(a : F)) = ∑' a : (M : Set F), lhsTerm k z a :=
    eN.tsum_eq (fun a : (M : Set F) => lhsTerm k z a)
  have hmain := H4'.tsum_eq
  rw [tsum_mul_left, hLn, hR] at hmain
  refine ⟨hsL, hsR, ?_⟩
  rw [← hmain]
  have hc0 : (covol M : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (covol_pos hM).ne'
  have hf0 : ((k - 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  simp only [lipConst, cst, card_realEmb, div_pow, pow_mul]
  field_simp

end GlobalTheory.LipschitzTR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyConstantSpecLocalRingConstBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem locallyConstant_spec_local_eq_closedPoint {R A : Type} [CommRing A] [IsLocalRing A]
    (f : LocallyConstant (Spec (CommRingCat.of A)) R) (x : Spec (CommRingCat.of A)) :
    f x = f (IsLocalRing.closedPoint A : PrimeSpectrum A) := by
  have hx : (x : PrimeSpectrum A) ⤳ IsLocalRing.closedPoint A :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (IsLocalRing.le_maximalIdeal (x : PrimeSpectrum A).isPrime.ne_top)
  have ho : IsOpen (f ⁻¹' {f (IsLocalRing.closedPoint A : PrimeSpectrum A)}) := f.isLocallyConstant _
  exact hx.mem_open ho rfl

theorem locallyConstant_spec_local_bijective :
    ∀ (R : Type) (A : Type) [CommRing A] [IsLocalRing A],
      Function.Bijective (fun c : R => LocallyConstant.const (Spec (CommRingCat.of A)) c) := by
  intro R A _ _
  refine ⟨fun c d h => ?_, fun f => ⟨f (IsLocalRing.closedPoint A : PrimeSpectrum A), ?_⟩⟩
  · have := congrArg (fun g : LocallyConstant (Spec (CommRingCat.of A)) R =>
      g (IsLocalRing.closedPoint A : PrimeSpectrum A)) h
    exact this
  · ext x
    simp only [LocallyConstant.coe_const, Function.const_apply]
    exact (locallyConstant_spec_local_eq_closedPoint f x).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialOperatorFderivFormulaStatement
section
open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_operator_fderiv_formula : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (κ κ' κ₁' : Type) [Fintype κ] [Fintype κ'] [Fintype κ₁']
    (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (f : SchwartzMap (κ ⊕ κ' → V) ℂ),
    Differentiable ℝ (qOp P f) ∧ ∀ (s v : κ ⊕ κ₁' → V),
      fderiv ℝ (qOp P f) s v = qOp P (pd (padL (κ' := κ') (v ∘ Sum.inl)) f) s + qOp ((pd (v ∘ Sum.inr)).comp P) f s := by
  first | exact @GlobalTheory.SliceOp.differentiable_qOp_and_fderiv | exact GlobalTheory.SliceOp.differentiable_qOp_and_fderiv | (intros; apply GlobalTheory.SliceOp.differentiable_qOp_and_fderiv <;> assumption)
end

