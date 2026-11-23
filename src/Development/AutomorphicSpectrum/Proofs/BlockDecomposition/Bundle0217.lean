module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0188
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoincareValueBoundOnCube
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0195
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarChartIntegralComparison
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0207
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0205
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0192
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0191
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0196
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0204
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterOperatorPreservesWave
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveTimeAverageIsWave

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevInequalityOnGroup
section
noncomputable section
open MeasureTheory Matrix Finset
open scoped ContDiff
namespace GlobalTheory.CompanionTheory.SobGL
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem bound_on_cube (n : ℕ) (Q : Set (Idx n → ℝ)) (hQc : IsCompact Q) (hQ : ∀ t ∈ Q, 1 + cm t ∈ GLs n)
    (L : List (Idx n)) : ∃ (W : Finset (List (Idx n))) (B : ℝ), 0 ≤ B ∧
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) →
        ∀ t ∈ Q, ‖Dw L f (1 + cm t)‖ ^ 2 ≤ B * ∑ w ∈ W, ‖Rw w f (1 + cm t)‖ ^ 2 := by
  obtain ⟨m, c, w, hc, hrep⟩ := _root_.GlobalTheory.CompanionTheory.SobGL.Expand.Dw_eq_comb n L
  obtain ⟨-, hcm, -, -⟩ := GlobalTheory.T.chart_and_right_words_smooth n
  have hK : IsCompact ((fun t => 1 + cm t) '' Q) := hQc.image (continuous_const.add hcm)
  have hKsub : (fun t => 1 + cm t) '' Q ⊆ GLs n := by
    rintro _ ⟨t, ht, rfl⟩
    exact hQ t ht
  have hb : ∀ i, ∃ M, ∀ y ∈ (fun t => 1 + cm t) '' Q, ‖c i y‖ ≤ M := fun i =>
    hK.exists_bound_of_continuousOn ((hc i).continuousOn.mono hKsub)
  choose M hM using hb
  refine ⟨Finset.univ.image w, (∑ i, M i ^ 2) * m, by positivity, ?_⟩
  intro V _ _ f hf t ht
  have hy : 1 + cm t ∈ GLs n := hQ t ht
  have hyK : 1 + cm t ∈ (fun t => 1 + cm t) '' Q := ⟨t, ht, rfl⟩
  rw [hrep V f hf _ hy]
  have h1 : ‖∑ i, c i (1 + cm t) • Rw (w i) f (1 + cm t)‖ ≤
      ∑ i, M i * ‖Rw (w i) f (1 + cm t)‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hM i _ hyK) (norm_nonneg _)
  have h3 : ∑ i, ‖Rw (w i) f (1 + cm t)‖ ^ 2 ≤
      (m : ℝ) * ∑ u ∈ Finset.univ.image w, ‖Rw u f (1 + cm t)‖ ^ 2 := by
    have hi : ∀ i, ‖Rw (w i) f (1 + cm t)‖ ^ 2 ≤ ∑ u ∈ Finset.univ.image w, ‖Rw u f (1 + cm t)‖ ^ 2 :=
      fun i => Finset.single_le_sum (f := fun u => ‖Rw u f (1 + cm t)‖ ^ 2)
        (fun u _ => by positivity) (Finset.mem_image_of_mem w (Finset.mem_univ i))
    calc ∑ i, ‖Rw (w i) f (1 + cm t)‖ ^ 2
        ≤ ∑ _i : Fin m, ∑ u ∈ Finset.univ.image w, ‖Rw u f (1 + cm t)‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => hi i
      _ = (m : ℝ) * ∑ u ∈ Finset.univ.image w, ‖Rw u f (1 + cm t)‖ ^ 2 := by simp
  calc ‖∑ i, c i (1 + cm t) • Rw (w i) f (1 + cm t)‖ ^ 2
      ≤ (∑ i, M i * ‖Rw (w i) f (1 + cm t)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ i, M i ^ 2) * ∑ i, ‖Rw (w i) f (1 + cm t)‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ (∑ i, M i ^ 2) * ((m : ℝ) * ∑ u ∈ Finset.univ.image w, ‖Rw u f (1 + cm t)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (∑ i, M i ^ 2) * m * ∑ u ∈ Finset.univ.image w, ‖Rw u f (1 + cm t)‖ ^ 2 := by ring

theorem sobG : PositivityTheory.RgBcC.SobG := by
  intro n _ _ μ _
  obtain ⟨hGo, hcm, hcm0, hsm⟩ := GlobalTheory.T.chart_and_right_words_smooth n
  set U0 : Set (Idx n → ℝ) := {t | 1 + cm t ∈ GLs n} with hU0def
  have hU0 : IsOpen U0 := hGo.preimage (continuous_const.add hcm)
  have h0 : (0 : Idx n → ℝ) ∈ U0 := by
    show 1 + cm 0 ∈ GLs n
    rw [hcm0, add_zero]
    show Matrix.det (1 : Mat n) ≠ 0
    simp
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hU0 0 h0
  set ε : ℝ := δ / 2 with hε
  have hεpos : 0 < ε := by positivity
  set Q : Set (Idx n → ℝ) := Set.Icc 0 (fun _ => ε) with hQdef
  have hQc : IsCompact Q := isCompact_Icc
  have hQU : Q ⊆ U0 := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, dist_zero_right]
    refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg hεpos.le).mpr fun i => ?_) (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (ht.1 i)]
    exact ht.2 i
  have hQG : ∀ t ∈ Q, 1 + cm t ∈ GLs n := fun t ht => hQU ht
  obtain ⟨T, C1, hC1, hsob⟩ := _root_.GlobalTheory.CompanionTheory.SobCube.sobolev_cube (Idx n) ε hεpos
  have hbd := fun L => bound_on_cube n Q hQc hQG L
  choose W B hB hWB using hbd
  have hK : IsCompact ((fun t => 1 + cm t) '' Q) := hQc.image (continuous_const.add hcm)
  have hKsub : (fun t => 1 + cm t) '' Q ⊆ GLs n := by
    rintro _ ⟨t, ht, rfl⟩
    exact hQG t ht
  obtain ⟨hlg, hlgc⟩ := GlobalTheory.T.length_continuous_proper_sublevel n
  obtain ⟨r, hr⟩ := hK.exists_bound_of_continuousOn (hlg.mono hKsub)
  set S : Set (G n) := {y | lg (y : Mat n) ≤ r} with hSdef
  have hSc : IsCompact S := hlgc r
  have hcov : ∀ t ∈ Q, ∃ y ∈ S, (y : Mat n) = 1 + cm t := by
    intro t ht
    have hdet : IsUnit (1 + cm t).det := isUnit_iff_ne_zero.mpr (hQG t ht)
    refine ⟨Matrix.nonsingInvUnit _ hdet, ?_, rfl⟩
    show lg (1 + cm t) ≤ r
    have h := hr _ ⟨t, ht, rfl⟩
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  obtain ⟨C2, hC2, hcmp⟩ := _root_.GlobalTheory.CompanionTheory.SobGL.lebesgue_le_haar n μ Q S hQc hSc hcov
  refine ⟨T.biUnion W, r, C1 * C2 * ∑ L ∈ T, B L, ?_⟩
  intro V _ _ _ f hf x hx
  obtain ⟨hgs, hgR⟩ := GlobalTheory.T.left_translate_right_derivative n V f hf x hx
  obtain ⟨hFs, hpd⟩ := _root_.GlobalTheory.CompanionTheory.SobGL.Chart.chart_main n V (fun y => f (x * y)) hgs
  have hxmul : ∀ y ∈ GLs n, x * y ∈ GLs n := by
    intro y hy
    show Matrix.det (x * y) ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hx hy
  have hRc : ∀ w, ContinuousOn (Rw w f) (GLs n) := fun w => ((hsm V f hf).1 w).continuousOn
  let φ : Mat n → ℝ := fun y => ∑ w ∈ T.biUnion W, ‖Rw w f (x * y)‖ ^ 2
  have hφc : ContinuousOn φ (GLs n) := by
    apply continuousOn_finsetSum
    intro w _
    exact (((hRc w).comp (continuous_const.mul continuous_id).continuousOn
      (fun y hy => hxmul y hy)).norm).pow 2
  have hφ0 : ∀ y, 0 ≤ φ y := fun y => Finset.sum_nonneg fun _ _ => by positivity
  have hmain := hcmp φ hφc hφ0
  have hF := hsob V U0 (fun t => f (x * (1 + cm t))) hU0 hQU hFs
  have hstep : ∀ L ∈ T, ∫ t in Q, ‖pd L (fun t => f (x * (1 + cm t))) t‖ ^ 2 ≤
      B L * (C2 * ∫ y in S, φ (y : Mat n) ∂μ) := by
    intro L hL
    have hcongr : ∫ t in Q, ‖pd L (fun t => f (x * (1 + cm t))) t‖ ^ 2 =
        ∫ t in Q, ‖Dw L (fun y => f (x * y)) (1 + cm t)‖ ^ 2 :=
      setIntegral_congr_fun measurableSet_Icc (fun t ht => by rw [hpd L t (hQG t ht)])
    rw [hcongr]
    have hle : ∀ t ∈ Q, ‖Dw L (fun y => f (x * y)) (1 + cm t)‖ ^ 2 ≤ B L * φ (1 + cm t) := by
      intro t ht
      refine (hWB L V (fun y => f (x * y)) hgs t ht).trans (mul_le_mul_of_nonneg_left ?_ (hB L))
      calc ∑ w ∈ W L, ‖Rw w (fun y => f (x * y)) (1 + cm t)‖ ^ 2
          = ∑ w ∈ W L, ‖Rw w f (x * (1 + cm t))‖ ^ 2 :=
            Finset.sum_congr rfl fun w _ => by rw [hgR w _ (hQG t ht)]
        _ ≤ φ (1 + cm t) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_biUnion_of_mem W hL)
              (fun _ _ _ => by positivity)
    have hint : IntegrableOn (fun t => B L * φ (1 + cm t)) Q volume := by
      refine ContinuousOn.integrableOn_compact hQc ?_
      exact continuousOn_const.mul
        (hφc.comp (continuous_const.add hcm).continuousOn (fun t ht => hQG t ht))
    calc ∫ t in Q, ‖Dw L (fun y => f (x * y)) (1 + cm t)‖ ^ 2
        ≤ ∫ t in Q, B L * φ (1 + cm t) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => by positivity) hint
            ((ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall hle))
      _ = B L * ∫ t in Q, φ (1 + cm t) := integral_const_mul _ _
      _ ≤ B L * (C2 * ∫ y in S, φ (y : Mat n) ∂μ) := mul_le_mul_of_nonneg_left hmain (hB L)
  have hsplit : ∫ y in S, φ (y : Mat n) ∂μ =
      ∑ w ∈ T.biUnion W, ∫ y in S, ‖Rw w f (x * (y : Mat n))‖ ^ 2 ∂μ := by
    refine integral_finsetSum _ fun w _ => ?_
    refine ContinuousOn.integrableOn_compact hSc (Continuous.continuousOn ?_)
    have hval : ∀ y : G n, x * (y : Mat n) ∈ GLs n := fun y =>
      hxmul _ ((Matrix.isUnit_iff_isUnit_det _).mp y.isUnit).ne_zero
    exact (((hRc w).comp_continuous (continuous_const.mul Units.continuous_val) hval).norm).pow 2
  have hF0 : f (x * (1 + cm 0)) = f x := by rw [hcm0, add_zero, mul_one]
  calc ‖f x‖ ^ 2 = ‖f (x * (1 + cm 0))‖ ^ 2 := by rw [hF0]
    _ ≤ C1 * ∑ L ∈ T, ∫ t in Q, ‖pd L (fun t => f (x * (1 + cm t))) t‖ ^ 2 := hF
    _ ≤ C1 * ∑ L ∈ T, B L * (C2 * ∫ y in S, φ (y : Mat n) ∂μ) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep) hC1
    _ = C1 * C2 * (∑ L ∈ T, B L) * ∫ y in S, φ (y : Mat n) ∂μ := by
        rw [← Finset.sum_mul]
        ring
    _ = C1 * C2 * (∑ L ∈ T, B L) *
        ∑ w ∈ T.biUnion W, ∫ y in S, ‖Rw w f (x * (y : Mat n))‖ ^ 2 ∂μ := by rw [hsplit]

end GlobalTheory.CompanionTheory.SobGL
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveIntegralIdentity
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem secondCountable_G (n : ℕ) : SecondCountableTopology (G n) := by
  haveI : SecondCountableTopology (Mat n) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Mat n)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact (Units.isEmbedding_embedProduct (M := Mat n)).secondCountableTopology

theorem val_mem_GLs {n : ℕ} (y : G n) : y.val ∈ GLs n := by
  have : IsUnit y.val.det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
  exact this.ne_zero

theorem continuous_lg (hL : LgFacts) {n : ℕ} : Continuous (fun y : G n => lg y.val) := by
  have h1 : ContinuousOn (lg (n := n)) (GLs n) := ((hL n).2.2.2.1).continuousOn
  exact h1.comp_continuous Units.continuous_val val_mem_GLs

theorem locallyCompact_G (hL : LgFacts) (n : ℕ) : LocallyCompactSpace (G n) := by
  haveI : WeaklyLocallyCompactSpace (G n) := ⟨fun x => ⟨{y : G n | lg y.val ≤ lg x.val + 1},
    (hL n).2.2.2.2.1 _, by
      have : {y : G n | lg y.val < lg x.val + 1} ∈ 𝓝 x :=
        (isOpen_lt (continuous_lg hL) continuous_const).mem_nhds (by simp)
      exact Filter.mem_of_superset this (fun y (hy : lg y.val < _) => show lg y.val ≤ _ from le_of_lt hy)⟩⟩
  infer_instance

theorem sigmaCompact_G (hL : LgFacts) (n : ℕ) : SigmaCompactSpace (G n) := by
  refine ⟨⟨fun k : ℕ => {y : G n | lg y.val ≤ k}, fun k => (hL n).2.2.2.2.1 _, ?_⟩⟩
  ext y
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  obtain ⟨k, hk⟩ := exists_nat_ge (lg y.val)
  exact ⟨k, hk⟩

theorem cls_inner {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {f f' : Mat n → V} (hf : MemLp (fun y : G n => f y.val) 2 μ)
    (hf' : MemLp (fun y : G n => f' y.val) 2 μ) :
    ⟪cls μ f, cls μ f'⟫_ℂ = ∫ y : G n, ⟪f y.val, f' y.val⟫_ℂ ∂μ := by
  have e1 : cls μ f = hf.toLp _ := by
    unfold cls; exact dif_pos hf
  have e2 : cls μ f' = hf'.toLp _ := by
    unfold cls; exact dif_pos hf'
  rw [e1, e2, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hf'.coeFn_toLp] with y h1 h2
  rw [h1, h2]

theorem bump_complex {g : ℝ → ℝ} {T₀ : ℝ} (hg : IsBump g T₀) :
    Continuous (fun t => (g t : ℂ)) ∧ HasCompactSupport (fun t => (g t : ℂ)) := by
  refine ⟨Complex.continuous_ofReal.comp hg.1.continuous, ?_⟩
  refine HasCompactSupport.intro (isCompact_Icc (a := -|T₀|) (b := |T₀|)) (fun t ht => ?_)
  have h1 : |T₀| < |t| := by
    by_contra h
    exact ht (abs_le.1 (not_lt.1 h))
  have h2 : g t = 0 := hg.2.2 t (lt_of_le_of_lt (le_abs_self _) h1)
  simp [h2]

theorem phi_integral {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Φ : C₀(ℝ, ℂ) →L[ℂ] (H →L[ℂ] H)) (b : H) (hFc : Fcurve) {g : ℝ → ℝ} {T₀ : ℝ} (hg : IsBump g T₀)
    (c : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ∀ v : H, ⟪v, Φ (∫ t, (g t : ℂ) • toC0 (wv c N 0 t)) b⟫_ℂ =
      ∫ t, (g t : ℂ) * ⟪v, Φ (toC0 (wv c N 0 t)) b⟫_ℂ := by
  have hcurve : Continuous (fun t => toC0 (wv c N 0 t)) :=
    continuous_iff_continuousAt.2 fun t =>
      (hFc c N 0 (by omega) t).2.continuousAt
  have hi : Integrable (fun t => (g t : ℂ) • toC0 (wv c N 0 t)) :=
    ((bump_complex hg).1.smul hcurve).integrable_of_hasCompactSupport
      ((bump_complex hg).2.smul_right)
  let L : C₀(ℝ, ℂ) →L[ℂ] H := (ContinuousLinearMap.apply ℂ H b).comp Φ
  have hL : ∀ t, L ((g t : ℂ) • toC0 (wv c N 0 t)) = (g t : ℂ) • Φ (toC0 (wv c N 0 t)) b := by
    intro t
    simp [L]
  have hi' : Integrable (fun t => (g t : ℂ) • Φ (toC0 (wv c N 0 t)) b) := by
    simpa only [hL] using L.integrable_comp hi
  have e : Φ (∫ t, (g t : ℂ) • toC0 (wv c N 0 t)) b = ∫ t, (g t : ℂ) • Φ (toC0 (wv c N 0 t)) b := by
    have := L.integral_comp_comm hi
    simp only [hL] at this
    rw [this]
    rfl
  intro v
  rw [e, ← integral_inner hi' v]
  simp only [inner_smul_right]

theorem test_fubini {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (hLg : LgFacts) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    {W : ℝ → G n → V} (hW : Continuous (Function.uncurry W)) {Ψ : G n → V} (hΨ : Continuous Ψ)
    (hΨc : HasCompactSupport Ψ) {γ : ℝ → ℂ} (hγ : Continuous γ) (hγc : HasCompactSupport γ) :
    ∫ y, ⟪Ψ y, ∫ t, γ t • W t y⟫_ℂ ∂μ = ∫ t, γ t * ∫ y, ⟪Ψ y, W t y⟫_ℂ ∂μ := by
  haveI := secondCountable_G n
  haveI := sigmaCompact_G hLg n
  haveI : SigmaFinite μ := Measure.IsHaarMeasure.sigmaFinite μ
  have h1 : ∀ y, ⟪Ψ y, ∫ t, γ t • W t y⟫_ℂ = ∫ t, γ t * ⟪Ψ y, W t y⟫_ℂ := by
    intro y
    have hc : Continuous (fun t => W t y) := hW.comp (by fun_prop : Continuous fun t : ℝ => (t, y))
    have hi : Integrable (fun t => γ t • W t y) :=
      (hγ.smul hc).integrable_of_hasCompactSupport hγc.smul_right
    rw [← integral_inner hi]
    simp only [inner_smul_right]
  simp only [h1]
  have hcont : Continuous (Function.uncurry fun (y : G n) (t : ℝ) => γ t * ⟪Ψ y, W t y⟫_ℂ) := by
    have h2 : Continuous (fun p : G n × ℝ => W p.2 p.1) :=
      hW.comp (by fun_prop : Continuous fun p : G n × ℝ => (p.2, p.1))
    have h3 : Continuous (fun p : G n × ℝ => Ψ p.1) := hΨ.comp continuous_fst
    exact (hγ.comp continuous_snd).mul (h3.inner h2)
  have hint : Integrable (Function.uncurry fun (y : G n) (t : ℝ) => γ t * ⟪Ψ y, W t y⟫_ℂ) (μ.prod volume) := by
    refine hcont.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (hΨc.isCompact.prod hγc.isCompact) (fun p hp => ?_)
    rcases p with ⟨y, t⟩
    by_cases hy : y ∈ tsupport Ψ
    · have ht : t ∉ tsupport γ := fun ht => hp ⟨hy, ht⟩
      simp [Function.uncurry, image_eq_zero_of_notMem_tsupport ht]
    · simp [Function.uncurry, image_eq_zero_of_notMem_tsupport hy]
  rw [integral_integral_swap hint]
  simp only [integral_const_mul]

theorem waveInt : WaveInt := by
  intro n _ _ μ _ E _ Ω T F c hS g T₀ hg N b U hN hW hU f' hf' hcls x hx
  obtain ⟨hLg, -, -, -, -, -, -, hCS, -, hPW, -⟩ := hS
  have hFc : Fcurve := hCS.2.2.1
  haveI := secondCountable_G n
  haveI := locallyCompact_G hLg n
  obtain ⟨hγ, hγc⟩ := bump_complex hg
  set γ : ℝ → ℂ := fun t => (g t : ℂ) with hγdef

  have hUc : Continuous (Function.uncurry fun (t : ℝ) (y : G n) => U t y.val) := by
    have h1 : ContinuousOn (Function.uncurry U) (Set.univ ×ˢ GLs n) := hW.1.continuousOn
    exact h1.comp_continuous (f := fun p : ℝ × G n => (p.1, p.2.val))
      (continuous_fst.prodMk (Units.continuous_val.comp continuous_snd))
      (fun p => ⟨trivial, val_mem_GLs _⟩)
  have hfc : Continuous (fun y : G n => f' y.val) :=
    hf'.1.continuousOn.comp_continuous Units.continuous_val val_mem_GLs
  have hF₁ : Continuous (fun y : G n => ∫ t, γ t • U t y.val) := by
    have hc : Continuous (Function.uncurry fun (y : G n) (t : ℝ) => γ t • U t y.val) := by
      have h2 : Continuous (fun p : G n × ℝ => U p.2 p.1.val) :=
        hUc.comp (by fun_prop : Continuous fun p : G n × ℝ => (p.2, p.1))
      exact (hγ.comp continuous_snd).smul h2
    have h3 := continuous_parametric_integral_of_continuous (μ := (volume : Measure ℝ)) hc hγc.isCompact
    refine h3.congr (fun y => ?_)
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => ?_)
    simp [image_eq_zero_of_notMem_tsupport ht]

  have hMemU : ∀ t, MemLp (fun y : G n => U t y.val) 2 μ := fun t => (hU t).1.2 []
  have hMemf : MemLp (fun y : G n => f' y.val) 2 μ := hf'.2 []
  have hcalc := phi_integral F.Φ b hFc hg c hN
  have hpw := (hPW c g T₀ hg).2 N hN
  have test : ∀ ψ : Mat n → E.V, Continuous (fun y : G n => ψ y.val) →
      HasCompactSupport (fun y : G n => ψ y.val) →
      ∫ y : G n, ⟪ψ y.val, ∫ t, γ t • U t y.val⟫_ℂ ∂μ = ∫ y : G n, ⟪ψ y.val, f' y.val⟫_ℂ ∂μ := by
    intro ψ hψ hψc
    have hMemψ : MemLp (fun y : G n => ψ y.val) 2 μ := hψ.memLp_of_hasCompactSupport hψc
    rw [test_fubini μ hLg hUc hψ hψc hγ hγc, ← cls_inner μ hMemψ hMemf, hcls, ← hpw, hcalc (cls μ ψ)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [← (hU t).2, cls_inner μ hMemψ (hMemU t), hγdef]

  have hxu : IsUnit x := (Matrix.isUnit_iff_isUnit_det x).2 (isUnit_iff_ne_zero.2 hx)
  obtain ⟨xg, rfl⟩ := hxu
  set Dm : Mat n → E.V := fun y => (∫ t, γ t • U t y) - f' y with hDm
  have hD : Continuous (fun y : G n => Dm y.val) := hF₁.sub hfc
  set bc : G n → ℝ := fun y => max 0 (lg (1 : Mat n) + 1 - lg (xg⁻¹ * y).val) with hbc
  have hbcc : Continuous bc := by
    have h1 : Continuous (fun y : G n => lg (xg⁻¹ * y).val) :=
      (continuous_lg hLg).comp (continuous_const.mul continuous_id)
    exact continuous_const.max (continuous_const.sub h1)
  have hK : IsCompact ((fun y : G n => xg * y) '' {y : G n | lg y.val ≤ lg (1 : Mat n) + 1}) :=
    ((hLg n).2.2.2.2.1 _).image (continuous_const.mul continuous_id)
  have hbz : ∀ y, y ∉ ((fun y : G n => xg * y) '' {y : G n | lg y.val ≤ lg (1 : Mat n) + 1}) → bc y = 0 := by
    intro y hy
    have h1 : ¬ lg (xg⁻¹ * y).val ≤ lg (1 : Mat n) + 1 := fun h => hy ⟨xg⁻¹ * y, h, by simp⟩
    simp only [hbc]
    exact max_eq_left (by linarith [not_le.1 h1])
  set ψ : Mat n → E.V := fun y => ((max 0 (lg (1 : Mat n) + 1 - lg ((xg⁻¹ : G n).val * y)) : ℝ) : ℂ) • Dm y with hψdef
  have hψv : ∀ y : G n, ψ y.val = ((bc y : ℝ) : ℂ) • Dm y.val := by
    intro y
    simp only [hψdef, hbc, Units.val_mul]
  have hψ : Continuous (fun y : G n => ψ y.val) := by
    simp only [hψv]
    exact (Complex.continuous_ofReal.comp hbcc).smul hD
  have hψc : HasCompactSupport (fun y : G n => ψ y.val) := by
    refine HasCompactSupport.intro hK (fun y hy => ?_)
    simp [hψv, hbz y hy]
  have hcomp : ∀ {f₁ : G n → E.V}, Continuous f₁ → Integrable (fun y : G n => ⟪ψ y.val, f₁ y⟫_ℂ) μ := by
    intro f₁ h₁
    refine (hψ.inner h₁).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro hK (fun y hy => ?_)
    simp [hψv, hbz y hy]
  have hzero : ∫ y : G n, ⟪ψ y.val, Dm y.val⟫_ℂ ∂μ = 0 := by
    have h1 : ∀ y : G n, ⟪ψ y.val, Dm y.val⟫_ℂ =
        ⟪ψ y.val, ∫ t, γ t • U t y.val⟫_ℂ - ⟪ψ y.val, f' y.val⟫_ℂ := fun y => inner_sub_right _ _ _
    simp only [h1]
    rw [integral_sub (hcomp hF₁) (hcomp hfc), test ψ hψ hψc, sub_self]

  set hh : G n → ℝ := fun y => bc y * ‖Dm y.val‖ ^ 2 with hhdef
  have hhc : Continuous hh := hbcc.mul (hD.norm.pow 2)
  have hinn : ∀ y : G n, ⟪ψ y.val, Dm y.val⟫_ℂ = ((hh y : ℝ) : ℂ) := by
    intro y
    rw [hψv, inner_smul_left, inner_self_eq_norm_sq_to_K]
    simp [hhdef]
  have hhz : ∫ y, hh y ∂μ = 0 := by
    simp only [hinn] at hzero
    rw [integral_complex_ofReal] at hzero
    exact_mod_cast hzero
  have hhi : Integrable hh μ := by
    refine hhc.integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro hK (fun y hy => ?_)
    simp [hhdef, hbz y hy]
  have hh0 : 0 ≤ hh := fun y => mul_nonneg (le_max_left _ _) (by positivity)
  have hae := (integral_eq_zero_iff_of_nonneg hh0 hhi).1 hhz
  have hfun : hh = 0 := (Continuous.ae_eq_iff_eq μ hhc continuous_zero).1 hae
  have hat : hh xg = 0 := congrFun hfun xg
  have hb1 : bc xg = 1 := by
    simp [hbc]
  have hnorm : ‖Dm xg.val‖ = 0 := by
    have : ‖Dm xg.val‖ ^ 2 = 0 := by simpa [hhdef, hb1] using hat
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  exact sub_eq_zero.1 (norm_eq_zero.1 hnorm)

end GlobalTheory.CompanionTheory.KerFc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelComposition
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem integral_smul_integral_shift {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [CompleteSpace V] {g g' : ℝ → ℝ} {T T' : ℝ} (hg : IsBump g T) (hg' : IsBump g' T')
    {φ : ℝ → V} (hφ : Continuous φ) :
    ∫ t, (g t : ℂ) • ∫ s, (g' s : ℂ) • φ (t + s) = ∫ r, (gconv g g' r : ℂ) • φ r := by
  have cg : Continuous g := hg.1.continuous
  have cg' : Continuous g' := hg'.1.continuous
  let F : ℝ → ℝ → V := fun t r => ((g t * g' (r - t) : ℝ) : ℂ) • φ r
  have hFc : Continuous (Function.uncurry F) := by
    have : Function.uncurry F = fun p : ℝ × ℝ => ((g p.1 * g' (p.2 - p.1) : ℝ) : ℂ) • φ p.2 := rfl
    rw [this]
    fun_prop
  have hFs : HasCompactSupport (Function.uncurry F) := by
    refine HasCompactSupport.intro
      (K := Set.Icc (-|T|) |T| ×ˢ Set.Icc (-(|T| + |T'|)) (|T| + |T'|))
      (isCompact_Icc.prod isCompact_Icc) ?_
    rintro ⟨t, r⟩ h
    by_cases ht : T < |t|
    · simp [Function.uncurry, F, hg.2.2 t ht]
    · by_cases hr : T' < |r - t|
      · simp [Function.uncurry, F, hg'.2.2 _ hr]
      · exfalso
        apply h
        have h1 : |t| ≤ |T| := (not_lt.mp ht).trans (le_abs_self T)
        have h2 : |r - t| ≤ |T'| := (not_lt.mp hr).trans (le_abs_self T')
        have h3 : |r| ≤ |t| + |r - t| := by simpa using abs_add_le t (r - t)
        exact ⟨abs_le.mp h1, abs_le.mp (by linarith)⟩
  have hFi : Integrable (Function.uncurry F) (volume.prod volume) :=
    hFc.integrable_of_hasCompactSupport hFs
  have hL : ∀ t, (g t : ℂ) • ∫ s, (g' s : ℂ) • φ (t + s) = ∫ r, F t r := by
    intro t
    rw [← integral_add_left_eq_self (fun r => F t r) t, ← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [F, add_sub_cancel_left, Complex.ofReal_mul, mul_smul]
  have hR : ∀ r, (gconv g g' r : ℂ) • φ r = ∫ t, F t r := by
    intro r
    simp only [F, gconv]
    rw [integral_smul_const, integral_complex_ofReal]
  simp only [hL, hR]
  exact integral_integral_swap hFi

theorem wave_compose : RCalc → WaveSpeed → ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V)
    (w w' : List (Bool × ℕ)) (g g' : ℝ → ℝ) (T T' : ℝ), IsWave E u → IsBump g T → IsBump g' T' →
    ∃ v : ℝ → Mat n → E.V, IsWave E v ∧
      (∀ x ∈ GLs n, v 0 x = zOp w' (fun x' => ∫ t, (g' t : ℂ) • u t x') x) ∧
      ∀ x ∈ GLs n, zOp w (fun x' => ∫ t, (g t : ℂ) • v t x') x =
        zOp (w ++ w') (fun x' => ∫ t, (gconv g g' t : ℂ) • u t x') x := by
  intro hR hS n E u w w' g g' T T' hu hg hg'
  have : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  have hu' : IsWave E (fun t => zOp w' (u t)) := WaveZ.isWave_zOp hR n E u w' hu
  have hv := WaveAvg.isWave_avg hS n E (fun t => zOp w' (u t)) g' T' hu' hg'
  refine ⟨_, hv, ?_, ?_⟩
  · intro x hx
    have h := ZOpAvg.zOp_avg n u g' T' w' hu.1 hg' x hx
    simp only [zero_add]
    exact h.symm
  · intro x hx
    have hb := isBump_gconv g g' T T' hg hg'
    have hφ : ∀ x' ∈ GLs n, Continuous fun r => zOp w' (u r) x' := fun x' hx' =>
      hu'.1.continuousOn.comp_continuous (f := fun r : ℝ => (r, x')) (by fun_prop)
        (fun r => ⟨trivial, hx'⟩)
    have h1 : ∀ x' ∈ GLs n, (∫ t, (g t : ℂ) • ∫ s, (g' s : ℂ) • zOp w' (u (t + s)) x') =
        ∫ r, (gconv g g' r : ℂ) • zOp w' (u r) x' := fun x' hx' =>
      integral_smul_integral_shift hg hg' (hφ x' hx')
    rw [zOp_agree_GLs n w _ _ h1 x hx,
      ZOpAvg.zOp_avg n (fun t => zOp w' (u t)) (gconv g g') (T + T') w hu'.1 hb x hx,
      ZOpAvg.zOp_avg n u (gconv g g') (T + T') (w ++ w') hu.1 hb x hx]
    simp only [Swap.zOp_append]

end GlobalTheory.CompanionTheory.WaveMult
end
end

