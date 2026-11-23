module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0189
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0188

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsoluteCutoffBound
section
noncomputable section

open Filter Topology
open scoped ZeroAtInfty InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.FcCut

open PositivityTheory.RgBcC.Fc

def mulC (a : ℝ → ℂ) (ha : Continuous a) (f : C₀(ℝ, ℂ)) (R : ℝ) (hf : ∀ y, R ≤ |y| → a y * f y = 0) :
    C₀(ℝ, ℂ) :=
  ⟨⟨fun y => a y * f y, ha.mul f.continuous⟩, by
    have hK : (Set.Icc (-R) R)ᶜ ∈ cocompact ℝ := isCompact_Icc.compl_mem_cocompact
    refine (tendsto_const_nhds (x := (0 : ℂ))).congr' ?_
    filter_upwards [hK] with y hy
    have hR : R ≤ |y| := by
      by_contra hlt
      push_neg at hlt
      exact hy ⟨(abs_lt.mp hlt).1.le, (abs_lt.mp hlt).2.le⟩
    show (0 : ℂ) = a y * f y
    rw [hf y hR]⟩

@[simp] theorem mulC_apply (a : ℝ → ℂ) (ha : Continuous a) (f : C₀(ℝ, ℂ)) (R : ℝ)
    (hf : ∀ y, R ≤ |y| → a y * f y = 0) (y : ℝ) : mulC a ha f R hf y = a y * f y := rfl

section Core

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : Submodule ℂ H} {Ω : M →ₗ[ℂ] M} {T : H →L[ℂ] H}

theorem inner_star_mul (F : FCalc H M Ω T) (x : H) (a b : C₀(ℝ, ℂ)) :
    ⟪F.Φ (star a * b) x, x⟫_ℂ = ⟪F.Φ b x, F.Φ a x⟫_ℂ := by
  rw [F.map_mul, F.map_star, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.adjoint_inner_left]

theorem core (F : FCalc H M Ω T) (c : ℝ) (x : H)
    (hyp : ∀ g, ∃ v : M, (v : H) = F.Φ g x ∧ (⟪(Ω v : H), v⟫_ℂ).re ≤ c * ‖(v : H)‖ ^ 2)
    (f : C₀(ℝ, ℂ)) (δ R : ℝ) (hδ : 0 < δ) (h1 : ∀ y, y ≤ c + δ → f y = 0)
    (h2 : ∀ y, R ≤ |y| → f y = 0) : F.Φ f x = 0 := by
  let h := mulC (fun y => (y : ℂ)) Complex.continuous_ofReal f R
    (fun y hy => by rw [h2 y hy, mul_zero])
  let r := mulC (fun y => ((Real.sqrt (max (y - c - δ) 0) : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (by fun_prop)) f R (fun y hy => by rw [h2 y hy, mul_zero])
  obtain ⟨v, hv, hle⟩ := hyp f
  have hΩ : (Ω v : H) = F.Φ h x := F.omega f h (fun y => rfl) x v hv
  have hid : star r * r = star f * h - ((c + δ : ℝ) : ℂ) • (star f * f) := by
    ext y
    by_cases hy : y ≤ c + δ
    · simp [r, h, h1 y hy]
    · have hpos : 0 ≤ y - c - δ := by linarith [not_le.mp hy]
      have hs : ((Real.sqrt (y - c - δ) : ℝ) : ℂ) * ((Real.sqrt (y - c - δ) : ℝ) : ℂ)
          = (y : ℂ) - c - δ := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt hpos]; push_cast; ring
      simp only [r, h, ZeroAtInftyContinuousMap.coe_mul, ZeroAtInftyContinuousMap.coe_star,
        ZeroAtInftyContinuousMap.coe_sub, ZeroAtInftyContinuousMap.coe_smul, Pi.mul_apply, Pi.star_apply,
        Pi.sub_apply, Pi.smul_apply, mulC_apply, max_eq_left hpos, star_mul', smul_eq_mul]
      simp only [Complex.star_def, Complex.conj_ofReal]
      push_cast
      linear_combination ((starRingEnd ℂ) (f y) * f y) * hs
  have e : ((‖F.Φ r x‖ ^ 2 : ℝ) : ℂ) = ⟪(Ω v : H), v⟫_ℂ - ((c + δ : ℝ) : ℂ) * ((‖(v : H)‖ ^ 2 : ℝ) : ℂ) := by
    have a1 := inner_star_mul F x r r
    have a2 := inner_star_mul F x f h
    have a3 := inner_star_mul F x f f
    rw [hid, map_sub, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      inner_sub_left, inner_smul_left, a2, a3, Complex.conj_ofReal,
      inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at a1
    rw [hΩ, hv]
    push_cast
    simpa using a1.symm
  have e' := congrArg Complex.re e
  rw [Complex.ofReal_re, Complex.sub_re, Complex.re_ofReal_mul, Complex.ofReal_re] at e'
  have hn : ‖(v : H)‖ ^ 2 ≤ 0 := by
    have p1 : 0 ≤ ‖F.Φ r x‖ ^ 2 := by positivity
    nlinarith
  have hv0 : ‖(v : H)‖ = 0 := by
    have := sq_nonneg ‖(v : H)‖
    exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm hn this)
  rw [← hv]
  exact norm_eq_zero.mp hv0

theorem approx (c : ℝ) (g : C₀(ℝ, ℂ)) (hg : ∀ y, y ≤ c → g y = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ (f : C₀(ℝ, ℂ)) (δ R : ℝ), 0 < δ ∧ (∀ y, y ≤ c + δ → f y = 0) ∧ (∀ y, R ≤ |y| → f y = 0) ∧
      ‖g - f‖ ≤ 2 * ε := by

  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ y, R ≤ |y| → ‖g y‖ ≤ ε := by
    have ht : Tendsto g (cocompact ℝ) (𝓝 0) := g.zero_at_infty'
    have hm : {y | ‖g y‖ < ε} ∈ cocompact ℝ := by
      have := ht (Metric.ball_mem_nhds (0 : ℂ) hε)
      simpa [Metric.ball, dist_zero_right] using this
    obtain ⟨t, ht1, ht2⟩ := Filter.mem_cocompact.mp hm
    obtain ⟨r, hr⟩ := ht1.isBounded.subset_closedBall (0 : ℝ)
    refine ⟨r + 1, fun y hy => ?_⟩
    have hyt : y ∈ tᶜ := fun hyt => by
      have := hr hyt
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
      linarith
    exact (ht2 hyt).le

  obtain ⟨δ, hδ, hδc⟩ : ∃ δ > 0, ∀ y, y ≤ c + δ → ‖g y‖ ≤ ε := by
    obtain ⟨d, hd, hdc⟩ := Metric.continuous_iff.mp g.continuous c ε hε
    refine ⟨d / 2, by positivity, fun y hy => ?_⟩
    by_cases hyc : y ≤ c
    · rw [hg y hyc, norm_zero]; exact hε.le
    · have : dist y c < d := by
        rw [Real.dist_eq, abs_of_pos (by linarith [not_le.mp hyc])]
        linarith
      have h3 : dist (g y) (g c) < ε := hdc y this
      rw [hg c le_rfl, dist_zero_right] at h3
      exact h3.le
  let m : ℝ → ℝ := fun y => min 1 (max 0 (‖g y‖ / ε - 1))
  have hm0 : ∀ y, ‖g y‖ ≤ ε → m y = 0 := fun y hy => by
    have : ‖g y‖ / ε - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one hε]; exact hy
    simp only [m, max_eq_left this]
    exact min_eq_right zero_le_one
  have hmc : Continuous m := by
    have := g.continuous
    fun_prop
  let f := mulC (fun y => (m y : ℂ)) (Complex.continuous_ofReal.comp hmc) g R
    (fun y hy => by rw [hm0 y (hR y hy)]; simp)
  refine ⟨f, δ, R, hδ, fun y hy => ?_, fun y hy => ?_, ?_⟩
  · simp [f, hm0 y (hδc y hy)]
  · simp [f, hm0 y (hR y hy)]
  · rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    refine (BoundedContinuousFunction.norm_le (by positivity)).mpr fun y => ?_
    have hy : (g - f).toBCF y = (1 - (m y : ℂ)) * g y := by
      show g y - (m y : ℂ) * g y = _
      ring
    rw [hy, norm_mul]
    have hm1 : m y ≤ 1 := min_le_left _ _
    have hm2 : 0 ≤ m y := le_min zero_le_one (le_max_left _ _)
    have hn : ‖(1 - (m y : ℂ))‖ = 1 - m y := by
      have : (1 - (m y : ℂ)) = ((1 - m y : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    rw [hn]
    by_cases hb : 2 * ε ≤ ‖g y‖
    · have : m y = 1 := by
        have h1 : 1 ≤ ‖g y‖ / ε - 1 := by
          have : 2 ≤ ‖g y‖ / ε := by rw [le_div_iff₀ hε]; exact hb
          linarith
        exact min_eq_left (h1.trans (le_max_right _ _))
      rw [this]; simp; positivity
    · have hgy := (not_le.mp hb).le
      have : 0 ≤ ‖g y‖ := norm_nonneg _
      nlinarith

theorem absCut : AbsCut := by
  intro H _ _ _ M Ω T F c x hyp g hg
  refine norm_eq_zero.mp (le_antisymm (le_of_forall_pos_le_add fun e he => ?_) (norm_nonneg _))
  have hx : 0 < ‖x‖ + 1 := by positivity
  obtain ⟨f, δ, R, hδ, h1, h2, hfg⟩ := approx c g hg (e / (2 * (‖x‖ + 1))) (by positivity)
  have hz := core F c x hyp f δ R hδ h1 h2
  have hsplit : F.Φ g x = F.Φ (g - f) x := by
    rw [map_sub, ContinuousLinearMap.sub_apply, hz, sub_zero]
  have hb : ‖F.Φ (g - f) x‖ ≤ 2 * (e / (2 * (‖x‖ + 1))) * ‖x‖ :=
    ((F.Φ (g - f)).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right ((F.norm_le _).trans hfg) (norm_nonneg _))
  have hc : 2 * (e / (2 * (‖x‖ + 1))) * ‖x‖ ≤ e := by
    have : 2 * (e / (2 * (‖x‖ + 1))) * ‖x‖ = e * (‖x‖ / (‖x‖ + 1)) := by
      field_simp
    rw [this]
    have : ‖x‖ / (‖x‖ + 1) ≤ 1 := by
      rw [div_le_one hx]; linarith
    nlinarith
  rw [hsplit]
  linarith

end Core

end GlobalTheory.CompanionTheory.FcCut
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqSumOfKernel
section
open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem act_eq_sum_of_kernel : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) {ι : Type} [Fintype ι] (c : ι → ℂ) (ks : ι → Mat n → (E.V →L[ℂ] E.V)) (k : Mat n → (E.V →L[ℂ] E.V)) (f : Mat n → E.V), (∀ i, KReg (ks i)) → (∀ y ∈ GLs n, k y = ∑ i, c i • ks i y) → ContinuousOn f (GLs n) → ∀ x ∈ GLs n, act μ E k f x = ∑ i, c i • act μ E (ks i) f x := by
  intro hL n _ _ μ _ E ι _ c ks k f hks hk hf x hx
  haveI := FiniteDimensional.complete ℂ E.V
  have hval : ∀ y : G n, y.val ∈ GLs n := fun y => by
    have := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
    exact this.ne_zero
  have hcv : Continuous (fun y : G n => y.val) := Units.continuous_val
  have hmul : ∀ y : G n, x * y.val ∈ GLs n := fun y => by
    have h1 : x.det ≠ 0 := hx
    have h2 : y.val.det ≠ 0 := hval y
    change (x * y.val).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero h1 h2
  have hint : ∀ i, Integrable (fun y : G n => ks i y.val (f (x * y.val))) μ := by
    intro i
    obtain ⟨hc, R, hR⟩ := hks i
    have hcont : Continuous (fun y : G n => ks i y.val (f (x * y.val))) := by
      have h1 : Continuous (fun y : G n => ks i y.val) :=
        hc.comp_continuous hcv hval
      have h2 : Continuous (fun y : G n => f (x * y.val)) :=
        hf.comp_continuous (continuous_const.mul hcv) hmul
      exact h1.clm_apply h2
    have hsupp : HasCompactSupport (fun y : G n => ks i y.val (f (x * y.val))) := by
      refine HasCompactSupport.intro ((hL n).2.2.2.2.1 R) ?_
      intro y hy
      have hy' : R < lg y.val := not_le.1 hy
      simp [hR y.val (hval y) hy']
    exact hcont.integrable_of_hasCompactSupport hsupp
  unfold act
  have hpt : (fun y : G n => k y.val (f (x * y.val)))
      = fun y : G n => ∑ i, c i • ks i y.val (f (x * y.val)) := by
    funext y
    rw [hk y.val (hval y)]
    simp [ContinuousLinearMap.sum_apply]
  have hi : ∀ i ∈ (Finset.univ : Finset ι),
      Integrable (fun y : G n => c i • ks i y.val (f (x * y.val))) μ :=
    fun i _ => (hint i).smul (c i)
  rw [hpt, MeasureTheory.integral_finsetSum _ hi]
  exact Finset.sum_congr rfl (fun i _ => integral_smul (c i) _)

end GlobalTheory.CompanionTheory.WaveMult
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjKInner
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveK.Base

open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveK
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def RwLin : Prop :=
  ∀ (n : ℕ) (V W : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (ι : Type) [Fintype ι] (L : ι → V →L[ℝ] W) (f : ι → Mat n → V), (∀ i, ContDiffOn ℝ ∞ (f i) (GLs n)) →
    ∀ (w : List (Bool × Fin n × Fin n)), ∀ x ∈ GLs n, Rw w (fun y => ∑ i, L i (f i y)) x = ∑ i, L i (Rw w (f i) x)

end GlobalTheory.CompanionTheory.WaveK.Base
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BumpConvolutionSupport
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem hasCompactSupport_of_isBump {g : ℝ → ℝ} {T : ℝ} (hg : IsBump g T) : HasCompactSupport g := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) T) fun x hx => hg.2.2 x ?_
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at hx
  exact hx

theorem isBump_gconv : ∀ (g g' : ℝ → ℝ) (T T' : ℝ), IsBump g T → IsBump g' T' → IsBump (gconv g g') (T + T') := by
  intro g g' T T' hg hg'
  refine ⟨?_, ?_, ?_⟩
  · have hconv : gconv g g' = MeasureTheory.convolution g g' (ContinuousLinearMap.mul ℝ ℝ) volume := by
      funext r
      simp [gconv, MeasureTheory.convolution]
    rw [hconv]
    exact (hasCompactSupport_of_isBump hg').contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
      hg.1.continuous.locallyIntegrable hg'.1
  · intro r
    unfold gconv
    calc ∫ t, g t * g' (-r - t) = ∫ t, g (-t) * g' (-r - -t) := (integral_neg_eq_self _ _).symm
      _ = ∫ t, g t * g' (r - t) := by
        congr 1
        funext t
        rw [hg.2.1 t, show -r - -t = -(r - t) by ring, hg'.2.1]
  · intro r hr
    have hzero : ∀ t, g t * g' (r - t) = 0 := by
      intro t
      by_cases ht : T < |t|
      · rw [hg.2.2 t ht, zero_mul]
      · rw [hg'.2.2 (r - t) ?_, mul_zero]
        have h1 := abs_sub_abs_le_abs_sub r t
        have ht' := not_lt.mp ht
        linarith
    simp [gconv, hzero]

end GlobalTheory.CompanionTheory.WaveMult
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirOperatorFormula
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.Casimir

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem isOpen_GLs : IsOpen (GLs n) := by
  have hc : Continuous (fun g : Mat n => g.det) := Continuous.matrix_det continuous_id
  exact (isOpen_compl_singleton (x := (0 : ℂ))).preimage hc

theorem contDiff_mul_right (X : Mat n) : ContDiff ℝ ∞ (fun g : Mat n => g * X) :=
  ((LinearMap.mulRight ℝ X).toContinuousLinearMap).contDiff

theorem differentiableAt_Rd {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (X : Mat n) {g : Mat n}
    (hg : g ∈ GLs n) : DifferentiableAt ℝ (Rd X f) g := by
  have h1 := hf.fderiv_of_isOpen (m := 1) isOpen_GLs (by norm_cast)
  have h2 : ContDiffOn ℝ 1 (Rd X f) (GLs n) :=
    h1.clm_apply ((contDiff_mul_right X).contDiffOn.of_le (by norm_cast))
  exact (h2.contDiffAt (isOpen_GLs.mem_nhds hg)).differentiableAt (by norm_num)

theorem Rd_zero (X : Mat n) : Rd X (0 : Mat n → V) = 0 := by
  funext g
  have : fderiv ℝ (0 : Mat n → V) g = 0 := by
    simpa using fderiv_const_apply (𝕜 := ℝ) (x := g) (0 : V)
  simp [Rd, this]

theorem Eu_zero (s : Bool) (a b : Fin n) : Eu s a b (0 : Mat n → V) = 0 := by
  simp [Eu, Rd_zero]

theorem Epow_one (s : Bool) (c a : Fin n) (f : Mat n → V) : Epow s 1 c a f = Eu s c a f := by
  simp only [Epow]
  rw [Finset.sum_eq_single a]
  · simp
  · intro d _ hd
    simp [hd, Eu_zero]
  · simp

theorem Rd_comb (X : Mat n) (σ : ℂ) {u v : Mat n → V} {g : Mat n} (hu : DifferentiableAt ℝ u g)
    (hv : DifferentiableAt ℝ v g) :
    Rd X ((1 / 2 : ℂ) • (u + σ • v)) g = (1 / 2 : ℂ) • (Rd X u g + σ • Rd X v g) := by
  have hsv : DifferentiableAt ℝ (σ • v) g := hv.const_smul σ
  have h1 : fderiv ℝ ((1 / 2 : ℂ) • (u + σ • v)) g = (1 / 2 : ℂ) • fderiv ℝ (u + σ • v) g :=
    fderiv_const_smul (hu.add hsv) _
  have h2 : fderiv ℝ (u + σ • v) g = fderiv ℝ u g + fderiv ℝ (σ • v) g := fderiv_add hu hsv
  have h3 : fderiv ℝ (σ • v) g = σ • fderiv ℝ v g := fderiv_const_smul hv _
  show fderiv ℝ ((1 / 2 : ℂ) • (u + σ • v)) g (g * X) = _
  rw [h1, h2, h3]
  rfl

theorem comb_identity (P B C Q : V) :
    (2 : ℂ) • ((1 / 2 : ℂ) • ((1 / 2 : ℂ) • (P + (-Complex.I) • B) +
          (-Complex.I) • ((1 / 2 : ℂ) • (C + (-Complex.I) • Q))) +
        (1 / 2 : ℂ) • ((1 / 2 : ℂ) • (P + Complex.I • B) +
          Complex.I • ((1 / 2 : ℂ) • (C + Complex.I • Q)))) = P - Q := by
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem Eu_Eu {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (a c : Fin n) {g : Mat n}
    (hg : g ∈ GLs n) :
    Eu s a c (Eu s c a f) g =
      (1 / 2 : ℂ) • ((1 / 2 : ℂ) • (Rd (Matrix.single a c 1) (Rd (Matrix.single c a 1) f) g +
            (if s then -Complex.I else Complex.I) •
              Rd (Matrix.single a c 1) (Rd (Matrix.single c a Complex.I) f) g) +
        (if s then -Complex.I else Complex.I) •
          ((1 / 2 : ℂ) • (Rd (Matrix.single a c Complex.I) (Rd (Matrix.single c a 1) f) g +
            (if s then -Complex.I else Complex.I) •
              Rd (Matrix.single a c Complex.I) (Rd (Matrix.single c a Complex.I) f) g))) := by
  have hu := differentiableAt_Rd hf (Matrix.single c a (1 : ℂ)) hg
  have hv := differentiableAt_Rd hf (Matrix.single c a Complex.I) hg
  have e := fun X : Mat n => Rd_comb X (if s then -Complex.I else Complex.I) hu hv
  show ((1 / 2 : ℂ) • (Rd (Matrix.single a c 1) (Eu s c a f) +
    (if s then -Complex.I else Complex.I) • Rd (Matrix.single a c Complex.I) (Eu s c a f))) g = _
  simp only [Pi.smul_apply, Pi.add_apply]
  have e' : ∀ X : Mat n, Rd X (Eu s c a f) g = _ := e
  rw [e', e']

theorem omFormula : OmFormula := by
  intro n V _ _ f hf g hg
  have hgel : ∀ s : Bool, gel s 2 f g = ∑ a, ∑ c, Eu s a c (Eu s c a f) g := by
    intro s
    simp only [gel, Finset.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    have h2 : Epow s 2 a a f = ∑ c, Eu s a c (Epow s 1 c a f) := rfl
    simp only [h2, Finset.sum_apply, Epow_one]
  simp only [Om, Pi.smul_apply, Pi.add_apply, hgel]
  rw [← Finset.sum_add_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Eu_Eu hf true a c hg, Eu_Eu hf false a c hg]
  have key := comb_identity (V := V)
    (Rd (Matrix.single a c 1) (Rd (Matrix.single c a 1) f) g)
    (Rd (Matrix.single a c 1) (Rd (Matrix.single c a Complex.I) f) g)
    (Rd (Matrix.single a c Complex.I) (Rd (Matrix.single c a 1) f) g)
    (Rd (Matrix.single a c Complex.I) (Rd (Matrix.single c a Complex.I) f) g)
  simp only [↓reduceIte, Bool.false_eq_true]
  exact key

end GlobalTheory.CompanionTheory.Casimir
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartAndRightWordsSmooth
section
open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.SobGL.Smooth

theorem isOpen_GLs' (n : ℕ) : IsOpen (GLs n) := by
  have : Continuous fun g : Mat n => g.det := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage this

theorem continuous_cm' (n : ℕ) : Continuous (cm (n := n)) := by
  unfold cm
  exact continuous_finsetSum _ fun p _ => (continuous_apply p).smul continuous_const

theorem cm_zero' (n : ℕ) : cm (n := n) 0 = 0 := by
  simp [cm]

def mulRight' {n : ℕ} (X : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)

theorem contDiffOn_fderiv_apply' {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) {A : E → E} (hA : ContDiffOn ℝ ∞ A U) :
    ContDiffOn ℝ ∞ (fun g => fderiv ℝ f g (A g)) U := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  exact h1.clm_apply hA

theorem Rw_contDiffOn' {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (w : List (Idx n)) :
    ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih =>
    exact contDiffOn_fderiv_apply' (isOpen_GLs' n) ih (mulRight' (bs p)).contDiff.contDiffOn

theorem Dw_contDiffOn' {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (L : List (Idx n)) :
    ContDiffOn ℝ ∞ (Dw L f) (GLs n) := by
  induction L with
  | nil => exact hf
  | cons p L ih =>
    exact contDiffOn_fderiv_apply' (isOpen_GLs' n) ih contDiffOn_const

theorem smooth_all : ∀ n : ℕ, IsOpen (GLs n) ∧ Continuous (cm (n := n)) ∧ cm (n := n) 0 = 0 ∧
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) →
      (∀ w, ContDiffOn ℝ ∞ (Rw w f) (GLs n)) ∧ ∀ L : List (Idx n), ContDiffOn ℝ ∞ (Dw L f) (GLs n) :=
  fun n => ⟨isOpen_GLs' n, continuous_cm' n, cm_zero' n, fun _ _ _ _ hf =>
    ⟨Rw_contDiffOn' hf, Dw_contDiffOn' hf⟩⟩

end GlobalTheory.CompanionTheory.SobGL.Smooth
end
end

