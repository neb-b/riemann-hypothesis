module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ComplexMinusRealLineMeasureCoordinates

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ARpowHalfSq
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.AutomorphyFactorLemmas

open UpperTheory.Esk

theorem a_sq_rpow {n : ℝ} (hn : 0 ≤ n) (k : ℕ) : (n ^ 2) ^ ((k : ℝ) / 2) = n ^ k := by
  rw [← Real.rpow_natCast n 2, ← Real.rpow_mul hn, ← Real.rpow_natCast n k]
  congr 1
  push_cast <;> ring

theorem a_rpow_half_sq {a : ℝ} (ha : 0 ≤ a) (k : ℕ) : a ^ ((k : ℝ) / 2) * a ^ ((k : ℝ) / 2) = a ^ k := by
  rw [← Real.mul_rpow ha ha, ← sq, a_sq_rpow ha]

theorem p5 (k : ℕ) (g : GL (Fin 2) ℝ) (z : P) : ‖j1 k g z‖ * |(g • z).1.im| ^ ((k : ℝ) / 2) = |z.1.im| ^ ((k : ℝ) / 2) := by
  have hden : den g z.1 ≠ 0 := den_ne g z.2
  have hD : 0 < ‖den g z.1‖ := norm_pos_iff.mpr hden
  have hdet : 0 < |g.val.det| := abs_pos.mpr g.det_ne_zero
  have him : (g • z).1.im = g.val.det * z.1.im / Complex.normSq (den g z.1) := by
    rw [coe_smul, im_div]
  have hns : Complex.normSq (den g z.1) = ‖den g z.1‖ ^ 2 := Complex.normSq_eq_norm_sq _
  have habs : |(g • z).1.im| = |g.val.det| * |z.1.im| / ‖den g z.1‖ ^ 2 := by
    rw [him, hns, abs_div, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖den g z.1‖ ^ 2)]
  have hj : ‖j1 k g z‖ = ‖den g z.1‖ ^ k * |g.val.det| ^ (-(k : ℝ) / 2) := by
    rw [j1, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  have hinv : |g.val.det| ^ (-(k : ℝ) / 2) * |g.val.det| ^ ((k : ℝ) / 2) = 1 := by
    rw [neg_div, Real.rpow_neg (abs_nonneg _), inv_mul_cancel₀ (Real.rpow_pos_of_pos hdet _).ne']
  have hDk : ‖den g z.1‖ ^ k ≠ 0 := pow_ne_zero _ hD.ne'
  rw [hj, habs, Real.div_rpow (by positivity) (by positivity), Real.mul_rpow (abs_nonneg _) (abs_nonneg _),
    a_sq_rpow (norm_nonneg _)]
  rw [show ∀ A B C E : ℝ, A * B * (C * E / A) = (B * C) * E * (A / A) from fun _ _ _ _ => by ring,
    hinv, div_self hDk, one_mul, mul_one]

theorem a_sub_conj_ne (z w : P) (h : 0 < z.1.im * w.1.im) : z.1 - conj w.1 ≠ 0 := by
  intro h0
  have him := congrArg Complex.im h0
  simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at him
  have hzw : z.1.im = -w.1.im := by linarith
  rw [hzw] at h
  nlinarith [sq_nonneg w.1.im]

theorem p6 (k : ℕ) (z w : P) (hk : 1 ≤ k) : ‖q1 k z w‖ * |z.1.im| ^ ((k : ℝ) / 2) = ((k : ℝ) - 1) / (4 * Real.pi) * kap z w ^ ((k : ℝ) / 2) * |w.1.im| ^ ((k : ℝ) / 2) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (k : ℝ) / 2 ≠ 0 := by
    intro h0
    linarith
  by_cases h : 0 < z.1.im * w.1.im
  · have hq : q1 k z w = ((k : ℂ) - 1) / (4 * Real.pi) * ((w.1 - conj w.1) / (z.1 - conj w.1)) ^ k := by
      rw [q1, if_pos h]
    have hkap : kap z w = 4 * (z.1.im * w.1.im) / ‖z.1 - conj w.1‖ ^ 2 := by
      rw [kap, if_pos h]
    have hd : z.1 - conj w.1 ≠ 0 := a_sub_conj_ne z w h
    have hdn : 0 < ‖z.1 - conj w.1‖ := norm_pos_iff.mpr hd
    have hww : ‖w.1 - conj w.1‖ = 2 * |w.1.im| := by
      rw [Complex.sub_conj, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_two]
    have hc : ‖((k : ℂ) - 1) / (4 * Real.pi)‖ = ((k : ℝ) - 1) / (4 * Real.pi) := by
      have hpi := Real.pi_pos
      have e : ((k : ℂ) - 1) / (4 * Real.pi) = ((((k : ℝ) - 1) / (4 * Real.pi) : ℝ) : ℂ) := by
        push_cast <;> ring
      rw [e, Complex.norm_real, Real.norm_of_nonneg (by apply div_nonneg <;> linarith)]
    have hzw : z.1.im * w.1.im = |z.1.im| * |w.1.im| := by
      rw [← abs_mul, abs_of_pos h]
    have h4 : (4 : ℝ) ^ ((k : ℝ) / 2) = 2 ^ k := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, a_sq_rpow (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hq, norm_mul, hc, norm_pow, norm_div, hww, hkap, hzw,
      Real.div_rpow (by positivity) (by positivity), a_sq_rpow hdn.le,
      Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow (abs_nonneg _) (abs_nonneg _), h4,
      div_pow, mul_pow, ← a_rpow_half_sq (abs_nonneg w.1.im) k]
    ring
  · have hq : q1 k z w = 0 := by
      rw [q1, if_neg h]
    have hkap : kap z w = 0 := by
      rw [kap, if_neg h]
    rw [hq, hkap, norm_zero, zero_mul, Real.zero_rpow hk0, mul_zero, zero_mul]

end UpperTheory.Esk.AutomorphyFactorLemmas
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ActionIntegralSwapProof
section
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UpperTheory.Esk.AnnihilatorQuotientResidues

variable {G Y : Type} [Group G] [MeasurableSpace Y] [MulAction G Y] {μ : Measure Y}

def actEquiv (hP : Pres G μ) (g : G) : Y ≃ᵐ Y where
  toEquiv := MulAction.toPerm g
  measurable_toFun := (hP g).measurable
  measurable_invFun := (hP g⁻¹).measurable

lemma embed (hP : Pres G μ) (g : G) : MeasurableEmbedding (fun y : Y => g • y) :=
  (actEquiv hP g).measurableEmbedding

lemma enorm_cut {b : Y → ℝ} (hb : IsCut G b) (y : Y) (x : ℂ) :
    ‖b y • x‖ₑ = ENNReal.ofReal (b y) * ‖x‖ₑ := by
  rw [enorm_smul, Real.enorm_eq_ofReal (hb.nonneg y)]

lemma lint_split [Countable G] (hP : Pres G μ) {b b' : Y → ℝ} (hb : IsCut G b) (hb' : IsCut G b')
    (u : Y → ℝ≥0∞) (hu : Measurable u) :
    ∫⁻ y, ENNReal.ofReal (b y) * u y ∂μ
      = ∑' g : G, ∫⁻ y, ENNReal.ofReal (b' (g • y)) * (ENNReal.ofReal (b y) * u y) ∂μ := by
  rw [← lintegral_tsum]
  · congr 1
    funext y
    rw [ENNReal.tsum_mul_right, ← ENNReal.ofReal_tsum_of_nonneg (fun g => hb'.nonneg _)
      (hb'.sum y).summable, (hb'.sum y).tsum_eq, ENNReal.ofReal_one, one_mul]
  · intro g
    exact ((ENNReal.measurable_ofReal.comp (hb'.meas.comp (hP g).measurable)).mul
      ((ENNReal.measurable_ofReal.comp hb.meas).mul hu)).aemeasurable

lemma lint_term (hP : Pres G μ) {b b' : Y → ℝ} (u : Y → ℝ≥0∞)
    (hinv : ∀ (g : G) y, u (g • y) = u y) (g : G) :
    ∫⁻ y, ENNReal.ofReal (b' (g • y)) * (ENNReal.ofReal (b y) * u y) ∂μ
      = ∫⁻ y, ENNReal.ofReal (b (g⁻¹ • y)) * (ENNReal.ofReal (b' y) * u y) ∂μ := by
  have h := (hP g).lintegral_comp_emb (embed hP g)
    (fun z => ENNReal.ofReal (b (g⁻¹ • z)) * (ENNReal.ofReal (b' z) * u z))
  rw [← h]
  congr 1
  funext y
  simp only [inv_smul_smul, hinv, mul_left_comm]

lemma lint_eq [Countable G] (hP : Pres G μ) {b b' : Y → ℝ} (hb : IsCut G b) (hb' : IsCut G b')
    (u : Y → ℝ≥0∞) (hu : Measurable u) (hinv : ∀ (g : G) y, u (g • y) = u y) :
    ∫⁻ y, ENNReal.ofReal (b y) * u y ∂μ = ∫⁻ y, ENNReal.ofReal (b' y) * u y ∂μ := by
  rw [lint_split hP hb hb' u hu, lint_split hP hb' hb u hu]
  calc _ = ∑' g : G, ∫⁻ y, ENNReal.ofReal (b (g⁻¹ • y)) * (ENNReal.ofReal (b' y) * u y) ∂μ :=
        tsum_congr (lint_term hP u hinv)
    _ = _ := (Equiv.inv G).tsum_eq
        (fun g => ∫⁻ y, ENNReal.ofReal (b (g • y)) * (ENNReal.ofReal (b' y) * u y) ∂μ)

lemma integrable_swap [Countable G] (hP : Pres G μ) {b b' : Y → ℝ} (hb : IsCut G b) (hb' : IsCut G b')
    (u : Y → ℂ) (hu : Measurable u) (hinv : ∀ (g : G) y, u (g • y) = u y)
    (hi : Integrable (fun y => b y • u y) μ) : Integrable (fun y => b' y • u y) μ := by
  refine ⟨(hb'.meas.smul hu).aestronglyMeasurable, ?_⟩
  have h := hi.hasFiniteIntegral
  have e := lint_eq hP hb hb' (fun y => ‖u y‖ₑ) hu.enorm (fun g y => by simp only [hinv])
  simp only [HasFiniteIntegral, enorm_cut hb, enorm_cut hb'] at h ⊢
  rwa [← e]

lemma int_split [Countable G] (hP : Pres G μ) {b b' : Y → ℝ} (hb : IsCut G b) (hb' : IsCut G b')
    (u : Y → ℂ) (hu : Measurable u) (hi : Integrable (fun y => b y • u y) μ) :
    ∫ y, b y • u y ∂μ = ∑' g : G, ∫ y, b' (g • y) • (b y • u y) ∂μ := by
  rw [← integral_tsum]
  · congr 1
    funext y
    rw [(hb'.sum y).summable.tsum_smul_const, (hb'.sum y).tsum_eq, one_smul]
  · intro g
    exact ((hb'.meas.comp (hP g).measurable).smul (hb.meas.smul hu)).aestronglyMeasurable
  · have h := hi.hasFiniteIntegral
    have e := lint_split hP hb hb' (fun y => ‖u y‖ₑ) hu.enorm
    simp only [HasFiniteIntegral, enorm_cut hb, enorm_cut hb'] at h e ⊢
    rw [← e]
    exact h.ne

lemma int_term (hP : Pres G μ) {b b' : Y → ℝ} (u : Y → ℂ)
    (hinv : ∀ (g : G) y, u (g • y) = u y) (g : G) :
    ∫ y, b' (g • y) • (b y • u y) ∂μ = ∫ y, b (g⁻¹ • y) • (b' y • u y) ∂μ := by
  have h := (hP g).integral_comp (embed hP g) (fun z => b (g⁻¹ • z) • (b' z • u z))
  rw [← h]
  congr 1
  funext y
  rw [inv_smul_smul, hinv, smul_comm]

lemma int_eq [Countable G] (hP : Pres G μ) {b b' : Y → ℝ} (hb : IsCut G b) (hb' : IsCut G b')
    (u : Y → ℂ) (hu : Measurable u) (hinv : ∀ (g : G) y, u (g • y) = u y)
    (hi : Integrable (fun y => b y • u y) μ) (hi' : Integrable (fun y => b' y • u y) μ) :
    ∫ y, b y • u y ∂μ = ∫ y, b' y • u y ∂μ := by
  rw [int_split hP hb hb' u hu hi, int_split hP hb' hb u hu hi']
  calc _ = ∑' g : G, ∫ y, b (g⁻¹ • y) • (b' y • u y) ∂μ := tsum_congr (int_term hP u hinv)
    _ = _ := (Equiv.inv G).tsum_eq (fun g => ∫ y, b (g • y) • (b' y • u y) ∂μ)

end UpperTheory.Esk.AnnihilatorQuotientResidues

theorem UpperTheory.Esk.action_integral_swap_proof : UpperTheory.Esk.C1 := by
  intro G Y _ _ _ _ μ hP b b' hb hb'
  refine ⟨fun u hu hinv => UpperTheory.Esk.AnnihilatorQuotientResidues.lint_eq hP hb hb' u hu hinv, fun u hu hinv hi => ?_⟩
  have hi' := UpperTheory.Esk.AnnihilatorQuotientResidues.integrable_swap hP hb hb' u hu hinv hi
  exact ⟨hi', UpperTheory.Esk.AnnihilatorQuotientResidues.int_eq hP hb hb' u hu hinv hi hi'⟩
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.BNeg
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.AutomorphyFactorLemmas

open UpperTheory.Esk

theorem b_cv : Continuous (fun z : P => z.1) := by
  exact continuous_subtype_val

theorem b_ne (z w : ℂ) (h : 0 < z.im * w.im) : z - conj w ≠ 0 := by
  intro h0
  have h1 := congrArg Complex.im h0
  simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at h1
  have h2 : w.im = -z.im := by linarith
  rw [h2] at h
  nlinarith [mul_self_nonneg z.im]

theorem b_neg (z w : P) (h : ¬ 0 < z.1.im * w.1.im) : z.1.im * w.1.im < 0 := by
  have hne : z.1.im * w.1.im ≠ 0 := mul_ne_zero z.2 w.2
  exact lt_of_le_of_ne (not_lt.mp h) hne

theorem p7 (k : ℕ) (g : GL (Fin 2) ℝ) : Continuous (j1 k g) := by
  unfold j1 den
  exact (((continuous_const.mul b_cv).add continuous_const).pow k).mul continuous_const

theorem p8 (k : ℕ) : Continuous fun p : P × P => q1 k p.1 p.2 := by
  have hz : Continuous fun p : P × P => p.1.1 := b_cv.comp continuous_fst
  have hw : Continuous fun p : P × P => p.2.1 := b_cv.comp continuous_snd
  have hf : Continuous fun p : P × P => p.1.1.im * p.2.1.im :=
    (Complex.continuous_im.comp hz).mul (Complex.continuous_im.comp hw)
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : 0 < p.1.1.im * p.2.1.im
  · have hU : ∀ᶠ q in nhds p, 0 < q.1.1.im * q.2.1.im := (hf.tendsto p).eventually (lt_mem_nhds hp)
    have hg : ContinuousAt (fun q : P × P =>
        ((k : ℂ) - 1) / (4 * Real.pi) * ((q.2.1 - conj q.2.1) / (q.1.1 - conj q.2.1)) ^ k) p := by
      apply ContinuousAt.mul continuousAt_const
      apply ContinuousAt.pow
      apply ContinuousAt.div
      · exact (hw.sub (Complex.continuous_conj.comp hw)).continuousAt
      · exact (hz.sub (Complex.continuous_conj.comp hw)).continuousAt
      · exact b_ne _ _ hp
    apply hg.congr
    filter_upwards [hU] with q hq
    simp only [q1, if_pos hq]
  · have hV : ∀ᶠ q in nhds p, q.1.1.im * q.2.1.im < 0 :=
      (hf.tendsto p).eventually (gt_mem_nhds (b_neg p.1 p.2 hp))
    have hg : ContinuousAt (fun _ : P × P => (0 : ℂ)) p := continuousAt_const
    apply hg.congr
    filter_upwards [hV] with q hq
    simp only [q1, if_neg (not_lt.mpr hq.le)]

theorem p9 (k : ℕ) (w : P) : Hol1 fun z => q1 k z w := by
  intro t ht
  have ht' : t.im ≠ 0 := ht
  apply DifferentiableAt.differentiableWithinAt
  have hcont : Continuous fun s : ℂ => s.im * w.1.im := Complex.continuous_im.mul continuous_const
  by_cases hp : 0 < t.im * w.1.im
  · have hU : ∀ᶠ s in nhds t, 0 < s.im * w.1.im := (hcont.tendsto t).eventually (lt_mem_nhds hp)
    have hd : DifferentiableAt ℂ (fun s : ℂ =>
        ((k : ℂ) - 1) / (4 * Real.pi) * ((w.1 - conj w.1) / (s - conj w.1)) ^ k) t := by
      apply DifferentiableAt.mul (differentiableAt_const _)
      apply DifferentiableAt.pow
      apply DifferentiableAt.div (differentiableAt_const _) (differentiableAt_id.sub (differentiableAt_const _))
      exact b_ne _ _ hp
    apply hd.congr_of_eventuallyEq
    filter_upwards [hU] with s hs
    have hs' : s.im ≠ 0 := fun h0 => by rw [h0, zero_mul] at hs; exact lt_irrefl _ hs
    simp only [ext1, dif_pos hs', q1, if_pos hs]
  · have hneg : t.im * w.1.im < 0 := lt_of_le_of_ne (not_lt.mp hp) (mul_ne_zero ht' w.2)
    have hV : ∀ᶠ s in nhds t, s.im * w.1.im < 0 := (hcont.tendsto t).eventually (gt_mem_nhds hneg)
    apply (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq
    filter_upwards [hV] with s hs
    by_cases hs' : s.im ≠ 0
    · simp only [ext1, dif_pos hs', q1, if_neg (not_lt.mpr hs.le)]
    · simp only [ext1, dif_neg hs']

end UpperTheory.Esk.AutomorphyFactorLemmas
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.CountingMeasureInvarianceProof
section
noncomputable section

open MeasureTheory

namespace UpperTheory.Esk.CountingMeasureInvariance

variable {G Ω X : Type} [Group G] [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω] [Countable Ω]
  [MeasurableSpace X] [MulAction G Ω] [MulAction G X]

theorem meas_of_left {f : Ω × X → ℝ} (hf : ∀ ω, Measurable fun x => f (ω, x)) : Measurable f := by
  intro s hs
  have : f ⁻¹' s = ⋃ ω : Ω, ({ω} : Set Ω) ×ˢ ((fun x => f (ω, x)) ⁻¹' s) := by
    ext ⟨ω, x⟩; simp
  rw [this]
  exact MeasurableSet.iUnion fun ω => (MeasurableSet.of_discrete (s := {ω})).prod (hf ω hs)

omit [Countable Ω] in
theorem count_pres (g : G) :
    MeasurePreserving (fun ω : Ω => g • ω) Measure.count Measure.count := by
  have hm : ∀ h : G, Measurable (fun ω : Ω => h • ω) := fun h => Measurable.of_discrete
  refine ⟨hm g, le_antisymm ((MulAction.injective g).map_count_le (hm g)) ?_⟩
  calc (Measure.count : Measure Ω)
      = (Measure.count.map (fun ω : Ω => g⁻¹ • ω)).map (fun ω => g • ω) := by
        rw [Measure.map_map (hm g) (hm g⁻¹)]
        simp [Function.comp_def]
    _ ≤ Measure.count.map (fun ω : Ω => g • ω) :=
        Measure.map_mono ((MulAction.injective g⁻¹).map_count_le (hm _)) (hm g)

theorem pres_prod (μ : Measure X) [SigmaFinite μ] (hμ : Pres G μ) :
    Pres G ((Measure.count : Measure Ω).prod μ) := fun g =>
  (count_pres g).prod (hμ g)


open Classical in
def cut (R : Set Ω) (β : Ω → X → ℝ) (p : Ω × X) : ℝ := by
  classical
  exact if p.1 ∈ R then β p.1 p.2 else 0

theorem cut_isCut (R : Set Ω) (hR : ∀ ω, ∃! r, r ∈ R ∧ r ∈ MulAction.orbit G ω) (β : Ω → X → ℝ)
    (hβ : ∀ r ∈ R, IsCut (MulAction.stabilizer G r) (β r)) : IsCut G (cut R β) := by
  refine ⟨?_, ?_, ?_⟩
  · refine meas_of_left fun ω => ?_
    by_cases h : ω ∈ R
    · simpa [cut, h] using (hβ ω h).meas
    · simp [cut, h]
  · rintro ⟨ω, x⟩
    unfold cut
    split_ifs with h
    · exact (hβ _ h).nonneg x
    · exact le_rfl
  · rintro ⟨ω, x⟩
    obtain ⟨r, ⟨hrR, g₀, hg₀'⟩, hu⟩ := hR ω
    have hg₀ : g₀ • ω = r := hg₀'
    have key : ∀ g : G, g • ω ∈ R → g • ω = r := fun g hg => hu _ ⟨hg, MulAction.mem_orbit ω g⟩
    let e : MulAction.stabilizer G r → G := fun s => (s : G) * g₀
    have he : Function.Injective e := fun s t h => Subtype.ext (mul_right_cancel h)
    rw [← he.hasSum_iff]
    · convert (hβ r hrR).sum (g₀ • x) using 1
      funext s
      have hs : (s : G) • r = r := s.2
      have h2 : ((s : G) * g₀) • ω = r := by rw [mul_smul, hg₀, hs]
      simp only [Function.comp_apply, e, cut, Prod.smul_mk, h2, mul_smul, Subgroup.smul_def]
      split_ifs with hc
      · rfl
      · exact absurd (h2.symm ▸ hrR) hc
    · intro g hg
      simp only [cut, Prod.smul_mk]
      rw [ite_eq_right]
      intro hgR
      apply hg
      refine ⟨⟨g * g₀⁻¹, ?_⟩, ?_⟩
      · rw [MulAction.mem_stabilizer_iff, mul_smul, ← hg₀, inv_smul_smul, key g hgR, hg₀]
      · simp [e]

end UpperTheory.Esk.CountingMeasureInvariance

open UpperTheory.Esk.CountingMeasureInvariance in
theorem UpperTheory.Esk.counting_measure_invariance_proof : UpperTheory.Esk.C1 → UpperTheory.Esk.C4 := by
  intro hC1 G Ω X _ _ _ _ _ _ _ _ μ _ hμ b hb u hu hinv hint R hR β hβ
  have hP : Pres G ((Measure.count : Measure Ω).prod μ) := pres_prod μ hμ
  have hb' := cut_isCut R hR β hβ
  obtain ⟨hI', hE⟩ := (hC1 G (Ω × X) ((Measure.count : Measure Ω).prod μ) hP b (cut R β) hb hb').2
    u hu hinv hint
  have hsec : ∀ ω, Integrable (fun x => cut R β (ω, x) • u (ω, x)) μ := by
    have := hI'.prod_right_ae
    rwa [Measure.ae_count_iff] at this
  have hF : Integrable (fun ω => ∫ x, cut R β (ω, x) • u (ω, x) ∂μ) Measure.count :=
    hI'.integral_prod_left
  have hsum : HasSum (fun ω => ∫ x, cut R β (ω, x) • u (ω, x) ∂μ)
      (∫ y, b y • u y ∂((Measure.count : Measure Ω).prod μ)) := by
    rw [hE, integral_prod _ hI', integral_countable hF]
    simp only [count_real_singleton, one_smul]
    exact (integrable_count_iff.mp hF).of_norm.hasSum
  refine ⟨fun r hr => by simpa [cut, hr] using hsec r, ?_⟩
  have hsupp : Function.support (fun ω => ∫ x, cut R β (ω, x) • u (ω, x) ∂μ) ⊆ R := by
    intro ω hω
    by_contra h
    apply hω
    simp [cut, h]
  rw [← hasSum_subtype_iff_of_support_subset hsupp] at hsum
  convert hsum using 1
  funext r
  simp [cut, r.2]
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.Imports
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.RadialIntegralLemmas
open UpperTheory.Esk

def F (k : ℕ) (g : GL (Fin 2) ℝ) (z : P) : ℂ := q1 k z (g • z) * j1 k g z

def U (k : ℕ) (g : GL (Fin 2) ℝ) (z : P) : ℂ := if 0 < z.1.im then F k g z else 0

def eta (a b : ℝ) : ℂ := ((a : ℂ) - b * Complex.I) / (Real.sqrt (a ^ 2 + b ^ 2) : ℂ)

end UpperTheory.Esk.RadialIntegralLemmas
end
end

