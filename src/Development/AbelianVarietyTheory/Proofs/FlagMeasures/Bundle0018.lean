module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardHermitianMatricesDvdSq
section
open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

theorem card_hermitian_dvd_sq {A : Type} [CommRing A] [Finite A] (c : A →+* A)
    (hc : ∀ u, c (c u) = u) (ω : A) (hω : IsUnit (ω - c ω)) (p : A) (hp : c p = p) (m : ℕ) :
    Nat.card {H : Matrix (Fin m) (Fin m) A // (∀ a b, c (H b a) = H a b) ∧ ∀ a b, p ∣ H a b} ^ 2
      = Nat.card {u : A // p ∣ u} ^ (m * m) := by
  have hmem : ∀ u : A, u ∈ Ideal.span {p} → c u ∈ Ideal.span {p} := by
    intro u hu
    rw [Ideal.mem_span_singleton] at hu ⊢
    have := map_dvd c hu
    rwa [hp] at this
  let σ : (Fin m → Fin m → Ideal.span {p}) →+ (Fin m → Fin m → Ideal.span {p}) :=
    { toFun := fun H a b => ⟨c (H b a).1, hmem _ (H b a).2⟩
      map_zero' := by
        funext a b
        exact Subtype.ext (by simp)
      map_add' := fun H K => by
        funext a b
        exact Subtype.ext (by simp) }
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    funext a b
    exact Subtype.ext (hc _)
  have hs : ∀ (r : A) x, σ (r • x) = c r • σ x := fun r x => by
    funext a b
    exact Subtype.ext (map_mul c r _)
  have h := (card_fixed_sq c hc hω σ hσ hs).1
  let e : {H : Matrix (Fin m) (Fin m) A // (∀ a b, c (H b a) = H a b) ∧ ∀ a b, p ∣ H a b} ≃
      {x : Fin m → Fin m → Ideal.span {p} // σ x = x} :=
    { toFun := fun H => ⟨fun a b => ⟨H.1 a b, Ideal.mem_span_singleton.2 (H.2.2 a b)⟩, by
        funext a b
        exact Subtype.ext (H.2.1 a b)⟩
      invFun := fun x => ⟨fun a b => (x.1 a b).1,
        fun a b => congrArg Subtype.val (congrFun (congrFun x.2 a) b),
        fun a b => Ideal.mem_span_singleton.1 (x.1 a b).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have e2 : {u : A // p ∣ u} ≃ Ideal.span {p} :=
    Equiv.subtypeEquivRight fun u => Ideal.mem_span_singleton.symm
  rw [Nat.card_congr e, h, Nat.card_congr e2, Nat.card_fun, Nat.card_fun, ← pow_mul]
  simp

end GlobalTheory.GramCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClassNumberLeMinkowskiCount
section
open NumberField

namespace GlobalTheory

theorem classNumber_le_minkowski_count :
    ∀ (K : Type) [Field K] [NumberField K], (classNumber K : ℝ) ≤
      Real.sqrt |(discr K : ℝ)| * (1 + Real.log (Real.sqrt |(discr K : ℝ)|)) ^ Module.finrank ℚ K :=
  fun K _ _ => classNumber_le_sqrt_discr_mul_pow K

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousAtZeroOfSqueezePowBounds
section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace GlobalTheory

theorem squeeze_continuousAt_zero (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (d : ℕ)
    (f : V → ℝ≥0∞) (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ η : ℝ, 0 < η ∧ ∀ x : V, ‖x‖ < η →
      ENNReal.ofReal ((1 + ε)⁻¹ ^ d) * c ≤ f x ∧ f x ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ d) * c) :
    f 0 = c ∧ ContinuousAt f 0 := by
  have h1 : Tendsto (fun ε : ℝ => (1 + ε)⁻¹ ^ d) (𝓝 0) (𝓝 1) := by
    have : ContinuousAt (fun ε : ℝ => (1 + ε)⁻¹ ^ d) 0 :=
      ((continuous_const.add continuous_id).continuousAt.inv₀ (by
        change (1 + 0 : ℝ) ≠ 0
        simpa only [add_zero] using (one_ne_zero : (1 : ℝ) ≠ 0))).pow d
    simpa using this.tendsto
  have h2 : Tendsto (fun ε : ℝ => ((1 + ε) / (1 - ε)) ^ d) (𝓝 0) (𝓝 1) := by
    have : ContinuousAt (fun ε : ℝ => ((1 + ε) / (1 - ε)) ^ d) 0 :=
      ((continuous_const.add continuous_id).continuousAt.div
        (continuous_const.sub continuous_id).continuousAt (by
          change (1 - 0 : ℝ) ≠ 0
          simpa only [sub_zero] using (one_ne_zero : (1 : ℝ) ≠ 0))).pow d
    simpa using this.tendsto
  have hL : Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 + ε)⁻¹ ^ d) * c) (𝓝 0) (𝓝 c) := by
    have := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1) (Or.inr hc)
    simpa using this
  have hU : Tendsto (fun ε : ℝ => ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ d) * c) (𝓝 0) (𝓝 c) := by
    have := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h2) (Or.inr hc)
    simpa using this
  have hI : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT zero_lt_one
  have hf : Tendsto f (𝓝 0) (𝓝 c) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      have e1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), a < ENNReal.ofReal ((1 + ε)⁻¹ ^ d) * c :=
        nhdsWithin_le_nhds (hL.eventually (lt_mem_nhds ha))
      obtain ⟨ε, hε, hεI⟩ := (e1.and hI).exists
      obtain ⟨η, hη, hx⟩ := h ε hεI.1 hεI.2
      filter_upwards [Metric.ball_mem_nhds (0 : V) hη] with x hxb
      rw [mem_ball_zero_iff] at hxb
      exact lt_of_lt_of_le hε (hx x hxb).1
    · intro a ha
      have e1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ d) * c < a :=
        nhdsWithin_le_nhds (hU.eventually (gt_mem_nhds ha))
      obtain ⟨ε, hε, hεI⟩ := (e1.and hI).exists
      obtain ⟨η, hη, hx⟩ := h ε hεI.1 hεI.2
      filter_upwards [Metric.ball_mem_nhds (0 : V) hη] with x hxb
      rw [mem_ball_zero_iff] at hxb
      exact lt_of_le_of_lt (hx x hxb).2 hε
  have h0 : f 0 = c := tendsto_nhds_unique (tendsto_pure_nhds f 0) (hf.mono_left (pure_le_nhds 0))
  refine ⟨h0, ?_⟩
  unfold ContinuousAt
  rw [h0]
  exact hf

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CumulantLowerBoundOfBoundedCentred
section
open Matrix Finset Real

namespace GlobalTheory

theorem cumulant_lower_bound_of_bounded_centred :
    ∀ (ι : Type) [Fintype ι] (w y : ι → ℝ) (R : ℝ), 0 < R → (∀ J, 0 ≤ w J) → ∑ J, w J = 1 →
      ∑ J, w J * y J = 0 → (∀ J, w J ≠ 0 → |y J| ≤ R) →
      min 1 (1 / R) * (∑ J, w J * y J ^ 2) / 4 ≤ Real.log (∑ J, w J * Real.exp (y J)) := by
  intro ι _ w y R hR hw hs hm hb
  obtain ⟨hexp, hlog⟩ := _root_.GlobalTheory.exp_quadratic_lower_and_log_linear_lower
  set t : ℝ := min 1 (1 / R) with ht
  set V : ℝ := ∑ J, w J * y J ^ 2 with hV
  set S : ℝ := ∑ J, w J * Real.exp (y J) with hS
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have htR : t * R ≤ 1 := by
    have : t ≤ 1 / R := min_le_right _ _
    rwa [le_div_iff₀ hR] at this
  have hty : ∀ J, w J ≠ 0 → |t * y J| ≤ 1 := by
    intro J hJ
    rw [abs_mul, abs_of_pos ht0]
    exact (mul_le_mul_of_nonneg_left (hb J hJ) ht0.le).trans htR
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun J _ => mul_nonneg (hw J) (sq_nonneg _)
  have htV : t ^ 2 * V ≤ 1 := by
    rw [hV, Finset.mul_sum, ← hs]
    refine Finset.sum_le_sum fun J _ => ?_
    by_cases hJ : w J = 0
    · simp [hJ]
    · have h1 : (t * y J) ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one _).2 (hty J hJ)
      have := mul_le_mul_of_nonneg_left h1 (hw J)
      nlinarith
  have hlow : 1 + t ^ 2 * V / 3 ≤ ∑ J, w J * Real.exp (t * y J) := by
    have e : 1 + t ^ 2 * V / 3 = ∑ J, w J * (1 + t * y J + (t * y J) ^ 2 / 3) := by
      have e2 : ∀ J, w J * (1 + t * y J + (t * y J) ^ 2 / 3)
          = w J + t * (w J * y J) + t ^ 2 / 3 * (w J * y J ^ 2) := fun J => by ring
      simp only [e2, Finset.sum_add_distrib, ← Finset.mul_sum, hs, hm]
      rw [← hV]; ring
    rw [e]
    refine Finset.sum_le_sum fun J _ => ?_
    by_cases hJ : w J = 0
    · simp [hJ]
    · exact mul_le_mul_of_nonneg_left (hexp _ (hty J hJ)) (hw J)
  have hS1 : 1 ≤ S := by
    have : ∑ J, w J * (y J + 1) = 1 := by
      simp only [mul_add, mul_one, Finset.sum_add_distrib, hs, hm, zero_add]
    rw [← this]
    exact Finset.sum_le_sum fun J _ =>
      mul_le_mul_of_nonneg_left (Real.add_one_le_exp _) (hw J)
  have hS0 : 0 < S := by linarith
  set F : ℝ := Real.log S with hF
  have hEF : Real.exp F = S := Real.exp_log hS0
  have hpt : ∀ J, Real.exp (t * y J)
      ≤ Real.exp (t * F) * (t * (Real.exp (y J) / S) + (1 - t)) := by
    intro J
    have h := convexOn_exp.2 (Set.mem_univ (y J - F)) (Set.mem_univ 0) ht0.le
      (sub_nonneg.2 ht1) (by ring)
    simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at h
    rw [Real.exp_sub, hEF] at h
    have e : t * y J = t * F + t * (y J - F) := by ring
    rw [e, Real.exp_add]
    exact mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
  have hup : ∑ J, w J * Real.exp (t * y J) ≤ Real.exp (t * F) := by
    calc ∑ J, w J * Real.exp (t * y J)
        ≤ ∑ J, w J * (Real.exp (t * F) * (t * (Real.exp (y J) / S) + (1 - t))) :=
          Finset.sum_le_sum fun J _ => mul_le_mul_of_nonneg_left (hpt J) (hw J)
      _ = ∑ J, (Real.exp (t * F) * t / S * (w J * Real.exp (y J))
            + Real.exp (t * F) * (1 - t) * w J) :=
          Finset.sum_congr rfl fun J _ => by ring
      _ = Real.exp (t * F) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs, ← hS]
          field_simp
          ring
  have hu0 : 0 ≤ t ^ 2 * V / 3 := by positivity
  have h1 := hlog (t ^ 2 * V / 3) hu0 (by linarith)
  have h2 : Real.log (1 + t ^ 2 * V / 3) ≤ t * F := by
    rw [Real.log_le_iff_le_exp (by linarith)]
    exact hlow.trans hup
  have h3 : t * (t * V / 4) ≤ t * F := by nlinarith
  exact le_of_mul_le_mul_left h3 ht0

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqZeroOfExpDecayOfFourierEqZeroOnHalfLine
section
open MeasureTheory Filter Set
open scoped Topology FourierTransform

namespace GlobalTheory

theorem integrable_exp_neg_mul_abs_line {c : ℝ} (hc : 0 < c) :
    Integrable (fun s : ℝ => Real.exp (-(c * |s|))) := by
  first
  | exact @_root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs
  | exact _root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs
  | (apply _root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegrableExpNegAbs.integrable_exp_neg_mul_abs ..)

theorem eq_zero_of_exp_decay_of_fourier_eq_zero_on_halfLine :
    ∀ (φ : ℝ → ℂ) (R : ℝ), Continuous φ →
      (∃ A e : ℝ, 0 < e ∧ ∀ s, ‖φ s‖ ≤ A * Real.exp (-(e * |s|))) →
      (∀ ξ : ℝ, R ≤ ξ → ∫ s : ℝ, Complex.exp (-(Complex.I * ξ * s)) * φ s = 0) → φ = 0 := by
  rintro φ R hφ ⟨A, e, he, hb⟩ hz
  set U : Set ℂ := {z | -(e / 2) < z.im} ∩ {z | z.im < e / 2} with hUdef
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hUc : Convex ℝ U := (convex_halfSpace_im_gt _).inter (convex_halfSpace_im_lt _)
  have hre : ∀ x : ℝ, (x : ℂ) ∈ U := fun x => by
    simp only [hUdef, mem_inter_iff, mem_setOf_eq, Complex.ofReal_im]
    constructor <;> linarith
  have hint : Integrable (fun s : ℝ => A * Real.exp (-(e / 2 * |s|))) :=
    (integrable_exp_neg_mul_abs_line (half_pos he)).const_mul A
  have hA : 0 ≤ A := by
    have := (norm_nonneg _).trans (hb 0)
    simpa using this
  have hbound : ∀ s : ℝ, ∀ y ∈ U,
      ‖Complex.exp (-(Complex.I * y * s)) * φ s‖ ≤ A * Real.exp (-(e / 2 * |s|)) := by
    intro s y hy
    have hy' : |y.im| ≤ e / 2 := abs_le.2 ⟨hy.1.le, hy.2.le⟩
    have h1 : (-(Complex.I * y * s)).re = y.im * s := by simp
    have h2 : y.im * s ≤ e / 2 * |s| := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hy' (abs_nonneg _)
    rw [norm_mul, Complex.norm_exp, h1]
    calc Real.exp (y.im * s) * ‖φ s‖
        ≤ Real.exp (e / 2 * |s|) * (A * Real.exp (-(e * |s|))) :=
          mul_le_mul (Real.exp_le_exp.2 h2) (hb s) (norm_nonneg _) (Real.exp_pos _).le
      _ = A * Real.exp (-(e / 2 * |s|)) := by
          rw [mul_left_comm, ← Real.exp_add]
          congr 2
          ring
  have hdiff := (differentiableOn_integral_of_holomorphic_of_locally_dominated
    (μ := (volume : Measure ℝ))
    (F := fun (s : ℝ) (y : ℂ) => Complex.exp (-(Complex.I * y * s)) * φ s) hUo
    (fun y _ => Continuous.aestronglyMeasurable (by fun_prop))
    (Eventually.of_forall fun s => Differentiable.differentiableOn (by fun_prop))
    (fun x hx => ⟨U, hUo.mem_nhds hx, _, hint, Eventually.of_forall hbound⟩)).1
  have han := hdiff.analyticOnNhd hUo
  have hfr : ∃ᶠ y in 𝓝[≠] (R : ℂ),
      ∫ s : ℝ, Complex.exp (-(Complex.I * y * s)) * φ s = 0 := by
    have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] R) (𝓝[≠] (R : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto R).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simpa using (ne_of_gt hx)
    refine ht.frequently (Eventually.frequently ?_)
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hz x (le_of_lt hx)
  have hzero := han.eqOn_zero_of_preconnected_of_frequently_eq_zero hUc.isPreconnected
    (hre R) hfr
  have hF : 𝓕 φ = 0 := by
    funext w
    rw [Real.fourier_real_eq_integral_exp_smul]
    have := hzero (hre (2 * Real.pi * w))
    simp only [Pi.zero_apply] at this ⊢
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [smul_eq_mul]
    congr 2
    push_cast
    ring
  have hφi : Integrable φ :=
    ((integrable_exp_neg_mul_abs_line he).const_mul A).mono' hφ.aestronglyMeasurable
      (Eventually.of_forall hb)
  have hinv := hφ.fourierInv_fourier_eq hφi (by rw [hF]; exact integrable_zero _ _ _)
  rw [← hinv, hF]
  funext x
  simp [Real.fourierInv_eq]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableCosetSectionStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_measurable_coset_section' : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G] [MeasurableSpace G] [BorelSpace G] (L : Subgroup G), IsClosed (L : Set G) → ∃ σ : G → G, Measurable σ ∧ (∀ x, σ x * x⁻¹ ∈ L) ∧ ∀ l ∈ L, ∀ x, σ (l * x) = σ x := by
  first | exact @GlobalTheory.exists_measurable_coset_section | exact GlobalTheory.exists_measurable_coset_section | (intros; apply GlobalTheory.exists_measurable_coset_section <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableLintegralCosetEqOneClosedSubgrouStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_measurable_lintegral_coset_eq_one_closedSubgroup : ∀ (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] (j : H →* G), Topology.IsClosedEmbedding j → ∃ b : G → ENNReal, Measurable b ∧ ∀ g, ∫⁻ h, b (j h * g) ∂ν = 1 := by
  first | exact @GlobalTheory.exists_measurable_lintegral_coset_eq_one | exact GlobalTheory.exists_measurable_lintegral_coset_eq_one | (intros; apply GlobalTheory.exists_measurable_lintegral_coset_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNetCardLeOfSubsetClosedBall
section
open Metric

namespace GlobalTheory

theorem exists_net_card_le_of_subset_closedBall :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (S : Set E)
      (R δ : ℝ), 0 < δ → 0 ≤ R → S ⊆ closedBall 0 R →
      ∃ T : Finset E, (T : Set E) ⊆ S ∧ (T.card : ℝ) ≤ (1 + 2 * R / δ) ^ Module.finrank ℝ E ∧
        ∀ x ∈ S, ∃ t ∈ T, dist x t ≤ δ := by
  intro E _ _ _ S R δ hδ hR hS
  classical
  let P : Finset E → Prop := fun T =>
    (T : Set E) ⊆ S ∧ (T : Set E).Pairwise fun a b => δ ≤ dist a b
  have hb : ∀ T, P T → (T.card : ℝ) ≤ (1 + 2 * R / δ) ^ Module.finrank ℝ E := fun T hT =>
    finset_card_le_of_separated T hδ hR 0 (fun a ha => hS (hT.1 ha)) hT.2
  obtain ⟨N, hN⟩ := exists_nat_ge ((1 + 2 * R / δ) ^ Module.finrank ℝ E)
  let Q : ℕ → Prop := fun n => ∃ T, P T ∧ T.card = n
  have hQ0 : Q 0 := ⟨∅, ⟨by simp, by simp⟩, rfl⟩
  obtain ⟨T, hT, hTc⟩ : Q (Nat.findGreatest Q N) := Nat.findGreatest_spec (Nat.zero_le N) hQ0
  refine ⟨T, hT.1, hb T hT, fun x hx => ?_⟩
  by_contra hcon
  push Not at hcon
  have hxT : x ∉ T := fun h => by
    have := hcon x h
    rw [dist_self] at this
    linarith
  have hP : P (insert x T) := by
    refine ⟨?_, ?_⟩
    · rw [Finset.coe_insert]
      exact Set.insert_subset hx hT.1
    · rw [Finset.coe_insert]
      refine hT.2.insert fun b hb' _ => ⟨(hcon b hb').le, ?_⟩
      rw [dist_comm]
      exact (hcon b hb').le
  have hle : (insert x T).card ≤ N := by
    exact_mod_cast (hb _ hP).trans hN
  have := Nat.le_findGreatest (P := Q) hle ⟨_, hP, rfl⟩
  rw [Finset.card_insert_of_notMem hxT] at this
  omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPrimitiveAddCharInvolutionInvariant
section
open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

theorem exists_isPrimitive_invol_invariant {B : Type} [CommRing B] [Fintype B] (c : B →+* B)
    (hc : ∀ u, c (c u) = u) (ω : B) (hω : IsUnit (ω - c ω))
    (hfix : ∀ t, c t = t → t ≠ 0 → IsUnit t) :
    ∃ χ : AddChar B ℂ, χ.IsPrimitive ∧ ∀ u, χ (c u) = χ u := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · refine ⟨1, fun a ha => absurd (Subsingleton.elim a 0) ha, fun u => by simp⟩
  obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (a := (1 : B))).2 one_ne_zero
  let T : B →+ B := AddMonoidHom.id B + c.toAddMonoidHom
  have hT : ∀ u, T u = u + c u := fun u => rfl
  refine ⟨ψ.compAddMonoidHom T, ?_, ?_⟩
  · intro a ha h
    have hex : ∃ u, a * u + c (a * u) ≠ 0 := by
      by_contra hne
      push_neg at hne
      have h1 := hne 1
      have h2 := hne ω
      rw [mul_one] at h1
      rw [map_mul] at h2
      have h3 : a * (ω - c ω) = 0 := by linear_combination h2 - c ω * h1
      exact ha ((hω.mul_left_eq_zero).1 h3)
    obtain ⟨u, hu⟩ := hex
    have hs : c (a * u + c (a * u)) = a * u + c (a * u) := by
      rw [map_add (f := _), hc, add_comm]
    obtain ⟨s', hs'⟩ := (hfix _ hs hu).exists_right_inv
    have hcs : c s' = s' := by
      have h4 := congrArg c hs'
      rw [map_mul, hs, map_one] at h4
      linear_combination s' * h4 - c s' * hs'
    have h5 : T (a * (u * s')) = 1 := by
      rw [hT, ← mul_assoc, map_mul c (a * u), hcs, ← hs']
      ring
    have h6 := DFunLike.congr_fun h (u * s')
    rw [AddChar.mulShift_apply, AddChar.compAddMonoidHom_apply, h5] at h6
    exact hψ (by simpa using h6)
  · intro u
    simp only [AddChar.compAddMonoidHom_apply, hT, hc, add_comm]

end GlobalTheory.GramCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetIwasawaSliceOfTransversalStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurableSet_iwasawa_slice_of_transversal : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [PolishSpace G] [MeasurableSpace G] [BorelSpace G] (N M K : Subgroup G) (σ : G → G), MeasurableSet (N : Set G) → MeasurableSet (M : Set G) → MeasurableSet (K : Set G) → Measurable σ → (∀ x, σ x * x⁻¹ ∈ K ⊓ M) → (∀ l ∈ K ⊓ M, ∀ x, σ (l * x) = σ x) → (∀ m ∈ M, ∀ u ∈ N, m * u * m⁻¹ ∈ N) → (∀ u ∈ N, ∀ m ∈ M, u * m ∈ K → u = 1) → ∀ DN DM : Set G, MeasurableSet DN → MeasurableSet DM → ∃ D : Set G, MeasurableSet D ∧ ∀ u ∈ N, ∀ m ∈ M, ∀ k ∈ K, (u * m * k ∈ D ↔ u ∈ DN ∧ m * (k * (σ k)⁻¹) ∈ DM) := by
  first | exact @GlobalTheory.exists_measurableSet_slice_of_transversal | exact GlobalTheory.exists_measurableSet_slice_of_transversal | (intros; apply GlobalTheory.exists_measurableSet_slice_of_transversal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumProdFixedPlaceAverageStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_prod_fixed_place_average_alt : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Fintype (G i)] [∀ i, DecidableEq (G i)] {V : Type} [AddCommGroup V] [Module ℂ V] (a : ∀ i, G i → ℂ) (f : (∀ i, G i) → V), (∀ i (γ : ∀ i, G i), γ i = 1 → ∑ β : G i, a i β • f (Function.update γ i β) = f γ) → ∑ γ : (∀ i, G i), (∏ i, a i (γ i)) • f γ = f 1 := by
  first | exact @GlobalTheory.sum_prod_fixed_place_average | exact GlobalTheory.sum_prod_fixed_place_average | (intros; apply GlobalTheory.sum_prod_fixed_place_average <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumProdOfLocalChoicesBijectionStatement
section
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_prod_of_local_choices_bijection : ∀ {ι Q R : Type} {O : ι → Type} [CommSemiring R] [TopologicalSpace R] [∀ p, Nonempty (O p)] (s : Finset ι) (Φ : Q → ∀ p, O p) (Tq : Set Q) (U : ∀ p, Set (O p)), (∀ p ∈ s, (U p).Finite) → (∀ c ∈ Tq, ∀ c' ∈ Tq, (∀ p ∈ s, Φ c p = Φ c' p) → c = c') → (∀ c ∈ Tq, ∀ p ∈ s, Φ c p ∈ U p) → (∀ x : ∀ p, O p, (∀ p ∈ s, x p ∈ U p) → ∃ c ∈ Tq, ∀ p ∈ s, Φ c p = x p) → ∀ g : ∀ p, O p → R, Tq.Finite ∧ (∑' c : Q, if c ∈ Tq then ∏ p ∈ s, g p (Φ c p) else 0) = ∏ p ∈ s, ∑' o : O p, if o ∈ U p then g p o else 0 := by
  first | exact @GlobalTheory.prod_sum_of_local_choices | exact GlobalTheory.prod_sum_of_local_choices | (intros; apply GlobalTheory.prod_sum_of_local_choices <;> assumption)
end

