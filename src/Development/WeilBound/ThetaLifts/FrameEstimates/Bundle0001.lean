module

public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.CoefRealA
section
noncomputable section

namespace PositivityTheory.ThKEst.RealFourierCoefficientBounds

open MeasureTheory SchwartzMap
open scoped FourierTransform ContDiff

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def q (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (M N : ℕ) : Seminorm ℂ (SchwartzMap V ℂ) :=
  (Finset.Iic (M, N)).sup fun m => SchwartzMap.seminorm ℂ m.1 m.2

theorem q_cont (M N : ℕ) : Continuous (q V M N) := by
  unfold q
  exact Seminorm.continuous_finsetSup (E := SchwartzMap V ℂ) (s := Finset.Iic (M, N))
    fun m _ => (schwartz_withSeminorms ℂ V ℂ).continuous_seminorm m

def H (f₁ f₂ : SchwartzMap V ℂ) (x : V) (u : V) : ℂ := f₁ (u + x) * (starRingEnd ℂ) (f₂ u)

theorem conj_smooth (f : SchwartzMap V ℂ) : ContDiff ℝ ∞ fun u => (starRingEnd ℂ) (f u) :=
  Complex.conjCLE.contDiff.comp (f.smooth ⊤)

theorem shift_smooth (f : SchwartzMap V ℂ) (x : V) : ContDiff ℝ ∞ fun u => f (u + x) :=
  (f.smooth ⊤).comp (contDiff_id.add contDiff_const)

theorem H_smooth (f₁ f₂ : SchwartzMap V ℂ) (x : V) : ContDiff ℝ ∞ (H f₁ f₂ x) :=
  (shift_smooth f₁ x).mul (conj_smooth f₂)

omit [InnerProductSpace ℝ V] in
theorem peetre (x u : V) : 1 + ‖x‖ ≤ (1 + ‖u + x‖) * (1 + ‖u‖) := by
  have h : ‖x‖ ≤ ‖u + x‖ + ‖u‖ := by simpa using norm_sub_le (u + x) u
  nlinarith [norm_nonneg (u + x), norm_nonneg u, mul_nonneg (norm_nonneg (u + x)) (norm_nonneg u)]

theorem H_bound (N D : ℕ) (f₁ f₂ : SchwartzMap V ℂ) (x u : V) {j : ℕ} (hj : j ≤ N) :
    (1 + ‖x‖) ^ N * (1 + ‖u‖) ^ D * ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖ ≤
      2 ^ N * ((2 ^ (N + D) * q V (N + D) N f₁) * (2 ^ (N + D) * q V (N + D) N f₂)) := by
  set A := 2 ^ (N + D) * q V (N + D) N f₁ with hA
  set B := 2 ^ (N + D) * q V (N + D) N f₂ with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have h1 := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (shift_smooth f₁ x) (conj_smooth f₂) u (n := j)
    (by exact_mod_cast le_top)
  have key : ∀ i ∈ Finset.range (j + 1), (1 + ‖x‖) ^ N * (1 + ‖u‖) ^ D *
      ((j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun u => f₁ (u + x)) u‖ *
        ‖iteratedFDeriv ℝ (j - i) (fun u => (starRingEnd ℂ) (f₂ u)) u‖) ≤ (j.choose i : ℝ) * (A * B) := by
    intro i hi
    have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have e1 : ‖iteratedFDeriv ℝ (j - i) (fun u => (starRingEnd ℂ) (f₂ u)) u‖ = ‖iteratedFDeriv ℝ (j - i) f₂ u‖ :=
      Complex.conjLIE.norm_iteratedFDeriv_comp_left f₂ u (j - i)
    rw [e1, iteratedFDeriv_comp_add_right (f := f₁)]
    have b1 : (1 + ‖u + x‖) ^ N * ‖iteratedFDeriv ℝ i f₁ (u + x)‖ ≤ A :=
      one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N + D, N)) (by simp) (by simp; omega) f₁ (u + x)
    have b2 : (1 + ‖u‖) ^ (N + D) * ‖iteratedFDeriv ℝ (j - i) f₂ u‖ ≤ B :=
      one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N + D, N)) (by simp) (by simp; omega) f₂ u
    have b3 : (1 + ‖x‖) ^ N ≤ (1 + ‖u + x‖) ^ N * (1 + ‖u‖) ^ N := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (peetre x u) N
    calc _ ≤ ((1 + ‖u + x‖) ^ N * (1 + ‖u‖) ^ N) * (1 + ‖u‖) ^ D *
          ((j.choose i : ℝ) * ‖iteratedFDeriv ℝ i f₁ (u + x)‖ * ‖iteratedFDeriv ℝ (j - i) f₂ u‖) := by
          gcongr
      _ = (j.choose i : ℝ) * (((1 + ‖u + x‖) ^ N * ‖iteratedFDeriv ℝ i f₁ (u + x)‖) *
          ((1 + ‖u‖) ^ (N + D) * ‖iteratedFDeriv ℝ (j - i) f₂ u‖)) := by ring
      _ ≤ _ := by gcongr
  calc _ ≤ (1 + ‖x‖) ^ N * (1 + ‖u‖) ^ D * ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun u => f₁ (u + x)) u‖ *
        ‖iteratedFDeriv ℝ (j - i) (fun u => (starRingEnd ℂ) (f₂ u)) u‖ :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (A * B) := by
        rw [Finset.mul_sum]; exact Finset.sum_le_sum key
    _ = 2 ^ j * (A * B) := by
        rw [← Finset.sum_mul]; congr 1; exact_mod_cast Nat.sum_range_choose j
    _ ≤ 2 ^ N * (A * B) := by gcongr; norm_num

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem wt_int : Integrable fun u : V => ((1 + ‖u‖) ^ (Module.finrank ℝ V + 1))⁻¹ := by
  have h := integrable_one_add_norm (E := V) (μ := volume) (r := ((Module.finrank ℝ V + 1 : ℕ) : ℝ))
    (by push_cast; linarith)
  refine h.congr (Filter.Eventually.of_forall fun u => ?_)
  simp only
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]

theorem H_int (N : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (f₁ f₂ : SchwartzMap V ℂ) (x : V) (j : ℕ), j ≤ N →
    Integrable (fun u => ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖) ∧
    (1 + ‖x‖) ^ N * ∫ u, ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖ ≤
      K * (q V (N + (Module.finrank ℝ V + 1)) N f₁ * q V (N + (Module.finrank ℝ V + 1)) N f₂) := by
  set D := Module.finrank ℝ V + 1 with hD
  refine ⟨2 ^ N * 2 ^ (N + D) * 2 ^ (N + D) * ∫ u : V, ((1 + ‖u‖) ^ D)⁻¹, ?_, fun f₁ f₂ x j hj => ?_⟩
  · have : 0 ≤ ∫ u : V, ((1 + ‖u‖) ^ D)⁻¹ := integral_nonneg fun u => by positivity
    positivity
  set C := 2 ^ N * ((2 ^ (N + D) * q V (N + D) N f₁) * (2 ^ (N + D) * q V (N + D) N f₂)) with hC
  have hb : ∀ u, (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖ ≤ C * ((1 + ‖u‖) ^ D)⁻¹ := by
    intro u
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    have := H_bound N D f₁ f₂ x u hj
    linarith [mul_right_comm ((1 + ‖x‖) ^ N) ((1 + ‖u‖) ^ D) ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖]
  have hw : Integrable fun u : V => C * ((1 + ‖u‖) ^ D)⁻¹ := (wt_int (V := V)).const_mul C
  have hc : Continuous fun u => ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖ :=
    ((H_smooth f₁ f₂ x).continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
  have hi : Integrable fun u => ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖ := by
    refine hw.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
    rw [norm_norm]
    refine le_trans ?_ (hb u)
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (by linarith [norm_nonneg x]))
  refine ⟨hi, ?_⟩
  rw [← integral_const_mul]
  refine (integral_mono (hi.const_mul _) hw hb).trans (le_of_eq ?_)
  rw [integral_const_mul, hC]; ring

theorem fourier_bound (N : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (f₁ f₂ : SchwartzMap V ℂ) (x w : V),
    ‖𝓕 (H f₁ f₂ x) w‖ * (1 + ‖x‖ + ‖w‖) ^ N ≤
      K * (q V (N + (Module.finrank ℝ V + 1)) N f₁ * q V (N + (Module.finrank ℝ V + 1)) N f₂) := by
  obtain ⟨K, hK, h⟩ := H_int (V := V) N
  refine ⟨2 ^ N * (2 * (2 ^ N * ((N + 1) * K))), by positivity, fun f₁ f₂ x w => ?_⟩
  set Q := q V (N + (Module.finrank ℝ V + 1)) N f₁ * q V (N + (Module.finrank ℝ V + 1)) N f₂ with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have step : ∀ n ≤ N, (1 + ‖x‖) ^ N * (‖w‖ ^ n * ‖𝓕 (H f₁ f₂ x) w‖) ≤ 2 ^ N * ((N + 1) * K) * Q := by
    intro n hn
    have h1 := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K := 0) (N := (N : ℕ∞)) (f := H f₁ f₂ x)
      ((H_smooth f₁ f₂ x).of_le (by exact_mod_cast le_top))
      (fun k m hk hm => by
        have hk0 : k = 0 := by simpa using hk
        subst hk0
        simpa using (h f₁ f₂ x m (by exact_mod_cast hm)).1)
      (k := 0) (n := n) (by simp) (by exact_mod_cast hn) w
    simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul, Nat.cast_zero, mul_zero, zero_add,
      Finset.range_one, Finset.singleton_product, Finset.sum_map, Function.Embedding.sectR_apply] at h1
    calc _ ≤ (1 + ‖x‖) ^ N * (2 ^ n * ∑ j ∈ Finset.range (n + 1), ∫ u, ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 ^ n * ∑ j ∈ Finset.range (n + 1), (1 + ‖x‖) ^ N * ∫ u, ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖ := by
          rw [← Finset.mul_sum]; ring
      _ ≤ 2 ^ n * ∑ _j ∈ Finset.range (n + 1), K * Q := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j hj => ?_) (by positivity)
          exact (h f₁ f₂ x j ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)).trans hn)).2
      _ = 2 ^ n * ((n + 1) * K) * Q := by simp; ring
      _ ≤ _ := by gcongr; norm_num
  have s0 := step 0 (Nat.zero_le _)
  have sN := step N le_rfl
  have e1 : (1 + ‖x‖ + ‖w‖) ^ N ≤ (1 + ‖x‖) ^ N * (1 + ‖w‖) ^ N := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity)
      (by nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg w)]) N
  have e2 : (1 + ‖w‖) ^ N ≤ 2 ^ N * (1 + ‖w‖ ^ N) := by
    have := add_pow_le (zero_le_one' ℝ) (norm_nonneg w) N
    rw [one_pow] at this
    refine this.trans ?_
    gcongr
    · norm_num
    · omega
  calc _ ≤ ‖𝓕 (H f₁ f₂ x) w‖ * ((1 + ‖x‖) ^ N * (2 ^ N * (1 + ‖w‖ ^ N))) := by
        gcongr
        exact e1.trans (by gcongr)
    _ = 2 ^ N * ((1 + ‖x‖) ^ N * (‖w‖ ^ 0 * ‖𝓕 (H f₁ f₂ x) w‖) +
          (1 + ‖x‖) ^ N * (‖w‖ ^ N * ‖𝓕 (H f₁ f₂ x) w‖)) := by ring
    _ ≤ 2 ^ N * (2 ^ N * ((N + 1) * K) * Q + 2 ^ N * ((N + 1) * K) * Q) := by gcongr
    _ = _ := by ring

theorem main (N : ℕ) : ∃ p : Seminorm ℂ (SchwartzMap V ℂ), Continuous p ∧ ∀ (f₁ f₂ : SchwartzMap V ℂ) (x y : V),
    ‖∫ u, Complex.exp (2 * Real.pi * Complex.I * (inner ℝ u y : ℝ)) * f₁ (u + x) * (starRingEnd ℂ) (f₂ u)‖ *
      (1 + ‖x‖ + ‖y‖) ^ N ≤ p f₁ * p f₂ := by
  obtain ⟨K, hK, h⟩ := fourier_bound (V := V) N
  let c : NNReal := ⟨Real.sqrt K, Real.sqrt_nonneg K⟩
  refine ⟨c • q V (N + (Module.finrank ℝ V + 1)) N, ?_, fun f₁ f₂ x y => ?_⟩
  · exact (q_cont _ _).const_smul c
  have e : (∫ u, Complex.exp (2 * Real.pi * Complex.I * (inner ℝ u y : ℝ)) * f₁ (u + x) *
      (starRingEnd ℂ) (f₂ u)) = 𝓕 (H f₁ f₂ x) (-y) := by
    rw [Real.fourier_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [H, inner_neg_right, smul_eq_mul, mul_assoc]
    congr 2
    push_cast; ring
  have h1 := h f₁ f₂ x (-y)
  rw [norm_neg] at h1
  rw [e]
  refine h1.trans (le_of_eq ?_)
  have hc : (c : ℝ) * c = K := Real.mul_self_sqrt hK
  simp only [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
  rw [← hc]; ring

end PositivityTheory.ThKEst.RealFourierCoefficientBounds

end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.FourierInjA
section
open MeasureTheory BoundedContinuousFunction

namespace PositivityTheory.ThKEst.FourInj

theorem polish_of_lc (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] : PolishSpace G := by
  let _ : UniformSpace G := IsTopologicalAddGroup.rightUniformSpace G
  have : IsUniformAddGroup G := isUniformAddGroup_of_addCommGroup
  have : CompleteSpace G := IsRightUniformAddGroup.completeSpace_of_weaklyLocallyCompactSpace G
  have : (uniformity G).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  have : TopologicalSpace.IsCompletelyMetrizableSpace G := inferInstance
  infer_instance

variable {X A : Type} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]

theorem real_ae_zero (μ : Measure X) (e : A → X →ᵇ ℂ) (h1 : ∃ a, e a = 1) (hmul : ∀ a b, ∃ c, e c = e a * e b)
    (hstar : ∀ a, ∃ c, e c = star (e a)) (hsep : ∀ x y, x ≠ y → ∃ a, e a x ≠ e a y) {h : X → ℝ}
    (hi : Integrable h μ) (h0 : ∀ a, ∫ x, h x • e a x ∂μ = 0) : h =ᵐ[μ] 0 := by
  let V : Submodule ℂ (X →ᵇ ℂ) := Submodule.span ℂ (Set.range e)
  have hV1 : (1 : X →ᵇ ℂ) ∈ V := Submodule.subset_span h1
  have hVmul : ∀ p ∈ V, ∀ q ∈ V, p * q ∈ V := by
    intro p hp q hq
    have : V * V ≤ V := by
      rw [Submodule.span_mul_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
      exact hmul a b
    exact this (Submodule.mul_mem_mul hp hq)
  have hVstar : ∀ p ∈ V, star p ∈ V := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact Submodule.subset_span (hstar a)
    | zero => rw [star_zero]; exact V.zero_mem
    | add x y _ _ hx hy => rw [star_add]; exact V.add_mem hx hy
    | smul c x _ hx => rw [star_smul]; exact V.smul_mem _ hx
  let S : StarSubalgebra ℂ (X →ᵇ ℂ) :=
    { toSubalgebra := V.toSubalgebra hV1 (fun p q hp hq => hVmul p hp q hq)
      star_mem' := fun {p} hp => hVstar p hp }
  have hint : ∀ {k : X → ℝ}, Integrable k μ → ∀ g : X →ᵇ ℂ, Integrable (fun x => k x • g x) μ := by
    intro k hk g
    exact hk.smul_bdd ‖g‖ g.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => g.norm_coe_le_norm x)
  have hV0 : ∀ g ∈ V, ∫ x, h x • g x ∂μ = 0 := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact h0 a
    | zero => simp
    | add p q _ _ hp hq =>
      simp only [BoundedContinuousFunction.add_apply, smul_add]
      rw [integral_add (hint hi p) (hint hi q), hp, hq, add_zero]
    | smul c p _ hp =>
      simp only [BoundedContinuousFunction.smul_apply, smul_comm (h _) c]
      rw [integral_smul, hp, smul_zero]
  have hfin : ∀ {k : X → ℝ}, Integrable k μ → IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (k x)) :=
    fun hk => isFiniteMeasure_withDensity_ofReal hk.2
  have hwd : ∀ {k : X → ℝ}, Integrable k μ → ∀ g : X →ᵇ ℂ,
      ∫ x, g x ∂(μ.withDensity fun x => ENNReal.ofReal (k x)) = ∫ x, max (k x) 0 • g x ∂μ := by
    intro k hk g
    rw [integral_withDensity_eq_integral_toReal_smul₀ hk.aemeasurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal']
  have := hfin hi
  have := hfin hi.neg
  have hPP : (μ.withDensity fun x => ENNReal.ofReal (h x)) = μ.withDensity fun x => ENNReal.ofReal ((-h) x) := by
    refine ext_of_forall_mem_subalgebra_integral_eq_of_polish (𝕜 := ℂ) (A := S) ?_ ?_
    · intro x y hxy
      obtain ⟨a, ha⟩ := hsep x y hxy
      exact ⟨e a, ⟨(e a).toContinuousMap, ⟨e a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩, rfl⟩, ha⟩
    · intro g hg
      rw [hwd hi, hwd hi.neg, ← sub_eq_zero, ← integral_sub (hint hi.pos_part g) (hint hi.neg.pos_part g),
        ← hV0 g hg]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [← sub_smul, Pi.neg_apply, max_zero_sub_max_neg_zero_eq_self]
  have hae := (withDensity_eq_iff hi.aemeasurable.ennreal_ofReal hi.neg.aemeasurable.ennreal_ofReal
    ((lintegral_ofReal_le_lintegral_enorm h).trans_lt hi.2).ne).1 hPP
  filter_upwards [hae] with x hx
  have := congrArg ENNReal.toReal hx
  simp only [ENNReal.toReal_ofReal', Pi.neg_apply] at this
  have h2 := max_zero_sub_max_neg_zero_eq_self (h x)
  rw [this, sub_self] at h2
  exact h2.symm

theorem complex_ae_zero (μ : Measure X) (e : A → X →ᵇ ℂ) (h1 : ∃ a, e a = 1) (hmul : ∀ a b, ∃ c, e c = e a * e b)
    (hstar : ∀ a, ∃ c, e c = star (e a)) (hsep : ∀ x y, x ≠ y → ∃ a, e a x ≠ e a y) {H : X → ℂ}
    (hi : Integrable H μ) (h0 : ∀ a, ∫ x, e a x * H x ∂μ = 0) : H =ᵐ[μ] 0 := by
  have hint : ∀ {k : X → ℂ}, Integrable k μ → ∀ g : X →ᵇ ℂ, Integrable (fun x => g x * k x) μ := by
    intro k hk g
    exact hk.bdd_mul (c := ‖g‖) g.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => g.norm_coe_le_norm x)
  have hic : Integrable (fun x => (starRingEnd ℂ) (H x)) μ :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hi
  have hc : ∀ a, ∫ x, e a x * (starRingEnd ℂ) (H x) ∂μ = 0 := by
    intro a
    obtain ⟨c, hc⟩ := hstar a
    have := congrArg (starRingEnd ℂ) (h0 c)
    rw [← integral_conj, map_zero, hc] at this
    simpa using this
  have hre : (fun x => (H x).re) =ᵐ[μ] 0 := by
    refine real_ae_zero μ e h1 hmul hstar hsep hi.re fun a => ?_
    have : ∀ x, (H x).re • e a x = (1 / 2 : ℂ) * (e a x * H x + e a x * (starRingEnd ℂ) (H x)) := fun x => by
      rw [← mul_add, Complex.add_conj, Complex.real_smul]; push_cast; ring
    simp only [this]
    rw [integral_const_mul, integral_add (hint hi _) (hint hic _), h0, hc]; simp
  have him : (fun x => (H x).im) =ᵐ[μ] 0 := by
    refine real_ae_zero μ e h1 hmul hstar hsep hi.im fun a => ?_
    have : ∀ x, (H x).im • e a x = (-Complex.I / 2 : ℂ) * (e a x * H x - e a x * (starRingEnd ℂ) (H x)) := fun x => by
      rw [← mul_sub, Complex.sub_conj, Complex.real_smul]; push_cast
      linear_combination ((H x).im * e a x) * Complex.I_mul_I
    simp only [this]
    rw [integral_const_mul, integral_sub (hint hi _) (hint hic _), h0, hc]; simp
  filter_upwards [hre, him] with x h1 h2
  exact Complex.ext h1 h2

end PositivityTheory.ThKEst.FourInj
end

