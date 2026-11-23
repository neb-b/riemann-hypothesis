module

public import Mathlib

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.CosDens
section
noncomputable section

namespace PI.VolStabS

open MeasureTheory Topology

def CosDens : Prop :=
  ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] (ν m : Measure X) [IsFiniteMeasure m],
    IsFiniteMeasureOnCompacts ν →
    ∀ (H : ℕ → AddSubgroup X), (∀ n, IsOpen (H n : Set X)) → (∀ n, IsCompact (H n : Set X)) →
      Antitone H → (∀ N ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N) →
      ∀ (c0 : X) (κ : ENNReal), m {z | z - c0 ∈ H 0}ᶜ = 0 →
        (∀ n h, h - c0 ∈ H 0 → m {z | z - h ∈ H n} = κ * ν {z | z - h ∈ H n}) →
        ∀ S : Set X, IsCompact S → m S = κ * ν (S ∩ {z | z - c0 ∈ H 0})

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.HenselCount
section
noncomputable section

namespace PI.VolStabS

open MeasureTheory Topology

def HenselCount : Prop :=
  ∀ (V X : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X),
    μ.IsAddHaarMeasure → ν.IsAddHaarMeasure →
    ∀ (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X), (∀ n, IsOpen (Λ n : Set V)) →
      (∀ n, IsCompact (Λ n : Set V)) → Antitone Λ → (∀ n, IsOpen (H n : Set X)) →
      (∀ n, IsCompact (H n : Set X)) →
      ∀ D : V →+ X, (∀ n, (Λ n).map D = H n) →
      ∀ (G : V → X) (y : V),
        (∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1)) →
        ∀ n h, h - G y ∈ H 0 →
          μ {Z | Z ∈ Λ 0 ∧ G (y + Z) - h ∈ H n} * ν (H 0) = μ (Λ 0) * ν (H n)

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LBSubm
section
noncomputable section

namespace PI.VolStabS

open MeasureTheory Topology Set Filter
open scoped ENNReal

def SubmLB : Prop :=
  ∀ (n m : ℕ) (μ : Measure (Fin n → ℝ)) (ν : Measure (Fin m → ℝ)), μ.IsAddHaarMeasure →
    ν.IsAddHaarMeasure → ∀ (f : (Fin n → ℝ) → (Fin m → ℝ)), ContDiff ℝ 1 f → ∀ x0,
      Function.Surjective (fderiv ℝ f x0) → ∀ W : Set (Fin n → ℝ), IsOpen W → x0 ∈ W →
      ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ⊤ ∧ ∃ N ∈ 𝓝 (f x0), ∀ S ⊆ N, MeasurableSet S →
        c * ν S ≤ μ (f ⁻¹' S ∩ W)

private theorem exists_clm_rightInverse_of_surjective {n m : ℕ}
    (A : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) (hA : Function.Surjective A) :
    ∃ R : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ), ∀ y, A (R y) = y := by
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (LinearMap.range_eq_top.mpr hA)
  refine ⟨LinearMap.toContinuousLinearMap g, fun y => ?_⟩
  have := LinearMap.congr_fun hg y
  simpa using this

private theorem isAddHaarMeasure_map_restrict_slab {n m : ℕ} (μ : Measure (Fin n → ℝ))
    [μ.IsAddHaarMeasure] (A : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ))
    (R : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) (hAR : ∀ y, A (R y) = y) (p : Fin n → ℝ)
    {r : ℝ} (hr : 0 < r) :
    (Measure.map A (μ.restrict {x | ‖x - R (A x) - (p - R (A p))‖ < r})).IsAddHaarMeasure := by
  have hZ : IsOpen {x : Fin n → ℝ | ‖x - R (A x) - (p - R (A p))‖ < r} := by
    exact isOpen_lt (by fun_prop) continuous_const
  have hAm : Measurable A := A.continuous.measurable
  have key : ∀ x t, x + R t - R (A (x + R t)) = x - R (A x) := by
    intro x t; rw [map_add (f := _), hAR, map_add (f := _)]; abel
  have happ : ∀ S, MeasurableSet S →
      Measure.map A (μ.restrict {x | ‖x - R (A x) - (p - R (A p))‖ < r}) S
        = μ (A ⁻¹' S ∩ {x | ‖x - R (A x) - (p - R (A p))‖ < r}) := by
    intro S hS
    rw [Measure.map_apply hAm hS, Measure.restrict_apply (hAm hS)]
  refine { lt_top_of_isCompact := ?_, map_add_left_eq_self := ?_, open_pos := ?_ }
  · intro K hK
    rw [happ K hK.measurableSet]
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hK.isBounded
    have hsub : A ⁻¹' K ∩ {x | ‖x - R (A x) - (p - R (A p))‖ < r} ⊆
        Metric.closedBall (0 : Fin n → ℝ) (‖R‖ * C + (‖p - R (A p)‖ + r)) := by
      intro x hx
      rw [Metric.mem_closedBall, dist_zero_right]
      have h1 : ‖A x‖ ≤ C := hC _ hx.1
      have h2 : ‖x - R (A x) - (p - R (A p))‖ < r := hx.2
      have h3 : ‖R (A x)‖ ≤ ‖R‖ * C :=
        (R.le_opNorm _).trans (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
      have h4 : ‖x - R (A x)‖ ≤ ‖x - R (A x) - (p - R (A p))‖ + ‖p - R (A p)‖ := by
        have e : x - R (A x) = (x - R (A x) - (p - R (A p))) + (p - R (A p)) := by abel
        calc ‖x - R (A x)‖ = ‖(x - R (A x) - (p - R (A p))) + (p - R (A p))‖ := by rw [← e]
          _ ≤ _ := norm_add_le _ _
      have e' : x = R (A x) + (x - R (A x)) := by abel
      calc ‖x‖ = ‖R (A x) + (x - R (A x))‖ := by rw [← e']
        _ ≤ ‖R (A x)‖ + ‖x - R (A x)‖ := norm_add_le _ _
        _ ≤ ‖R‖ * C + (‖p - R (A p)‖ + r) := by linarith
    exact (measure_mono hsub).trans_lt measure_closedBall_lt_top
  · intro t
    ext S hS
    rw [Measure.map_apply (measurable_const_add t) hS, happ _ (measurable_const_add t hS),
      happ S hS]
    have hset : A ⁻¹' ((fun y => t + y) ⁻¹' S) ∩ {x | ‖x - R (A x) - (p - R (A p))‖ < r}
        = (fun x => x + R t) ⁻¹' (A ⁻¹' S ∩ {x | ‖x - R (A x) - (p - R (A p))‖ < r}) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq]
      rw [key x t, map_add (f := _), hAR, add_comm t (A x)]
    rw [hset, measure_preimage_add_right]
  · intro O hO hne
    rw [happ O hO.measurableSet]
    obtain ⟨y, hy⟩ := hne
    have hopen : IsOpen (A ⁻¹' O ∩ {x | ‖x - R (A x) - (p - R (A p))‖ < r}) :=
      (hO.preimage A.continuous).inter hZ
    have hA1 : A (R y + (p - R (A p))) = y := by
      rw [map_add (f := _), map_sub, hAR, hAR, sub_self, add_zero]
    have hmem : R y + (p - R (A p)) ∈ A ⁻¹' O ∩ {x | ‖x - R (A x) - (p - R (A p))‖ < r} := by
      refine ⟨?_, ?_⟩
      · show A (R y + (p - R (A p))) ∈ O
        rw [hA1]; exact hy
      · show ‖R y + (p - R (A p)) - R (A (R y + (p - R (A p)))) - (p - R (A p))‖ < r
        rw [hA1]
        have e : R y + (p - R (A p)) - R y - (p - R (A p)) = 0 := by abel
        rw [e, norm_zero]; exact hr
    exact hopen.measure_ne_zero μ ⟨_, hmem⟩


set_option maxHeartbeats 800000 in
theorem submLB_holds : SubmLB := by
  intro n m μ ν hμ hν f hf x0 hsurj W hW hx0W
  have := hμ
  have := hν
  obtain ⟨A, hAdef⟩ : ∃ A : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ), A = fderiv ℝ f x0 := ⟨_, rfl⟩
  rw [← hAdef] at hsurj
  obtain ⟨R, hAR⟩ := exists_clm_rightInverse_of_surjective A hsurj
  have hfd : HasStrictFDerivAt f A x0 := by
    rw [hAdef]; exact hf.hasStrictFDerivAt (by norm_num)
  obtain ⟨h, hhdef⟩ : ∃ h : (Fin n → ℝ) → (Fin n → ℝ),
      h = fun x => x + R (f x - A x) + (R (A x0) - R (f x0)) := ⟨_, rfl⟩
  have hfh : ∀ x, f x = A (h x) + (f x0 - A x0) := by
    intro x; rw [hhdef]; simp only [map_add (f := _), map_sub, hAR]; abel
  have hhx0 : h x0 = x0 := by
    rw [hhdef]; simp only [map_sub]; abel
  have hC : ContDiff ℝ 1 h := by
    rw [hhdef]
    exact (contDiff_id.add (R.contDiff.comp (hf.sub A.contDiff))).add contDiff_const
  have hh : HasStrictFDerivAt h
      ((ContinuousLinearEquiv.refl ℝ (Fin n → ℝ) : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) :
        (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) x0 := by
    have h1 : HasStrictFDerivAt (fun x => f x - A x) (A - A) x0 := hfd.sub A.hasStrictFDerivAt
    have h2 := ((hasStrictFDerivAt_id x0).add (R.hasStrictFDerivAt.comp x0 h1)).add_const
      (R (A x0) - R (f x0))
    rw [hhdef]
    convert h2 using 1 <;> first | rfl | (funext x; simp) | (ext v; simp) | (ext v i; simp)
  have hdiff : Differentiable ℝ h := hC.differentiable (by norm_num)
  have hdet : Continuous fun x => (fderiv ℝ h x).det :=
    ContinuousLinearMap.continuous_det.comp (hC.continuous_fderiv (by norm_num))
  have hdet0 : (fderiv ℝ h x0).det = 1 := by
    rw [hh.hasFDerivAt.fderiv]
    first
    | simp [ContinuousLinearMap.det]
    | simp
    | norm_num [ContinuousLinearMap.det, LinearMap.det_id]
  obtain ⟨U0, hU0⟩ : ∃ U0 : Set (Fin n → ℝ), U0 = W ∩ {x | |(fderiv ℝ h x).det| < 2} :=
    ⟨_, rfl⟩
  have hU0open : IsOpen U0 := by
    rw [hU0]; exact hW.inter (isOpen_lt (continuous_abs.comp hdet) continuous_const)
  have hx0U0 : x0 ∈ U0 := by
    rw [hU0]
    refine ⟨hx0W, ?_⟩
    show |(fderiv ℝ h x0).det| < 2
    rw [hdet0]; norm_num
  have hU0W : U0 ⊆ W := by rw [hU0]; exact Set.inter_subset_left
  have hU0det : ∀ x ∈ U0, |(fderiv ℝ h x).det| < 2 := by
    rw [hU0]; exact fun x hx => hx.2
  have himg : h '' U0 ∈ 𝓝 x0 := by
    have hmap : Filter.map h (𝓝 x0) = 𝓝 (h x0) := hh.map_nhds_eq_of_equiv
    have : h '' U0 ∈ Filter.map h (𝓝 x0) := Filter.image_mem_map (hU0open.mem_nhds hx0U0)
    rwa [hmap, hhx0] at this
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 himg
  obtain ⟨r, hr, hrδ⟩ : ∃ r : ℝ, 0 < r ∧ r + r = δ := ⟨δ / 2, by linarith, by ring⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : Measure (Fin m → ℝ),
      ρ = Measure.map A (μ.restrict {x | ‖x - R (A x) - (x0 - R (A x0))‖ < r}) := ⟨_, rfl⟩
  have hρ : ρ.IsAddHaarMeasure := by
    rw [hρdef]; exact isAddHaarMeasure_map_restrict_slab μ A R hAR x0 hr
  obtain ⟨c0, hc0pos, hρeq⟩ : ∃ c0 : NNReal, 0 < c0 ∧ ρ = c0 • ν := by
    refine ⟨ρ.addHaarScalarFactor ν, Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ρ ν, ?_⟩
    first
    | exact Measure.isAddLeftInvariant_eq_smul ρ ν
    | exact Measure.isAddHaarMeasure_eq_smul_of_isAddHaarMeasure ρ ν
    | exact Measure.isAddLeftInvariant_eq_smul_of_innerRegular ρ ν
    | exact Measure.isAddLeftInvariant_eq_smul_of_regular ρ ν
  have hK0 : ENNReal.ofReal 2 ≠ 0 := (ENNReal.ofReal_pos.2 two_pos).ne'
  have hpos : (0 : ℝ) < ‖R‖ + 1 := by positivity
  refine ⟨(ENNReal.ofReal 2)⁻¹ * c0, ?_, ?_, Metric.ball (f x0) (r / (‖R‖ + 1)),
    Metric.ball_mem_nhds _ (div_pos hr hpos), ?_⟩
  · first
    | exact ENNReal.mul_pos (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)
        (ENNReal.coe_ne_zero.2 hc0pos.ne')
    | (apply ENNReal.mul_pos <;> simp [hc0pos.ne'])
  · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hK0) ENNReal.coe_ne_top
  · intro S hSN hS
    have hAm : Measurable A := A.continuous.measurable
    have hS'' : MeasurableSet ((fun y => y + (f x0 - A x0)) ⁻¹' S) := measurable_add_const _ hS
    have hM : MeasurableSet (f ⁻¹' S ∩ U0) :=
      (hf.continuous.measurable hS).inter hU0open.measurableSet
    have hsub : A ⁻¹' ((fun y => y + (f x0 - A x0)) ⁻¹' S) ∩
        {x | ‖x - R (A x) - (x0 - R (A x0))‖ < r} ⊆ h '' (f ⁻¹' S ∩ U0) := by
      rintro u ⟨huS, huZ⟩
      have huS' : A u + (f x0 - A x0) ∈ S := huS
      have huZ' : ‖u - R (A u) - (x0 - R (A x0))‖ < r := huZ
      have hN := hSN huS'
      rw [Metric.mem_ball, dist_eq_norm] at hN
      have e1 : A u + (f x0 - A x0) - f x0 = A (u - x0) := by rw [map_sub]; abel
      rw [e1] at hN
      have e2 : u - x0 = R (A (u - x0)) + (u - R (A u) - (x0 - R (A x0))) := by
        rw [map_sub, map_sub]; abel
      have hne : ‖R‖ + 1 ≠ 0 := hpos.ne'
      have hR1 : ‖R (A (u - x0))‖ ≤ r := by
        have ht := norm_nonneg (A (u - x0))
        calc ‖R (A (u - x0))‖ ≤ ‖R‖ * ‖A (u - x0)‖ := R.le_opNorm _
          _ ≤ (‖R‖ + 1) * ‖A (u - x0)‖ := by nlinarith
          _ ≤ (‖R‖ + 1) * (r / (‖R‖ + 1)) := mul_le_mul_of_nonneg_left hN.le hpos.le
          _ = r := by field_simp
      have hu : u ∈ Metric.ball x0 δ := by
        rw [Metric.mem_ball, dist_eq_norm, e2]
        calc ‖R (A (u - x0)) + (u - R (A u) - (x0 - R (A x0)))‖
            ≤ ‖R (A (u - x0))‖ + ‖u - R (A u) - (x0 - R (A x0))‖ := norm_add_le _ _
          _ < δ := by linarith
      obtain ⟨x, hxU0, rfl⟩ := hball hu
      refine ⟨x, ⟨?_, hxU0⟩, rfl⟩
      show f x ∈ S
      rw [hfh x]; exact huS'
    have h1 : ν S = ν ((fun y => y + (f x0 - A x0)) ⁻¹' S) :=
      (measure_preimage_add_right ν _ S).symm
    have h2 : ρ ((fun y => y + (f x0 - A x0)) ⁻¹' S)
        = (c0 : ℝ≥0∞) * ν ((fun y => y + (f x0 - A x0)) ⁻¹' S) := by
      rw [hρeq]
      first
      | exact Measure.nnreal_smul_coe_apply _ _ _
      | simp
      | rfl
    have h3 : ρ ((fun y => y + (f x0 - A x0)) ⁻¹' S) = μ (A ⁻¹' ((fun y => y + (f x0 - A x0)) ⁻¹' S) ∩
        {x | ‖x - R (A x) - (x0 - R (A x0))‖ < r}) := by
      rw [hρdef, Measure.map_apply hAm hS'', Measure.restrict_apply (hAm hS'')]
    have h5 : μ (h '' (f ⁻¹' S ∩ U0)) ≤
        ∫⁻ x in f ⁻¹' S ∩ U0, ENNReal.ofReal |(fderiv ℝ h x).det| ∂μ := by
      first
      | exact addHaar_image_le_lintegral_abs_det_fderiv μ hM
          (fun x _ => (hdiff x).hasFDerivAt.hasFDerivWithinAt)
      | exact addHaar_image_le_lintegral_abs_det_fderiv hM
          (fun x _ => (hdiff x).hasFDerivAt.hasFDerivWithinAt)
    have h6 : ∫⁻ x in f ⁻¹' S ∩ U0, ENNReal.ofReal |(fderiv ℝ h x).det| ∂μ ≤
        ∫⁻ _ in f ⁻¹' S ∩ U0, ENNReal.ofReal 2 ∂μ := by
      have hle : ∀ x ∈ f ⁻¹' S ∩ U0, ENNReal.ofReal |(fderiv ℝ h x).det| ≤ ENNReal.ofReal 2 :=
        fun x hx => ENNReal.ofReal_le_ofReal (hU0det x hx.2).le
      first
      | exact setLIntegral_mono' hM hle
      | exact setLIntegral_mono measurable_const hle
      | exact lintegral_mono_ae ((ae_restrict_iff' hM).2 (Filter.Eventually.of_forall hle))
    have h7 : ∫⁻ _ in f ⁻¹' S ∩ U0, ENNReal.ofReal 2 ∂μ = ENNReal.ofReal 2 * μ (f ⁻¹' S ∩ U0) := by
      first
      | exact setLIntegral_const _ _
      | rw [lintegral_const, Measure.restrict_apply_univ]
    have h8 : μ (f ⁻¹' S ∩ U0) ≤ μ (f ⁻¹' S ∩ W) :=
      measure_mono (fun x hx => ⟨hx.1, hU0W hx.2⟩)
    have key : (c0 : ℝ≥0∞) * ν S ≤ ENNReal.ofReal 2 * μ (f ⁻¹' S ∩ W) := by
      rw [h1, ← h2, h3]
      calc _ ≤ μ (h '' (f ⁻¹' S ∩ U0)) := measure_mono hsub
        _ ≤ _ := h5
        _ ≤ _ := h6
        _ = _ := h7
        _ ≤ _ := by gcongr
    calc (ENNReal.ofReal 2)⁻¹ * c0 * ν S = (ENNReal.ofReal 2)⁻¹ * (c0 * ν S) := mul_assoc _ _ _
      _ ≤ (ENNReal.ofReal 2)⁻¹ * (ENNReal.ofReal 2 * μ (f ⁻¹' S ∩ W)) := by gcongr
      _ = μ (f ⁻¹' S ∩ W) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hK0 ENNReal.ofReal_ne_top, one_mul]

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensFF
section
noncomputable section

namespace PI.VolStabS

def ffH {K : Type} [CommRing K] (σ : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)
    (x y : Fin M → K) : K :=
  ∑ i, ∑ j, σ (x i) * J i j * y j

def ffGram {K : Type} [CommRing K] (σ : K →+* K) {M a : ℕ} (J : Matrix (Fin M) (Fin M) K)
    (X : Fin a → Fin M → K) : Matrix (Fin a) (Fin a) K :=
  fun i j => ffH σ J (X i) (X j)

def IsQuadInv (k K : Type) [Field k] [CommRing K] [Algebra k K] (σ : K ≃ₐ[k] K) : Prop :=
  (∀ x, σ (σ x) = x) ∧
    ((IsField K ∧ Module.finrank k K = 2 ∧ σ ≠ AlgEquiv.refl) ∨
      ∃ e : K ≃ₐ[k] k × k, ∀ x, e (σ x) = (e x).swap)

def FFCount : Prop :=
  ∀ M : ℕ, ∃ C : ℝ, ∀ (k K : Type) [Field k] [Finite k] [CommRing K] [Algebra k K]
    (σ : K ≃ₐ[k] K), IsQuadInv k K σ → (2 : k) ≠ 0 →
    ∀ J : Matrix (Fin M) (Fin M) K, (∀ i j, σ (J j i) = J i j) → IsUnit J.det →
    ∀ a : ℕ, a + 2 ≤ M → ∀ T : Matrix (Fin a) (Fin a) K, (∀ i j, σ (T j i) = T i j) →
    IsUnit T.det →
    |(Nat.card {X : Fin a → Fin M → K // ffGram (σ : K →+* K) J X = T} : ℝ) /
        (Nat.card k : ℝ) ^ (2 * M * a - a ^ 2) - 1| ≤ C * ((Nat.card k : ℝ)⁻¹) ^ 2

def FFSplit : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (M a : ℕ), a ≤ M →
    ∀ J : Matrix (Fin M) (Fin M) (k × k), (∀ i j, (J j i).swap = J i j) → IsUnit J.det →
    ∀ T : Matrix (Fin a) (Fin a) (k × k), (∀ i j, (T j i).swap = T i j) → IsUnit T.det →
    (Nat.card {X : Fin a → Fin M → k × k //
        ffGram (RingEquiv.prodComm (R := k) (S := k)).toRingHom J X = T} : ℝ) =
      (∏ i : Fin a, ((Nat.card k : ℝ) ^ M - (Nat.card k : ℝ) ^ (i : ℕ))) *
        (Nat.card k : ℝ) ^ (a * (M - a))

def FFInert : Prop :=
  ∀ (k K : Type) [Field k] [Finite k] [Field K] [Algebra k K] (σ : K ≃ₐ[k] K),
    (∀ x, σ (σ x) = x) → Module.finrank k K = 2 → σ ≠ AlgEquiv.refl → (2 : k) ≠ 0 →
    ∀ (M a : ℕ), a ≤ M →
    ∀ J : Matrix (Fin M) (Fin M) K, (∀ i j, σ (J j i) = J i j) → IsUnit J.det →
    ∀ T : Matrix (Fin a) (Fin a) K, (∀ i j, σ (T j i) = T i j) → IsUnit T.det →
    (Nat.card {X : Fin a → Fin M → K // ffGram (σ : K →+* K) J X = T} : ℝ) =
      ∏ j : Fin a, ((Nat.card k : ℝ) ^ (2 * (M - j) - 1) -
        (-1) ^ (M - j) * (Nat.card k : ℝ) ^ (M - j - 1))

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensSAChar
section
noncomputable section

open NumberField

namespace PI.VolStabS

def ChInf : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Λ : Submodule (𝓞 F) F), (∃ c : F, c ≠ 0 ∧ c ∈ Λ) →
    (∀ c : F, c ≠ 0 → ¬ ∀ a ∈ Λ, ∃ r : 𝓞 F, a = c * r) →
    ∀ χ : AddChar (InfiniteAdeleRing F) ℂ, Continuous χ →
    (∀ a ∈ Λ, χ (algebraMap F (InfiniteAdeleRing F) a) = 1) → ∀ x, χ x = 1

def ChLift : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : AddChar (InfiniteAdeleRing F) ℂ), Continuous χ →
    ∃ ℓ : InfiniteAdeleRing F →+ ℂ, Continuous ℓ ∧ ∀ x, χ x = Complex.exp (ℓ x)

def AddIntF : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (Λ : Submodule (𝓞 F) F), (∃ c : F, c ≠ 0 ∧ c ∈ Λ) →
    (∀ c : F, c ≠ 0 → ¬ ∀ a ∈ Λ, ∃ r : 𝓞 F, a = c * r) →
    ∀ g : F →+ ℂ, (∀ a ∈ Λ, ∃ n : ℤ, g a = n) → ∀ a, g a = 0

theorem chInf_of (hL : ChLift) (hA : AddIntF) : ChInf := by
  intro F _ _ Λ hne hnot χ hχ hΛ x
  obtain ⟨ℓ, hℓc, hℓ⟩ := hL F χ hχ
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]

  let g : F →+ ℂ := (AddMonoidHom.mulLeft (2 * (Real.pi : ℂ) * Complex.I)⁻¹).comp
    (ℓ.comp (algebraMap F (InfiniteAdeleRing F)).toAddMonoidHom)
  have hgv : ∀ a, g a = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ℓ (algebraMap F _ a) := fun a => rfl
  have hgint : ∀ a ∈ Λ, ∃ n : ℤ, g a = n := by
    intro a ha
    have h1 := hΛ a ha
    rw [hℓ, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    refine ⟨n, ?_⟩
    rw [hgv, hn, inv_mul_eq_iff_eq_mul₀ h2, mul_comm]
  have hg0 := hA F Λ hne hnot g hgint
  have hℓ0 : ∀ a : F, ℓ (algebraMap F (InfiniteAdeleRing F) a) = 0 := by
    intro a
    have h3 := hg0 a
    rw [hgv] at h3
    exact (mul_eq_zero.mp h3).resolve_left (inv_ne_zero h2)

  have hfun : (ℓ : InfiniteAdeleRing F → ℂ) = fun _ => 0 :=
    (InfiniteAdeleRing.denseRange_algebraMap F).equalizer hℓc continuous_const
      (funext fun a => hℓ0 a)
  rw [hℓ, congrFun hfun x, Complex.exp_zero]

end PI.VolStabS
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoPolish
section
noncomputable section

namespace PI.VolStabS.TopoPolish

open Topology TopologicalSpace Set

theorem polish_of_lcsc (Y : Type) [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    [SecondCountableTopology Y] : PolishSpace Y := by
  classical
  let K := CompactExhaustion.choice Y
  let b : Set (Set (OnePoint Y)) :=
    ((fun s : Set Y => ((↑) : Y → OnePoint Y) '' s) '' countableBasis Y) ∪
      Set.range (fun m : ℕ => (((↑) : Y → OnePoint Y) '' K m)ᶜ)
  have hopen : ∀ m, IsOpen ((((↑) : Y → OnePoint Y) '' K m)ᶜ) := fun m =>
    OnePoint.isOpen_compl_image_coe.mpr ⟨(K.isCompact m).isClosed, K.isCompact m⟩
  have hb : IsTopologicalBasis b := by
    refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro u (⟨s, hs, rfl⟩ | ⟨m, rfl⟩)
      · exact OnePoint.isOpenEmbedding_coe.isOpenMap _ (isOpen_of_mem_countableBasis hs)
      · exact hopen m
    · intro a u ha hu
      induction a using OnePoint.rec with
      | infty =>
        have hc := (OnePoint.isOpen_iff_of_mem ha).mp hu
        obtain ⟨m, hm⟩ := K.exists_superset_of_isCompact hc.2
        refine ⟨_, Or.inr ⟨m, rfl⟩, ?_, ?_⟩
        · rintro ⟨y, -, hy⟩
          exact OnePoint.coe_ne_infty y hy
        · intro x hx
          induction x using OnePoint.rec with
          | infty => exact ha
          | coe y =>
            by_contra hyu
            exact hx ⟨y, hm hyu, rfl⟩
      | coe y =>
        have hu' : IsOpen (((↑) : Y → OnePoint Y) ⁻¹' u) := hu.preimage OnePoint.continuous_coe
        obtain ⟨v, hv, hyv, hvu⟩ :=
          (isBasis_countableBasis Y).exists_subset_of_mem_open (show y ∈ _ from ha) hu'
        refine ⟨_, Or.inl ⟨v, hv, rfl⟩, ⟨y, hyv, rfl⟩, ?_⟩
        rintro _ ⟨z, hz, rfl⟩
        exact hvu hz
  haveI : SecondCountableTopology (OnePoint Y) :=
    hb.secondCountableTopology (((countable_countableBasis Y).image _).union (Set.countable_range _))
  haveI : PolishSpace (OnePoint Y) := by
    haveI : MetrizableSpace (OnePoint Y) := metrizableSpace_of_t3_secondCountable _
    letI := metrizableSpaceMetric (OnePoint Y)
    haveI : CompleteSpace (OnePoint Y) := complete_of_compact
    infer_instance
  haveI : PolishSpace (Set.range ((↑) : Y → OnePoint Y)) := OnePoint.isOpen_range_coe.polishSpace
  exact (OnePoint.isOpenEmbedding_coe.isEmbedding.toHomeomorph).isClosedEmbedding.polishSpace

end PI.VolStabS.TopoPolish
end
end

