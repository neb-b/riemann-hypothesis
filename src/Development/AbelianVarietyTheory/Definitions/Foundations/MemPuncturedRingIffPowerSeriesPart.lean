module

public import Mathlib

@[expose] public section

open scoped PowerSeries LaurentSeries Topology ENNReal NNReal ContDiff
open Filter Metric

noncomputable section

namespace GlobalTheory.Conv

def radius (f : ℂ⟦X⟧) : ℝ≥0∞ :=
  (FormalMultilinearSeries.ofScalars ℂ fun n => PowerSeries.coeff n f).radius

def sum (f : ℂ⟦X⟧) (u : ℂ) : ℂ := ∑' n, PowerSeries.coeff n f * u ^ n

def ConvergesOn (ε : ℝ) (f : ℂ⟦X⟧) : Prop :=
  ∀ u : ℂ, ‖u‖ < ε → Summable fun n => PowerSeries.coeff n f * u ^ n

theorem ConvergesOn.mono {ε ε' : ℝ} {f : ℂ⟦X⟧} (h : ConvergesOn ε f) (hε : ε' ≤ ε) :
    ConvergesOn ε' f := fun u hu => h u (hu.trans_le hε)

theorem convergesOn_iff_le_radius {ε : ℝ} {f : ℂ⟦X⟧} :
    ConvergesOn ε f ↔ ENNReal.ofReal ε ≤ radius f := by
  constructor
  · intro h
    refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    have hr' : (r : ℝ) < ε := by
      rw [← ENNReal.ofReal_coe_nnreal] at hr
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.2).1 hr
    apply FormalMultilinearSeries.le_radius_of_summable_norm
    have := (summable_norm_iff.2 (h (r : ℝ) (by simpa using hr')))
    simpa [FormalMultilinearSeries.ofScalars_norm] using this
  · intro h u hu
    have hu' : u ∈ Metric.eball (0 : ℂ) (radius f) := by
      rw [mem_eball_zero_iff]
      refine lt_of_lt_of_le ?_ h
      rw [← ofReal_norm]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)).2 hu
    have := FormalMultilinearSeries.summable _ hu'
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using this

theorem radius_pos_iff {f : ℂ⟦X⟧} : 0 < radius f ↔ ∃ ε > 0, ConvergesOn ε f := by
  constructor
  · intro h
    obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 h
    refine ⟨r, by simpa using hr0, convergesOn_iff_le_radius.2 ?_⟩
    simpa using hr.le
  · rintro ⟨ε, hε, h⟩
    exact (ENNReal.ofReal_pos.2 hε).trans_le (convergesOn_iff_le_radius.1 h)

theorem hasSum_mul {f g : ℂ⟦X⟧} {u : ℂ} (hf : Summable fun n => PowerSeries.coeff n f * u ^ n)
    (hg : Summable fun n => PowerSeries.coeff n g * u ^ n) :
    HasSum (fun n => PowerSeries.coeff n (f * g) * u ^ n) (sum f u * sum g u) := by
  have hf' := summable_norm_iff.2 hf
  have hg' := summable_norm_iff.2 hg
  have key : ∀ n, PowerSeries.coeff n (f * g) * u ^ n =
      ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, (PowerSeries.coeff kl.1 f * u ^ kl.1) *
        (PowerSeries.coeff kl.2 g * u ^ kl.2) := by
    intro n
    rw [PowerSeries.coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hkl]
    ring
  simp only [key]
  rw [sum, sum, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf' hg']
  exact (summable_norm_sum_mul_antidiagonal_of_summable_norm hf' hg').of_norm.hasSum

theorem hasSum_C (c u : ℂ) :
    HasSum (fun n => PowerSeries.coeff n (PowerSeries.C c) * u ^ n) c := by
  have := hasSum_single (f := fun n => PowerSeries.coeff n (PowerSeries.C c) * u ^ n) 0
    (fun n hn => by simp [PowerSeries.coeff_C, hn])
  simpa using this

theorem hasSum_X (u : ℂ) :
    HasSum (fun n => PowerSeries.coeff n (PowerSeries.X : ℂ⟦X⟧) * u ^ n) u := by
  have := hasSum_single (f := fun n => PowerSeries.coeff n (PowerSeries.X : ℂ⟦X⟧) * u ^ n) 1
    (fun n hn => by simp [PowerSeries.coeff_X, hn])
  simpa using this

@[simp] theorem sum_C (c u : ℂ) : sum (PowerSeries.C c) u = c := (hasSum_C c u).tsum_eq

@[simp] theorem sum_zero_right (f : ℂ⟦X⟧) : sum f 0 = PowerSeries.constantCoeff f := by
  have := hasSum_single (f := fun n => PowerSeries.coeff n f * (0 : ℂ) ^ n) 0
    (fun n hn => by simp [hn])
  simpa [sum] using this.tsum_eq

def discSeries (ε : ℝ) : Subalgebra ℂ ℂ⟦X⟧ where
  carrier := {f | ConvergesOn ε f}
  mul_mem' hf hg u hu := (hasSum_mul (hf u hu) (hg u hu)).summable
  add_mem' hf hg u hu := by simpa [add_mul] using (hf u hu).add (hg u hu)
  algebraMap_mem' c u _ := (hasSum_C c u).summable

theorem mem_discSeries {ε : ℝ} {f : ℂ⟦X⟧} : f ∈ discSeries ε ↔ ConvergesOn ε f := Iff.rfl

theorem discSeries_anti : Antitone discSeries := fun _ _ h _ hf => ConvergesOn.mono hf h

theorem X_mem_discSeries (ε : ℝ) : (PowerSeries.X : ℂ⟦X⟧) ∈ discSeries ε :=
  fun u _ => (hasSum_X u).summable

def evalDisc (ε : ℝ) (u₀ : ℂ) (h : ‖u₀‖ < ε) : discSeries ε →ₐ[ℂ] ℂ where
  toFun f := sum f u₀
  map_one' := by simpa using sum_C 1 u₀
  map_mul' f g := (hasSum_mul (f.2 u₀ h) (g.2 u₀ h)).tsum_eq
  map_zero' := by simp [sum]
  map_add' f g := by
    simpa [sum, add_mul] using (f.2 u₀ h).tsum_add (g.2 u₀ h)
  commutes' c := sum_C c u₀

@[simp] theorem evalDisc_apply {ε : ℝ} {u₀ : ℂ} (h : ‖u₀‖ < ε) (f : discSeries ε) :
    evalDisc ε u₀ h f = sum f u₀ := rfl

theorem hasFPowerSeriesOnBall_sum {f : ℂ⟦X⟧} (h : 0 < radius f) :
    HasFPowerSeriesOnBall (sum f)
      (FormalMultilinearSeries.ofScalars ℂ fun n => PowerSeries.coeff n f) 0 (radius f) := by
  have h1 : sum f = (FormalMultilinearSeries.ofScalars ℂ fun n => PowerSeries.coeff n f).sum := by
    funext u
    simp [sum, FormalMultilinearSeries.sum, mul_comm]
  rw [h1]
  exact FormalMultilinearSeries.hasFPowerSeriesOnBall _ h

theorem ConvergesOn.analyticOnNhd {ε : ℝ} {f : ℂ⟦X⟧} (h : ConvergesOn ε f) :
    AnalyticOnNhd ℂ (sum f) (ball 0 ε) := by
  intro u hu
  have hu' : ‖u‖ < ε := by simpa using hu
  have hε : 0 < ε := (norm_nonneg u).trans_lt hu'
  refine (hasFPowerSeriesOnBall_sum (radius_pos_iff.2 ⟨ε, hε, h⟩)).analyticAt_of_mem ?_
  rw [mem_eball_zero_iff]
  refine lt_of_lt_of_le ?_ (convergesOn_iff_le_radius.1 h)
  rw [← ofReal_norm]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)).2 hu'

def taylor (F : ℂ → ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk fun n => (n.factorial : ℂ)⁻¹ * iteratedDeriv n F 0

theorem hasSum_taylor {ε : ℝ} {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball 0 ε)) {u : ℂ}
    (hu : ‖u‖ < ε) : HasSum (fun n => PowerSeries.coeff n (taylor F) * u ^ n) (F u) := by
  have := Complex.hasSum_taylorSeries_on_ball hF (z := u) (by simpa using hu)
  refine this.congr_fun fun n => ?_
  simp only [taylor, PowerSeries.coeff_mk, sub_zero, smul_eq_mul]
  ring

theorem taylor_mem_discSeries {ε : ℝ} {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball 0 ε)) :
    taylor F ∈ discSeries ε := fun _ hu => (hasSum_taylor hF hu).summable

theorem sum_taylor {ε : ℝ} {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball 0 ε)) {u : ℂ}
    (hu : ‖u‖ < ε) : sum (taylor F) u = F u := (hasSum_taylor hF hu).tsum_eq

def convSeries : Subalgebra ℂ ℂ⟦X⟧ where
  carrier := {f | 0 < radius f}
  mul_mem' {f g} hf hg := by
    obtain ⟨ε, hε, hf⟩ := radius_pos_iff.1 hf
    obtain ⟨δ, hδ, hg⟩ := radius_pos_iff.1 hg
    exact radius_pos_iff.2 ⟨min ε δ, lt_min hε hδ, mul_mem
      (discSeries_anti (min_le_left ε δ) hf) (discSeries_anti (min_le_right ε δ) hg)⟩
  add_mem' {f g} hf hg := by
    obtain ⟨ε, hε, hf⟩ := radius_pos_iff.1 hf
    obtain ⟨δ, hδ, hg⟩ := radius_pos_iff.1 hg
    exact radius_pos_iff.2 ⟨min ε δ, lt_min hε hδ, add_mem
      (discSeries_anti (min_le_left ε δ) hf) (discSeries_anti (min_le_right ε δ) hg)⟩
  algebraMap_mem' c := radius_pos_iff.2 ⟨1, one_pos, (discSeries 1).algebraMap_mem c⟩

theorem mem_convSeries {f : ℂ⟦X⟧} : f ∈ convSeries ↔ ∃ ε > 0, f ∈ discSeries ε := radius_pos_iff

theorem discSeries_le_convSeries {ε : ℝ} (hε : 0 < ε) : discSeries ε ≤ convSeries :=
  fun _ hf => mem_convSeries.2 ⟨ε, hε, hf⟩

theorem mem_convSeries_iff_eventually {f : ℂ⟦X⟧} :
    f ∈ convSeries ↔ ∀ᶠ u in 𝓝 (0 : ℂ), Summable fun n => PowerSeries.coeff n f * u ^ n := by
  simp only [mem_convSeries, Metric.eventually_nhds_iff, dist_zero_right]
  rfl

theorem mem_convSeries_of_summable {f : ℂ⟦X⟧} {u : ℂ} (hu : u ≠ 0)
    (h : Summable fun n => PowerSeries.coeff n f * u ^ n) : f ∈ convSeries := by
  refine mem_convSeries.2 ⟨‖u‖, norm_pos_iff.2 hu, fun v hv => ?_⟩
  refine Summable.of_norm_bounded (summable_norm_iff.2 h) fun n => ?_
  simp only [norm_mul, norm_pow]
  gcongr

theorem eventually_hasSum (f : convSeries) :
    ∀ᶠ u in 𝓝 (0 : ℂ), HasSum (fun n => PowerSeries.coeff n (f : ℂ⟦X⟧) * u ^ n) (sum f u) :=
  (mem_convSeries_iff_eventually.1 f.2).mono fun _ h => h.hasSum

theorem analyticAt_sum {f : ℂ⟦X⟧} (hf : f ∈ convSeries) : AnalyticAt ℂ (sum f) 0 :=
  (hasFPowerSeriesOnBall_sum hf).analyticAt

theorem taylor_spec {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) :
    taylor F ∈ convSeries ∧ sum (taylor F) =ᶠ[𝓝 0] F := by
  obtain ⟨ε, hε, h⟩ := hF.exists_ball_analyticOnNhd
  refine ⟨discSeries_le_convSeries hε (taylor_mem_discSeries h.differentiableOn), ?_⟩
  filter_upwards [ball_mem_nhds (0 : ℂ) hε] with u hu
  exact sum_taylor h.differentiableOn (by simpa using hu)

theorem eq_zero_of_frequently_sum_eq_zero {f : ℂ⟦X⟧} (hf : f ∈ convSeries)
    (h : ∃ᶠ u in 𝓝[≠] (0 : ℂ), sum f u = 0) : f = 0 := by
  have h1 := (analyticAt_sum hf).frequently_zero_iff_eventually_zero.1 h
  have h2 := (hasFPowerSeriesOnBall_sum hf).hasFPowerSeriesAt.eq_zero_of_eventually h1
  rw [FormalMultilinearSeries.ofScalars_series_eq_zero] at h2
  ext n
  simpa using congrFun h2 n

def germ : convSeries →+* Germ (𝓝 (0 : ℂ)) ℂ where
  toFun f := (sum f : Germ (𝓝 (0 : ℂ)) ℂ)
  map_one' := by
    rw [← Germ.coe_one, Germ.coe_eq]
    exact Eventually.of_forall fun u => by simpa using sum_C 1 u
  map_mul' f g := by
    rw [← Germ.coe_mul, Germ.coe_eq]
    filter_upwards [eventually_hasSum f, eventually_hasSum g] with u hf hg
    exact (hasSum_mul hf.summable hg.summable).tsum_eq
  map_zero' := by
    rw [← Germ.coe_zero, Germ.coe_eq]
    exact Eventually.of_forall fun u => by simp [sum]
  map_add' f g := by
    rw [← Germ.coe_add, Germ.coe_eq]
    filter_upwards [eventually_hasSum f, eventually_hasSum g] with u hf hg
    simpa [sum, add_mul] using hf.summable.tsum_add hg.summable

theorem germ_apply (f : convSeries) : germ f = (sum f : Germ (𝓝 (0 : ℂ)) ℂ) := rfl

theorem germ_injective : Function.Injective germ := by
  refine (injective_iff_map_eq_zero _).2 fun f hf => Subtype.ext ?_
  rw [germ_apply, ← Germ.coe_zero, Germ.coe_eq] at hf
  exact eq_zero_of_frequently_sum_eq_zero f.2 (hf.filter_mono nhdsWithin_le_nhds).frequently

theorem mem_range_germ {F : ℂ → ℂ} :
    (F : Germ (𝓝 (0 : ℂ)) ℂ) ∈ germ.range ↔ AnalyticAt ℂ F 0 := by
  constructor
  · rintro ⟨f, hf⟩
    exact (analyticAt_sum f.2).congr (Germ.coe_eq.1 hf)
  · intro h
    exact ⟨⟨taylor F, (taylor_spec h).1⟩, Germ.coe_eq.2 (taylor_spec h).2⟩

def u : convSeries := ⟨PowerSeries.X, discSeries_le_convSeries one_pos (X_mem_discSeries 1)⟩

theorem isUnit_iff {f : convSeries} : IsUnit f ↔ PowerSeries.constantCoeff (f : ℂ⟦X⟧) ≠ 0 := by
  constructor
  · intro h
    exact (h.map (PowerSeries.constantCoeff.comp convSeries.val.toRingHom)).ne_zero
  · intro h
    have h0 : sum f 0 ≠ 0 := by simpa using h
    obtain ⟨g, hg⟩ := mem_range_germ.2 ((analyticAt_sum f.2).inv h0)
    refine IsUnit.of_mul_eq_one g (germ_injective ?_)
    rw [map_mul, map_one, show germ g = _ from hg, germ_apply, ← Germ.coe_mul, ← Germ.coe_one,
      Germ.coe_eq]
    filter_upwards [(analyticAt_sum f.2).continuousAt.eventually_ne h0] with v hv
    simp [hv]

def evalZero : convSeries →ₐ[ℂ] ℂ where
  __ := PowerSeries.constantCoeff.comp convSeries.val.toRingHom
  commutes' c := by simp

@[simp] theorem evalZero_apply (f : convSeries) :
    evalZero f = PowerSeries.constantCoeff (f : ℂ⟦X⟧) := rfl

theorem eventually_sum_eval (P : Polynomial convSeries) (a : convSeries) :
    ∀ᶠ v in 𝓝 (0 : ℂ), sum (P.eval a : convSeries) v =
      ∑ i ∈ Finset.range (P.natDegree + 1), sum (P.coeff i : convSeries) v * sum a v ^ i := by
  have h : germ (P.eval a) = ((fun v => ∑ i ∈ Finset.range (P.natDegree + 1),
      sum (P.coeff i : convSeries) v * sum a v ^ i : ℂ → ℂ) : Germ (𝓝 (0 : ℂ)) ℂ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Polynomial.eval_eq_sum_range, map_sum]
    simp only [map_mul, map_pow, germ_apply]
    have := map_sum (Germ.coeRingHom (R := ℂ) (𝓝 (0 : ℂ)))
      (fun i => sum (P.coeff i : convSeries) * sum a ^ i) (Finset.range (P.natDegree + 1))
    simp only [map_mul, map_pow, Germ.coe_coeRingHom] at this
    rw [← this]
    apply Germ.coe_eq.2
    filter_upwards [] with v
    simp
  exact Germ.coe_eq.1 h

theorem exists_isRoot (P : Polynomial convSeries) (z₀ : ℂ)
    (h₀ : (P.map (evalZero : convSeries →+* ℂ)).eval z₀ = 0)
    (h₁ : (P.map (evalZero : convSeries →+* ℂ)).derivative.eval z₀ ≠ 0) :
    ∃ a : convSeries, P.IsRoot a ∧ evalZero a = z₀ := by
  set F : ℂ × ℂ → ℂ := fun p =>
    ∑ i ∈ Finset.range (P.natDegree + 1), sum (P.coeff i : convSeries) p.1 * p.2 ^ i with hF
  have hFa : AnalyticAt ℂ F (0, z₀) := by
    refine Finset.analyticAt_fun_sum _ fun i _ => AnalyticAt.mul ?_ (analyticAt_snd.pow i)
    exact AnalyticAt.comp (g := sum (P.coeff i : convSeries)) (f := Prod.fst)
      (analyticAt_sum (P.coeff i).2) analyticAt_fst
  have hF0 : ∀ z, F (0, z) = (P.map (evalZero : convSeries →+* ℂ)).eval z := by
    intro z
    rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
    simp [hF]
  have hc : ContDiffAt ℂ ω F (0, z₀) := hFa.contDiffAt
  have hinv : (fderiv ℂ F (0, z₀) ∘L .inr ℂ ℂ ℂ).IsInvertible := by
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ h₁), ?_⟩
    have h2 : HasFDerivAt (fun z : ℂ => F (0, z)) (fderiv ℂ F (0, z₀) ∘L .inr ℂ ℂ ℂ) z₀ :=
      HasFDerivAt.comp (g := F) (f := fun z : ℂ => ((0 : ℂ), z)) z₀
        hFa.differentiableAt.hasFDerivAt (hasFDerivAt_prodMk_right (0 : ℂ) z₀)
    have h3 := ((P.map (evalZero : convSeries →+* ℂ)).hasDerivAt z₀).hasFDerivAt
    simp only [hF0] at h2
    rw [h2.unique h3]
    ext
    simp
  have hω : (ω : WithTop ℕ∞) ≠ 0 := by simp
  have hg : AnalyticAt ℂ (hc.implicitFunction hω hinv) 0 :=
    (hc.contDiffAt_implicitFunction hω hinv).analyticAt
  have hg0 : hc.implicitFunction hω hinv 0 = z₀ := hc.implicitFunction_apply_self hω hinv
  have hge := hc.eventually_apply_implicitFunction hω hinv
  obtain ⟨ha, hsum⟩ := taylor_spec hg
  refine ⟨⟨_, ha⟩, germ_injective ?_, ?_⟩
  · rw [map_zero, germ_apply, ← Germ.coe_zero, Germ.coe_eq]
    filter_upwards [eventually_sum_eval P ⟨_, ha⟩, hsum, hge] with v h1 h2 h3
    rw [h1]
    simp only [h2]
    rw [hF0, h₀] at h3
    exact h3
  · rw [evalZero_apply, ← sum_zero_right]
    exact hsum.self_of_nhds.trans hg0

def puncturedDisc (ε : ℝ) : Set ℂ := ball 0 ε \ {0}

theorem mem_puncturedDisc {ε : ℝ} {v : ℂ} : v ∈ puncturedDisc ε ↔ v ≠ 0 ∧ ‖v‖ < ε := by
  simp [puncturedDisc, and_comm]

theorem isOpen_puncturedDisc (ε : ℝ) : IsOpen (puncturedDisc ε) :=
  isOpen_ball.sdiff isClosed_singleton

theorem puncturedDisc_mono : Monotone puncturedDisc := fun _ _ h _ hv =>
  mem_puncturedDisc.2 ⟨(mem_puncturedDisc.1 hv).1, (mem_puncturedDisc.1 hv).2.trans_le h⟩

theorem puncturedDisc_mem_nhds {ε : ℝ} (hε : 0 < ε) : puncturedDisc ε ∈ 𝓝[≠] (0 : ℂ) :=
  inter_mem (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds 0 hε)) self_mem_nhdsWithin

theorem eventually_iff_exists_puncturedDisc {p : ℂ → Prop} :
    (∀ᶠ v in 𝓝[≠] (0 : ℂ), p v) ↔ ∃ ε > 0, ∀ v ∈ puncturedDisc ε, p v := by
  constructor
  · intro h
    obtain ⟨ε, hε, h⟩ := Metric.mem_nhdsWithin_iff.1 h
    exact ⟨ε, hε, fun v hv => h hv⟩
  · rintro ⟨ε, hε, h⟩
    exact mem_of_superset (puncturedDisc_mem_nhds hε) h

def lsum (f : ℂ⸨X⸩) (v : ℂ) : ℂ := ∑' n : ℤ, f.coeff n * v ^ n

theorem hasSum_coe_iff {g : ℂ⟦X⟧} {v a : ℂ} :
    HasSum (fun n : ℤ => (g : ℂ⸨X⸩).coeff n * v ^ n) a ↔
      HasSum (fun n : ℕ => PowerSeries.coeff n g * v ^ n) a := by
  rw [← (Nat.cast_injective (R := ℤ)).hasSum_iff]
  · simp [Function.comp_def]
  · intro n hn
    have : n < 0 := by
      by_contra h
      exact hn ⟨n.toNat, by omega⟩
    simp [PowerSeries.coeff_coe, this]

theorem hasSum_single_mul {f : ℂ⸨X⸩} {v a : ℂ} (hv : v ≠ 0) (m : ℤ)
    (h : HasSum (fun n : ℤ => f.coeff n * v ^ n) a) :
    HasSum (fun n : ℤ => (HahnSeries.single m (1 : ℂ) * f).coeff n * v ^ n) (v ^ m * a) := by
  rw [← (Equiv.addRight m).hasSum_iff]
  refine (h.mul_left (v ^ m)).congr_fun fun n => ?_
  simp only [Function.comp_apply, Equiv.coe_addRight, HahnSeries.coeff_single_mul_add,
    zpow_add₀ hv]
  ring

theorem summable_single_mul_iff {f : ℂ⸨X⸩} {v : ℂ} (hv : v ≠ 0) (m : ℤ) :
    (Summable fun n : ℤ => (HahnSeries.single m (1 : ℂ) * f).coeff n * v ^ n) ↔
      Summable fun n : ℤ => f.coeff n * v ^ n := by
  refine ⟨fun h => ?_, fun h => (hasSum_single_mul hv m h.hasSum).summable⟩
  have := (hasSum_single_mul hv (-m) h.hasSum).summable
  rwa [← mul_assoc, HahnSeries.single_mul_single, neg_add_cancel, mul_one,
    HahnSeries.single_zero_one, one_mul] at this

theorem summable_single_mul_coe_iff {g : ℂ⟦X⟧} {v : ℂ} (hv : v ≠ 0) (m : ℤ) :
    (Summable fun n : ℤ => (HahnSeries.single m (1 : ℂ) * (g : ℂ⸨X⸩)).coeff n * v ^ n) ↔
      Summable fun n : ℕ => PowerSeries.coeff n g * v ^ n := by
  rw [summable_single_mul_iff hv]
  exact exists_congr fun _ => hasSum_coe_iff

theorem hasSum_single_mul_coe {g : ℂ⟦X⟧} {v : ℂ} (hv : v ≠ 0) (m : ℤ)
    (h : Summable fun n : ℕ => PowerSeries.coeff n g * v ^ n) :
    HasSum (fun n : ℤ => (HahnSeries.single m (1 : ℂ) * (g : ℂ⸨X⸩)).coeff n * v ^ n)
      (v ^ m * sum g v) :=
  hasSum_single_mul hv m (hasSum_coe_iff.2 h.hasSum)

@[simp] theorem lsum_coe (g : ℂ⟦X⟧) (v : ℂ) : lsum (g : ℂ⸨X⸩) v = sum g v := by
  by_cases h : Summable fun n : ℕ => PowerSeries.coeff n g * v ^ n
  · exact (hasSum_coe_iff.2 h.hasSum).tsum_eq
  · rw [sum, tsum_eq_zero_of_not_summable h, lsum, tsum_eq_zero_of_not_summable]
    exact fun h' => h (hasSum_coe_iff.1 h'.hasSum).summable

theorem hasSum_mul_laurent {f g : ℂ⸨X⸩} {v : ℂ} (hv : v ≠ 0)
    (hf : Summable fun n : ℤ => f.coeff n * v ^ n) (hg : Summable fun n : ℤ => g.coeff n * v ^ n) :
    HasSum (fun n : ℤ => (f * g).coeff n * v ^ n) (lsum f v * lsum g v) := by
  obtain ⟨a, p, rfl⟩ : ∃ (a : ℤ) (p : ℂ⟦X⟧), f = HahnSeries.single a (1 : ℂ) * (p : ℂ⸨X⸩) :=
    ⟨_, _, f.single_order_mul_powerSeriesPart.symm⟩
  obtain ⟨b, q, rfl⟩ : ∃ (a : ℤ) (p : ℂ⟦X⟧), g = HahnSeries.single a (1 : ℂ) * (p : ℂ⸨X⸩) :=
    ⟨_, _, g.single_order_mul_powerSeriesPart.symm⟩
  rw [summable_single_mul_coe_iff hv] at hf hg
  rw [lsum, lsum, (hasSum_single_mul_coe hv a hf).tsum_eq, (hasSum_single_mul_coe hv b hg).tsum_eq,
    mul_mul_mul_comm, HahnSeries.single_mul_single, mul_one, ← PowerSeries.coe_mul,
    mul_mul_mul_comm, ← zpow_add₀ hv]
  exact hasSum_single_mul hv _ (hasSum_coe_iff.2 (hasSum_mul hf hg))

theorem hasSum_single_laurent (m : ℤ) (c v : ℂ) :
    HasSum (fun n : ℤ => (HahnSeries.single m c : ℂ⸨X⸩).coeff n * v ^ n) (c * v ^ m) := by
  have := hasSum_single (f := fun n : ℤ => (HahnSeries.single m c : ℂ⸨X⸩).coeff n * v ^ n) m
    (fun n hn => by simp [HahnSeries.coeff_single_of_ne hn])
  simpa using this

@[simp] theorem lsum_single (m : ℤ) (c v : ℂ) : lsum (HahnSeries.single m c) v = c * v ^ m :=
  (hasSum_single_laurent m c v).tsum_eq

@[simp] theorem lsum_algebraMap (c v : ℂ) : lsum (algebraMap ℂ ℂ⸨X⸩ c) v = c := by
  rw [LaurentSeries.algebraMap_apply, HahnSeries.C_apply, lsum_single]
  simp

def puncturedRing (ε : ℝ) : Subalgebra ℂ ℂ⸨X⸩ where
  carrier := {f | ∀ v ∈ puncturedDisc ε, Summable fun n : ℤ => f.coeff n * v ^ n}
  mul_mem' hf hg v hv :=
    (hasSum_mul_laurent (mem_puncturedDisc.1 hv).1 (hf v hv) (hg v hv)).summable
  add_mem' hf hg v hv := by simpa [add_mul] using (hf v hv).add (hg v hv)
  algebraMap_mem' c v _ := by
    rw [LaurentSeries.algebraMap_apply, HahnSeries.C_apply]
    exact (hasSum_single_laurent 0 c v).summable

theorem mem_puncturedRing {ε : ℝ} {f : ℂ⸨X⸩} :
    f ∈ puncturedRing ε ↔ ∀ v ∈ puncturedDisc ε, Summable fun n : ℤ => f.coeff n * v ^ n := Iff.rfl

theorem puncturedRing_anti : Antitone puncturedRing :=
  fun _ _ h _ hf v hv => hf v (puncturedDisc_mono h hv)

theorem single_mem_puncturedRing (ε : ℝ) (m : ℤ) (c : ℂ) :
    (HahnSeries.single m c : ℂ⸨X⸩) ∈ puncturedRing ε :=
  fun v _ => (hasSum_single_laurent m c v).summable

theorem single_mul_coe_mem_puncturedRing {ε : ℝ} {g : ℂ⟦X⟧} (m : ℤ) :
    HahnSeries.single m (1 : ℂ) * (g : ℂ⸨X⸩) ∈ puncturedRing ε ↔ g ∈ discSeries ε := by
  constructor
  · intro h v hv
    rcases eq_or_ne v 0 with rfl | h0
    · exact summable_of_ne_finset_zero (s := {0}) fun n hn => by
        simp [show n ≠ 0 by simpa using hn]
    · exact (summable_single_mul_coe_iff h0 m).1 (h v (mem_puncturedDisc.2 ⟨h0, hv⟩))
  · intro h v hv
    exact (summable_single_mul_coe_iff (mem_puncturedDisc.1 hv).1 m).2
      (h v (mem_puncturedDisc.1 hv).2)

theorem mem_puncturedRing_iff_powerSeriesPart {ε : ℝ} {f : ℂ⸨X⸩} :
    f ∈ puncturedRing ε ↔ f.powerSeriesPart ∈ discSeries ε := by
  rw [← single_mul_coe_mem_puncturedRing f.order, f.single_order_mul_powerSeriesPart]

def evalAt (ε : ℝ) (u₀ : ℂ) (h : u₀ ∈ puncturedDisc ε) : puncturedRing ε →ₐ[ℂ] ℂ where
  toFun f := lsum f u₀
  map_one' := by simpa using lsum_single 0 1 u₀
  map_mul' f g := (hasSum_mul_laurent (mem_puncturedDisc.1 h).1 (f.2 u₀ h) (g.2 u₀ h)).tsum_eq
  map_zero' := by simp [lsum]
  map_add' f g := by
    simpa [lsum, add_mul] using (f.2 u₀ h).tsum_add (g.2 u₀ h)
  commutes' c := lsum_algebraMap c u₀

theorem lsum_eq {ε : ℝ} {f : ℂ⸨X⸩} (hf : f ∈ puncturedRing ε) {v : ℂ} (hv : v ∈ puncturedDisc ε) :
    lsum f v = v ^ f.order * sum f.powerSeriesPart v := by
  have := hasSum_single_mul_coe (mem_puncturedDisc.1 hv).1 f.order
    (mem_puncturedRing_iff_powerSeriesPart.1 hf v (mem_puncturedDisc.1 hv).2)
  rw [f.single_order_mul_powerSeriesPart] at this
  exact this.tsum_eq

theorem analyticOnNhd_lsum {ε : ℝ} {f : ℂ⸨X⸩} (hf : f ∈ puncturedRing ε) :
    AnalyticOnNhd ℂ (lsum f) (puncturedDisc ε) := by
  intro v hv
  have h1 : AnalyticAt ℂ (fun w : ℂ => w ^ f.order * sum f.powerSeriesPart w) v :=
    (analyticAt_id.fun_zpow (mem_puncturedDisc.1 hv).1).mul
      ((mem_discSeries.1 (mem_puncturedRing_iff_powerSeriesPart.1 hf)).analyticOnNhd v hv.1)
  refine h1.congr ?_
  filter_upwards [(isOpen_puncturedDisc ε).mem_nhds hv] with w hw
  exact (lsum_eq hf hw).symm

theorem eq_zero_of_frequently_lsum_eq_zero {ε : ℝ} (hε : 0 < ε) {f : ℂ⸨X⸩}
    (hf : f ∈ puncturedRing ε) (h : ∃ᶠ v in 𝓝[≠] (0 : ℂ), lsum f v = 0) : f = 0 := by
  rw [← LaurentSeries.powerSeriesPart_eq_zero]
  refine eq_zero_of_frequently_sum_eq_zero
    (discSeries_le_convSeries hε (mem_puncturedRing_iff_powerSeriesPart.1 hf)) ?_
  refine (h.and_eventually (puncturedDisc_mem_nhds hε)).mono fun v hv => ?_
  have := hv.1
  rw [lsum_eq hf hv.2] at this
  exact (mul_eq_zero.1 this).resolve_left (zpow_ne_zero _ (mem_puncturedDisc.1 hv.2).1)

def convLaurent : IntermediateField ℂ ℂ⸨X⸩ where
  carrier := {f | ∃ ε > 0, f ∈ puncturedRing ε}
  mul_mem' := by
    rintro f g ⟨ε, hε, hf⟩ ⟨δ, hδ, hg⟩
    exact ⟨min ε δ, lt_min hε hδ, mul_mem
      (puncturedRing_anti (min_le_left ε δ) hf) (puncturedRing_anti (min_le_right ε δ) hg)⟩
  add_mem' := by
    rintro f g ⟨ε, hε, hf⟩ ⟨δ, hδ, hg⟩
    exact ⟨min ε δ, lt_min hε hδ, add_mem
      (puncturedRing_anti (min_le_left ε δ) hf) (puncturedRing_anti (min_le_right ε δ) hg)⟩
  algebraMap_mem' c := ⟨1, one_pos, (puncturedRing 1).algebraMap_mem c⟩
  inv_mem' := by
    rintro f ⟨ε, hε, hf⟩
    rcases eq_or_ne f 0 with rfl | h0
    · exact ⟨1, one_pos, by simp⟩
    let p : convSeries :=
      ⟨_, discSeries_le_convSeries hε (mem_puncturedRing_iff_powerSeriesPart.1 hf)⟩
    have hp : IsUnit p := isUnit_iff.2 <| by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
      simpa [p] using h0
    obtain ⟨q, hq⟩ := hp.exists_right_inv
    obtain ⟨δ, hδ, hq'⟩ := mem_convSeries.1 q.2
    have hq1 : (f.powerSeriesPart : ℂ⸨X⸩) * ((q : ℂ⟦X⟧) : ℂ⸨X⸩) = 1 := by
      rw [← PowerSeries.coe_mul, ← PowerSeries.coe_one]
      exact congrArg (fun x : convSeries => ((x : ℂ⟦X⟧) : ℂ⸨X⸩)) hq
    have : f⁻¹ = HahnSeries.single (-f.order) (1 : ℂ) * ((q : ℂ⟦X⟧) : ℂ⸨X⸩) := by
      refine inv_eq_of_mul_eq_one_right ?_
      nth_rw 1 [← f.single_order_mul_powerSeriesPart]
      rw [mul_mul_mul_comm, hq1, HahnSeries.single_mul_single]
      simp
    exact ⟨δ, hδ, this ▸ (single_mul_coe_mem_puncturedRing _).2 hq'⟩

theorem mem_convLaurent {f : ℂ⸨X⸩} : f ∈ convLaurent ↔ ∃ ε > 0, f ∈ puncturedRing ε := Iff.rfl

theorem puncturedRing_le_convLaurent {ε : ℝ} (hε : 0 < ε) :
    puncturedRing ε ≤ convLaurent.toSubalgebra := fun _ hf => ⟨ε, hε, hf⟩

theorem mem_convLaurent_of_summable {f : ℂ⸨X⸩} {v : ℂ} (hv : v ≠ 0)
    (h : Summable fun n : ℤ => f.coeff n * v ^ n) : f ∈ convLaurent := by
  rw [← f.single_order_mul_powerSeriesPart, summable_single_mul_coe_iff hv] at h
  obtain ⟨ε, hε, hg⟩ := mem_convSeries.1 (mem_convSeries_of_summable hv h)
  exact ⟨ε, hε, mem_puncturedRing_iff_powerSeriesPart.2 hg⟩

theorem eventually_lsum_ne_zero {f : ℂ⸨X⸩} (hf : f ∈ convLaurent) (h0 : f ≠ 0) :
    ∀ᶠ v in 𝓝[≠] (0 : ℂ), lsum f v ≠ 0 := by
  obtain ⟨ε, hε, hf⟩ := hf
  exact not_frequently.1 fun h => h0 (eq_zero_of_frequently_lsum_eq_zero hε hf h)

section Expand

variable (k : ℕ) (hk : k ≠ 0)

end Expand

section Scheme

open CategoryTheory AlgebraicGeometry

end Scheme

end GlobalTheory.Conv
