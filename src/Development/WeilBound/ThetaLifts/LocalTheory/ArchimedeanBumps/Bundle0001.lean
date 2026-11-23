module

public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.DictHaar
section
noncomputable section

namespace PositivityTheory.ThKG.Loc.Bump

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

variable {ι : Type} [Fintype ι]

theorem map_mul_vol (s : ι → ℂ) (hs : ∀ w, s w ≠ 0) :
    Measure.map (fun c : ι → ℂ => s * c) volume = ENNReal.ofReal (∏ w, ‖s w‖ ^ 2)⁻¹ • volume := by
  let f : (ι → ℂ) →ₗ[ℝ] (ι → ℂ) := LinearMap.pi fun i => (LinearMap.mul ℝ ℂ (s i)).comp (LinearMap.proj i)
  have hd : LinearMap.det f = ∏ w, ‖s w‖ ^ 2 := by
    rw [LinearMap.det_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    have := Algebra.norm_apply ℝ (s i)
    rw [Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq] at this
    exact this.symm
  have hp : 0 < ∏ w, ‖s w‖ ^ 2 := Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (hs w)) 2
  have := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ι → ℂ)) (f := f) (by rw [hd]; exact hp.ne')
  rw [hd, abs_of_pos (inv_pos.2 hp)] at this
  exact this

def dens (c : ι → ℂ) : ℝ≥0 := ⟨(∏ w, ‖c w‖ ^ 2)⁻¹, by positivity⟩

theorem measurable_dens : Measurable (dens : (ι → ℂ) → ℝ≥0) := by
  refine Measurable.subtype_mk ?_
  fun_prop

theorem ae_ne : ∀ᵐ c : ι → ℂ, ∀ w, c w ≠ 0 := by
  rw [ae_all_iff]
  intro w
  exact (Measure.quasiMeasurePreserving_eval (fun _ : ι => (volume : Measure ℂ)) w).ae (p := fun z => z ≠ 0)
    (by rw [ae_iff]; simp)

theorem dens_inv (s : ι → ℂ) (hs : ∀ w, s w ≠ 0) (A : Set (ι → ℂ)) (hA : MeasurableSet A) :
    volume.withDensity (fun c => (dens c : ℝ≥0∞)) ((fun c => s * c) ⁻¹' A) = volume.withDensity (fun c => (dens c : ℝ≥0∞)) A := by
  have hm : Measurable fun c : ι → ℂ => s * c := by fun_prop
  have hp : 0 < ∏ w, ‖s w‖ ^ 2 := Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (hs w)) 2
  have hd : Measurable fun c : ι → ℂ => (dens c : ℝ≥0∞) := measurable_dens.coe_nnreal_ennreal
  rw [withDensity_apply _ (hm hA), withDensity_apply _ hA, ← lintegral_indicator (hm hA), ← lintegral_indicator hA]
  have e : ∀ c, ((fun c => s * c) ⁻¹' A).indicator (fun c => (dens c : ℝ≥0∞)) c =
      ENNReal.ofReal (∏ w, ‖s w‖ ^ 2) * A.indicator (fun c => (dens c : ℝ≥0∞)) (s * c) := by
    intro c
    by_cases h : s * c ∈ A
    · rw [indicator_of_mem (show c ∈ (fun c => s * c) ⁻¹' A from h), indicator_of_mem h, ← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul hp.le]
      congr 1
      change (∏ w, ‖c w‖ ^ 2)⁻¹ = (∏ w, ‖s w‖ ^ 2) * (∏ w, ‖(s * c) w‖ ^ 2)⁻¹
      simp only [Pi.mul_apply, norm_mul, mul_pow, Finset.prod_mul_distrib, mul_inv]
      rw [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul]
    · rw [indicator_of_notMem (show c ∉ (fun c => s * c) ⁻¹' A from h), indicator_of_notMem h, mul_zero]
  simp only [e]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_map (hd.indicator hA) hm, map_mul_vol s hs,
    lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul hp.le, mul_inv_cancel₀ hp.ne', ENNReal.ofReal_one,
    one_mul]

theorem haar_units {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (j : G → ι → ℂ) (hj : IsOpenEmbedding j) (hr : range j = {c | ∀ w, c w ≠ 0}) (hm : ∀ a b, j (a * b) = j a * j b)
    (x : Measure G) [x.IsHaarMeasure] : ∃ κ : ℝ, 0 < κ ∧ ∀ g : (ι → ℂ) → ℂ,
      ∫ l, g (j l) ∂x = κ * ∫ c, g c * ((∏ w, ‖c w‖ ^ 2 : ℝ) : ℂ)⁻¹ := by
  haveI := hj.locallyCompactSpace
  haveI := hj.isEmbedding.secondCountableTopology
  have he := hj.measurableEmbedding
  let ν : Measure (ι → ℂ) := volume.withDensity fun c => (dens c : ℝ≥0∞)
  let y : Measure G := ν.comap j
  have hy : ∀ A, y A = ν (j '' A) := fun A => he.comap_apply ν A
  have hne : ∀ a w, j a w ≠ 0 := fun a => (hr ▸ mem_range_self a : j a ∈ {c : ι → ℂ | ∀ w, c w ≠ 0})
  haveI : y.IsMulLeftInvariant := ⟨fun g => by
    ext A hA
    rw [Measure.map_apply (measurable_const_mul g) hA, hy, hy, ← dens_inv (j g) (hne g) _ (he.measurableSet_image' hA)]
    congr 1
    ext c
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨g * a, ha, hm g a⟩
    · rintro ⟨a, ha, e⟩
      refine ⟨g⁻¹ * a, by simpa using ha, ?_⟩
      have h1 : j g * j (g⁻¹ * a) = j g * c := by rw [← hm, mul_inv_cancel_left]; exact e
      funext w
      exact mul_left_cancel₀ (hne g w) (congrFun h1 w)⟩
  haveI : IsFiniteMeasureOnCompacts y := ⟨fun K hK => by
    have hc := hK.image hj.continuous
    rw [hy, withDensity_apply _ hc.measurableSet]
    have hco : ContinuousOn (fun c : ι → ℂ => (dens c : ℝ)) (j '' K) := by
      refine ContinuousOn.inv₀ (by fun_prop) ?_
      rintro _ ⟨a, _, rfl⟩
      exact (Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (hne a w)) 2).ne'
    exact (hasFiniteIntegral_iff_ofNNReal).1 (hco.integrableOn_compact hc).2⟩
  haveI : y.IsOpenPosMeasure := ⟨fun O hO hn h => by
    rw [hy, withDensity_apply_eq_zero measurable_dens.coe_nnreal_ennreal] at h
    have : {c | (dens c : ℝ≥0∞) ≠ 0} ∩ j '' O = j '' O := by
      refine inter_eq_right.2 ?_
      rintro _ ⟨a, _, rfl⟩ h0
      have h1 : (dens (j a) : ℝ) = 0 := by exact_mod_cast (ENNReal.coe_eq_zero.1 h0)
      exact (inv_pos.2 (Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 (hne a w)) 2)).ne' h1
    rw [this] at h
    exact (hj.isOpenMap O hO).measure_ne_zero volume (hn.image j) h⟩
  haveI : y.IsHaarMeasure := {}
  refine ⟨Measure.haarScalarFactor x y, by exact_mod_cast Measure.haarScalarFactor_pos_of_isHaarMeasure x y, fun g => ?_⟩
  conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul x y]
  have hν : ν.restrict {c | ∀ w, c w ≠ 0} = volume.withDensity fun c => (dens c : ℝ≥0∞) :=
    Measure.restrict_eq_self_of_ae_mem ((withDensity_absolutelyContinuous _ _).ae_le ae_ne)
  rw [integral_smul_nnreal_measure, ← he.integral_map, he.map_comap, hr, hν,
    integral_withDensity_eq_integral_smul measurable_dens, NNReal.smul_def, Complex.real_smul]
  congr 2
  funext c
  rw [NNReal.smul_def, Complex.real_smul, mul_comm, ← Complex.ofReal_inv]
  rfl

end PositivityTheory.ThKG.Loc.Bump

end
end

-- bundled from Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.ExistsDensity
section
noncomputable section

namespace PositivityTheory.ThKG.Loc.Bump

open MeasureTheory Filter Topology Set
open scoped FourierTransform SchwartzMap RealInnerProductSpace

variable {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]

theorem core_bump {Ω : Type} [TopologicalSpace Ω] [T2Space Ω] [MeasurableSpace Ω] [OpensMeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure] (π : Ω → X) (hπ : Continuous π) (x₀ : X) (G : Ω → ℂ) (U S : Set Ω)
    (hU : IsOpen U) (hG : ContinuousOn G U) (hS : IsCompact S) (hSU : S ⊆ U) (ε : ℝ) (hε : 0 < ε)
    (hb : ∀ p, dist (π p) x₀ ≤ ε → p ∈ S) (hpos : ∀ p, π p = x₀ → 0 < (G p).re) (p₀ : Ω) (h₀ : π p₀ = x₀) :
    ∃ φ : 𝓢(X, ℂ), (∀ p, φ (π p) ≠ 0 → p ∈ S) ∧ Integrable (fun p => φ (π p) * G p) μ ∧ ∫ p, φ (π p) * G p ∂μ ≠ 0 := by
  have hre : ContinuousOn (fun p => (G p).re) S := Complex.continuous_re.comp_continuousOn (hG.mono hSU)
  have hB : IsCompact (S ∩ (fun p => (G p).re) ⁻¹' Iic 0) :=
    hS.of_isClosed_subset (hre.preimage_isClosed_of_isClosed hS.isClosed isClosed_Iic) inter_subset_left
  have hc : IsClosed (π '' (S ∩ (fun p => (G p).re) ⁻¹' Iic 0)) := (hB.image hπ).isClosed
  have hx : x₀ ∉ π '' (S ∩ (fun p => (G p).re) ⁻¹' Iic 0) := by
    rintro ⟨p, ⟨_, hp⟩, e⟩
    exact absurd (hpos p e) (not_lt.2 hp)
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hc.isOpen_compl x₀ hx
  let b : ContDiffBump x₀ := ⟨min δ ε / 2, min δ ε, by positivity, by have := lt_min hδ hε; linarith⟩
  have hbs : ∀ x, b x ≠ 0 → dist x x₀ < min δ ε := fun x h => by
    have : x ∈ Function.support b := h
    rw [b.support_eq] at this
    exact this
  have hcs : HasCompactSupport fun x => ((b x : ℝ) : ℂ) := b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  have hsm : ContDiff ℝ (⊤ : ℕ∞) fun x => ((b x : ℝ) : ℂ) := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hin : ∀ p, b (π p) ≠ 0 → p ∈ S := fun p h => hb p ((hbs _ h).le.trans (min_le_right _ _))
  have hsupp : ∀ {E : Type} [Zero E] [TopologicalSpace E] (g : Ω → E), (∀ p, b (π p) = 0 → g p = 0) → tsupport g ⊆ S := by
    intro E _ _ g hg
    refine closure_minimal (fun p hp => hin p fun h => hp (hg p h)) hS.isClosed
  have hcont : Continuous fun p => ((b (π p) : ℝ) : ℂ) * G p := by
    refine ContinuousOn.continuous_of_tsupport_subset (s := U) ?_ hU ((hsupp _ fun p h => by simp [h]).trans hSU)
    exact ((Complex.continuous_ofReal.comp (b.continuous.comp hπ)).continuousOn).mul hG
  have hk : HasCompactSupport fun p => ((b (π p) : ℝ) : ℂ) * G p :=
    hS.of_isClosed_subset (isClosed_tsupport _) (hsupp _ fun p h => by simp [h])
  have hint := hcont.integrable_of_hasCompactSupport (μ := μ) hk
  refine ⟨hcs.toSchwartzMap hsm, fun p h => hin p fun h' => h (by simp [h']), by simpa using hint, fun h => ?_⟩
  have h1 : ∫ p, (((b (π p) : ℝ) : ℂ) * G p).re ∂μ = 0 := by
    have := integral_re hint
    simp only [RCLike.re_to_complex] at this
    rw [this]
    have h' : ∫ p, ((b (π p) : ℝ) : ℂ) * G p ∂μ = 0 := by simpa using h
    rw [h']; rfl
  have h2 : 0 < ∫ p, (((b (π p) : ℝ) : ℂ) * G p).re ∂μ := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := p₀) (Complex.continuous_re.comp hcont)
      (hk.comp_left (g := Complex.re) rfl) (fun p => ?_) ?_
    · by_cases hp : b (π p) = 0
      · simp [hp]
      · have hS' := hin p hp
        have : 0 < (G p).re := by
          by_contra hn
          exact hball ((hbs _ hp).trans_le (min_le_left _ _)) ⟨p, ⟨hS', not_lt.1 hn⟩, rfl⟩
        simp only [Complex.re_ofReal_mul, Pi.zero_apply]
        exact mul_nonneg b.nonneg this.le
    · have : b (π p₀) = 1 := b.one_of_mem_closedBall (by rw [h₀]; exact Metric.mem_closedBall_self b.rIn_pos.le)
      simp only [Complex.re_ofReal_mul, this, one_mul]
      exact (hpos p₀ h₀).ne'
  exact h2.ne' h1

def ch (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

theorem norm_ch (t : ℝ) : ‖ch t‖ = 1 := by
  have : (2 * Real.pi * Complex.I * t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [ch, this, Complex.norm_exp_ofReal_mul_I]

theorem continuous_ch : Continuous ch := by unfold ch; fun_prop

theorem ch_add (s t : ℝ) : ch (s + t) = ch s * ch t := by
  rw [ch, ch, ch, ← Complex.exp_add]; congr 1; push_cast; ring

variable [MeasurableSpace X] [BorelSpace X]

theorem exists_density (φ : 𝓢(X, ℂ)) : ∃ a : 𝓢(X, ℂ), ∀ x, φ x = ∫ η, ch ⟪η, x⟫ * a η := by
  refine ⟨𝓕 φ, fun x => ?_⟩
  have h : (𝓕⁻ (𝓕 φ) : 𝓢(X, ℂ)) = φ := FourierTransform.fourierInv_fourier_eq φ
  conv_lhs => rw [← h]
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  refine integral_congr_ae (Eventually.of_forall fun η => ?_)
  simp only [ch, smul_eq_mul]
  congr 2
  push_cast; ring

theorem fourier_vanish {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ] (π : Ω → X) (hπ : Measurable π) (g : Ω → ℂ)
    (hg : Integrable g μ) (h : ∀ η, ∫ p, ch ⟪η, π p⟫ * g p ∂μ = 0) (φ : 𝓢(X, ℂ)) : ∫ p, φ (π p) * g p ∂μ = 0 := by
  obtain ⟨a, ha⟩ := exists_density φ
  have hi : Integrable (fun q : Ω × X => ch ⟪q.2, π q.1⟫ * (g q.1 * a q.2)) (μ.prod volume) := by
    refine (hg.mul_prod a.integrable).bdd_mul (c := 1) ?_ (Eventually.of_forall fun q => (norm_ch _).le)
    exact (continuous_ch.measurable.comp (measurable_snd.inner (hπ.comp measurable_fst))).aestronglyMeasurable
  calc ∫ p, φ (π p) * g p ∂μ = ∫ p, ∫ η, ch ⟪η, π p⟫ * (g p * a η) ∂volume ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun p => ?_)
        simp only [ha]
        rw [← integral_mul_const]
        congr 1; funext η; ring
    _ = ∫ η, ∫ p, ch ⟪η, π p⟫ * (g p * a η) ∂μ := integral_integral_swap hi
    _ = 0 := by
        have : ∀ η, ∫ p, ch ⟪η, π p⟫ * (g p * a η) ∂μ = 0 := fun η => by
          simp only [← mul_assoc]
          rw [integral_mul_const, h, zero_mul]
        simp [this]

end PositivityTheory.ThKG.Loc.Bump

end
end

