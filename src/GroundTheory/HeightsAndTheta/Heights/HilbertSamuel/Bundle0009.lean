module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0008

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanNorms
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal

noncomputable section

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}

theorem continuousOn_source_of_chart {E : Type*} [TopologicalSpace E] {f : X → E} (j : Fin A.n)
    (hf : ContinuousOn (f ∘ (A.chart j).symm)
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (A.chart j).source)) :
    ContinuousOn f (A.chart j).source := by
  have h := hf.comp (A.chart j).continuousOn (fun y hy =>
    ⟨(A.chart j).map_source hy, by simpa [(A.chart j).left_inv hy] using hy⟩)
  exact h.congr (fun y hy => by simp [(A.chart j).left_inv hy])

theorem ptNormSq_eq_of_mem (W : Weight L) {n : ℕ} {s : Fin A.n → X → ℂ} (hs : s ∈ L.sections n)
    (j : Fin A.n) {x : X} (hx : x ∈ (A.chart j).source) :
    ptNormSq W n s x = ‖s j x‖ ^ 2 * Real.exp (-(n : ℝ) * W.φ j x) := by
  have hk : x ∈ (A.chart (chartIdx A x)).source := Classical.choose_spec (A.cover x)
  have hkj : x ∈ (A.chart (chartIdx A x)).source ∩ (A.chart j).source := ⟨hk, hx⟩
  have hg : 0 < ‖L.g (chartIdx A x) j x‖ ^ 2 := by
    have := L.ne_zero _ _ x hkj
    positivity
  have he : Real.exp ((n : ℝ) * Real.log (‖L.g (chartIdx A x) j x‖ ^ 2)) =
      (‖L.g (chartIdx A x) j x‖ ^ 2) ^ n := by
    rw [← Real.log_pow, Real.exp_log (pow_pos hg n)]
  rw [ptNormSq, hs.2.1 _ j x hkj, W.compat _ j x hkj, norm_mul, norm_pow,
    show -(n : ℝ) * (W.φ j x + Real.log (‖L.g (chartIdx A x) j x‖ ^ 2)) =
      -(n : ℝ) * W.φ j x - (n : ℝ) * Real.log (‖L.g (chartIdx A x) j x‖ ^ 2) by ring,
    Real.exp_sub, he]
  have hp : 0 < (‖L.g (chartIdx A x) j x‖ ^ 2) ^ n := pow_pos hg n
  field_simp
  ring

theorem ptNormSq_nonneg (W : Weight L) (n : ℕ) (s : Fin A.n → X → ℂ) (x : X) :
    0 ≤ ptNormSq W n s x := by
  unfold ptNormSq; positivity

theorem continuous_ptNormSq (W : Weight L) {n : ℕ} {s : Fin A.n → X → ℂ}
    (hs : s ∈ L.sections n) : Continuous (ptNormSq W n s) := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨j, hx⟩ := A.cover x
  have hsj : ContinuousOn (s j) (A.chart j).source :=
    continuousOn_source_of_chart j (hs.1 j j).continuousOn
  have hφj : ContinuousOn (W.φ j) (A.chart j).source :=
    continuousOn_source_of_chart j (W.smooth j j).continuousOn
  have hF : ContinuousOn (fun y => ‖s j y‖ ^ 2 * Real.exp (-(n : ℝ) * W.φ j y))
      (A.chart j).source :=
    ((hsj.norm.pow 2).mul ((continuousOn_const.mul hφj).rexp))
  have hopen := (A.chart j).open_source
  refine (hF.continuousAt (hopen.mem_nhds hx)).congr ?_
  filter_upwards [hopen.mem_nhds hx] with y hy
  exact (ptNormSq_eq_of_mem W hs j hy).symm

theorem ptNormSq_smul (W : Weight L) (n : ℕ) (c : ℂ) (s : Fin A.n → X → ℂ) (x : X) :
    ptNormSq W n (c • s) x = ‖c‖ ^ 2 * ptNormSq W n s x := by
  simp only [ptNormSq, Pi.smul_apply, smul_eq_mul, norm_mul]
  ring

variable [MeasurableSpace X] [BorelSpace X]

theorem SmoothVolume.isOpenPosMeasure (dV : SmoothVolume A) : dV.μ.IsOpenPosMeasure := by
  refine ⟨fun U hU ⟨x, hxU⟩ hzero => ?_⟩
  obtain ⟨j, hx⟩ := A.cover x
  set O := (A.chart j).target ∩ (A.chart j).symm ⁻¹' U with hOdef
  have hO : IsOpen O := (A.chart j).isOpen_inter_preimage_symm hU
  have hxO : A.chart j x ∈ O :=
    ⟨(A.chart j).map_source hx, by simpa [(A.chart j).left_inv hx] using hxU⟩
  have hOt : O ⊆ (A.chart j).target := inter_subset_left
  have hmeas : Measurable (U.indicator (1 : X → ℝ≥0∞)) := measurable_one.indicator hU.measurableSet
  have h1 := dV.chart_lintegral j _ hmeas
  have hL : ∫⁻ y in (A.chart j).source, U.indicator (1 : X → ℝ≥0∞) y ∂dV.μ = 0 := by
    rw [lintegral_indicator_one hU.measurableSet, Measure.restrict_apply hU.measurableSet]
    exact measure_mono_null inter_subset_left hzero
  rw [hL] at h1
  have h2 : ∫⁻ y in O, ENNReal.ofReal (dV.dens j y) = 0 := by
    refine le_antisymm ?_ bot_le
    calc ∫⁻ y in O, ENNReal.ofReal (dV.dens j y)
        = ∫⁻ y in O, U.indicator (1 : X → ℝ≥0∞) ((A.chart j).symm y) *
            ENNReal.ofReal (dV.dens j y) := by
          refine setLIntegral_congr_fun hO.measurableSet fun y hy => ?_
          rw [Set.indicator_of_mem (show (A.chart j).symm y ∈ U from hy.2), Pi.one_apply, one_mul]
      _ ≤ ∫⁻ y in (A.chart j).target, U.indicator (1 : X → ℝ≥0∞) ((A.chart j).symm y) *
            ENNReal.ofReal (dV.dens j y) := lintegral_mono_set hOt
      _ = 0 := h1.symm
  have hae : AEMeasurable (fun y => ENNReal.ofReal (dV.dens j y)) (volume.restrict O) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((((dV.smooth j).continuousOn).mono hOt).aemeasurable hO.measurableSet)
  have h3 := (lintegral_eq_zero_iff' hae).1 h2
  rw [EventuallyEq, ae_restrict_iff' hO.measurableSet] at h3
  have h4 : volume O = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h3] with y hy hyO
    exact (ENNReal.ofReal_pos.2 (dV.pos j y (hOt hyO))).ne' (hy hyO)
  exact hO.measure_ne_zero volume ⟨_, hxO⟩ h4

theorem integrable_ptNormSq (W : Weight L) (dV : SmoothVolume A) [CompactSpace X] {n : ℕ}
    {s : Fin A.n → X → ℂ} (hs : s ∈ L.sections n) : Integrable (ptNormSq W n s) dV.μ := by
  have := dV.isProb
  exact (continuous_ptNormSq W hs).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit [BorelSpace X] in
theorem sectionL2NormSq_nonneg (W : Weight L) (dV : SmoothVolume A) (n : ℕ) (s : Fin A.n → X → ℂ) :
    0 ≤ sectionL2NormSq W dV n s :=
  integral_nonneg fun x => ptNormSq_nonneg W n s x


omit [BorelSpace X] in
theorem sectionL2NormSq_smul (W : Weight L) (dV : SmoothVolume A) (n : ℕ) (c : ℂ)
    (s : Fin A.n → X → ℂ) : sectionL2NormSq W dV n (c • s) = ‖c‖ ^ 2 * sectionL2NormSq W dV n s := by
  simp only [sectionL2NormSq, ptNormSq_smul]
  exact integral_const_mul _ _

theorem ptNormSq_eq_zero_of_l2NormSq_eq_zero (W : Weight L) (dV : SmoothVolume A) [CompactSpace X]
    {n : ℕ} {s : Fin A.n → X → ℂ} (hs : s ∈ L.sections n) (h0 : sectionL2NormSq W dV n s = 0) (x : X) :
    ptNormSq W n s x = 0 := by
  have := dV.isOpenPosMeasure
  have hae := (integral_eq_zero_iff_of_nonneg (fun y => ptNormSq_nonneg W n s y)
    (integrable_ptNormSq W dV hs)).1 h0
  have := (Continuous.ae_eq_iff_eq (μ := dV.μ) (continuous_ptNormSq W hs) continuous_const).1 hae
  exact congrFun this x

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComplexFormsOnPoints
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem ComplexFormsOnPoints.proof (hR : PrimeComplexRadical.Statement)
    (hM : ComplexMinimalPrimesContract.Statement) : ComplexFormsOnPoints.Statement := by
  intro K _ ι _ P hP hrel F hF
  have hrad := hR (Σ k, ι k) P hP
  apply hrad
  rw [← Ideal.sInf_minimalPrimes]
  refine Ideal.mem_sInf.2 fun {Q} hQ => ?_
  have hQp : Q.IsPrime := hQ.1.1
  have hc := hM (Σ k, ι k) P hP Q hQ
  choose i hi using hrel

  let h0 : MRing ι := ∏ k, X ⟨k, i k⟩
  have h0P : h0 ∉ P := by
    intro hmem
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hP)).1 hmem
    exact hi k hk
  have hQh : map (Int.castRingHom ℂ) h0 ∉ Q := by
    intro hmem
    apply h0P
    rw [← hc]
    exact Ideal.mem_comap.2 hmem
  have hPQ : ∀ f ∈ P, map (Int.castRingHom ℂ) f ∈ Q := by
    intro f hf
    rw [← hc] at hf
    exact Ideal.mem_comap.1 hf
  have hv : F * map (Int.castRingHom ℂ) h0 ∈ vanishingIdeal ℂ (zeroLocus ℂ Q) := by
    rw [mem_vanishingIdeal_iff]
    intro z hz
    have hz : ∀ p ∈ Q, eval z p = 0 := hz
    change eval z _ = 0
    have hzh : eval z (map (Int.castRingHom ℂ) h0) = ∏ k, z ⟨k, i k⟩ := by
      simp [h0, map_prod]
    by_cases h0z : eval z (map (Int.castRingHom ℂ) h0) = 0
    · rw [map_mul, h0z, mul_zero]
    · have hne : ∀ k, z ⟨k, i k⟩ ≠ 0 := by
        rw [hzh] at h0z
        exact fun k => Finset.prod_ne_zero_iff.1 h0z k (Finset.mem_univ k)
      have hzP : z ∈ mcPts P := ⟨fun k => ⟨i k, hne k⟩, fun f hf => hz _ (hPQ f hf)⟩
      rw [map_mul, hF z hzP, zero_mul]
  rw [vanishingIdeal_zeroLocus_eq_radical, hQp.radical] at hv
  exact (hQp.mem_or_mem hv).resolve_right hQh

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDegLTGrowth
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open GroundTheory.Heights₂.Heights.NumbersDVR

section Growth

variable {K : Type} [Fintype K] [DecidableEq K]


omit [Fintype K] [DecidableEq K] in
theorem mixedDiff_of_fin_zero (bs : Fin 0 → K → ℤ) (f : (K → ℤ) → ℤ) : mixedDiff bs f = f := by
  simp [mixedDiff]


omit [Fintype K] [DecidableEq K] in
theorem mixedDiff_snoc_eq_diffStep {n : ℕ} (bs : Fin n → K → ℤ) (b : K → ℤ) (f : (K → ℤ) → ℤ) :
    mixedDiff (Fin.snoc bs b : Fin (n + 1) → K → ℤ) f = mixedDiff bs (diffStep b f) := by
  unfold mixedDiff
  rw [List.ofFn_succ']
  simp [List.concat_eq_append, List.foldr_append]


omit [Fintype K] [DecidableEq K] in
theorem degLT_diffStep_of_degLT_succ {n : ℕ} {f : (K → ℤ) → ℤ} (hf : DegLT f (n + 1)) (b : K → ℤ) :
    DegLT (diffStep b f) n := by
  intro bs
  have h := hf (Fin.snoc bs b : Fin (n + 1) → K → ℤ)
  rwa [mixedDiff_snoc_eq_diffStep] at h


omit [Fintype K] in
theorem diffStep_single_natCast (g : (K → ℤ) → ℤ) (m : K → ℕ) (k : K) :
    diffStep (Pi.single k 1) g (fun j => ((m + Pi.single k 1 : K → ℕ) j : ℤ)) =
      g (fun j => ((m + Pi.single k 1 : K → ℕ) j : ℤ)) - g (fun j => (m j : ℤ)) := by
  unfold diffStep
  congr 2
  funext j
  by_cases h : j = k
  · subst h; simp
  · simp [h]

theorem sum_add_pi_single_one (m : K → ℕ) (k : K) :
    ∑ j, (m + Pi.single k 1 : K → ℕ) j = ∑ j, m j + 1 := by
  simp [Finset.sum_add_distrib]

theorem abs_sub_le_of_unit_steps (G : (K → ℕ) → ℤ) (A : ℕ) (D : ℝ) (hD : 0 ≤ D) (s : ℕ) :
    ∀ a : K → ℕ, ∑ k, a k = s → (∀ k, A ≤ a k) →
      (∀ (m : K → ℕ) (k : K), (∀ j, A ≤ m j) → ∑ j, m j + 1 ≤ s →
        |((G (m + Pi.single k 1) : ℝ) - G m)| ≤ D) →
      |((G a : ℝ) - G (fun _ => A))| ≤ D * s := by
  induction s with
  | zero =>
    intro a hs ha _
    have : a = fun _ => A := by
      funext k
      have h0 := (Finset.sum_eq_zero_iff.mp hs) k (Finset.mem_univ k)
      have := ha k
      omega
    subst this
    simp
  | succ s ih =>
    intro a hs ha hstep
    by_cases hall : ∀ k, a k = A
    · have : a = fun _ => A := funext hall
      subst this
      simp only [sub_self, abs_zero]
      positivity
    · push Not at hall
      obtain ⟨k, hk⟩ := hall
      have hk' : A < a k := lt_of_le_of_ne (ha k) (Ne.symm hk)
      set m : K → ℕ := a - Pi.single k 1 with hm_def
      have hma : m + Pi.single k 1 = a := by
        funext j
        by_cases h : j = k
        · subst h; simp [m]; omega
        · simp [m, h]
      have hmA : ∀ j, A ≤ m j := by
        intro j
        by_cases h : j = k
        · subst h; simp [m]; omega
        · simp [m, h]; exact ha j
      have hms : ∑ j, m j = s := by
        have := sum_add_pi_single_one m k
        rw [hma, hs] at this
        omega
      have h1 := ih m hms hmA (fun m' k' hm' hs' => hstep m' k' hm' (by omega))
      have h2 := hstep m k hmA (by omega)
      rw [hma] at h2
      calc |((G a : ℝ) - G (fun _ => A))|
          = |((G a : ℝ) - G m) + ((G m : ℝ) - G (fun _ => A))| := by ring_nf
        _ ≤ |((G a : ℝ) - G m)| + |((G m : ℝ) - G (fun _ => A))| := abs_add_le _ _
        _ ≤ D + D * s := add_le_add h2 h1
        _ = D * ((s + 1 : ℕ) : ℝ) := by push_cast; ring

theorem degLT_succ_growth_natPow (n : ℕ) : ∀ g : (K → ℤ) → ℤ, DegLT g (n + 1) →
    ∃ (A : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ a : K → ℕ, (∀ k, A ≤ a k) →
      |(g (fun k => (a k : ℤ)) : ℝ)| ≤ C * (((∑ k, a k : ℕ) : ℝ) + 1) ^ n := by
  induction n with
  | zero =>
    intro g hg
    have hev : ∀ᶠ m in Filter.atTop, ∀ k, diffStep (Pi.single k 1) g m = 0 := by
      refine Filter.eventually_all.2 fun k => ?_
      have := degLT_diffStep_of_degLT_succ hg (Pi.single k 1) Fin.elim0
      simpa [mixedDiff_of_fin_zero] using this
    obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1 hev
    set A : ℕ := ∑ k, (m₀ k).toNat
    have hA : ∀ k, m₀ k ≤ (A : ℤ) := by
      intro k
      calc m₀ k ≤ ((m₀ k).toNat : ℤ) := Int.self_le_toNat _
        _ ≤ (A : ℤ) := by
          exact_mod_cast Finset.single_le_sum (f := fun k => (m₀ k).toNat)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    refine ⟨A, |(g (fun _ => (A : ℤ)) : ℝ)|, abs_nonneg _, fun a ha => ?_⟩
    have hw := abs_sub_le_of_unit_steps (fun a : K → ℕ => g (fun k => (a k : ℤ))) A 0 le_rfl (∑ k, a k) a rfl ha
      (fun m k hm _ => by
        have hge : m₀ ≤ fun j => ((m + Pi.single k 1 : K → ℕ) j : ℤ) := by
          intro j
          have := hA j
          have := hm j
          simp only [Pi.add_apply]
          push_cast
          have : (0 : ℤ) ≤ ((Pi.single k 1 : K → ℕ) j : ℤ) := Nat.cast_nonneg _
          omega
        have := hm₀ _ hge k
        rw [diffStep_single_natCast] at this
        rw [sub_eq_zero.mp this]
        simp)
    simp only [zero_mul] at hw
    simp only [pow_zero, mul_one]
    have := abs_sub_abs_le_abs_sub (g (fun k => (a k : ℤ)) : ℝ) (g (fun _ => (A : ℤ)) : ℝ)
    linarith
  | succ n ih =>
    intro g hg
    have hd : ∀ k, ∃ (A : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ a : K → ℕ, (∀ j, A ≤ a j) →
        |(diffStep (Pi.single k 1) g (fun j => (a j : ℤ)) : ℝ)| ≤
          C * (((∑ j, a j : ℕ) : ℝ) + 1) ^ n :=
      fun k => ih _ (degLT_diffStep_of_degLT_succ hg _)
    choose Ak Ck hCk hbk using hd
    set A : ℕ := ∑ k, Ak k
    set C : ℝ := ∑ k, Ck k
    have hC : 0 ≤ C := Finset.sum_nonneg fun k _ => hCk k
    have hAk : ∀ k, Ak k ≤ A := fun k =>
      Finset.single_le_sum (f := Ak) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
    have hCk' : ∀ k, Ck k ≤ C := fun k =>
      Finset.single_le_sum (f := Ck) (fun k _ => hCk k) (Finset.mem_univ k)
    set G0 : ℝ := |(g (fun _ => (A : ℤ)) : ℝ)|
    refine ⟨A, G0 + C, by positivity, fun a ha => ?_⟩
    set X : ℝ := ((∑ k, a k : ℕ) : ℝ) + 1 with hX
    have hS0 : (0 : ℝ) ≤ ((∑ k, a k : ℕ) : ℝ) := Nat.cast_nonneg _
    have hX1 : 1 ≤ X := by simp only [X]; linarith
    have hw := abs_sub_le_of_unit_steps (fun a : K → ℕ => g (fun k => (a k : ℤ))) A (C * X ^ n) (by positivity)
      (∑ k, a k) a rfl ha (fun m k hm hs => by
        have h1 := hbk k (m + Pi.single k 1) (fun j => le_trans (hAk k)
          (le_trans (hm j) (by simp)))
        rw [diffStep_single_natCast] at h1
        push_cast at h1 ⊢
        refine le_trans h1 ?_
        have hs' : ((∑ j, (m + Pi.single k 1 : K → ℕ) j : ℕ) : ℝ) + 1 ≤ X := by
          rw [sum_add_pi_single_one]; simp only [X]; exact_mod_cast Nat.add_le_add_right hs 1
        have h0 : (0 : ℝ) ≤ ((∑ j, (m + Pi.single k 1 : K → ℕ) j : ℕ) : ℝ) + 1 := by positivity
        push_cast at hs' h0
        exact le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hs' n) (hCk k))
          (mul_le_mul_of_nonneg_right (hCk' k) (by positivity)))
    simp only at hw
    have htri := abs_sub_abs_le_abs_sub (g (fun k => (a k : ℤ)) : ℝ) (g (fun _ => (A : ℤ)) : ℝ)
    have hSX : ((∑ k, a k : ℕ) : ℝ) ≤ X := by simp only [X]; linarith
    have hXn : X ^ n * ((∑ k, a k : ℕ) : ℝ) ≤ X ^ (n + 1) := by
      rw [pow_succ]; exact mul_le_mul_of_nonneg_left hSX (by positivity)
    have hX1n : 1 ≤ X ^ (n + 1) := one_le_pow₀ hX1
    have hG0 : 0 ≤ G0 := abs_nonneg _
    push_cast at hw htri
    calc |(g (fun k => (a k : ℤ)) : ℝ)|
        ≤ G0 + C * X ^ n * ((∑ k, a k : ℕ) : ℝ) := by push_cast; simp only [G0]; linarith
      _ ≤ G0 * X ^ (n + 1) + C * X ^ (n + 1) := by
          have := mul_le_mul_of_nonneg_left hXn hC
          have := mul_le_mul_of_nonneg_left hX1n hG0
          nlinarith
      _ = (G0 + C) * X ^ (n + 1) := by ring

end Growth

theorem DegLTGrowth.proof : DegLTGrowth.Statement := by
  intro K _ _ n g hg
  cases n with
  | zero =>
    have hev : ∀ᶠ m in Filter.atTop, g m = 0 := by
      simpa [mixedDiff_of_fin_zero] using hg Fin.elim0
    obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1 hev
    refine ⟨∑ k, (m₀ k).toNat, 0, fun a ha => ?_⟩
    have hge : m₀ ≤ fun k => (a k : ℤ) := by
      intro k
      calc m₀ k ≤ ((m₀ k).toNat : ℤ) := Int.self_le_toNat _
        _ ≤ ((∑ k, (m₀ k).toNat : ℕ) : ℤ) := by
          exact_mod_cast Finset.single_le_sum (f := fun k => (m₀ k).toNat)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
        _ ≤ (a k : ℤ) := by exact_mod_cast ha k
    rw [hm₀ _ hge]
    simp
  | succ n =>
    obtain ⟨A, C, _, hb⟩ := degLT_succ_growth_natPow n g hg
    refine ⟨A, C, fun a ha => ?_⟩
    have h := hb a ha
    have he : ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ) := by push_cast; ring
    rw [he, Real.rpow_natCast]
    push_cast at h
    exact h

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPrimeZariskiDense
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem PrimeZariskiDense.eval_eq_zero_of_mem_map {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) {F : MvPolynomial (Σ k, ι k) ℂ}
    (hF : F ∈ P.map (MvPolynomial.map (Int.castRingHom ℂ))) : eval z F = 0 := by
  have hle : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ RingHom.ker (eval z) := by
    rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, RingHom.mem_ker]
    exact hz.2 f hf
  exact RingHom.mem_ker.mp (hle hF)

theorem PrimeZariskiDense.proof (h1 : ComplexFormsOnPoints.Statement) (h2 : PrimeComplexRadical.Statement)
    (h3 : ComplexMinimalPrimesContract.Statement) : PrimeZariskiDense.Statement := by
  intro K _ ι _ P j hP hj g hg z hz
  by_cases hrel : IsRelevant P
  · set Pc := P.map (MvPolynomial.map (Int.castRingHom ℂ)) with hPc
    have hgj : g * map (Int.castRingHom ℂ) j ∈ Pc := by
      refine h1 K ι P hP hrel _ fun w hw => ?_
      rw [map_mul]
      by_cases hjw : eval w (map (Int.castRingHom ℂ) j) = 0
      · rw [hjw, mul_zero]
      · rw [hg w hw hjw, zero_mul]
    have hrad : Pc.radical = Pc := (h2 (Σ k, ι k) P hP).radical
    have hgPc : g ∈ Pc := by
      rw [← hrad, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
      intro Q hQ
      change Q ∈ Pc.minimalPrimes at hQ
      have hQp : Q.IsPrime := hQ.1.1
      have hjQ : map (Int.castRingHom ℂ) j ∉ Q := by
        intro h
        apply hj
        rw [← h3 (Σ k, ι k) P hP Q hQ, Ideal.mem_comap]
        exact h
      exact (hQp.mem_or_mem (hQ.1.2 hgj)).resolve_right hjQ
    exact PrimeZariskiDense.eval_eq_zero_of_mem_map P hz hgPc
  · exfalso
    simp only [IsRelevant, not_forall, not_exists, not_not] at hrel
    obtain ⟨k, hk⟩ := hrel
    obtain ⟨i, hi⟩ := hz.1 k
    apply hi
    simpa using hz.2 _ (hk i)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

