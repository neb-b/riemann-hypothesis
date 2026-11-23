module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0005

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ContinuousHermNormGroup
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory NumberField

noncomputable section

def ChowHeightConst.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n k : ℕ) (H : ArchData K n) (c : K), c ≠ 0 →
    chowHt H k 0 (C c : MvPolynomial (Fin k × Fin n) K) = 0

section Ball

open Matrix

variable {n : ℕ}

def ballProd (h : HermNorm n) (k : ℕ) : Set (Fin k × Fin n → ℂ) :=
  {u | ∀ i, h.norm (fun j => u (i, j)) < 1}

theorem continuous_hermNorm_group (h : HermNorm n) {k : ℕ} (i : Fin k) :
    Continuous fun u : Fin k × Fin n → ℂ => h.norm (fun j => u (i, j)) := by
  simp only [HermNorm.norm, Matrix.mulVec, dotProduct]
  fun_prop

theorem isOpen_ballProd (h : HermNorm n) (k : ℕ) : IsOpen (ballProd h k) := by
  have e : ballProd h k = ⋂ i, {u | h.norm (fun j => u (i, j)) < 1} := by
    ext u
    simp [ballProd]
  rw [e]
  exact isOpen_iInter_of_finite fun i => isOpen_lt (continuous_hermNorm_group h i) continuous_const

theorem zero_mem_ballProd (h : HermNorm n) (k : ℕ) : (0 : Fin k × Fin n → ℂ) ∈ ballProd h k := by
  intro i
  have e : (fun j : Fin n => (0 : Fin k × Fin n → ℂ) (i, j)) = 0 := rfl
  rw [e]
  simp [HermNorm.norm]

theorem norm_le_of_hermNorm_lt (h : HermNorm n) {v : Fin n → ℂ} (hv : h.norm v < 1) (j : Fin n) :
    ‖v j‖ ≤ ∑ j', ∑ l, ‖h.mat⁻¹ j' l‖ := by
  have hinv : h.mat⁻¹ * h.mat = 1 := Matrix.nonsing_inv_mul _ h.isUnit_det
  have hv' : v = h.mat⁻¹ *ᵥ (h.mat *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hcoord : ∀ l, ‖(h.mat *ᵥ v) l‖ ≤ 1 := by
    intro l
    have h1 : ‖(h.mat *ᵥ v) l‖ ^ 2 ≤ ∑ m, ‖(h.mat *ᵥ v) m‖ ^ 2 :=
      Finset.single_le_sum (f := fun m => ‖(h.mat *ᵥ v) m‖ ^ 2) (fun m _ => sq_nonneg _)
        (Finset.mem_univ l)
    have h2 : √(‖(h.mat *ᵥ v) l‖ ^ 2) ≤ h.norm v := Real.sqrt_le_sqrt h1
    rw [Real.sqrt_sq (norm_nonneg _)] at h2
    linarith
  calc ‖v j‖ = ‖(h.mat⁻¹ *ᵥ (h.mat *ᵥ v)) j‖ := by rw [← hv']
    _ = ‖∑ l, h.mat⁻¹ j l * (h.mat *ᵥ v) l‖ := rfl
    _ ≤ ∑ l, ‖h.mat⁻¹ j l * (h.mat *ᵥ v) l‖ := norm_sum_le _ _
    _ ≤ ∑ l, ‖h.mat⁻¹ j l‖ := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (hcoord l)
    _ ≤ ∑ j', ∑ l, ‖h.mat⁻¹ j' l‖ :=
        Finset.single_le_sum (f := fun j' => ∑ l, ‖h.mat⁻¹ j' l‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j)

theorem isBounded_ballProd (h : HermNorm n) (k : ℕ) : Bornology.IsBounded (ballProd h k) := by
  have hR : 0 ≤ ∑ j', ∑ l, ‖h.mat⁻¹ j' l‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine (Metric.isBounded_closedBall (x := (0 : Fin k × Fin n → ℂ))
    (r := ∑ j', ∑ l, ‖h.mat⁻¹ j' l‖)).subset fun u hu => ?_
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR]
  rintro ⟨i, j⟩
  exact norm_le_of_hermNorm_lt h (hu i) j

theorem volume_ballProd_pos (h : HermNorm n) (k : ℕ) : 0 < volume (ballProd h k) :=
  (isOpen_ballProd h k).measure_pos volume ⟨0, zero_mem_ballProd h k⟩

theorem volume_ballProd_lt_top (h : HermNorm n) (k : ℕ) : volume (ballProd h k) < ⊤ :=
  (isBounded_ballProd h k).measure_lt_top

theorem sphereMean_const (h : HermNorm n) (k : ℕ) (a : ℝ) : sphereMean h k (fun _ => a) = a :=
  setAverage_const (volume_ballProd_pos h k).ne' (volume_ballProd_lt_top h k).ne a

theorem mahler_C (h : HermNorm n) (k : ℕ) (z : ℂ) :
    mahler h k (C z : MvPolynomial (Fin k × Fin n) ℂ) = Real.log ‖z‖ := by
  unfold mahler
  simp only [eval_C]
  exact sphereMean_const h k _

end Ball

section ProductFormula

variable {K : Type*} [Field K] [NumberField K]

theorem prod_norm_embeddings (x : K) :
    ∏ σ : K →+* ℂ, ‖σ x‖ = ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by
  have h : ‖algebraMap ℚ ℂ (Algebra.norm ℚ x)‖ = ∏ σ : K →+* ℂ, ‖σ x‖ := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ x, norm_prod, ← Fintype.prod_equiv
      (RingHom.equivRatAlgHom K ℂ) (fun f => ‖f x‖) (fun φ => ‖φ x‖)
      fun _ => by simp [RingHom.equivRatAlgHom_apply]]
  rw [← h, eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs, Rat.cast_abs]

theorem sum_log_norm_embeddings {x : K} (hx : x ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log ‖σ x‖ = Real.log ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by
  rw [← prod_norm_embeddings, Real.log_prod]
  intro σ _
  exact norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hx)

theorem finsum_log_adicAbv {x : K} (hx : x ≠ 0) :
    ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      Real.log (NumberField.HeightOneSpectrum.adicAbv K v x) =
        -Real.log ((|Algebra.norm ℚ x| : ℚ) : ℝ) := by
  have hpos : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      0 < NumberField.HeightOneSpectrum.adicAbv K v x := fun v =>
    (NumberField.HeightOneSpectrum.adicAbv K v).pos hx
  rw [← Real.log_finprod hpos]
  have e : ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      NumberField.HeightOneSpectrum.adicAbv K v x = ∏ᶠ w : FinitePlace K, w x := by
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
    refine finprod_congr fun v => ?_
    rw [FinitePlace.equivHeightOneSpectrum_symm_apply, FinitePlace.norm_embedding]
  rw [e, FinitePlace.prod_eq_inv_abs_norm hx, Rat.cast_inv, Real.log_inv]

end ProductFormula

theorem chowHeightConst : ChowHeightConst.Statement := by
  intro K _ _ n k H c hc
  unfold chowHt
  have harch : ∀ σ : K →+* ℂ,
      mahler (H.normAt σ) k ((C c : MvPolynomial (Fin k × Fin n) K).map σ) = Real.log ‖σ c‖ :=
    fun σ => by rw [map_C, mahler_C]
  simp only [harch, gaussNorm_C, Nat.cast_zero, mul_zero, zero_mul, zero_div, add_zero,
    finsum_log_adicAbv hc, sum_log_norm_embeddings hc, neg_add_cancel]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.GaussSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem finsum_log_gaussNorm_mul {ι : Type*} {f g : MvPolynomial ι K} (hf : f ≠ 0) (hg : g ≠ 0) :
    ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v (f * g)) =
      (∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v f)) +
        ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), Real.log (gaussNorm v g) := by
  rw [← finsum_add_distrib (log_gaussNorm_support_finite hf) (log_gaussNorm_support_finite hg)]
  refine finsum_congr fun v => ?_
  rw [gaussNorm_mul, Real.log_mul (gaussNorm_pos v hf).ne' (gaussNorm_pos v hg).ne']

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MahlerSectionBasic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

variable {n : ℕ}

def ballH (h : HermNorm n) : Set (Fin n → ℂ) := {v | h.norm v < 1}

def nrmv (h : HermNorm n) (v : Fin n → ℂ) : Fin n → ℂ := fun j => ((h.norm v : ℝ) : ℂ)⁻¹ * v j

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaMultiplicityWeight
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module Set Filter Function

open scoped ENNReal NNReal

noncomputable section

theorem AreaMultiplicityWeight.setLIntegral_comp_mul_abs_det₀ {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set E} {f : E → E} {f' : E → E →L[ℝ] E}
    (hs : NullMeasurableSet s μ) (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hf : InjOn f s) (g : E → ℝ≥0∞) :
    ∫⁻ x in s, g (f x) * ENNReal.ofReal |(f' x).det| ∂μ = ∫⁻ y in f '' s, g y ∂μ := by
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, ts, ht, t_eq_s⟩
  have himg : f '' t =ᵐ[μ] f '' s := by
    have hst : s = t ∪ (s \ t) := by simp [union_eq_self_of_subset_left ts]
    rw [hst, image_union]
    refine (union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr ?_)).symm
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero _ (fun x hx ↦ ?_)
      (ae_eq_set.1 t_eq_s).2
    exact (hf' x hx.1).differentiableWithinAt.mono sdiff_subset
  rw [setLIntegral_congr t_eq_s.symm, ← setLIntegral_congr himg,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul μ ht (fun x hx => (hf' x (ts hx)).mono ts)
      (hf.mono ts)]
  congr 1
  funext x
  exact mul_comm _ _

theorem AreaMultiplicityWeight.proof : AreaMultiplicityWeight.Statement := by
  intro E _ _ _ _ _ μ _ A f f' hA hf'
  classical
  set B : Set E := {x ∈ A | (f' x).det ≠ 0} with hBdef
  have hBA : B ⊆ A := sep_subset _ _

  have hB : NullMeasurableSet B μ := by
    obtain ⟨d, hdm, hfd⟩ : AEMeasurable (fun x => (f' x).det) (μ.restrict A) :=
      ContinuousLinearMap.continuous_det.measurable.comp_aemeasurable
        (aemeasurable_fderivWithin μ hA hf')
    refine (hA.inter (hdm (measurableSet_singleton 0).compl)).nullMeasurableSet.congr ?_
    filter_upwards [(ae_restrict_iff' hA).1 hfd] with x hx
    change (x ∈ A ∩ d ⁻¹' {0}ᶜ) ↔ (x ∈ B)
    by_cases hxA : x ∈ A
    · simp [B, hxA, hx hxA]
    · simp [B, hxA]

  have hZ : μ (f '' {x ∈ A | (f' x).det = 0}) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
      (fun x hx => (hf' x hx.1).mono (sep_subset _ _)) (fun x hx => hx.2)

  let r : (E →L[ℝ] E) → ℝ≥0 := fun L => (‖L.inverse‖₊ + 1)⁻¹
  obtain ⟨t, L, htd, htm, hcov, happ, hL⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f B f'
      (fun x hx => (hf' x hx.1).mono hBA) r (fun _ => inv_ne_zero (by positivity))
  set P : ℕ → Set E := fun n => B ∩ t n with hPdef
  have hPm : ∀ n, NullMeasurableSet (P n) μ := fun n => hB.inter (htm n).nullMeasurableSet
  have hPd : Pairwise (Disjoint on P) := fun m n hmn =>
    (htd hmn).mono inter_subset_right inter_subset_right
  have hPA : ∀ n, P n ⊆ A := fun n => inter_subset_left.trans hBA
  have hderP : ∀ n, ∀ x ∈ P n, HasFDerivWithinAt f (f' x) (P n) x := fun n x hx =>
    (hf' x (hPA n hx)).mono (hPA n)
  have hinj : ∀ n, InjOn f (P n) := by
    intro n
    rcases (P n).eq_empty_or_nonempty with h | ⟨x, hx⟩
    · rw [h]; exact injOn_empty f
    obtain ⟨y, hy, hLy⟩ := hL ⟨x, hx.1⟩ n
    set e := (f' y).toContinuousLinearEquivOfDetNeZero hy.2
    have he : (e : E →L[ℝ] E) = L n := by
      rw [hLy]; exact ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
    have ha := happ n
    rw [← he] at ha
    refine ha.injOn ?_
    rcases subsingleton_or_nontrivial E with hE | hE
    · exact Or.inl hE
    right
    have hr : r (e : E →L[ℝ] E) = (‖(e.symm : E →L[ℝ] E)‖₊ + 1)⁻¹ := by
      simp only [r, ContinuousLinearMap.inverse_equiv]
    rw [hr]
    have hpos : 0 < ‖(e.symm : E →L[ℝ] E)‖₊ := by
      rw [pos_iff_ne_zero, ne_eq, nnnorm_eq_zero]
      intro h0
      obtain ⟨z, hz⟩ := exists_ne (0 : E)
      apply hz
      simpa using congrArg (fun T : E →L[ℝ] E => T (e z)) h0
    exact (inv_lt_inv₀ (by positivity) hpos).2 (lt_add_one _)
  have hBU : B = ⋃ n, P n := by
    rw [← inter_iUnion]; exact (inter_eq_left.2 hcov).symm
  have himg : ∀ n, NullMeasurableSet (f '' P n) μ := fun n =>
    nullMeasurable_image_of_fderivWithin μ (hPm n) (hderP n) (hinj n)

  have hNae : ∀ᵐ y ∂μ, ∑' n, (f '' P n).indicator (1 : E → ℝ≥0∞) y =
      (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hZ] with y hy
    have hU : {x ∈ A | f x = y} = ⋃ n, {x ∈ P n | f x = y} := by
      ext x
      simp only [mem_ofPred_eq, mem_iUnion]
      constructor
      · rintro ⟨hxA, hxy⟩
        have hxB : x ∈ B := ⟨hxA, fun hd => hy ⟨x, ⟨hxA, hd⟩, hxy⟩⟩
        obtain ⟨n, hn⟩ := mem_iUnion.1 (hcov hxB)
        exact ⟨n, ⟨hxB, hn⟩, hxy⟩
      · rintro ⟨n, hxP, hxy⟩
        exact ⟨hPA n hxP, hxy⟩
    rw [hU, encard_iUnion_nat_eq_tsum _ (fun m n hmn => (hPd hmn).mono (sep_subset _ _)
      (sep_subset _ _))]
    refine tsum_congr fun n => ?_
    by_cases hyn : y ∈ f '' P n
    · obtain ⟨x, hx, rfl⟩ := hyn
      have hs : {z ∈ P n | f z = f x} = {x} := by
        ext z
        simp only [mem_ofPred_eq, mem_singleton_iff]
        exact ⟨fun h => hinj n h.1 hx h.2, fun h => by subst h; exact ⟨hx, rfl⟩⟩
      rw [hs, encard_singleton, indicator_of_mem (mem_image_of_mem f hx)]
      simp
    · have hs : {z ∈ P n | f z = y} = ∅ := by
        ext z
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun hz e => hyn ⟨z, hz, e⟩
      rw [hs, encard_empty]
      simp [hyn]
  refine ⟨(AEMeasurable.tsum fun n => aemeasurable_one.indicator₀ (himg n)).congr hNae,
    fun g hg => ?_⟩
  calc ∫⁻ x in A, g (f x) * ENNReal.ofReal |(f' x).det| ∂μ
      = ∫⁻ x in B, g (f x) * ENNReal.ofReal |(f' x).det| ∂μ := by
        rw [← lintegral_indicator hA, ← lintegral_indicator₀ hB]
        congr 1; ext x
        by_cases hx : x ∈ A
        · by_cases hd : (f' x).det = 0
          · simp [indicator, hx, hd, B]
          · simp [indicator, hx, hd, B]
        · have : x ∉ B := fun h => hx h.1
          simp [hx, this]
    _ = ∑' n, ∫⁻ x in P n, g (f x) * ENNReal.ofReal |(f' x).det| ∂μ := by
        rw [hBU]; exact lintegral_iUnion₀ hPm (fun m n hmn => (hPd hmn).aedisjoint) _
    _ = ∑' n, ∫⁻ y in f '' P n, g y ∂μ := tsum_congr fun n =>
        AreaMultiplicityWeight.setLIntegral_comp_mul_abs_det₀ μ (hPm n) (hderP n) (hinj n) g
    _ = ∑' n, ∫⁻ y, (f '' P n).indicator g y ∂μ :=
        tsum_congr fun n => (lintegral_indicator₀ (himg n) g).symm
    _ = ∫⁻ y, ∑' n, (f '' P n).indicator g y ∂μ :=
        (lintegral_tsum fun n => hg.aemeasurable.indicator₀ (himg n)).symm
    _ = ∫⁻ y, (∑' n, (f '' P n).indicator (1 : E → ℝ≥0∞) y) * g y ∂μ := by
        congr 1; funext y
        rw [← ENNReal.tsum_mul_right]
        refine tsum_congr fun n => ?_
        by_cases h : y ∈ f '' P n <;> simp [h]
    _ = ∫⁻ y, (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞) * g y ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hNae] with y hy
        rw [hy]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PBaseChangeAvoid
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem BaseChangeAvoid.comap_eq_of_mem_minimalPrimes {K L : Type*} [Field K] [Field L] {n : ℕ}
    (σ : K →+* L) (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    {W : Ideal (MvPolynomial (Fin n) L)} (hW : W ∈ (I.map (MvPolynomial.map σ)).minimalPrimes) :
    W.comap (MvPolynomial.map σ) = I := by
  let : Algebra K L := σ.toAlgebra
  let : Algebra (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) L) := algebraMvPolynomial
  have : Module.Free K L := Module.Free.of_divisionRing K L
  have : Module.Flat (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) L) :=
    Module.Flat.isBaseChange K (MvPolynomial (Fin n) K) L (MvPolynomial (Fin n) L)
      Algebra.IsPushout.out
  have halg : algebraMap (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) L) = MvPolynomial.map σ :=
    rfl
  obtain ⟨⟨hWp, hIW⟩, hmin⟩ := hW
  have := hWp
  have hIP : I ≤ W.comap (MvPolynomial.map σ) := Ideal.map_le_iff_le_comap.mp hIW
  have : (W.comap (MvPolynomial.map σ)).IsPrime := Ideal.comap_isPrime _ W
  have : W.LiesOver (W.comap (MvPolynomial.map σ)) := ⟨by rw [Ideal.under_def, halg]⟩
  obtain ⟨W', hW'W, hW'p, hW'I⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := I) W hIP
  have hI' : I = W'.comap (MvPolynomial.map σ) := by rw [hW'I.over, Ideal.under_def, halg]
  have hIW' : I.map (MvPolynomial.map σ) ≤ W' := Ideal.map_le_iff_le_comap.mpr hI'.le
  have hWW' : W ≤ W' := hmin ⟨hW'p, hIW'⟩ hW'W
  rw [hI', le_antisymm hW'W hWW']

theorem BaseChangeAvoid.proof : BaseChangeAvoid.Statement := by
  intro K _ _ n I u σ hI hu W hW h
  have hW' : W ∈ relComps (I.map (MvPolynomial.map σ)) := by
    by_contra hn
    rw [Finsupp.mem_support_iff] at hW
    exact hW (by simp [fundCycle, Finsupp.onFinset_apply, hn])
  have := hI.isPrime
  have hc := BaseChangeAvoid.comap_eq_of_mem_minimalPrimes σ I hW'.1
  apply hu
  rw [← hc, Ideal.mem_comap]
  convert h using 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp [linForm, map_sum]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeHyperplaneNull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem ConeHyperplaneNull.proof (hZ : ZeroLocusDimH.Statement) (hC : ChowFormDimLe.Statement) :
    ConeHyperplaneNull.Statement := by
  intro n e h W f u hW hf hu
  have := hW.isPrime
  set J : Ideal (MvPolynomial (Fin n) ℂ) := W ⊔ Ideal.span {linForm u} with hJ

  have hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (e : ℕ) := by
    have h1 := hC ℂ n (e + 1) W f hW hf
    have hr : Ideal.Quotient.mk W (linForm u) ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ W) :=
      mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    have h2 := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor (le_sup_left : W ≤ J))
      (Ideal.Quotient.factor_surjective _) hr
      (by rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have h3 := h2.trans h1
    generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = a at h3 ⊢
    induction a using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe a =>
      induction a using ENat.recTopCoe with
      | top => exact absurd h3 (by norm_cast)
      | coe m =>
        have : m + 1 ≤ e + 1 := by exact_mod_cast h3
        exact_mod_cast (by omega : m ≤ e)

  let g : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n → ℂ) :=
    (Matrix.transpose h.mat).mulVecLin.comp (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap
  have hg : ∀ y, g y = h.pointOf y := fun _ => rfl
  have hinj : Function.Injective g := by
    have hu : IsUnit (Matrix.transpose h.mat) := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]; exact h.isUnit_det
    exact (Matrix.mulVec_injective_iff_isUnit.mpr hu).comp
      (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).injective
  obtain ⟨K, -, hK⟩ := (LinearMap.injective_iff_antilipschitz g).mp hinj

  have hsub : coneBall h W ∩ {y | ∑ j, u j * h.pointOf y j = 0} ⊆
      g ⁻¹' {x | ∀ q ∈ J, eval x q = 0} := by
    rintro y ⟨⟨-, hyW⟩, hyu⟩
    have hle : J ≤ RingHom.ker (eval (h.pointOf y)) := by
      refine sup_le (fun q hq => (RingHom.mem_ker).2 (hyW q hq)) ?_
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [linForm, map_sum] using hyu
    intro q hq
    rw [hg]
    exact (RingHom.mem_ker).1 (hle hq)
  have hdimH : dimH (coneBall h W ∩ {y | ∑ j, u j * h.pointOf y j = 0}) ≤ 2 * (e : ENNReal) :=
    (dimH_mono hsub).trans ((hK.dimH_preimage_le _).trans (hZ n e J hdim))
  have hlt : dimH (coneBall h W ∩ {y | ∑ j, u j * h.pointOf y j = 0}) <
      (((2 * (e + 1) : ℕ) : NNReal) : ENNReal) := by
    refine hdimH.trans_lt ?_
    rw [ENNReal.coe_natCast]
    exact_mod_cast (by omega : 2 * e < 2 * (e + 1))
  rw [show ((2 * (e + 1) : ℕ) : ℝ) = (((2 * (e + 1) : ℕ) : NNReal) : ℝ) from
    (NNReal.coe_natCast _).symm]
  exact hausdorffMeasure_of_dimH_lt hlt

end

end GroundTheory.Heights₂.Heights
end

