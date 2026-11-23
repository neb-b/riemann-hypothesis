module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsSectionOrder

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeFsLogIntegrable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Set Matrix Filter

noncomputable section

namespace ConeFsLog

variable {n : ℕ}

theorem dualNorm_pointOf (h : HermNorm n) (y : EuclideanSpace ℂ (Fin n)) :
    h.dualNorm (h.pointOf y) = ‖y‖ := by
  have hA : IsUnit h.matᵀ.det := by rw [Matrix.det_transpose]; exact h.isUnit_det
  rw [HermNorm.dualNorm, HermNorm.pointOf, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA,
    Matrix.one_mulVec, EuclideanSpace.norm_eq]

theorem sum_mul_pointOf (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    ∑ j, u j * h.pointOf y j = ∑ i, (h.mat *ᵥ u) i * y i := by
  simp only [HermNorm.pointOf, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem norm_sum_mul_pointOf_le (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    ‖∑ j, u j * h.pointOf y j‖ ≤ h.norm u * ‖y‖ := by
  rw [sum_mul_pointOf, HermNorm.norm, EuclideanSpace.norm_eq]
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_mul]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

theorem fsLog_pointOf (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    fsLog h u (h.pointOf y) = Real.log (‖∑ j, u j * h.pointOf y j‖ / ‖y‖) := by
  rw [fsLog, dualNorm_pointOf]

theorem fsLog_pointOf_le (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) :
    fsLog h u (h.pointOf y) ≤ max (Real.log (h.norm u)) 0 := by
  rw [fsLog_pointOf]
  rcases (div_nonneg (norm_nonneg _) (norm_nonneg y) :
    0 ≤ ‖∑ j, u j * h.pointOf y j‖ / ‖y‖).eq_or_lt with hr | hr
  · rw [← hr, Real.log_zero]; exact le_max_right _ _
  · refine (Real.log_le_log hr ?_).trans (le_max_left _ _)
    have hy : 0 < ‖y‖ := by
      rcases (norm_nonneg y).eq_or_lt with h0 | h0
      · simp [← h0] at hr
      · exact h0
    exact (div_le_iff₀ hy).mpr (norm_sum_mul_pointOf_le h u y)

theorem norm_le_of_fsLog_le (h : HermNorm n) (u : Fin n → ℂ) (y : EuclideanSpace ℂ (Fin n)) {t : ℝ}
    (hy : fsLog h u (h.pointOf y) ≤ -t) :
    ‖∑ j, u j * h.pointOf y j‖ ≤ Real.exp (-t) * ‖y‖ := by
  rw [fsLog_pointOf] at hy
  rcases (norm_nonneg y).eq_or_lt with h0 | h0
  · have := norm_sum_mul_pointOf_le h u y
    rw [← h0, mul_zero] at this
    rw [← h0, mul_zero]; exact this
  rcases (norm_nonneg (∑ j, u j * h.pointOf y j)).eq_or_lt with ha | ha
  · rw [← ha]; positivity
  · have := (Real.log_le_iff_le_exp (div_pos ha h0)).mp hy
    rwa [div_le_iff₀ h0] at this

end ConeFsLog


open ConeFsLog in
theorem ConeFsLogIntegrable.proof (hfin : ConeBallFinite.Statement)
    (hslab : ConeSlabBound.Statement) : ConeFsLogIntegrable.Statement := by
  intro n e h W f u hW hf hu
  have hS := hfin n e h W f hW hf
  obtain ⟨C, α, hα, hC⟩ := hslab n e h W f u hW hf hu
  set μ := (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)).restrict (coneBall h W)
  set F : EuclideanSpace ℂ (Fin n) → ℝ := fun y => fsLog h u (h.pointOf y) with hFdef
  set M := max (Real.log (h.norm u)) 0
  have hFm : Measurable F := by
    have : F = fun y => Real.log (‖∑ j, u j * h.pointOf y j‖ / ‖y‖) :=
      funext fun y => fsLog_pointOf h u y
    rw [this]
    have hp : Continuous (fun y : EuclideanSpace ℂ (Fin n) => h.pointOf y) := by
      unfold HermNorm.pointOf; fun_prop
    refine Real.measurable_log.comp (Measurable.div ?_ measurable_norm)
    exact (continuous_finsetSum _ fun j _ =>
      continuous_const.mul ((continuous_apply j).comp hp)).norm.measurable
  set G : EuclideanSpace ℂ (Fin n) → ℝ := fun y => max (-F y) 0
  have hGm : Measurable G := hFm.neg.max measurable_const

  have hG : ∫⁻ y, ENNReal.ofReal (G y) ∂μ < ⊤ := by
    rw [lintegral_eq_lintegral_meas_le (f := G) μ (Filter.Eventually.of_forall fun y => le_max_right _ _)
      hGm.aemeasurable]
    have hint : IntegrableOn (fun t => C * Real.exp (-α * t)) (Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 hα).const_mul C
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) hint.lintegral_lt_top
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t (ht : 0 < t) => ?_)
    rw [Measure.restrict_apply (measurableSet_le measurable_const hGm)]
    refine (measure_mono ?_).trans ((hC (Real.exp (-t)) (Real.exp_pos _)
      (Real.exp_le_one_iff.mpr (by linarith))).trans_eq ?_)
    · rintro y ⟨hy, hyS⟩
      refine ⟨hyS, norm_le_of_fsLog_le h u y ?_⟩
      have : t ≤ -F y := by
        rcases le_max_iff.mp (show t ≤ G y from hy) with h1 | h1
        · exact h1
        · linarith
      change F y ≤ -t; linarith
    · rw [← Real.exp_mul]; ring_nf
  refine ⟨hFm.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hle : ∀ y, ‖F y‖ₑ ≤ ENNReal.ofReal M + ENNReal.ofReal (G y) := by
    intro y
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := fsLog_pointOf_le h u y
    rcases le_or_gt 0 (F y) with h2 | h2
    · rw [abs_of_nonneg h2]; have := le_max_right (-F y) 0; linarith
    · rw [abs_of_neg h2]; have := le_max_left (-F y) 0; have := le_max_right (Real.log (h.norm u)) 0
      linarith
  refine lt_of_le_of_lt (lintegral_mono hle) ?_
  rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hS, hG⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeIntegralMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

noncomputable section

def zeroExt (m k : ℕ) : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin (m + k)) where
  toFun x := WithLp.toLp 2 (Fin.append (fun i => x i) 0)
  map_add' x y := by
    ext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp
  map_smul' c x := by
    ext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp

theorem norm_zeroExt (m k : ℕ) (x : EuclideanSpace ℂ (Fin m)) : ‖zeroExt m k x‖ = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, zeroExt, LinearMap.coe_mk, AddHom.coe_mk,
    Fin.sum_univ_add]
  simp

theorem isometry_zeroExt (m k : ℕ) : Isometry (zeroExt m k) :=
  AddMonoidHomClass.isometry_of_norm (zeroExt m k) (norm_zeroExt m k)

theorem coordBall_mass {n m : ℕ} (hmn : m ≤ n) :
    0 < Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, m ≤ (j : ℕ) → y j = 0} ∧
      Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)
        {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, m ≤ (j : ℕ) → y j = 0} < ⊤ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hset : {y : EuclideanSpace ℂ (Fin (m + k)) | ‖y‖ < 1 ∧ ∀ j : Fin (m + k), m ≤ (j : ℕ) → y j = 0} =
      zeroExt m k '' Metric.ball 0 1 := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_image, Metric.mem_ball, dist_zero_right]
    constructor
    · rintro ⟨hy, hz⟩
      refine ⟨WithLp.toLp 2 fun i => y (Fin.castAdd k i), ?_, ?_⟩
      · rw [← norm_zeroExt m k]
        convert hy using 2
        ext j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simp [zeroExt]
        · simp [zeroExt, hz (Fin.natAdd m i) (by simp)]
      · ext j
        refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simp [zeroExt]
        · simp [zeroExt, hz (Fin.natAdd m i) (by simp)]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨by rwa [norm_zeroExt], fun j hj => ?_⟩
      revert hj
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · intro hi
        simp at hi
        omega
      · intro _
        simp [zeroExt]
  rw [hset, (isometry_zeroExt m k).hausdorffMeasure_image (Or.inl (by positivity))]
  have hd : ((2 * m : ℕ) : ℝ) = (finrank ℝ (EuclideanSpace ℂ (Fin m)) : ℝ) := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  rw [hd]
  exact ⟨Metric.measure_ball_pos _ _ one_pos, measure_ball_lt_top⟩

def linProjₗ {m n : ℕ} (π : Fin m → Fin n → ℂ) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) where
  toFun := linProj π
  map_add' x y := by
    ext i
    simp [linProj, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext i
    simp [linProj, Finset.mul_sum, mul_left_comm]

theorem ae_fibreCount_eq_zero {n m : ℕ} (hnm : n < m) (h : HermNorm n)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (π : Fin m → Fin n → ℂ) :
    ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w = 0 := by
  set R := (LinearMap.range (linProjₗ π)).restrictScalars ℝ
  have hR : R ≠ ⊤ := by
    intro hT
    rw [Submodule.restrictScalars_eq_top_iff] at hT
    have h1 := LinearMap.finrank_range_le (linProjₗ π)
    rw [hT, finrank_top, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin] at h1
    omega
  have h0 : volume (R : Set (EuclideanSpace ℂ (Fin m))) = 0 := Measure.addHaar_submodule _ R hR
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with w hw
  rw [fibreCount, Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
  rintro y ⟨-, rfl⟩
  exact hw ⟨y, rfl⟩

theorem ConeIntegralMass.proof (hF : ConeFibreDegree.Statement) (hM : ConeMassOfFibre.Statement) :
    ConeIntegralMass.Statement := by
  intro n e δ h W f hW hf hδ
  have hfib := hF n e δ h W f hW hf hδ
  have hmass := hM n (e + 1) δ h W hW hfib
  unfold coneIntegral
  simp only [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
  rw [hmass]
  by_cases hn : e + 1 ≤ n
  · obtain ⟨hpos, hfin⟩ := coordBall_mass hn
    rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_div_assoc,
      div_self (ENNReal.toReal_pos hpos.ne' hfin.ne).ne', mul_one]
  · have hδ0 : δ = 0 := by
      have : (volume : Measure (Fin (e + 1) → Fin n → ℂ)).IsAddHaarMeasure :=
        Measure.pi.isAddHaarMeasure _
      have : (ae (volume : Measure (Fin (e + 1) → Fin n → ℂ))).NeBot := ae_neBot.2 (NeZero.ne _)
      have : (ae (volume : Measure (EuclideanSpace ℂ (Fin (e + 1))))).NeBot :=
        ae_neBot.2 (NeZero.ne _)
      obtain ⟨π, hπ⟩ := hfib.exists
      obtain ⟨w, hw1, hw2⟩ := (hπ.and (ae_fibreCount_eq_zero (by omega) h W π)).exists
      rw [hw1] at hw2
      exact_mod_cast hw2
    simp [hδ0]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeMapArea
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

theorem ConeMapArea.proof (h : ConeMapAreaOne.Statement) : ConeMapArea.Statement := by
  intro n e ι _ U D v F hUD hinj hF
  let g : ι → (Fin e → ℂ) × ℂ → EuclideanSpace ℂ (Fin n) := fun i q => q.2 • WithLp.toLp 2 (v i q.1)
  let S : ι → Set ((Fin e → ℂ) × ℂ) := fun i => {q | q.1 ∈ D i ∧ q.2 ≠ 0}
  have himg : (fun q : ι × (Fin e → ℂ) × ℂ => q.2.2 • WithLp.toLp 2 (v q.1 q.2.1)) ''
      {q | q.2.1 ∈ D q.1 ∧ q.2.2 ≠ 0} = ⋃ i, g i '' S i := by
    ext y
    simp only [Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro ⟨⟨i, x, t⟩, hq, rfl⟩
      exact ⟨i, (x, t), hq, rfl⟩
    · rintro ⟨i, ⟨x, t⟩, hq, rfl⟩
      exact ⟨(i, x, t), hq, rfl⟩
  have hinj_i : ∀ i, Set.InjOn (g i) (S i) := by
    intro i p hp p' hp' hpp
    exact (Prod.ext_iff.1 (@hinj (i, p) hp (i, p') hp' hpp)).2
  have hdisj : Pairwise (Function.onFun Disjoint fun i => g i '' S i) := by
    intro i j hij
    refine Set.disjoint_left.2 ?_
    rintro y ⟨p, hp, rfl⟩ ⟨p', hp', hpp⟩
    exact hij (congrArg Prod.fst (@hinj (j, p') hp' (i, p) hp hpp)).symm
  have hmeas : ∀ i, MeasurableSet (g i '' S i) := by
    intro i
    obtain ⟨-, hD, hDU, hv⟩ := hUD i
    refine MeasurableSet.image_of_continuousOn_injOn ?_ ?_ (hinj_i i)
    · exact (measurable_fst hD).inter (measurable_snd (measurableSet_singleton (0 : ℂ)).compl)
    · have hc : ContinuousOn (fun q : (Fin e → ℂ) × ℂ => WithLp.toLp 2 (v i q.1)) (S i) :=
        (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp_continuousOn
          ((hv.continuousOn.mono hDU).comp continuousOn_fst fun q hq => hq.1)
      exact continuousOn_snd.smul hc
  rw [himg, lintegral_iUnion hmeas hdisj, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun i => ?_
  obtain ⟨hU, hD, hDU, hv⟩ := hUD i
  exact h n e (U i) (D i) (v i) F hU hD hDU hv (hinj_i i) hF

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeMeetNull
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem ConeMeetNull.null_of_mem_not_mem (hZ : ZeroLocusDimH.Statement) {n e : ℕ} (h : HermNorm n)
    (W W' : Ideal (MvPolynomial (Fin n) ℂ)) [W.IsPrime]
    (hW : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) ≤ ((e + 1 : ℕ) : WithBot ℕ∞))
    (g : MvPolynomial (Fin n) ℂ) (hgW' : g ∈ W') (hgW : g ∉ W) :
    Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (coneBall h W ∩ coneBall h W') = 0 := by
  set J : Ideal (MvPolynomial (Fin n) ℂ) := W ⊔ Ideal.span {g} with hJ

  have hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (e : ℕ) :=
    ZeroLocusDimH.le_of_add_one_le_succ
      ((ZeroLocusDimH.ringKrullDim_quot_sup_add_one_le W g hgW).trans hW)

  let φ : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] (Fin n → ℂ) :=
    (Matrix.transpose h.mat).mulVecLin.comp (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap
  have hφ : ∀ y, φ y = h.pointOf y := fun _ => rfl
  have hinj : Function.Injective φ := by
    have hu : IsUnit (Matrix.transpose h.mat) := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]; exact h.isUnit_det
    exact (Matrix.mulVec_injective_iff_isUnit.mpr hu).comp
      (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).injective
  obtain ⟨K, -, hK⟩ := (LinearMap.injective_iff_antilipschitz φ).mp hinj

  have hsub : coneBall h W ∩ coneBall h W' ⊆ φ ⁻¹' {x | ∀ q ∈ J, eval x q = 0} := by
    rintro y ⟨⟨-, hyW⟩, ⟨-, hyW'⟩⟩
    have hle : J ≤ RingHom.ker (eval (h.pointOf y)) := by
      refine sup_le (fun q hq => (RingHom.mem_ker).2 (hyW q hq)) ?_
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      exact hyW' g hgW'
    intro q hq
    rw [hφ]
    exact (RingHom.mem_ker).1 (hle hq)
  have hdimH : dimH (coneBall h W ∩ coneBall h W') ≤ 2 * (e : ENNReal) :=
    (dimH_mono hsub).trans ((hK.dimH_preimage_le _).trans (hZ n e J hdim))
  have hlt : dimH (coneBall h W ∩ coneBall h W') < (((2 * (e + 1) : ℕ) : NNReal) : ENNReal) := by
    refine hdimH.trans_lt ?_
    rw [ENNReal.coe_natCast]
    exact_mod_cast (by omega : 2 * e < 2 * (e + 1))
  rw [show ((2 * (e + 1) : ℕ) : ℝ) = (((2 * (e + 1) : ℕ) : NNReal) : ℝ) from
    (NNReal.coe_natCast _).symm]
  exact hausdorffMeasure_of_dimH_lt hlt

theorem ConeMeetNull.proof (hZ : ZeroLocusDimH.Statement) : ConeMeetNull.Statement := by
  intro n e h W W' hWp hW'p hne hW hW'
  by_cases hle : W' ≤ W
  ·
    have hnle : ¬ W ≤ W' := fun h' => hne (le_antisymm h' hle)
    obtain ⟨g, hgW, hgW'⟩ := Set.not_subset.mp hnle
    rw [Set.inter_comm]
    exact ConeMeetNull.null_of_mem_not_mem hZ h W' W hW' g hgW hgW'
  · obtain ⟨g, hgW', hgW⟩ := Set.not_subset.mp hle
    exact ConeMeetNull.null_of_mem_not_mem hZ h W W' hW g hgW' hgW

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeSlabBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix

open scoped ENNReal NNReal

noncomputable section

theorem ConeSlabBound.proof (hV : VarietySlabMeasure.Statement) : ConeSlabBound.Statement := by
  intro n e h W f u hW hf hu
  have hWp : W.IsPrime := hW.isPrime
  have hdim := ChowFormDimLe.proof ℂ n (e + 1) W f hW hf

  let E := WithLp.linearEquiv 2 ℂ (Fin n → ℂ)
  let F : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (E.symm.toLinearMap ∘ₗ h.matᵀ.mulVecLin ∘ₗ E.toLinearMap)
  let L : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (E.symm.toLinearMap ∘ₗ (h.matᵀ)⁻¹.mulVecLin ∘ₗ E.toLinearMap)
  have hF : ∀ y i, F y i = h.pointOf y i := fun _ _ => rfl
  have hdet : IsUnit (h.matᵀ).det := by rw [Matrix.det_transpose]; exact h.isUnit_det
  have hLF : ∀ y, L (F y) = y := by
    intro y
    ext i
    change ((h.matᵀ)⁻¹ *ᵥ (h.matᵀ *ᵥ fun j => y j)) i = y i
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  obtain ⟨C, α, hC, hα, hb⟩ := hV n (e + 1) W u hWp hdim hu ‖F‖
  set s : ℝ := ((2 * (e + 1) : ℕ) : ℝ) with hs
  have hs0 : 0 ≤ s := Nat.cast_nonneg _
  let K : ℝ≥0 := ‖L‖₊
  refine ⟨(K : ℝ) ^ s * C, α, hα, fun ε hε hε1 => ?_⟩

  have hsub : coneBall h W ∩ {y | ‖∑ j, u j * h.pointOf y j‖ ≤ ε * ‖y‖} ⊆
      L '' {z | z ∈ zeroSetEuc W ∧ ‖z‖ ≤ ‖F‖ ∧ ‖∑ j, u j * z j‖ ≤ ε} := by
    rintro y ⟨⟨hy1, hyW⟩, hyu⟩
    refine ⟨F y, ⟨fun q hq => ?_, ?_, ?_⟩, hLF y⟩
    · have : (fun i => F y i) = h.pointOf y := funext (hF y)
      rw [this]
      exact hyW q hq
    · calc ‖F y‖ ≤ ‖F‖ * ‖y‖ := F.le_opNorm y
        _ ≤ ‖F‖ * 1 := mul_le_mul_of_nonneg_left hy1.le (norm_nonneg _)
        _ = ‖F‖ := mul_one _
    · simp only [hF]
      calc ‖∑ j, u j * h.pointOf y j‖ ≤ ε * ‖y‖ := hyu
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hy1.le hε.le
        _ = ε := mul_one _
  calc μH[s] (coneBall h W ∩ {y | ‖∑ j, u j * h.pointOf y j‖ ≤ ε * ‖y‖})
      ≤ μH[s] (L '' {z | z ∈ zeroSetEuc W ∧ ‖z‖ ≤ ‖F‖ ∧ ‖∑ j, u j * z j‖ ≤ ε}) := measure_mono hsub
    _ ≤ (K : ℝ≥0∞) ^ s * μH[s] {z | z ∈ zeroSetEuc W ∧ ‖z‖ ≤ ‖F‖ ∧ ‖∑ j, u j * z j‖ ≤ ε} :=
        L.lipschitz.hausdorffMeasure_image_le hs0 _
    _ ≤ (K : ℝ≥0∞) ^ s * ENNReal.ofReal (C * ε ^ α) := by
        gcongr
        exact hb ε hε hε1
    _ = ENNReal.ofReal ((K : ℝ) ^ s * C * ε ^ α) := by
        rw [mul_assoc, ENNReal.ofReal_mul (Real.rpow_nonneg K.coe_nonneg _),
          ← ENNReal.ofReal_rpow_of_nonneg K.coe_nonneg hs0, ENNReal.ofReal_coe_nnreal]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartLengthAlgClosed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section


open Classical in
def ChartLengthAlgClosed.Statement : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t u : Fin n → F)
    (q : MvPolynomial (Fin e × Fin n) F) (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I → Prime q → p = Ideal.span {q} →
      ¬ q ∣ specFirst f t →
        Module.length (Localization.AtPrime p) (ChartLoc I t e p ⧸ LinearMap.range
            (LinearMap.mulLeft (Localization.AtPrime p)
              (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u)))) =
          ∑ W ∈ (divCycle I u).support with Ideal.span {q} = incIdeal W e,
            ((divCycle I u W : ℕ) : ℕ∞)

end

end GroundTheory.Heights₂.Heights
end

