module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0004

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAreaGraphPartition
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped ENNReal NNReal
open Set Metric

noncomputable section

theorem AreaGraphPartition.proof : AreaGraphPartition.Statement := by
  intro k m U F hU hF r hr

  have hcont : ContinuousOn (fderiv ℝ F) U := hF.continuousOn_fderiv_of_isOpen hU le_rfl
  have hdiff : ∀ x ∈ U, DifferentiableAt ℝ F x := fun x hx =>
    (hF.differentiableOn one_ne_zero x hx).differentiableAt (hU.mem_nhds hx)

  have hball : ∀ x : U, ∃ ε > 0, ball (x : EuclideanSpace ℝ (Fin k)) ε ⊆ U ∧
      ∀ y ∈ ball (x : EuclideanSpace ℝ (Fin k)) ε, ‖fderiv ℝ F y - fderiv ℝ F x‖ ≤ r (fderiv ℝ F x) := by
    intro x
    have hpos : (0 : ℝ) < r (fderiv ℝ F x) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 (hr _))
    have hca : ContinuousAt (fderiv ℝ F) x := hcont.continuousAt (hU.mem_nhds x.2)
    obtain ⟨δ, δpos, hδ⟩ := Metric.continuousAt_iff.1 hca _ hpos
    obtain ⟨η, ηpos, hη⟩ := Metric.isOpen_iff.1 hU x x.2
    refine ⟨min δ η, lt_min δpos ηpos, (ball_subset_ball (min_le_right _ _)).trans hη, ?_⟩
    intro y hy
    have := hδ (lt_of_lt_of_le (mem_ball.1 hy) (min_le_left _ _))
    rw [dist_eq_norm] at this
    exact this.le
  choose ε εpos hεU hεD using hball

  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : U => ball (x : EuclideanSpace ℝ (Fin k)) (ε x)) (fun _ => isOpen_ball)
  have hcover : (⋃ x : U, ball (x : EuclideanSpace ℝ (Fin k)) (ε x)) = U := by
    apply Subset.antisymm
    · exact iUnion_subset fun x => hεU x
    · intro x hx
      exact mem_iUnion.2 ⟨⟨x, hx⟩, mem_ball_self (εpos _)⟩
  rcases U.eq_empty_or_nonempty with hUe | hUne
  ·
    refine ⟨fun _ => ∅, fun _ => 0, fun _ _ _ => disjoint_empty _, fun _ => MeasurableSet.empty,
      fun _ => empty_subset _, by simp [hUe], fun _ => fun x hx => absurd hx (notMem_empty x),
      fun _ x hx => absurd hx (notMem_empty x)⟩
  have hTne : T.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    obtain ⟨x, hx⟩ := hUne
    have : x ∈ ⋃ i ∈ T, ball ((i : U) : EuclideanSpace ℝ (Fin k)) (ε i) := by rw [hTU, hcover]; exact hx
    simp [h] at this
  obtain ⟨c, hc⟩ := hTc.exists_eq_range hTne
  set B : ℕ → Set (EuclideanSpace ℝ (Fin k)) := fun n => ball ((c n : U) : EuclideanSpace ℝ (Fin k)) (ε (c n)) with hB
  have hBU : ⋃ n, B n = U := by
    rw [← hcover, ← hTU, hc, biUnion_range]
  refine ⟨disjointed B, fun n => fderiv ℝ F (c n), disjoint_disjointed B,
    MeasurableSet.disjointed (fun n => measurableSet_ball), fun n => (disjointed_subset B n).trans
    (hεU (c n)), by rw [iUnion_disjointed, hBU], ?_, ?_⟩
  · intro n x hx y hy
    have hx' := disjointed_subset B n hx
    have hy' := disjointed_subset B n hy
    exact (convex_ball _ _).norm_image_sub_le_of_norm_fderiv_le'
      (fun z hz => hdiff z (hεU (c n) hz)) (fun z hz => hεD (c n) z hz) hy' hx'
  · intro n x hx
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact hεD (c n) x (disjointed_subset B n hx)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAreaMultiplicity
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module Set Filter Function

open scoped ENNReal NNReal

noncomputable section

theorem areaJacobian_eq_abs_det_comp {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (φ : F ≃ₗᵢ[ℝ] E) (L : E →ₗ[ℝ] F) :
    areaJacobian L = |LinearMap.det (φ.toLinearIsometry.toLinearMap ∘ₗ L)| := by
  have h1 : areaJacobian L = L.normDet := by
    have h := L.normDet_sq
    simp only [RCLike.ofReal_real_eq_id, id_eq] at h
    rw [areaJacobian, ← h, Real.sqrt_sq L.normDet_nonneg]
  rw [h1, ← LinearMap.normDet_eq_abs_det,
    LinearMap.normDet_comp_of_finrank_eq _ _ φ.toLinearEquiv.finrank_eq.symm,
    φ.toLinearIsometry.normDet_eq_one, one_mul]

theorem encard_iUnion_nat_eq_tsum {α : Type*} (s : ℕ → Set α) (hs : Pairwise (Disjoint on s)) :
    (((⋃ n, s n).encard : ℕ∞) : ℝ≥0∞) = ∑' n, (((s n).encard : ℕ∞) : ℝ≥0∞) := by
  let _ : MeasurableSpace α := ⊤
  have hm : ∀ t : Set α, MeasurableSet t := fun _ => MeasurableSpace.measurableSet_top
  rw [← Measure.count_apply (hm _), measure_iUnion hs (fun _ => hm _)]
  simp only [Measure.count_apply (hm _)]

theorem lintegral_abs_det_eq_lintegral_encard {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {A : Set E} {f : E → E} {f' : E → E →L[ℝ] E}
    (hA : MeasurableSet A) (hf' : ∀ x ∈ A, HasFDerivWithinAt f (f' x) A x) :
    ∫⁻ x in A, ENNReal.ofReal |(f' x).det| ∂μ =
      ∫⁻ y, (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞) ∂μ := by
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
  calc ∫⁻ x in A, ENNReal.ofReal |(f' x).det| ∂μ
      = ∫⁻ x in B, ENNReal.ofReal |(f' x).det| ∂μ := by
        rw [← lintegral_indicator hA, ← lintegral_indicator₀ hB]
        congr 1; ext x
        by_cases hx : x ∈ A
        · by_cases hd : (f' x).det = 0
          · simp [indicator, hx, hd, B]
          · simp [indicator, hx, hd, B]
        · have : x ∉ B := fun h => hx h.1
          simp [hx, this]
    _ = ∑' n, ∫⁻ x in P n, ENNReal.ofReal |(f' x).det| ∂μ := by
        rw [hBU]; exact lintegral_iUnion₀ hPm (fun m n hmn => (hPd hmn).aedisjoint) _
    _ = ∑' n, μ (f '' P n) := tsum_congr fun n =>
        lintegral_abs_det_fderiv_eq_addHaar_image₀ μ (hPm n) (hderP n) (hinj n)
    _ = ∑' n, ∫⁻ y, (f '' P n).indicator 1 y ∂μ :=
        tsum_congr fun n => (lintegral_indicator_one₀ (himg n)).symm
    _ = ∫⁻ y, ∑' n, (f '' P n).indicator 1 y ∂μ :=
        (lintegral_tsum fun n => aemeasurable_one.indicator₀ (himg n)).symm
    _ = ∫⁻ y, (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞) ∂μ := by
        apply lintegral_congr_ae
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

theorem AreaMultiplicity.proof : AreaMultiplicity.Statement := by
  intro E F _ _ _ _ _ _ _ _ _ _ k hE hF A f f' hA hf'
  subst hE
  let φ : F ≃ₗᵢ[ℝ] E := (stdOrthonormalBasis ℝ F).equiv (stdOrthonormalBasis ℝ E) (finCongr hF)
  let g : E → E := fun x => φ (f x)
  let g' : E → E →L[ℝ] E := fun x => (φ.toContinuousLinearEquiv : F →L[ℝ] E).comp (f' x)
  have hg' : ∀ x ∈ A, HasFDerivWithinAt g (g' x) A x := fun x hx =>
    (φ.toContinuousLinearEquiv : F →L[ℝ] E).hasFDerivAt.comp_hasFDerivWithinAt x (hf' x hx)
  have hJ : ∀ x, ENNReal.ofReal (areaJacobian (f' x : E →ₗ[ℝ] F)) =
      ENNReal.ofReal |(g' x).det| := by
    intro x
    rw [areaJacobian_eq_abs_det_comp φ]
    rfl
  have hN : ∀ y, {x ∈ A | f x = y} = {x ∈ A | g x = φ y} := by
    intro y; ext x; simp [g]
  simp_rw [hJ, hN]
  rw [lintegral_abs_det_eq_lintegral_encard μH[(finrank ℝ E : ℝ)] hA hg']
  have hφ : MeasurePreserving φ (μH[(finrank ℝ E : ℝ)] : Measure F) μH[(finrank ℝ E : ℝ)] :=
    φ.toIsometryEquiv.measurePreserving_hausdorffMeasure _
  have hφe : MeasurableEmbedding φ := φ.toHomeomorph.measurableEmbedding
  exact (hφ.lintegral_comp_emb hφe (fun z => (({x ∈ A | g x = z}.encard : ℕ∞) : ℝ≥0∞))).symm

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBadSetSmaller
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

theorem eval_pullback {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (P : MvPolynomial (Fin d) ℂ)
    (x : Fin n → ℂ) : eval x (pullback A P) = eval (A.mulVec x) P := by
  have h : ∀ i, eval x (linPoly A i) = A.mulVec x i := by
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [linPoly, Matrix.mulVec, dotProduct, map_sum]
  rw [pullback, aeval_eq_bind₁]
  change eval₂Hom (RingHom.id ℂ) x (bind₁ (linPoly A) P) = eval₂Hom (RingHom.id ℂ) (A.mulVec x) P
  rw [eval₂Hom_bind₁]
  congr 2
  funext i
  exact h i

theorem zeroSet_sup_span {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (f : MvPolynomial (Fin n) ℂ) :
    zeroSet (J ⊔ Ideal.span {f}) = zeroSet J ∩ {x | eval x f = 0} := by
  ext x
  have key : ∀ I : Ideal (MvPolynomial (Fin n) ℂ),
      (∀ q ∈ I, eval x q = 0) ↔ I ≤ RingHom.ker (eval x) :=
    fun I => ⟨fun h q hq => (RingHom.mem_ker).2 (h q hq), fun h q hq => (RingHom.mem_ker).1 (h hq)⟩
  simp only [zeroSet, Set.mem_ofPred_eq, Set.mem_inter_iff]
  rw [key, key, sup_le_iff, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]

theorem BadSetSmaller.proof : BadSetSmaller.Statement := by
  intro n d J A hJ hd hA P hP
  refine ⟨?_, ?_⟩
  · rw [zeroSet_sup_span]
    ext x
    simp [eval_pullback]
  · intro Q hQ
    have := hJ
    set f := pullback A P with hfdef
    have hf : Ideal.Quotient.mk J f ≠ 0 := by
      intro h0
      apply hP
      apply hA.injective
      rw [map_zero]
      simpa [projHom] using h0
    have hnz : Ideal.Quotient.mk J f ∈ nonZeroDivisors (MvPolynomial (Fin n) ℂ ⧸ J) :=
      mem_nonZeroDivisors_of_ne_zero hf
    have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnz
    have hmap : (Ideal.span {f}).map (Ideal.Quotient.mk J) = Ideal.span {Ideal.Quotient.mk J f} := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [← hmap, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup J _), hd] at h1
    have h2 : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ Q) ≤
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (J ⊔ Ideal.span {f})) :=
      ringKrullDim_le_of_surjective (Ideal.Quotient.factor hQ.1.2)
        (Ideal.Quotient.factor_surjective hQ.1.2)
    exact lt_of_le_of_lt h2 (ENat.WithBot.add_one_le_natCast_iff.mp h1)

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PBrouwerFixedPoint
section
set_option maxSynthPendingDepth 1

open scoped ContDiff
open Metric

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem BrouwerFixedPoint.smooth_of_changeOfVariablesDegree
    (hL : ChangeOfVariablesDegree.Statement) (n : ℕ) (g : (Fin n → ℝ) → Fin n → ℝ)
    (hg : ContDiff ℝ ∞ g) (hgb : ∀ x, ‖g x‖ ≤ 1) : ∃ x, g x = x := by
  by_contra hne
  push Not at hne
  have hcont : ContinuousOn (fun x => ‖x - g x‖) (closedBall (0 : Fin n → ℝ) 2) :=
    (continuous_id.sub hg.continuous).norm.continuousOn
  obtain ⟨x₀, -, hmin⟩ := (isCompact_closedBall (0 : Fin n → ℝ) 2).exists_isMinOn
    (nonempty_closedBall.2 zero_le_two) hcont
  have hε : 0 < ‖x₀ - g x₀‖ := norm_pos_iff.2 (sub_ne_zero.2 (hne x₀).symm)
  set δ := min ‖x₀ - g x₀‖ 1 with hδ_def
  have hδ : 0 < δ := lt_min hε one_pos

  let χ : ContDiffBump (0 : Fin n → ℝ) := ⟨2, 3, two_pos, by norm_num⟩
  let φ : (Fin n → ℝ) → Fin n → ℝ := fun x => x - χ x • g x
  have hφ : ContDiff ℝ ∞ φ := contDiff_id.sub (χ.contDiff.smul hg)
  have hφc : HasCompactSupport (fun x => φ x - x) := by
    have h : (fun x => φ x - x) = -((fun x => χ x) • g) := by
      funext x; simp [φ]
    rw [h]
    exact χ.hasCompactSupport.smul_right.neg
  have hφδ : ∀ x, δ ≤ ‖φ x‖ := by
    intro x
    by_cases hx : ‖x‖ ≤ 2
    · have hχ : χ x = 1 := χ.one_of_mem_closedBall (mem_closedBall_zero_iff.2 hx)
      have h2 : ‖x₀ - g x₀‖ ≤ ‖x - g x‖ :=
        isMinOn_iff.1 hmin x (mem_closedBall_zero_iff.2 hx)
      simp only [φ, hχ, one_smul]
      exact (min_le_left _ _).trans h2
    · push Not at hx
      have h1 : ‖χ x • g x‖ ≤ 1 := by
        rw [norm_smul, Real.norm_of_nonneg χ.nonneg]
        exact mul_le_one₀ χ.le_one (norm_nonneg _) (hgb x)
      have h3 : ‖x‖ - ‖χ x • g x‖ ≤ ‖φ x‖ := norm_sub_norm_le _ _
      have h4 : δ ≤ 1 := min_le_right _ _
      linarith

  let ψ : ContDiffBump (0 : Fin n → ℝ) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  have hzero : ∀ x, ψ (φ x) = 0 := by
    intro x
    by_contra h
    have hmem : φ x ∈ ball (0 : Fin n → ℝ) δ := by
      rw [← ψ.support_eq]; exact h
    rw [mem_ball_zero_iff] at hmem
    exact absurd (hφδ x) (not_le.2 hmem)
  have hL' := hL n φ hφ hφc ψ ψ.contDiff ψ.hasCompactSupport
  simp only [hzero, zero_mul, MeasureTheory.integral_zero] at hL'
  exact (ψ.integral_pos (μ := MeasureTheory.volume)).ne hL'

theorem BrouwerFixedPoint.proof (hL : ChangeOfVariablesDegree.Statement) :
    BrouwerFixedPoint.Statement := by
  intro n f hf hmaps
  by_contra hne
  push Not at hne
  set B := closedBall (0 : Fin n → ℝ) 1 with hB_def
  have hB : IsCompact B := isCompact_closedBall _ _
  have hcont : ContinuousOn (fun x => ‖f x - x‖) B := (hf.sub continuousOn_id).norm
  obtain ⟨x₀, hx₀, hmin⟩ := hB.exists_isMinOn (nonempty_closedBall.2 zero_le_one) hcont
  have hε : 0 < ‖f x₀ - x₀‖ := norm_pos_iff.2 (sub_ne_zero.2 (hne x₀ hx₀))

  let P : (Fin n → ℝ) → Fin n → ℝ := fun x i => max (min (x i) 1) (-1)
  have hPB : ∀ x, P x ∈ B := by
    intro x
    rw [hB_def, mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨le_max_right _ _, max_le (min_le_right _ _) (by norm_num)⟩
  have hPid : ∀ x ∈ B, P x = x := by
    intro x hx
    funext i
    have hi : |x i| ≤ 1 := by
      have h := (norm_le_pi_norm x i).trans (mem_closedBall_zero_iff.1 hx)
      rwa [Real.norm_eq_abs] at h
    rw [abs_le] at hi
    simp only [P, min_eq_left hi.2, max_eq_left hi.1]
  have hPlip : ∀ x y, dist (P x) (P y) ≤ dist x y := by
    intro x y
    refine (dist_pi_le_iff dist_nonneg).2 fun i => ?_
    calc dist (P x i) (P y i) = |max (min (x i) 1) (-1) - max (min (y i) 1) (-1)| :=
          Real.dist_eq _ _
      _ ≤ |min (x i) 1 - min (y i) 1| := abs_max_sub_max_le_abs _ _ _
      _ ≤ max |x i - y i| |1 - 1| := abs_min_sub_min_le_max _ _ _ _
      _ = dist (x i) (y i) := by simp [Real.dist_eq]
      _ ≤ dist x y := dist_le_pi_dist x y i

  let F : (Fin n → ℝ) → Fin n → ℝ := fun x => f (P x)
  have hFu : UniformContinuous F := by
    have hfu : UniformContinuousOn f B := hB.uniformContinuousOn_of_continuous hf
    rw [Metric.uniformContinuous_iff]
    intro η hη
    obtain ⟨d, hd, hfd⟩ := Metric.uniformContinuousOn_iff.1 hfu η hη
    exact ⟨d, hd, fun {a b} hab => hfd _ (hPB a) _ (hPB b) ((hPlip a b).trans_lt hab)⟩
  have hFB : ∀ x, ‖F x‖ ≤ 1 := fun x => mem_closedBall_zero_iff.1 (hmaps (hPB x))

  set a := ‖f x₀ - x₀‖ / 3 with ha_def
  have ha : 0 < a := by positivity
  obtain ⟨G, hG, hGF⟩ := hFu.exists_contDiff_dist_le ha
  set c := (1 + a)⁻¹ with hc_def
  have hc : c * (1 + a) = 1 := inv_mul_cancel₀ (by positivity)
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hGb : ∀ x, ‖G x‖ ≤ 1 + a := by
    intro x
    have h1 : ‖G x‖ ≤ ‖F x‖ + ‖G x - F x‖ := norm_le_norm_add_norm_sub' _ _
    have h2 : ‖G x - F x‖ < a := by rw [← dist_eq_norm]; exact hGF x
    linarith [hFB x]
  have hgb : ∀ x, ‖c • G x‖ ≤ 1 := by
    intro x
    rw [norm_smul, Real.norm_of_nonneg hc0.le]
    calc c * ‖G x‖ ≤ c * (1 + a) := mul_le_mul_of_nonneg_left (hGb x) hc0.le
      _ = 1 := hc
  obtain ⟨x, hx⟩ := BrouwerFixedPoint.smooth_of_changeOfVariablesDegree hL n (fun x => c • G x)
    (hG.const_smul c) hgb
  have hx' : c • G x = x := hx
  have hxB : x ∈ B := by
    rw [hB_def, mem_closedBall_zero_iff, ← hx']
    exact hgb x
  have hFx : F x = f x := by simp only [F, hPid x hxB]
  have h1 : ‖f x - G x‖ < a := by
    rw [← hFx, ← dist_eq_norm, dist_comm]; exact hGF x
  have h2 : ‖G x - x‖ ≤ a := by
    have h : G x - x = (1 - c) • G x := by
      rw [sub_smul, one_smul, hx']
    rw [h, norm_smul, Real.norm_of_nonneg (by linarith)]
    have := hGb x
    nlinarith
  have h3 : ‖f x - x‖ ≤ ‖f x - G x‖ + ‖G x - x‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
  have h4 : ‖f x₀ - x₀‖ ≤ ‖f x - x‖ := isMinOn_iff.1 hmin x hxB
  linarith

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeScaling
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial Pointwise

theorem eval_smul_of_isHomogeneous {n i : ℕ} {φ : MvPolynomial (Fin n) ℂ} (hφ : φ.IsHomogeneous i)
    (t : ℂ) (x : Fin n → ℂ) : eval (t • x) φ = t ^ i * eval x φ := by
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ j ∈ d.support, d j = i := by
    have h := hφ (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdeg]
  ring


end GroundTheory.Heights₂.Heights.ComplexSets
end

