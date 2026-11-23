module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0029
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0030
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PClosedPointChartField
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial

theorem ClosedPointChartField.proof : ClosedPointChartField.Statement := by
  intro F _ n I i hI hdim hXi
  have := hI.isPrime
  set ξ := genPt I
  have hξ : ξ i ≠ 0 := fun h =>
    hXi ((ChartZeroTrdeg.aeval_genPt_eq_zero_iff' I (X i)).1 (by simpa using h))
  set g : MvPolynomial (Fin n) F →ₐ[F] FractionRing (MvPolynomial (Fin n) F ⧸ I) :=
    aeval fun m => ξ m * (ξ i)⁻¹ with hg

  have hhom : ∀ (h : MvPolynomial (Fin n) F) (d : ℕ), h.IsHomogeneous d →
      ChartZeroTrdeg.homogAt h i d = h := by
    intro h d hh
    conv_rhs => rw [h.as_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    have hα' : (α.sum fun _ e => e) = d := by
      have := hh (mem_support_iff.mp hα)
      simpa [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] using this
    rw [hα', Nat.sub_self, pow_zero, mul_one]

  have hker : RingHom.ker g = I ⊔ Ideal.span {X i - 1} := by
    apply le_antisymm
    · intro p hp
      rw [RingHom.mem_ker] at hp
      have hH : ChartZeroTrdeg.homogAt p i p.totalDegree ∈ I := by
        rw [← ChartZeroTrdeg.aeval_genPt_eq_zero_iff',
          ChartZeroTrdeg.aeval_homogAt p i _ le_rfl ξ hξ]
        rw [← hg, hp, mul_zero]
      have hd : p - ChartZeroTrdeg.homogAt p i p.totalDegree ∈ Ideal.span {X i - 1} := by
        rw [← Ideal.Quotient.eq]
        have h1 : Ideal.Quotient.mk (Ideal.span {X i - 1}) (X i : MvPolynomial (Fin n) F) = 1 := by
          rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
          exact Ideal.subset_span rfl
        conv_lhs => rw [p.as_sum]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [ChartZeroTrdeg.homogAt, map_sum, map_mul, map_pow, h1, one_pow, mul_one]
      have := (I ⊔ Ideal.span {X i - 1}).add_mem (Ideal.mem_sup_left hH) (Ideal.mem_sup_right hd)
      simpa using this
    · refine sup_le ?_ ?_
      · intro f hf
        set_option synthInstance.maxHeartbeats 100000 in
          rw [RingHom.mem_ker, ← sum_homogeneousComponent f, map_sum]
        refine Finset.sum_eq_zero fun d _ => ?_
        have hh : (homogeneousComponent d f).IsHomogeneous d :=
          homogeneousComponent_isHomogeneous d f
        have h0 : aeval ξ (homogeneousComponent d f) = 0 :=
          (ChartZeroTrdeg.aeval_genPt_eq_zero_iff' I _).2 (hI.isHomog f hf d)
        by_cases hz : homogeneousComponent d f = 0
        · rw [hz, map_zero]
        have := ChartZeroTrdeg.aeval_homogAt (homogeneousComponent d f) i d
          (hh.totalDegree hz).le ξ hξ
        rw [hhom _ d hh, h0] at this
        exact (mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero _ hξ)
      · rw [Ideal.span_le, Set.singleton_subset_iff]
        change g (X i - 1) = 0
        simp [hg, hξ]

  let e : (MvPolynomial (Fin n) F ⧸ (I ⊔ Ideal.span {X i - 1})) ≃ₐ[F] g.range :=
    (Ideal.quotientEquivAlgOfEq F (hker.symm.trans (AlgHom.ker_rangeRestrict g).symm)).trans
      (Ideal.quotientKerAlgEquivOfSurjective g.rangeRestrict_surjective)
  have htr := GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof F n 0 I i hI (by simpa using hdim) hXi
  rw [Algebra.adjoin_range_eq_range_aeval] at htr
  have halg : Algebra.IsAlgebraic F g.range := trdeg_eq_zero_iff.1 (by simpa using htr)
  have hfield : IsField g.range := isField_of_isIntegral_of_isField' (Field.toIsField F)
  have : Algebra.FiniteType F g.range :=
    Algebra.FiniteType.of_surjective g.rangeRestrict g.rangeRestrict_surjective
  have : Module.Finite F g.range := Algebra.IsIntegral.finite
  exact ⟨MulEquiv.isField hfield e.toMulEquiv, Module.Finite.equiv e.symm.toLinearEquiv⟩

end ObjectsChow

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeAreaFormula
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal

noncomputable section

theorem volume_null_of_hausdorff_null {m : ℕ} {s : Set (EuclideanSpace ℂ (Fin m))}
    (hs : Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) s = 0) : volume s = 0 := by
  have hdim : finrank ℝ (EuclideanSpace ℂ (Fin m)) = 2 * m := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  have hμ : (Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) : Measure (EuclideanSpace ℂ (Fin m))) =
      Measure.hausdorffMeasure (finrank ℝ (EuclideanSpace ℂ (Fin m)) : ℝ) := by
    rw [hdim]
  rw [hμ] at hs
  exact Measure.absolutelyContinuous_isAddHaarMeasure volume
    (Measure.hausdorffMeasure (finrank ℝ (EuclideanSpace ℂ (Fin m)) : ℝ)) hs

theorem encard_iUnion_disjoint_nat {α : Type*} (s : ℕ → Set α) (hs : Pairwise (Function.onFun Disjoint s)) :
    (((⋃ i, s i).encard : ℕ∞) : ℝ≥0∞) = ∑' i, (((s i).encard : ℕ∞) : ℝ≥0∞) := by
  let _ : MeasurableSpace α := ⊤
  have hm : ∀ t : Set α, MeasurableSet t := fun _ => MeasurableSpace.measurableSet_top
  rw [← Measure.count_apply (hm _), measure_iUnion hs (fun _ => hm _)]
  simp only [Measure.count_apply (hm _)]

theorem volume_linProj_image_null {m n : ℕ} (π : Fin m → Fin n → ℂ) {s : Set (EuclideanSpace ℂ (Fin n))}
    (hs : Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) s = 0) : volume (linProj π '' s) = 0 := by
  refine volume_null_of_hausdorff_null (nonpos_iff_eq_zero.1 ?_)
  have hL := (LinearMap.toContinuousLinearMap (linProjₗ π)).lipschitz.hausdorffMeasure_image_le
    (d := ((2 * m : ℕ) : ℝ)) (by positivity) s
  rw [LinearMap.coe_toContinuousLinearMap', hs, mul_zero] at hL
  exact hL

theorem ConeAreaFormula.proof (hCover : ConeGraphCover.Statement) (hArea : GraphAreaFibre.Statement) :
    ConeAreaFormula.Statement := by
  intro n m h J hJ hm hmn hfin π g hg
  obtain ⟨e, Ω, Φ, hpc, hnull⟩ := hCover n m h J hJ hm hmn hfin
  let S : ℕ → Set (EuclideanSpace ℂ (Fin n)) := fun i => graphPt (e i) (Φ i) '' Ω i
  let D := disjointed S
  have hSm : ∀ i, MeasurableSet (S i) := fun i =>
    (hpc i).1.measurableSet.image_of_continuousOn_injOn
      (continuousOn_graphPt _ (hpc i).2.1.continuousOn) (graphPt_injective_of_graphBase _ _).injOn
  have hDm : ∀ i, MeasurableSet (D i) := MeasurableSet.disjointed hSm
  have hDS : ∀ i, D i ⊆ S i := disjointed_subset S
  have hDd : Pairwise (Function.onFun Disjoint D) := disjoint_disjointed S
  have hU : ⋃ i, D i = ⋃ i, S i := iUnion_disjointed
  have hUC : ⋃ i, D i ⊆ coneSet h J := Set.iUnion_subset fun i => (hDS i).trans (hpc i).2.2.1
  have hN : Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (coneSet h J \ ⋃ i, D i) = 0 := by
    rw [hU]; exact hnull
  have hCae : coneSet h J =ᵐ[Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)] ⋃ i, D i :=
    ae_eq_set.2 ⟨hN, by rw [Set.sdiff_eq_empty.2 hUC]; exact measure_empty⟩
  have hpiece := fun i => hArea m (n - m) n (e i) (Ω i) (Φ i) (hpc i).1 (hpc i).2.1 (D i) (hDS i)
    (hDm i) (coneTangent h J) (fun x hx _ => (hpc i).2.2.2 x hx) π
  have hcount : ∀ᵐ w ∂(volume : Measure (EuclideanSpace ℂ (Fin m))),
      ((fibreCount h J π w : ℕ∞) : ℝ≥0∞) * g w =
        ∑' i, (({y | y ∈ D i ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞) * g w := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (volume_linProj_image_null π hN)] with w hw
    rw [ENNReal.tsum_mul_right, fibreCount, ← encard_iUnion_disjoint_nat]
    · congr 3
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · rintro ⟨hy, rfl⟩
        by_contra hne
        exact hw ⟨y, ⟨hy, fun hyD => hne (by
          obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hyD
          exact ⟨i, hi, rfl⟩)⟩, rfl⟩
      · rintro ⟨i, hi, hw'⟩
        exact ⟨hUC (Set.mem_iUnion.2 ⟨i, hi⟩), hw'⟩
    · intro i j hij
      exact (hDd hij).mono (fun y hy => hy.1) (fun y hy => hy.1)
  calc volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
        ∫⁻ y in coneSet h J, g (linProj π y) * ENNReal.ofReal (coneJac h J π y)
          ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ))
      = ∑' i, volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ y in D i, g (linProj π y) * ENNReal.ofReal (coneJac h J π y)
            ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) := by
        rw [Measure.restrict_congr_set hCae, lintegral_iUnion hDm hDd, ENNReal.tsum_mul_left]
    _ = ∑' i, Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ w, (({y | y ∈ D i ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞) * g w :=
        tsum_congr fun i => (hpiece i).2 g hg
    _ = Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ w, ((fibreCount h J π w : ℕ∞) : ℝ≥0∞) * g w := by
        rw [ENNReal.tsum_mul_left, ← lintegral_tsum
          (f := fun i w => (({y | y ∈ D i ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞) * g w)
          fun i => (hpiece i).1.mul hg.aemeasurable, lintegral_congr_ae hcount]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeGraphCover
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

open scoped ENNReal NNReal

noncomputable section

theorem coneSet_hausdorff_null_of_dim_lt {n : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (d : ℕ) (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) < d) :
    Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (coneSet h J) = 0 := by
  set g : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (Matrix.transpose h.mat)⁻¹)
  have hu : IsUnit (Matrix.transpose h.mat).det := by rw [Matrix.det_transpose]; exact h.isUnit_det
  have hsub : coneSet h J ⊆ g '' zeroSetEuc J := by
    intro y hy
    refine ⟨WithLp.toLp 2 (h.pointOf y), hy, ?_⟩
    ext i
    simp [g, HermNorm.pointOf, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu]
  refine measure_mono_null hsub (nonpos_iff_eq_zero.1 ?_)
  calc Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (g '' zeroSetEuc J)
      ≤ (‖g‖₊ : ℝ≥0∞) ^ ((2 * d : ℕ) : ℝ) * Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (zeroSetEuc J) :=
        g.lipschitz.hausdorffMeasure_image_le (by positivity) _
    _ = 0 := by rw [NullSmaller.proof n d J hd, mul_zero]

theorem ConeGraphCover.proof (hDim : ConeFiniteFibreDim.Statement) (hTan : ConeTangentDim.Statement)
    (hLoc : ConeSmoothLocalGraph.Statement) : ConeGraphCover.Statement := by
  intro n m h J hJ hm hmn hfib
  have e0 : Fin n ≃ Fin m ⊕ Fin (n - m) :=
    (finCongr (Nat.add_sub_cancel' hmn).symm).trans finSumFinEquiv.symm
  rcases (hDim n m h J hJ hm hmn hfib).lt_or_eq with hlt | heq
  ·
    refine ⟨fun _ => e0, fun _ => ∅, fun _ => 0,
      fun _ => ⟨isOpen_empty, differentiableOn_empty, by simp, by simp⟩, ?_⟩
    exact measure_mono_null Set.sdiff_subset (coneSet_hausdorff_null_of_dim_lt h J m hlt)

  set S := {y | y ∈ coneSet h J ∧ finrank ℂ (coneTangent h J y) = m} with hSdef
  have hbad : Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (coneSet h J \ S) = 0 := by
    have hae := hTan n m h J hJ hm hmn hfib
    rw [ae_iff] at hae
    refine measure_mono_null ?_ (nonpos_iff_eq_zero.1 ((Measure.le_restrict_apply _ _).trans hae.le))
    intro y hy
    exact ⟨fun h' => hy.2 ⟨hy.1, h'⟩, hy.1⟩

  have hloc := fun y (hy : y ∈ S) => hLoc n m h J hJ.isPrime heq y hy.1 hy.2
  have : Nonempty (Fin n ≃ Fin m ⊕ Fin (n - m)) := ⟨e0⟩
  choose! E Om Ph U hUo hyU hCU hΩ hΦ hG hT using hloc

  obtain ⟨T, hTS, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable S U hUo
  have hScov : S ⊆ ⋃ y ∈ T, graphPt (E y) (Ph y) '' Om y := by
    intro y hy
    have hy' : y ∈ ⋃ z ∈ S, U z := Set.mem_biUnion hy (hyU y hy)
    rw [← hTU] at hy'
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 hy'
    exact Set.mem_biUnion hz (hCU z (hTS hz) ⟨hy.1, hyz⟩)
  rcases T.eq_empty_or_nonempty with hT0 | hTne
  ·
    refine ⟨fun _ => e0, fun _ => ∅, fun _ => 0,
      fun _ => ⟨isOpen_empty, differentiableOn_empty, by simp, by simp⟩, ?_⟩
    refine measure_mono_null ?_ hbad
    intro y hy
    refine ⟨hy.1, fun hyS => ?_⟩
    have hy' := hScov hyS
    simp [hT0] at hy'
  · obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
    have hfS : ∀ i, f i ∈ S := fun i => hTS (by rw [hf]; exact Set.mem_range_self i)
    refine ⟨fun i => E (f i), fun i => Om (f i), fun i => Ph (f i),
      fun i => ⟨hΩ _ (hfS i), hΦ _ (hfS i), hG _ (hfS i), hT _ (hfS i)⟩, ?_⟩
    refine measure_mono_null ?_ hbad
    intro y hy
    refine ⟨hy.1, fun hyS => hy.2 ?_⟩
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.1 (hScov hyS)
    rw [hf] at hz
    obtain ⟨i, rfl⟩ := hz
    exact Set.mem_iUnion.2 ⟨i, hyz⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeJacMeasurable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Module

noncomputable section

variable {n : ℕ}

def coneJacMat (h : HermNorm n) {k : ℕ} (g : Fin k → MvPolynomial (Fin n) ℂ)
    (y : EuclideanSpace ℂ (Fin n)) : Matrix (Fin k) (Fin n) ℂ :=
  Matrix.of (fun i j => eval (h.pointOf y) (pderiv j (g i))) * h.mat.transpose

theorem continuous_coneJacMat (h : HermNorm n) {k : ℕ} (g : Fin k → MvPolynomial (Fin n) ℂ) :
    Continuous (coneJacMat h g) := by
  unfold coneJacMat
  refine Continuous.matrix_mul ?_ continuous_const
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (MvPolynomial.continuous_eval _).comp h.continuous_pointOf

theorem mem_ker_coneJacMat (h : HermNorm n) {k : ℕ} (g : Fin k → MvPolynomial (Fin n) ℂ)
    (y v : EuclideanSpace ℂ (Fin n)) :
    v ∈ LinearMap.ker (Matrix.toEuclideanLin (coneJacMat h g y)) ↔
      ∀ i, ∑ j, eval (h.pointOf y) (pderiv j (g i)) * h.pointOf v j = 0 := by
  rw [LinearMap.mem_ker]
  change WithLp.toLp 2 (Matrix.mulVec (coneJacMat h g y) (WithLp.ofLp v)) = 0 ↔ _
  rw [WithLp.toLp_eq_zero, coneJacMat, ← Matrix.mulVec_mulVec, funext_iff]
  refine forall_congr' fun i => ?_
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
  rfl

theorem coneTangent_eq_ker (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)} {k : ℕ}
    (g : Fin k → MvPolynomial (Fin n) ℂ) (hg : Submodule.span _ (Set.range g) = J)
    {y : EuclideanSpace ℂ (Fin n)} (hy : y ∈ coneSet h J) :
    coneTangent h J y = LinearMap.ker (Matrix.toEuclideanLin (coneJacMat h g y)) := by
  ext v
  rw [mem_ker_coneJacMat]
  constructor
  · intro hv i
    exact hv (g i) (hg ▸ Submodule.subset_span ⟨i, rfl⟩)
  · intro hv q hq
    rw [← hg] at hq
    induction hq using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hv i
    | zero => simp
    | add x z _ _ hx hz => simp [add_mul, Finset.sum_add_distrib, hx, hz]
    | smul a x hxmem hx =>
      have hx0 : eval (h.pointOf y) x = 0 := hy x (hg ▸ hxmem)
      calc ∑ j, eval (h.pointOf y) (pderiv j (a • x)) * h.pointOf v j
          = eval (h.pointOf y) a * ∑ j, eval (h.pointOf y) (pderiv j x) * h.pointOf v j := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [smul_eq_mul, pderiv_mul, map_add (f := _), map_mul, map_mul, hx0]
            ring
        _ = 0 := by rw [hx, mul_zero]

theorem coneTangent_eq_bot (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {y : EuclideanSpace ℂ (Fin n)} (hy : y ∉ coneSet h J) : coneTangent h J y = ⊥ := by
  obtain ⟨q, hq, hq0⟩ : ∃ q ∈ J, eval (h.pointOf y) q ≠ 0 := by
    simpa [coneSet] using hy
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  apply h.pointOf_eq_zero
  funext l
  have h1 : ∑ j, eval (h.pointOf y) (pderiv j q) * h.pointOf v j = 0 := hv q hq
  have h2 : ∑ j, eval (h.pointOf y) (pderiv j (X l * q)) * h.pointOf v j = 0 :=
    hv _ (J.mul_mem_left _ hq)
  have h3 : ∀ j, eval (h.pointOf y) (pderiv j (X l * q)) * h.pointOf v j =
      h.pointOf y l * (eval (h.pointOf y) (pderiv j q) * h.pointOf v j) +
        if l = j then eval (h.pointOf y) q * h.pointOf v l else 0 := by
    intro j
    by_cases hj : l = j
    · subst hj
      simp
      ring
    · simp [pderiv_X_of_ne hj, hj]
      ring
  simp only [h3, Finset.sum_add_distrib, ← Finset.mul_sum, h1, mul_zero, zero_add,
    Finset.sum_ite_eq, Finset.mem_univ, if_true] at h2
  exact (mul_eq_zero.1 h2).resolve_left hq0

theorem starProjection_congr {U V : Submodule ℂ (EuclideanSpace ℂ (Fin n))} (e : U = V) :
    U.starProjection = V.starProjection := by
  subst e
  rfl

def gramOp {m : ℕ} (π : Fin m → Fin n → ℂ) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  (LinearMap.toContinuousLinearMap (linProjₗ π)).adjoint ∘L LinearMap.toContinuousLinearMap (linProjₗ π)

theorem continuous_gramOp (m : ℕ) : Continuous (gramOp (n := n) (m := m)) := by
  have hL : Continuous fun π : Fin m → Fin n → ℂ =>
      LinearMap.toContinuousLinearMap (linProjₗ π) := by
    refine continuous_clm_apply.2 fun v => ?_
    simp only [LinearMap.coe_toContinuousLinearMap']
    change Continuous fun π : Fin m → Fin n → ℂ => linProj π v
    unfold linProj
    fun_prop
  exact (ContinuousLinearMap.adjoint.continuous.comp hL).clm_comp hL

def compressDet {m : ℕ} (π : Fin m → Fin n → ℂ)
    (Q : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) : ℝ :=
  Complex.re (Q ∘L gramOp π ∘L Q + (1 - Q)).det

theorem continuous_compressDet (m : ℕ) :
    Continuous fun p : (Fin m → Fin n → ℂ) ×
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) => compressDet p.1 p.2 :=
  Complex.continuous_re.comp (ContinuousLinearMap.continuous_det.comp
    ((continuous_snd.clm_comp (((continuous_gramOp m).comp continuous_fst).clm_comp
      continuous_snd)).add (continuous_const.sub continuous_snd)))

theorem coneJac_eq_compressDet (hComp : TangentJacCompress.Statement) (h : HermNorm n)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) {m : ℕ} (π : Fin m → Fin n → ℂ)
    (y : EuclideanSpace ℂ (Fin n)) :
    coneJac h J π y = compressDet π (coneTangent h J y).starProjection := by
  rw [coneJac, compressDet, gramOp, ContinuousLinearMap.comp_assoc, ← hComp n m π (coneTangent h J y), Complex.ofReal_re]

theorem ConeJacMeasurable.proof (hComp : TangentJacCompress.Statement)
    (hKer : KernelProjMeasurable.Statement) : ConeJacMeasurable.Statement := by
  classical
  intro n m h J _ _ _ _
  refine Measurable.aemeasurable ?_
  obtain ⟨k, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian J)
  let P : EuclideanSpace ℂ (Fin n) → (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    (coneSet h J).piecewise
      (fun y => (LinearMap.ker (Matrix.toEuclideanLin (coneJacMat h g y))).starProjection) 0
  have hP : Measurable P :=
    Measurable.piecewise (isClosed_coneSet h J).measurableSet
      (hKer (EuclideanSpace ℂ (Fin n)) n k _ (continuous_coneJacMat h g)) measurable_const
  have hTP : ∀ y, (coneTangent h J y).starProjection = P y := by
    intro y
    by_cases hy : y ∈ coneSet h J
    · simp only [P, Set.piecewise_eq_of_mem _ _ _ hy]
      exact starProjection_congr (coneTangent_eq_ker h g hg hy)
    · simp only [P, Set.piecewise_eq_of_notMem _ _ _ hy]
      rw [starProjection_congr (coneTangent_eq_bot h hy), Submodule.starProjection_bot]
      rfl
  have hJac : (fun p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => coneJac h J p.1 p.2) =
      fun p => compressDet p.1 (P p.2) := by
    funext p
    rw [coneJac_eq_compressDet hComp, hTP]
  have hM : Measurable fun q : (Fin m → Fin n → ℂ) ×
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) => compressDet q.1 q.2 :=
    (continuous_compressDet m).measurable
  have hM2 : Measurable fun p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin n) => (p.1, P p.2) :=
    measurable_fst.prodMk (hP.comp measurable_snd)
  have hM3 := hM.comp hM2
  rw [hJac]
  exact hM3

end

end GroundTheory.Heights₂.Heights
end

