module

public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0065
public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GaussianProjectionConeCoarea
section
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

theorem coneArea_inter : ∀ (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → 0 < m → m ≤ n →
  (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
  ∀ (π : Fin m → Fin n → ℂ) (A : Set (EuclideanSpace ℂ (Fin n))), MeasurableSet A →
  ∀ g : EuclideanSpace ℂ (Fin m) → ℝ≥0∞, Measurable g →
    volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
        ∫⁻ y in coneSet h J ∩ A, g (linProj π y) * ENNReal.ofReal (coneJac h J π y) ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) =
      (Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
        ∫⁻ w : EuclideanSpace ℂ (Fin m), cntOver (coneSet h J ∩ A) π w * g w := by
  intro n m h J hJ hm hmn hfin π A hA g hg
  have hCover : ConeGraphCover.Statement := ConeGraphCover.proof ConeFiniteFibreDim.proof
    (ConeTangentDim.proof (ConeKrullDimLe.proof ConeFiniteFibreDim.proof) NullSmaller.full
      (FrameJacobianGeneric.proof JacobianRankGeneric.proof ConormalGenerationGeneric.proof))
    (ConeSmoothLocalGraph.proof PolyLocalGenerators.proof HolomorphicImplicitGraph.proof)
  have hArea : GraphAreaFibre.Statement :=
    GraphAreaFibre.proof (GraphAreaIntegral.proof GraphAreaHolomorphic.full) TangentJacComp.proof
      AreaMultiplicityWeight.proof
  obtain ⟨e, Ω, Φ, hpc, hnull⟩ := hCover n m h J hJ hm hmn hfin
  let S : ℕ → Set (EuclideanSpace ℂ (Fin n)) := fun i => graphPt (e i) (Φ i) '' Ω i
  let D₀ := disjointed S
  let D : ℕ → Set (EuclideanSpace ℂ (Fin n)) := fun i => D₀ i ∩ A
  have hSm : ∀ i, MeasurableSet (S i) := fun i =>
    (hpc i).1.measurableSet.image_of_continuousOn_injOn
      (continuousOn_graphPt _ (hpc i).2.1.continuousOn) (graphPt_injective_of_graphBase _ _).injOn
  have hD₀m : ∀ i, MeasurableSet (D₀ i) := MeasurableSet.disjointed hSm
  have hDm : ∀ i, MeasurableSet (D i) := fun i => (hD₀m i).inter hA
  have hD₀S : ∀ i, D₀ i ⊆ S i := disjointed_subset S
  have hDS : ∀ i, D i ⊆ S i := fun i => Set.inter_subset_left.trans (hD₀S i)
  have hDd : Pairwise (Function.onFun Disjoint D) := fun i j hij =>
    (disjoint_disjointed S hij).mono Set.inter_subset_left Set.inter_subset_left
  have hU₀ : ⋃ i, D₀ i = ⋃ i, S i := iUnion_disjointed
  have hUC₀ : ⋃ i, S i ⊆ coneSet h J := Set.iUnion_subset fun i => (hpc i).2.2.1
  have hUC : ⋃ i, D i ⊆ coneSet h J ∩ A := Set.iUnion_subset fun i y hy =>
    ⟨hUC₀ (hU₀ ▸ Set.mem_iUnion.2 ⟨i, hy.1⟩), hy.2⟩
  have hN : Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) ((coneSet h J ∩ A) \ ⋃ i, D i) = 0 := by
    refine measure_mono_null ?_ hnull
    rintro y ⟨⟨hyC, hyA⟩, hyD⟩
    refine ⟨hyC, fun hyS => hyD ?_⟩
    rw [← hU₀] at hyS
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hyS
    exact Set.mem_iUnion.2 ⟨i, hi, hyA⟩
  have hCae : (coneSet h J ∩ A : Set (EuclideanSpace ℂ (Fin n))) =ᵐ[Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)] ⋃ i, D i :=
    ae_eq_set.2 ⟨hN, by rw [Set.sdiff_eq_empty.2 hUC]; exact measure_empty⟩
  have hpiece := fun i => hArea m (n - m) n (e i) (Ω i) (Φ i) (hpc i).1 (hpc i).2.1 (D i) (hDS i)
    (hDm i) (coneTangent h J) (fun x hx _ => (hpc i).2.2.2 x hx) π
  have hcount : ∀ᵐ w ∂(volume : Measure (EuclideanSpace ℂ (Fin m))),
      cntOver (coneSet h J ∩ A) π w * g w =
        ∑' i, (({y | y ∈ D i ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞) * g w := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (volume_linProj_image_null π hN)] with w hw
    rw [ENNReal.tsum_mul_right, cntOver, ptsOver, ← encard_iUnion_disjoint_nat]
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
        ∫⁻ y in coneSet h J ∩ A, g (linProj π y) * ENNReal.ofReal (coneJac h J π y)
          ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ))
      = ∑' i, volume (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ y in D i, g (linProj π y) * ENNReal.ofReal (coneJac h J π y)
            ∂(Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ)) := by
        rw [Measure.restrict_congr_set hCae, lintegral_iUnion hDm hDd, ENNReal.tsum_mul_left]
    _ = ∑' i, Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ w, (({y | y ∈ D i ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞) * g w :=
        tsum_congr fun i => (hpiece i).2 g hg
    _ = Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1) *
          ∫⁻ w, cntOver (coneSet h J ∩ A) π w * g w := by
        rw [ENNReal.tsum_mul_left, ← lintegral_tsum
          (f := fun i w => (({y | y ∈ D i ∧ linProj π y = w}.encard : ℕ∞) : ℝ≥0∞) * g w)
          fun i => (hpiece i).1.mul hg.aemeasurable, lintegral_congr_ae hcount]

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsSigmaCompactConeInter
section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix

open scoped ENNReal

theorem chowGroups_le {n e δ : ℕ} {W : Ideal (MvPolynomial (Fin n) ℂ)}
    {g : MvPolynomial (Fin (e + 1) × Fin n) ℂ} (hW : IsProjPrime W) (hg : IsChowForm W (e + 1) g)
    (hδ : IsMultiHomog δ g) : e + 1 ≤ n := by
  by_contra hn
  have hfib := ConeFibreDegree.full n e δ (HermNorm.std n) W g hW hg hδ
  have hpos := ChowDegreePos.proof n (e + 1) δ W g (Nat.succ_pos e) hW hg hδ
  have : (volume : Measure (Fin (e + 1) → Fin n → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  have : (ae (volume : Measure (Fin (e + 1) → Fin n → ℂ))).NeBot := ae_neBot.2 (NeZero.ne _)
  have : (ae (volume : Measure (EuclideanSpace ℂ (Fin (e + 1))))).NeBot :=
    ae_neBot.2 (NeZero.ne _)
  obtain ⟨π, hπ⟩ := hfib.exists
  obtain ⟨w, hw1, hw2⟩ := (hπ.and (ae_fibreCount_eq_zero (by omega) (HermNorm.std n) W π)).exists
  rw [hw1] at hw2
  have h0 : δ = 0 := by exact_mod_cast hw2
  omega

theorem isSigmaCompact_cone_inter {n : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    {A : Set (EuclideanSpace ℂ (Fin n))} (hA : IsOpen A) : IsSigmaCompact (coneSet h J ∩ A) := by
  have hcl : IsClosed (coneSet h J) := isClosed_coneSet h J
  obtain ⟨F, hF, -, hU, -⟩ := hA.exists_iUnion_isClosed
  rw [← hU, Set.inter_iUnion]
  exact isSigmaCompact_iUnion _ fun i =>
    IsSigmaCompact.of_isClosed_subset isSigmaCompact_univ (hcl.inter (hF i)) (Set.subset_univ _)

theorem isScaleStable_coneSet {n : ℕ} (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    (hJ : IsProjPrime J) : IsScaleStable (coneSet h J) := by
  intro y hy t _ q hq
  rw [HermNorm.pointOf_smul']
  exact PointLine.smul_mem_zeroSet hJ.isHomog hy t q hq

theorem IsScaleStable.inter {n : ℕ} {S T : Set (EuclideanSpace ℂ (Fin n))} (hS : IsScaleStable S)
    (hT : IsScaleStable T) : IsScaleStable (S ∩ T) :=
  fun y hy t ht => ⟨hS y hy.1 t ht, hT y hy.2 t ht⟩

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LogGapMeasurableScaleStable
section
set_option maxSynthPendingDepth 1

open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

noncomputable section

variable {n : ℕ}

theorem continuous_pairing_pointOf (h : HermNorm n) (u : Fin n → ℂ) :
    Continuous fun y : EuclideanSpace ℂ (Fin n) => ∑ j, u j * h.pointOf y j := by
  have hp : Continuous (fun y : EuclideanSpace ℂ (Fin n) => h.pointOf y) := by
    unfold HermNorm.pointOf; fun_prop
  exact continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_apply j).comp hp)

theorem pairing_pointOf_smul (h : HermNorm n) (u : Fin n → ℂ) (t : ℂ)
    (y : EuclideanSpace ℂ (Fin n)) :
    ∑ j, u j * h.pointOf (t • y) j = t * ∑ j, u j * h.pointOf y j := by
  have hpt : h.pointOf (t • y) = t • h.pointOf y := by
    simp only [HermNorm.pointOf]
    rw [← Matrix.mulVec_smul]
    congr 1
  rw [hpt, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring

theorem dualNorm_pointOf_eq (h : HermNorm n) (y : EuclideanSpace ℂ (Fin n)) :
    h.dualNorm (h.pointOf y) = ‖y‖ := by
  have hA : IsUnit h.matᵀ.det := by rw [Matrix.det_transpose]; exact h.isUnit_det
  rw [HermNorm.dualNorm, HermNorm.pointOf, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA,
    Matrix.one_mulVec, EuclideanSpace.norm_eq]

theorem hermNorm_pos (h : HermNorm n) {u : Fin n → ℂ} (hu : u ≠ 0) : 0 < h.norm u := by
  have hne : h.mat *ᵥ u ≠ 0 := by
    intro h0
    apply hu
    have h1 := congrArg (fun v => h.mat⁻¹ *ᵥ v) h0
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h.isUnit_det] using h1
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  rw [HermNorm.norm]
  refine Real.sqrt_pos.mpr (Finset.sum_pos' (fun _ _ => by positivity)
    ⟨i, Finset.mem_univ _, ?_⟩)
  have : 0 < ‖(h.mat *ᵥ u) i‖ := norm_pos_iff.mpr hi
  positivity

theorem lt_logGap_iff (h : HermNorm n) {u : Fin n → ℂ} (hu : u ≠ 0) {s : ℝ≥0∞} (hs : s ≠ ⊤)
    (y : EuclideanSpace ℂ (Fin n)) :
    s < logGap h u y ↔
      ‖∑ j, u j * h.pointOf y j‖ < Real.exp (-s.toReal) * h.norm u * ‖y‖ := by
  have hN := hermNorm_pos h hu
  unfold logGap
  by_cases hy : y = 0
  · subst hy
    simp [HermNorm.pointOf]
  have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hc : 0 < Real.exp (-s.toReal) * h.norm u * ‖y‖ := by positivity
  by_cases hp : ∑ j, u j * h.pointOf y j = 0
  · simp [hy, hp, hs.lt_top, hc]
  · have hpn : 0 < ‖∑ j, u j * h.pointOf y j‖ := norm_pos_iff.mpr hp
    rw [if_neg hy, if_neg hp, ENNReal.lt_ofReal_iff_toReal_lt hs, fsLog, dualNorm_pointOf_eq,
      Real.log_div hpn.ne' hy'.ne', ← Real.log_lt_log_iff hpn hc,
      Real.log_mul (by positivity) hy'.ne', Real.log_mul (Real.exp_pos _).ne' hN.ne', Real.log_exp]
    constructor <;> intro hh <;> linarith

theorem lt_logGap_zero_iff (h : HermNorm n) {s : ℝ≥0∞} (hs : s ≠ ⊤)
    (y : EuclideanSpace ℂ (Fin n)) : s < logGap h 0 y ↔ y ≠ 0 := by
  unfold logGap
  by_cases hy : y = 0
  · simp [hy]
  · simp [hy, hs.lt_top]

theorem logGap_levelSet_top (h : HermNorm n) (u : Fin n → ℂ) :
    {y | (⊤ : ℝ≥0∞) < logGap h u y} = ∅ := by
  ext y
  simp

theorem logGap_levelSet (h : HermNorm n) (u : Fin n → ℂ) (s : ℝ≥0∞) :
    IsOpen {y | s < logGap h u y} ∧ IsScaleStable {y | s < logGap h u y} := by
  by_cases hs : s = ⊤
  · subst hs
    rw [logGap_levelSet_top]
    exact ⟨isOpen_empty, fun y hy => hy.elim⟩
  by_cases hu : u = 0
  · subst hu
    have hset : {y | s < logGap h 0 y} = {y : EuclideanSpace ℂ (Fin n) | y ≠ 0} :=
      Set.ext fun y => lt_logGap_zero_iff h hs y
    rw [hset]
    exact ⟨isOpen_ne, fun y hy t ht => smul_ne_zero ht hy⟩
  have hset : {y | s < logGap h u y} = {y : EuclideanSpace ℂ (Fin n) |
      ‖∑ j, u j * h.pointOf y j‖ < Real.exp (-s.toReal) * h.norm u * ‖y‖} :=
    Set.ext fun y => lt_logGap_iff h hu hs y
  rw [hset]
  refine ⟨isOpen_lt (continuous_pairing_pointOf h u).norm (continuous_const.mul continuous_norm),
    fun y hy t ht => ?_⟩
  have ht' : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have hy' : ‖∑ j, u j * h.pointOf y j‖ < Real.exp (-s.toReal) * h.norm u * ‖y‖ := hy
  show ‖∑ j, u j * h.pointOf (t • y) j‖ < Real.exp (-s.toReal) * h.norm u * ‖t • y‖
  rw [pairing_pointOf_smul, norm_mul, norm_smul]
  calc ‖t‖ * ‖∑ j, u j * h.pointOf y j‖
      < ‖t‖ * (Real.exp (-s.toReal) * h.norm u * ‖y‖) := mul_lt_mul_of_pos_left hy' ht'
    _ = Real.exp (-s.toReal) * h.norm u * (‖t‖ * ‖y‖) := by ring

theorem logGap_basic : ∀ (n : ℕ) (h : HermNorm n) (u : Fin n → ℂ),
    Measurable (logGap h u) ∧
      ∀ s : ℝ≥0∞, IsOpen {y | s < logGap h u y} ∧ IsScaleStable {y | s < logGap h u y} := by
  intro n h u
  exact ⟨measurable_of_Ioi fun s => (logGap_levelSet h u s).1.measurableSet,
    logGap_levelSet h u⟩

end

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MahlerMeasureOfProduct
section
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

theorem mahler_pow_mul {n e : ℕ} (h : HermNorm n) {q g : MvPolynomial (Fin e × Fin n) ℂ}
    (hq : q ≠ 0) (hg : g ≠ 0) (a : ℕ) :
    mahler h e (q ^ a * g) = (a : ℝ) * mahler h e q + mahler h e g := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ', mul_assoc, mahlerMul n e h _ _ hq (mul_ne_zero (pow_ne_zero _ hq) hg), ih]
    push_cast
    ring

theorem mahler_C_mul_prod_pow : ∀ (n e : ℕ) (h : HermNorm n) {ι : Type} (s : Finset ι) (q : ι → MvPolynomial (Fin e × Fin n) ℂ) (d : ι → ℕ) (a : ι → ℕ) (c : ℂ), c ≠ 0 → (∀ i ∈ s, q i ≠ 0 ∧ IsMultiHomog (d i) (q i)) → mahler h e (C c * ∏ i ∈ s, q i ^ a i) = Real.log ‖c‖ + ∑ i ∈ s, (a i : ℝ) * mahler h e (q i) := by
  classical
  intro n e h ι s q d a c hc hq
  revert hq
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp [mahler_C]
  · intro i s hi ih hq
    have hrest : ∀ j ∈ s, q j ≠ 0 ∧ IsMultiHomog (d j) (q j) := fun j hj => hq j (Finset.mem_insert_of_mem hj)
    have hne : C c * ∏ j ∈ s, q j ^ a j ≠ 0 :=
      mul_ne_zero (by simpa using hc) (Finset.prod_ne_zero_iff.2 fun j hj => pow_ne_zero _ (hrest j hj).1)
    rw [Finset.prod_insert hi, Finset.sum_insert hi, mul_left_comm (C c) (q i ^ a i),
      mahler_pow_mul h (hq i (Finset.mem_insert_self i s)).1 hne (a i), ih hrest]
    ring

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MeasurableFibreCountOver
section
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Short.Crofton

open TopologicalSpace

variable {m n : ℕ}

theorem isClosed_linProj_meets_compact {K : Set (EuclideanSpace ℂ (Fin n))} (hK : IsCompact K) :
    IsClosed {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) | ∃ y ∈ K, linProj p.1 y = p.2} := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (fun q : ((Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m)) × K =>
      linProj q.1.1 (q.2 : EuclideanSpace ℂ (Fin n))) := by
    unfold linProj
    fun_prop
  have hC : IsClosed {q : ((Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m)) × K |
      linProj q.1.1 (q.2 : EuclideanSpace ℂ (Fin n)) = q.1.2} :=
    isClosed_eq hc (continuous_snd.comp continuous_fst)
  have h2 := isClosedMap_fst_of_compactSpace _ hC
  convert h2 using 1
  ext p
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨(p, ⟨y, hy⟩), h, rfl⟩
  · rintro ⟨⟨p', y⟩, h, rfl⟩
    exact ⟨y, y.2, h⟩

theorem isSigmaCompact_of_isOpen_euclidean {U : Set (EuclideanSpace ℂ (Fin n))} (hU : IsOpen U) :
    IsSigmaCompact U := by
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  exact isSigmaCompact_iff_sigmaCompactSpace.mpr inferInstance

theorem measurableSet_linProj_meets {S U : Set (EuclideanSpace ℂ (Fin n))} (hS : IsSigmaCompact S)
    (hU : IsOpen U) :
    MeasurableSet {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) |
      ∃ y ∈ S ∩ U, linProj p.1 y = p.2} := by
  obtain ⟨K, hK, hKS⟩ := hS
  obtain ⟨L, hL, hLU⟩ := isSigmaCompact_of_isOpen_euclidean hU
  have hEq : {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) | ∃ y ∈ S ∩ U, linProj p.1 y = p.2} =
      ⋃ k, ⋃ l, {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) |
        ∃ y ∈ K k ∩ L l, linProj p.1 y = p.2} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨y, ⟨hyS, hyU⟩, h⟩
      rw [← hKS, Set.mem_iUnion] at hyS
      rw [← hLU, Set.mem_iUnion] at hyU
      obtain ⟨k, hk⟩ := hyS
      obtain ⟨l, hl⟩ := hyU
      exact ⟨k, l, y, ⟨hk, hl⟩, h⟩
    · rintro ⟨k, l, y, ⟨hk, hl⟩, h⟩
      refine ⟨y, ⟨?_, ?_⟩, h⟩
      · rw [← hKS]; exact Set.mem_iUnion.mpr ⟨k, hk⟩
      · rw [← hLU]; exact Set.mem_iUnion.mpr ⟨l, hl⟩
  rw [hEq]
  exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun l =>
    (isClosed_linProj_meets_compact ((hK k).inter (hL l))).measurableSet

theorem natCast_le_encard_ptsOver_iff (S : Set (EuclideanSpace ℂ (Fin n))) (π : Fin m → Fin n → ℂ)
    (w : EuclideanSpace ℂ (Fin m)) (N : ℕ) :
    (N : ℕ∞) ≤ (ptsOver S π w).encard ↔
      ∃ f : Fin N → countableBasis (EuclideanSpace ℂ (Fin n)),
        (∀ i j, i ≠ j → Disjoint (f i : Set (EuclideanSpace ℂ (Fin n))) (f j)) ∧
        ∀ i, ∃ y ∈ S ∩ (f i : Set (EuclideanSpace ℂ (Fin n))), linProj π y = w := by
  constructor
  · intro hN
    obtain ⟨t, htS, htN⟩ := Set.exists_subset_encard_eq hN
    have htf : t.Finite := Set.finite_of_encard_eq_coe htN
    have hcard : htf.toFinset.card = N := by
      have := htf.encard_eq_coe_toFinset_card
      rw [htN] at this
      exact_mod_cast this.symm
    let e : Fin N ≃ {x // x ∈ htf.toFinset} := (htf.toFinset.equivFinOfCardEq hcard).symm
    let g : Fin N → EuclideanSpace ℂ (Fin n) := fun i => (e i : EuclideanSpace ℂ (Fin n))
    have hg_mem : ∀ i, g i ∈ t := fun i => htf.mem_toFinset.mp (e i).2
    have hg_inj : Function.Injective g := by
      intro i j hij
      exact e.injective (Subtype.ext hij)
    obtain ⟨V, hV, hVd⟩ := (Set.finite_range g).t2_separation
    have hB : ∀ i, ∃ v ∈ countableBasis (EuclideanSpace ℂ (Fin n)), g i ∈ v ∧ v ⊆ V (g i) := fun i =>
      (isBasis_countableBasis (EuclideanSpace ℂ (Fin n))).exists_subset_of_mem_open (hV (g i)).1 (hV (g i)).2
    choose v hvB hgv hvV using hB
    refine ⟨fun i => ⟨v i, hvB i⟩, ?_, ?_⟩
    · intro i j hij
      have hne : g i ≠ g j := fun h => hij (hg_inj h)
      exact (hVd (Set.mem_range_self i) (Set.mem_range_self j) hne).mono (hvV i) (hvV j)
    · intro i
      have := htS (hg_mem i)
      exact ⟨g i, ⟨this.1, hgv i⟩, this.2⟩
  · rintro ⟨f, hfd, hf⟩
    choose y hy hyw using hf
    have hinj : Function.Injective y := by
      intro i j hij
      by_contra hne
      have hd := hfd i j hne
      exact Set.disjoint_left.mp hd (hy i).2 (hij ▸ (hy j).2)
    have hsub : Set.range y ⊆ ptsOver S π w := by
      rintro _ ⟨i, rfl⟩
      exact ⟨(hy i).1, hyw i⟩
    calc (N : ℕ∞) = (Set.range y).encard := by
          rw [← Set.image_univ, hinj.encard_image, Set.encard_univ]; simp
      _ ≤ (ptsOver S π w).encard := Set.encard_le_encard hsub

theorem measurableSet_natCast_le_encard_ptsOver {S : Set (EuclideanSpace ℂ (Fin n))}
    (hS : IsSigmaCompact S) (N : ℕ) :
    MeasurableSet {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) |
      (N : ℕ∞) ≤ (ptsOver S p.1 p.2).encard} := by
  haveI : Countable (countableBasis (EuclideanSpace ℂ (Fin n))) :=
    (countable_countableBasis (EuclideanSpace ℂ (Fin n))).to_subtype
  have hEq : {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) |
      (N : ℕ∞) ≤ (ptsOver S p.1 p.2).encard} =
      ⋃ f : Fin N → countableBasis (EuclideanSpace ℂ (Fin n)),
        ({_p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) |
          ∀ i j, i ≠ j → Disjoint (f i : Set (EuclideanSpace ℂ (Fin n))) (f j)} ∩
        ⋂ i, {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) |
          ∃ y ∈ S ∩ (f i : Set (EuclideanSpace ℂ (Fin n))), linProj p.1 y = p.2}) := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter]
    exact natCast_le_encard_ptsOver_iff S p.1 p.2 N
  rw [hEq]
  exact MeasurableSet.iUnion fun f => (MeasurableSet.const _).inter
    (MeasurableSet.iInter fun i => measurableSet_linProj_meets hS (isOpen_of_mem_countableBasis (f i).2))

theorem measurable_cntOver : ∀ (n m : ℕ) (S : Set (EuclideanSpace ℂ (Fin n))), IsSigmaCompact S →
    Measurable (fun p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) => cntOver S p.1 p.2) := by
  intro n m S hS
  have h : (fun p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) => cntOver S p.1 p.2) =
      fun p => ⨆ N : ℕ, {p : (Fin m → Fin n → ℂ) × EuclideanSpace ℂ (Fin m) |
        (N : ℕ∞) ≤ (ptsOver S p.1 p.2).encard}.indicator (fun _ => (N : ℝ≥0∞)) p := by
    funext p
    simp only [cntOver, Set.indicator_apply, Set.mem_setOf_eq]
    generalize (ptsOver S p.1 p.2).encard = e
    induction e using ENat.recTopCoe with
    | top => simp [ENNReal.iSup_natCast]
    | coe k =>
      apply le_antisymm
      · exact le_iSup_of_le k (by simp)
      · refine iSup_le fun N => ?_
        split_ifs with hN
        · have : N ≤ k := by exact_mod_cast hN
          simpa using this
        · exact zero_le
  rw [h]
  exact Measurable.iSup fun N => measurable_const.indicator (measurableSet_natCast_le_encard_ptsOver hS N)

end GlobalTheory.CompanionTheory.Ar.Short.Crofton
end

