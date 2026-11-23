module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0068
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0071
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0072
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0035
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0058
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0067

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamChartInt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

theorem ParamChartInt.proof (hCA : ChartIntCountAdd.Statement) (hPI : ParamPieceInt.Statement)
    (hCN : ParamCritNull.Statement) (hOR : ParamOffRegularZero.Statement)
    (hRP : RegularInjectivePieces.Statement) (hDI : ParamDensIntegrable.Statement) :
    ParamChartInt.Statement := by
  intro n d W A σ r r' N hW hdim hA hσ hinj hN hrr hprop hcov f φ hf hfc hfN hφ
  classical
  set F : (Fin d → ℂ) → ℝ := fun w => f (σ w) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ σ) w with hF
  have hf0 : ∀ x, x ∉ N → f x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hfN h)
  set g : (Fin d → ℂ) → Fin d → ℂ := fun v => A *ᵥ σ v with hg
  set Ω : Set (Fin d → ℂ) := Metric.ball 0 r ∩ σ ⁻¹' N with hΩ
  have hΩo : IsOpen Ω := hσ.continuousOn.isOpen_inter_preimage Metric.isOpen_ball hN
  have hmv : Differentiable ℂ (fun x : Fin n → ℂ => A *ᵥ x) := by
    have h := (Matrix.mulVecLin A).toContinuousLinearMap.differentiable
    convert h using 1
    ext x i
    rfl
  have hgd : DifferentiableOn ℂ g Ω := hmv.comp_differentiableOn (hσ.mono Set.inter_subset_left)
  set Reg : Set (Fin d → ℂ) := {w | w ∈ Metric.ball (0 : Fin d → ℂ) r ∧ σ w ∈ N ∧
      LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} with hReg
  obtain ⟨P, hPm, hPd, hPU, hPinj⟩ := hRP d Ω g hΩo hgd
  have hPReg : ⋃ i, P i = Reg := by
    rw [hPU]; ext w
    simp only [hΩ, Reg, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, and_assoc]
  have hPsub : ∀ i, P i ⊆ Reg := fun i => hPReg ▸ Set.subset_iUnion P i
  have hRegB : Reg ⊆ Metric.ball 0 r := fun w hw => hw.1
  have hPB : ∀ i, P i ⊆ Metric.ball 0 r := fun i => (hPsub i).trans hRegB
  have hσP : ∀ i, MeasurableSet (σ '' P i) := fun i =>
    (hPm i).image_of_continuousOn_injOn (hσ.continuousOn.mono (hPB i)) (hinj.mono (hPB i))
  have hσReg : σ '' Reg = ⋃ i, σ '' P i := by rw [← hPReg, Set.image_iUnion]

  let E : ℕ → Set (Fin n → ℂ) := fun i => Nat.casesOn i (σ '' Reg)ᶜ fun j => σ '' P j
  have hEm : ∀ i, MeasurableSet (E i) := by
    intro i
    cases i with
    | zero => show MeasurableSet (σ '' Reg)ᶜ; rw [hσReg]; exact (MeasurableSet.iUnion hσP).compl
    | succ j => exact hσP j
  have hdisjP : ∀ i j, i ≠ j → Disjoint (σ '' P i) (σ '' P j) := by
    intro i j hij
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    have hba := hinj (hPB j hb) (hPB i ha) hab
    subst hba
    exact Set.disjoint_left.1 (hPd hij) ha hb
  have hEd : Pairwise (Function.onFun Disjoint E) := by
    intro i j hij
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hij
      | succ j => exact Set.disjoint_compl_left_iff_subset.2 (Set.image_mono (hPsub j))
    | succ i =>
      cases j with
      | zero => exact Set.disjoint_compl_right_iff_subset.2 (Set.image_mono (hPsub i))
      | succ j => exact hdisjP i j fun h => hij (by rw [h])
  have hEU : ⋃ i, E i = Set.univ := by
    refine Set.eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ σ '' Reg
    · rw [hσReg, Set.mem_iUnion] at hx
      obtain ⟨j, hj⟩ := hx
      exact Set.mem_iUnion.2 ⟨j + 1, hj⟩
    · exact Set.mem_iUnion.2 ⟨0, hx⟩

  have hsum := hCA n d W A f φ E hW hdim hA hf.continuous hfc hφ hEm hEd
  rw [hEU, Set.indicator_univ] at hsum
  have h0 : chartInt W A ((E 0).indicator f) φ = 0 := hOR n d W A σ r N hσ hcov f φ hfN
  have hi : ∀ j, chartInt W A ((E (j + 1)).indicator f) φ = ∫ w in P j, F w := fun j =>
    hPI n d W A σ r r' N hσ hinj hN hrr hprop hcov f φ (P j) hφ (hPm j) (hPB j)
      (fun w hw => ⟨(hPsub j hw).2.1, (hPsub j hw).2.2⟩) (hPinj j)
  have hL : HasSum (fun j => ∫ w in P j, F w) (chartInt W A f φ) := by
    have h1 := (hasSum_nat_add_iff' 1).2 hsum
    rw [Finset.sum_range_one, h0, sub_zero] at h1
    have h2 : (fun j => chartInt W A ((E (j + 1)).indicator f) φ) = fun j => ∫ w in P j, F w :=
      funext hi
    rwa [h2] at h1

  have hint : IntegrableOn F (Metric.ball 0 r) :=
    hDI n d W σ r r' N hσ hrr hprop f φ hf.continuous hfN hφ
  have hR : HasSum (fun j => ∫ w in P j, F w) (∫ w in Reg, F w) := by
    have h1 := hasSum_integral_iUnion hPm hPd (by rw [hPReg]; exact hint.mono_set hRegB)
    rwa [hPReg] at h1
  have hnull := hCN n d W A σ r N hW hdim hA hσ hinj hN fun w hw hwN => (hprop w hw hwN).1
  have hB : ∫ w in Metric.ball 0 r, F w = ∫ w in Reg, F w := by
    refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
      Metric.isOpen_ball.measurableSet.nullMeasurableSet hRegB ?_
    have hae : ∀ᵐ w ∂(volume : Measure (Fin d → ℂ)), w ∉ {w | w ∈ Metric.ball (0 : Fin d → ℂ) r ∧
        σ w ∈ N ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = 0} :=
      measure_eq_zero_iff_ae_notMem.1 hnull
    filter_upwards [hae] with w hw hwd
    obtain ⟨hwB, hwR⟩ := hwd
    by_cases hwN : σ w ∈ N
    · exfalso
      by_cases hdet : LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = 0
      · exact hw ⟨hwB, hwN, hdet⟩
      · exact hwR ⟨hwB, hwN, hdet⟩
    · show f (σ w) * _ = 0
      rw [hf0 _ hwN, zero_mul]
  rw [hB]
  exact hL.unique hR

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamDensIntegrable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology ComplexSets
open scoped ContDiff

noncomputable section

theorem ParamDensIntegrable.analyticOnNhd_of_differentiableOn {k m : ℕ} {U : Set (Fin k → ℂ)}
    {f : (Fin k → ℂ) → Fin m → ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := by
  refine analyticOnNhd_pi_iff.2 fun j => ?_
  have hj : DifferentiableOn ℂ (fun t => f t j) U := differentiableOn_pi.1 hf j
  refine IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hU hj.continuousOn fun w hw i => ?_
  have hw : DifferentiableAt ℂ (fun t => f t j) (Function.update w i (w i)) := by
    rw [Function.update_eq_self]
    exact (hj w hw).differentiableAt (hU.mem_nhds hw)
  exact hw.comp (w i) (hasFDerivAt_update w (w i)).differentiableAt

theorem ParamDensIntegrable.proof : ParamDensIntegrable.Statement := by
  intro n d W σ r r' N hσ hrr' hN f φ hf hfN hφ
  set B := Metric.ball (0 : Fin d → ℂ) r with hB
  choose U hUo hZU hφU using hφ
  set V : Set (Fin d → ℂ) := B ∩ σ ⁻¹' (⋂ k, U k) with hV
  have hσc : ContinuousOn σ B := hσ.continuousOn
  have hVo : IsOpen V := hσc.isOpen_inter_preimage Metric.isOpen_ball (isOpen_iInter_of_finite hUo)
  have hσ2 : ContDiffOn ℝ 2 σ B :=
    ((ParamDensIntegrable.analyticOnNhd_of_differentiableOn Metric.isOpen_ball hσ).contDiffOn_of_completeSpace).restrict_scalars ℝ
  have hc2 : ∀ k, ContDiffOn ℝ 2 (φ k ∘ σ) V := by
    intro k
    exact ((hφU k).of_le (WithTop.coe_le_coe.2 le_top)).comp (hσ2.mono Set.inter_subset_left)
      fun w hw => Set.mem_iInter.1 hw.2 k
  have hmaV : ContinuousOn (ReciprocityTheory.AnForm.maDens fun k => φ k ∘ σ) V :=
    ReciprocityTheory.AnForm.M.maDens_continuousOn _ _ hVo hc2
  have hcont : ContinuousOn (fun w => f (σ w) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ σ) w) B := by
    refine continuousOn_of_forall_continuousAt fun w hw => ?_
    by_cases hs : σ w ∈ tsupport f
    · have hwV : w ∈ V := ⟨hw, Set.mem_iInter.2 fun k => hZU k (hN w hw (hfN hs)).1⟩
      exact ((hf.continuousAt).comp (hσc.continuousAt (Metric.isOpen_ball.mem_nhds hw))).mul
        (hmaV.continuousAt (hVo.mem_nhds hwV))
    · have hO : IsOpen (B ∩ σ ⁻¹' (tsupport f)ᶜ) :=
        hσc.isOpen_inter_preimage Metric.isOpen_ball (isClosed_tsupport f).isOpen_compl
      refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [hO.mem_nhds ⟨hw, hs⟩] with w' hw'
      simp [image_eq_zero_of_notMem_tsupport hw'.2]
  have hK : IsCompact (Metric.closedBall (0 : Fin d → ℂ) r') := isCompact_closedBall 0 r'
  have hKB : Metric.closedBall (0 : Fin d → ℂ) r' ⊆ B := Metric.closedBall_subset_ball hrr'
  refine ((hcont.mono hKB).integrableOn_compact hK).of_forall_sdiff_eq_zero Metric.isOpen_ball.measurableSet ?_
  rintro w ⟨hwB, hwK⟩
  have hf0 : f (σ w) = 0 := by
    by_contra h
    exact hwK (Metric.mem_closedBall.2 (by
      simpa using (hN w hwB (hfN (subset_tsupport f h))).2))
  simp [hf0]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamOffRegularZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

theorem ParamOffRegularZero.proof : ParamOffRegularZero.Statement := by
  intro n d W A σ r N hσ hZN f φ hfN
  set g : (Fin d → ℂ) → Fin d → ℂ := fun v => A *ᵥ σ v with hg
  set C : Set (Fin d → ℂ) := {w | w ∈ Metric.ball (0 : Fin d → ℂ) r ∧ σ w ∈ N ∧
      LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = 0} with hC
  set R : Set (Fin d → ℂ) := {w | w ∈ Metric.ball (0 : Fin d → ℂ) r ∧ σ w ∈ N ∧
      LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} with hR
  have hgd : ∀ w ∈ Metric.ball (0 : Fin d → ℂ) r, DifferentiableAt ℂ g w := by
    intro w hw
    have hσw : DifferentiableAt ℂ σ w := (hσ w hw).differentiableAt (Metric.isOpen_ball.mem_nhds hw)
    exact (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).differentiableAt.comp w hσw
  have hnull : volume (g '' C) = 0 := by
    refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun w => (fderiv ℂ g w).restrictScalars ℝ) ?_ ?_
    · intro w hw
      exact ((hgd w hw.1).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    · intro w hw
      rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
        LinearMap.det_restrictScalars, hw.2.2, Algebra.norm_complex_apply, map_zero]
  have hz : ∀ y ∉ g '' C, chartDens W A ((σ '' R)ᶜ.indicator f) φ y = 0 := by
    intro y hy
    unfold chartDens sheetSum
    apply finsum_eq_zero_of_forall_eq_zero
    intro x
    classical
    rw [finsum_eq_if]
    split_ifs with hx hs
    · by_cases hxR : x ∈ σ '' R
      · simp [hxR]
      by_cases hf : f x = 0
      · simp [hxR, hf]
      exfalso
      have hxN : x ∈ N := hfN (subset_tsupport f (Function.mem_support.mpr hf))
      obtain ⟨w, hw, rfl⟩ := hZN ⟨hx.1, hxN⟩
      have hdet : LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = 0 := by
        by_contra hne
        exact hxR ⟨w, ⟨hw, hxN, hne⟩, rfl⟩
      exact hy ⟨w, ⟨hw, hxN, hdet⟩, hx.2⟩
    · rfl
    · rfl
  unfold chartInt
  apply integral_eq_zero_of_ae
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun y hy => ?_) hnull
  by_contra h
  exact hy (by simpa using hz y h)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimeTubeVolume
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets Metric

noncomputable section

theorem primeTube_isClosed_zeroSet {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroSet J) := by
  have : zeroSet J = ⋂ q ∈ J, {x : Fin n → ℂ | eval x q = 0} := by ext x; simp [zeroSet]
  rw [this]
  exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const

theorem primeTube_isClosed_zeroSetEuc {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) :
    IsClosed (zeroSetEuc J) := by
  have : zeroSetEuc J = ⋂ q ∈ J, {z : EuclideanSpace ℂ (Fin n) | eval (fun i => z i) q = 0} := by
    ext z; simp [zeroSetEuc]
  rw [this]
  exact isClosed_biInter fun q _ =>
    isClosed_eq ((MvPolynomial.continuous_eval q).comp (PiLp.continuous_ofLp 2 _)) continuous_const

theorem primeTube_exists_dim {n k : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : J.IsPrime)
    (hk : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ (k : ℕ)) :
    ∃ d : ℕ, d ≤ k ∧ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d : ℕ) := by
  have hnn : 0 ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) := ringKrullDim_nonneg_of_nontrivial
  generalize ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = x at hnn hk ⊢
  induction x using WithBot.recBotCoe with
  | bot => simp at hnn
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      rw [← WithBot.coe_natCast] at hk
      exact absurd (WithBot.coe_le_coe.1 hk) (by simp)
    | coe m => exact ⟨m, by exact_mod_cast hk, by norm_cast⟩

theorem primeTube_exact (hL : VarietyMassLower.Statement) (hM : MassFinite.Statement) {n d : ℕ}
    {J : Ideal (MvPolynomial (Fin n) ℂ)} {K : Set (Fin n → ℂ)} (hJ : J.IsPrime)
    (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d : ℕ)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Ioc (0 : ℝ) 1,
      volume (thickening r (zeroSet J ∩ K)) ≤ ENNReal.ofReal (C * r ^ ((2 * n : ℤ) - 2 * d)) := by
  set e : (Fin n → ℂ) → EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 with he_def
  have hdist : ∀ x y : Fin n → ℂ, dist x y ≤ dist (e x) (e y) := fun x y =>
    by simpa [he_def] using (PiLp.lipschitzWith_ofLp 2 (fun _ : Fin n => ℂ)).dist_le_mul (e x) (e y)
  obtain ⟨R, hR⟩ := ((hK.image (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ))).isBounded).exists_norm_le
  have hRK : ∀ x ∈ K, ‖e x‖ ≤ R := fun x hx => hR _ ⟨x, hx, rfl⟩
  obtain ⟨c, hc0, hc⟩ := hL n d J hJ hd R
  set M : ENNReal := μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ ball (0 : EuclideanSpace ℂ (Fin n)) (R + 1))
  have hMfin : M ≠ ⊤ := (hM n d J hJ hd (R + 1)).ne
  refine ⟨M.toReal * 4 ^ d * (4 * Real.pi) ^ n / c, by positivity, fun r hr => ?_⟩
  obtain ⟨hr0, hr1⟩ := hr
  set S := zeroSet J ∩ K
  have hS : IsCompact S := hK.inter_left (primeTube_isClosed_zeroSet J)

  set δ : NNReal := (r / 2).toNNReal
  have hδ : ((2 * δ : NNReal) : ℝ) = r := by
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (by positivity)]; push_cast; ring
  have hpack : packingNumber (2 * δ) S ≠ ⊤ := by
    obtain ⟨N, -, hNfin, hN⟩ := exists_finite_isCover_of_isCompact (ε := δ)
      (by rw [ne_eq, ← NNReal.coe_eq_zero, Real.coe_toNNReal _ (by positivity)]; exact (by positivity : r / 2 ≠ 0)) hS
    exact ne_top_of_le_ne_top (Set.encard_ne_top_iff.2 hNfin)
      ((packingNumber_two_mul_le_externalCoveringNumber δ S).trans hN.externalCoveringNumber_le_encard)
  set T0 := maximalSeparatedSet (2 * δ) S
  have hTfin : T0.Finite :=
    Set.encard_ne_top_iff.1 (by rw [encard_maximalSeparatedSet hpack]; exact hpack)
  set T := hTfin.toFinset
  have hTS : ∀ t ∈ T, t ∈ S := fun t ht => maximalSeparatedSet_subset (by simpa [T] using ht)

  have hcov : thickening r S ⊆ ⋃ t ∈ T, ball t (2 * r) := by
    intro p hp
    obtain ⟨s, hs, hps⟩ := mem_thickening_iff.1 hp
    have hs' := (isCover_maximalSeparatedSet hpack).subset_iUnion_closedBall hs
    obtain ⟨t, ht, hst⟩ := Set.mem_iUnion₂.1 hs'
    rw [mem_closedBall, hδ] at hst
    refine Set.mem_iUnion₂.2 ⟨t, by simpa [T] using ht, ?_⟩
    rw [mem_ball]
    linarith [dist_triangle p s t]
  have hvol : volume (thickening r S) ≤ ENNReal.ofReal ((T.card : ℝ) * (Real.pi * (2 * r) ^ 2) ^ n) := by
    refine (measure_mono hcov).trans ((measure_biUnion_finset_le T _).trans (le_of_eq ?_))
    simp only [volume_ball_pi_complex _ (by positivity : (0 : ℝ) < 2 * r), Finset.sum_const, nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]

  have hsep := isSeparated_maximalSeparatedSet (ε := 2 * δ) (A := S)
  have hdisj : (↑T : Set (Fin n → ℂ)).PairwiseDisjoint (fun t => zeroSetEuc J ∩ ball (e t) (r / 2)) := by
    intro x hx y hy hxy
    refine Set.disjoint_left.2 fun z hzx hzy => ?_
    have h1 : ((2 * δ : NNReal) : ENNReal) < edist x y := hsep (by simpa [T] using hx) (by simpa [T] using hy) hxy
    rw [edist_dist, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity), hδ] at h1
    have h2 := dist_triangle_left (e x) (e y) z
    simp only [Set.mem_inter_iff, mem_ball] at hzx hzy
    linarith [hdist x y, hzx.2, hzy.2]
  have hsub : (⋃ t ∈ T, zeroSetEuc J ∩ ball (e t) (r / 2)) ⊆
      zeroSetEuc J ∩ ball (0 : EuclideanSpace ℂ (Fin n)) (R + 1) := by
    refine Set.iUnion₂_subset fun t ht => fun z ⟨hz, hzt⟩ => ⟨hz, ?_⟩
    rw [mem_ball_zero_iff]
    rw [mem_ball, dist_eq_norm] at hzt
    have := hRK t (hTS t ht).2
    have := norm_le_norm_add_norm_sub' z (e t)
    linarith
  have hmass : (T.card : ENNReal) * ENNReal.ofReal (c * (r / 2) ^ (2 * d)) ≤ M := by
    refine le_trans ?_ (measure_mono hsub)
    rw [measure_biUnion_finset hdisj fun t _ =>
      (primeTube_isClosed_zeroSetEuc J).measurableSet.inter measurableSet_ball]
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun t ht => hc (e t) ?_ (hRK t (hTS t ht).2) (r / 2) ⟨by positivity, by linarith⟩
    have htZ := (hTS t ht).1
    intro q hq
    simpa [he_def] using htZ q hq
  have hcount : (T.card : ℝ) * (c * (r / 2) ^ (2 * d)) ≤ M.toReal := by
    have := ENNReal.toReal_mono hMfin hmass
    rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity)] at this

  refine hvol.trans (ENNReal.ofReal_le_ofReal ?_)
  set Y : ℝ := r ^ ((2 * n : ℤ) - 2 * d)
  have hY : Y * r ^ (2 * d) = r ^ (2 * n) := by
    simp only [Y]
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hr0.ne']
    congr 1; push_cast; ring
  have h4 : (r / 2) ^ (2 * d) * 4 ^ d = r ^ (2 * d) := by
    rw [div_pow, pow_mul, pow_mul]; field_simp; norm_num
  have hX : (T.card : ℝ) * (Real.pi * (2 * r) ^ 2) ^ n =
      (T.card : ℝ) * (c * (r / 2) ^ (2 * d)) * ((4 : ℝ) ^ d * (4 * Real.pi) ^ n * Y / c) := by
    rw [← h4] at hY
    have hX' : (Real.pi * (2 * r) ^ 2) ^ n = (4 * Real.pi) ^ n * r ^ (2 * n) := by
      rw [pow_mul, ← mul_pow]; ring
    rw [hX', ← hY]
    field_simp
  rw [hX]
  calc (T.card : ℝ) * (c * (r / 2) ^ (2 * d)) * ((4 : ℝ) ^ d * (4 * Real.pi) ^ n * Y / c)
      ≤ M.toReal * ((4 : ℝ) ^ d * (4 * Real.pi) ^ n * Y / c) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = M.toReal * 4 ^ d * (4 * Real.pi) ^ n / c * Y := by ring

theorem PrimeTubeVolume.proof (hL : VarietyMassLower.Statement) (hM : MassFinite.Statement) :
    PrimeTubeVolume.Statement := by
  intro n k J K hJ hk hK
  obtain ⟨d, hdk, hd⟩ := primeTube_exists_dim hJ hk
  obtain ⟨C, hC, hCr⟩ := primeTube_exact hL hM hJ hd hK
  refine ⟨C, hC, fun r hr => (hCr r hr).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hC))⟩
  exact zpow_le_zpow_right_of_le_one₀ hr.1 hr.2 (by omega)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPrimitiveFormWindow
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

theorem PrimitiveFormWindow.proof : PrimitiveFormWindow.Statement := by
  intro σ _ X w d A hX hiso ℓ N a δ q ha hδ hq hp hsep hrel
  obtain ⟨N₀, k, f, hN₀o, hwN₀, hfa, hXN⟩ := hX
  obtain ⟨W₀, hW₀, hW₀iso⟩ := hiso
  have hev := (show ∀ᶠ z in 𝓝 w, z ∈ N₀ from hN₀o.mem_nhds hwN₀).and
    ((show ∀ᶠ z in 𝓝 w, z ∈ W₀ from hW₀).and (hp.and (Filter.eventually_all.2 hrel)))
  obtain ⟨ε, hε, hεs⟩ := Metric.nhds_basis_closedBall.eventually_iff.1 hev
  set K : Set (σ → ℂ) := Metric.sphere w ε ∩ (fun z i => f i z) ⁻¹' {0} with hK
  have hsN : Metric.sphere w ε ⊆ N₀ := fun z hz => (hεs (Metric.sphere_subset_closedBall hz)).1
  have hKc : IsCompact K := by
    refine (isCompact_sphere w ε).of_isClosed_subset ?_ Set.inter_subset_left
    refine ContinuousOn.preimage_isClosed_of_isClosed ?_ Metric.isClosed_sphere isClosed_singleton
    exact continuousOn_pi.2 fun i => ((hfa i).continuousOn).mono hsN
  have hKX : ∀ z ∈ K, z ∈ X := by
    intro z hz
    have : z ∈ X ∩ N₀ := by
      rw [hXN]
      refine ⟨hsN hz.1, fun i => ?_⟩
      have := congrFun (Set.mem_singleton_iff.1 hz.2) i
      simpa using this
    exact this.1
  have hXK : ∀ z ∈ X, z ∈ Metric.sphere w ε → z ∈ K := by
    intro z hzX hzs
    refine ⟨hzs, ?_⟩
    have : z ∈ X ∩ N₀ := ⟨hzX, hsN hzs⟩
    rw [hXN] at this
    exact Set.mem_singleton_iff.2 (funext this.2)
  have hAK : A w ∉ A '' K := by
    rintro ⟨z, hzK, hAz⟩
    have hzw := (hεs (Metric.sphere_subset_closedBall hzK.1)).2.1
    have hzeq := hW₀iso z ⟨hKX z hzK, hzw⟩ hAz
    have h1 := hzK.1
    rw [hzeq, Metric.mem_sphere, dist_self] at h1
    exact hε.ne h1
  have hclo : IsClosed (A '' K) := (hKc.image A.continuous).isClosed
  have hev2 := (show ∀ᶠ y in 𝓝 (A w), y ∈ (A '' K)ᶜ from hclo.isOpen_compl.mem_nhds hAK).and
    ((Filter.eventually_all.2 fun j => (ha j).eventually_analyticAt).and
      (hδ.eventually_analyticAt.and
        ((Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
          (hq i j).eventually_analyticAt).and hsep)))
  obtain ⟨ρ, hρ, hρs⟩ := Metric.nhds_basis_ball.eventually_iff.1 hev2
  refine ⟨Metric.ball w ε, Metric.ball (A w) ρ, N₀, k, f, Metric.isOpen_ball, Metric.mem_ball_self hε,
    Metric.isOpen_ball, convex_ball _ _, Metric.mem_ball_self hρ, hN₀o, ?_, hfa, hXN, ?_, ?_, ?_,
    fun j y hy => (hρs hy).2.1 j, fun y hy => (hρs hy).2.2.1, fun i j y hy => (hρs hy).2.2.2.1 i j,
    fun y hy => (hρs hy).2.2.2.2⟩
  · rw [closure_ball w hε.ne']
    exact fun z hz => (hεs hz).1
  · rintro z ⟨hzX, hzc⟩ hzB
    rw [closure_ball w hε.ne'] at hzc
    rcases (Metric.mem_closedBall.1 hzc).lt_or_eq with h | h
    · exact Metric.mem_ball.2 h
    · exact absurd ⟨z, hXK z hzX (Metric.mem_sphere.2 h), rfl⟩ (hρs hzB).1
  · rintro z ⟨hzX, hzW⟩
    exact (hεs (Metric.ball_subset_closedBall hzW)).2.2.1 hzX
  · rintro i z ⟨hzX, hzW⟩
    exact (hεs (Metric.ball_subset_closedBall hzW)).2.2.2 i hzX

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

