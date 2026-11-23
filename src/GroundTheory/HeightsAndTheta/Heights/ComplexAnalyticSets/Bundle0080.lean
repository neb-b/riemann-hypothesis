module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0072
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0043
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0054
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0039
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0047
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0073
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0051
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0070
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationLength

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegularInjectivePieces
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology

noncomputable section

namespace RegularInjectivePieces

theorem analyticOnNhd_of_differentiableOn {k m : ℕ} {U : Set (Fin k → ℂ)} {f : (Fin k → ℂ) → Fin m → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) : AnalyticOnNhd ℂ f U := by
  refine analyticOnNhd_pi_iff.2 fun j => ?_
  have hj : DifferentiableOn ℂ (fun t => f t j) U := differentiableOn_pi.1 hf j
  refine IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hU hj.continuousOn fun w hw i => ?_
  have hw : DifferentiableAt ℂ (fun t => f t j) (Function.update w i (w i)) := by
    rw [Function.update_eq_self]
    exact (hj w hw).differentiableAt (hU.mem_nhds hw)
  exact hw.comp (w i) (hasFDerivAt_update w (w i)).differentiableAt

theorem local_injective {d : ℕ} {U : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → Fin d → ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) :
    IsOpen {w | w ∈ U ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} ∧
    ∀ w ∈ {w | w ∈ U ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0},
      ∃ V : Set (Fin d → ℂ), IsOpen V ∧ w ∈ V ∧
        V ⊆ {w | w ∈ U ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} ∧ Set.InjOn g V := by
  have hA : AnalyticOnNhd ℂ g U := analyticOnNhd_of_differentiableOn hU hg
  have hRopen : IsOpen {w | w ∈ U ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} := by
    have hc : ContinuousOn (fun w => (fderiv ℂ g w).det) U :=
      ContinuousLinearMap.continuous_det.comp_continuousOn hA.fderiv.continuousOn
    exact hc.isOpen_inter_preimage hU isOpen_compl_singleton
  refine ⟨hRopen, fun w hw => ?_⟩
  have hs : HasStrictFDerivAt g
      (((fderiv ℂ g w).toContinuousLinearEquivOfDetNeZero hw.2 : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ)) :
        (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) w := by
    rw [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero]
    exact (hA w hw.1).hasStrictFDerivAt
  refine ⟨(hs.toOpenPartialHomeomorph g).source ∩ _, (hs.toOpenPartialHomeomorph g).open_source.inter hRopen,
    ⟨hs.mem_toOpenPartialHomeomorph_source, hw⟩, Set.inter_subset_right, ?_⟩
  have hinj := (hs.toOpenPartialHomeomorph g).injOn
  rw [HasStrictFDerivAt.toOpenPartialHomeomorph_coe] at hinj
  exact hinj.mono Set.inter_subset_left

end RegularInjectivePieces


open RegularInjectivePieces in
theorem RegularInjectivePieces.proof : RegularInjectivePieces.Statement := by
  intro d U g hU hg
  obtain ⟨hRopen, key⟩ := local_injective hU hg
  set R := {w | w ∈ U ∧ LinearMap.det (fderiv ℂ g w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0} with hR
  choose! V hVo hVm hVR hVi using key
  obtain ⟨T, hTc, hTU⟩ :=
    TopologicalSpace.isOpen_iUnion_countable (fun w : R => V w) (fun w => hVo w w.2)
  have hUnion : ⋃ w : R, V w = R := by
    ext x
    simp only [Set.mem_iUnion]
    exact ⟨fun ⟨w, hx⟩ => hVR w w.2 hx, fun hx => ⟨⟨x, hx⟩, hVm x hx⟩⟩
  rcases T.eq_empty_or_nonempty with hT0 | hTne
  · refine ⟨fun _ => ∅, fun _ => MeasurableSet.empty, fun i j _ => disjoint_bot_left, ?_,
      fun _ => Set.injOn_empty _⟩
    rw [← hUnion, ← hTU, hT0]
    simp
  · obtain ⟨f, hf⟩ := hTc.exists_eq_range hTne
    refine ⟨disjointed (fun n => V (f n)),
      MeasurableSet.disjointed (fun n => (hVo _ (f n).2).measurableSet), disjoint_disjointed _, ?_,
      fun n => (hVi _ (f n).2).mono (disjointed_subset _ n)⟩
    rw [iUnion_disjointed]
    calc ⋃ n, V (f n) = ⋃ i ∈ Set.range f, V i :=
        (Set.biUnion_range (f := f) (g := fun i : R => V (i : Fin d → ℂ))).symm
      _ = ⋃ i ∈ T, V i := by rw [hf]
      _ = R := hTU.trans hUnion

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetImageArea
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Matrix

open scoped ENNReal

noncomputable section

theorem measurable_sheetJac {n d : ℕ} (s : (Fin d → ℂ) → Fin n → ℂ) : Measurable (sheetJac s) := by
  let C₁ : (Fin n → ℂ) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (WithLp.linearEquiv 2 ℝ (Fin n → ℂ)).symm.toLinearMap
  let C₂ : EuclideanSpace ℂ (Fin d) →L[ℝ] (Fin d → ℂ) :=
    LinearMap.toContinuousLinearMap (WithLp.linearEquiv 2 ℝ (Fin d → ℂ)).toLinearMap
  have hΦ : Continuous fun M : (Fin d → ℂ) →L[ℝ] (Fin n → ℂ) => C₁.comp (M.comp C₂) :=
    continuous_const.clm_comp (continuous_id.clm_comp continuous_const)
  have h : sheetJac s = (fun M : EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin n) =>
      areaJacobian (M : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n))) ∘
      (fun M : (Fin d → ℂ) →L[ℝ] (Fin n → ℂ) => C₁.comp (M.comp C₂)) ∘ fderiv ℝ s := by
    funext y
    rfl
  rw [h]
  exact (continuous_areaJacobian.comp hΦ).measurable.comp (measurable_fderiv ℝ s)

theorem SheetImageArea.proof (h : SheetImageAreaSet.Statement) : SheetImageArea.Statement := by
  classical
  intro n d A U s hU hs hA B hB hBU g hg
  let U' : Set (EuclideanSpace ℂ (Fin d)) := WithLp.ofLp ⁻¹' U
  let T : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin n) := fun y => WithLp.toLp 2 (s (WithLp.ofLp y))
  let T' := U'.piecewise T (fun _ => 0)
  have hU' : IsOpen U' := hU.preimage (PiLp.continuous_ofLp 2 _)
  have hT : ContinuousOn T U' :=
    (PiLp.continuous_toLp 2 _).comp_continuousOn
      (hs.continuousOn.comp (PiLp.continuous_ofLp 2 _).continuousOn fun _ hy => hy)
  have hT'm : Measurable T' := hT.measurable_piecewise continuousOn_const hU'.measurableSet
  have hEq : ∀ y ∈ B, T' y = T y := fun y hy => Set.piecewise_eq_of_mem _ _ _ (hBU y hy)
  have hJ : Measurable fun y : EuclideanSpace ℂ (Fin d) => ENNReal.ofReal (sheetJac s (WithLp.ofLp y)) :=
    ENNReal.measurable_ofReal.comp ((measurable_sheetJac s).comp (PiLp.continuous_ofLp 2 _).measurable)
  let ρ := (μH[((2 * d : ℕ) : ℝ)].restrict B).withDensity
    fun y : EuclideanSpace ℂ (Fin d) => ENNReal.ofReal (sheetJac s (WithLp.ofLp y))
  have hmap : ρ.map T' = (μH[((2 * d : ℕ) : ℝ)]).restrict (T '' B) := by
    ext S hS
    have hpre : MeasurableSet (T' ⁻¹' S) := hT'm hS
    rw [Measure.map_apply hT'm hS, withDensity_apply _ hpre, Measure.restrict_restrict hpre,
      Measure.restrict_apply hS,
      ← h n d A U s hU hs hA _ (hpre.inter hB) fun y hy => hBU y hy.2]
    congr 1
    ext z
    constructor
    · rintro ⟨y, ⟨hyS, hyB⟩, rfl⟩
      exact ⟨by simpa [Set.mem_preimage, hEq y hyB] using hyS, y, hyB, rfl⟩
    · rintro ⟨hzS, y, hyB, rfl⟩
      exact ⟨y, ⟨by simpa [Set.mem_preimage, hEq y hyB] using hzS, hyB⟩, rfl⟩
  calc ∫⁻ y in B, g (WithLp.toLp 2 (s (WithLp.ofLp y))) * ENNReal.ofReal (sheetJac s (WithLp.ofLp y))
          ∂(μH[((2 * d : ℕ) : ℝ)])
      = ∫⁻ y in B, ENNReal.ofReal (sheetJac s (WithLp.ofLp y)) * g (T' y) ∂(μH[((2 * d : ℕ) : ℝ)]) :=
        setLIntegral_congr_fun hB fun y hy => by rw [hEq y hy, mul_comm]
    _ = ∫⁻ y, g (T' y) ∂ρ := (lintegral_withDensity_eq_lintegral_mul _ hJ (hg.comp hT'm)).symm
    _ = ∫⁻ z, g z ∂(ρ.map T') := (lintegral_map hg hT'm).symm
    _ = _ := by rw [hmap]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetImageAreaSet
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module Matrix

open scoped ENNReal

noncomputable section

theorem SheetImageAreaSet.proof : SheetImageAreaSet.Statement := by
  classical
  intro n d A U s hU hs hA B hB hBU
  rcases U.eq_empty_or_nonempty with rfl | ⟨y₀, hy₀⟩
  · obtain rfl : B = ∅ := Set.eq_empty_of_forall_notMem fun y hy => hBU y hy
    simp
  let Ue : Set (EuclideanSpace ℂ (Fin d)) := WithLp.ofLp ⁻¹' U
  have hUe : IsOpen Ue := hU.preimage (PiLp.continuous_ofLp 2 _)
  let T : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin n) := fun y => WithLp.toLp 2 (s (WithLp.ofLp y))
  let P : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin d) :=
    (WithLp.linearEquiv 2 ℂ (Fin d → ℂ)).symm.toLinearMap ∘ₗ Matrix.mulVecLin A ∘ₗ
      (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap
  have hPT : ∀ y ∈ Ue, P (T y) = y := fun y hy => by
    simp [P, T, hA _ hy]
  have hPs : Function.Surjective P := by
    have hle : Ue ⊆ (LinearMap.range P : Set _) := fun y hy => ⟨T y, hPT y hy⟩
    refine LinearMap.range_eq_top.1 (Submodule.eq_top_of_nonempty_interior' _
      ⟨WithLp.toLp 2 y₀, interior_mono hle ?_⟩)
    rw [hUe.interior_eq]
    exact hy₀
  obtain ⟨m, e, Q, L, π, hQn, hQ⟩ := SheetImageAreaSet.exists_adapted_frame P hPs
  let F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m) := fun x => π (T (L.symm x))
  let Ω : Set (EuclideanSpace ℂ (Fin d)) := L.symm ⁻¹' Ue
  have hLc : Continuous L.symm := LinearMap.continuous_of_finiteDimensional _
  have hΩ : IsOpen Ω := hUe.preimage hLc
  have hQT : ∀ y ∈ Ue, Q (T y) = graphPt e F (L y) := by
    intro y hy
    rw [hQ, hPT y hy]
    simp [graphPt, F]
  have hsd : ∀ y ∈ Ue, DifferentiableAt ℂ s (WithLp.ofLp y) := fun y hy =>
    hs.differentiableAt (hU.mem_nhds hy)
  have hTd : ∀ y ∈ Ue, DifferentiableAt ℂ T y := fun y hy =>
    (PiLp.hasFDerivAt_toLp (𝕜 := ℂ) 2 _).differentiableAt.comp y
      ((hsd y hy).comp y (PiLp.hasFDerivAt_ofLp (𝕜 := ℂ) 2 y).differentiableAt)
  have hLd : ∀ x, DifferentiableAt ℂ (fun x => L.symm x) x := fun x => by
    simpa using (LinearMap.toContinuousLinearMap L.symm.toLinearMap).differentiableAt (x := x)
  have hπd : ∀ z, DifferentiableAt ℂ (fun z => π z) z := fun z => by
    simpa using (LinearMap.toContinuousLinearMap π).differentiableAt (x := z)
  have hFd : DifferentiableOn ℂ F Ω := fun x hx =>
    ((hπd _).comp x ((hTd _ hx).comp x (hLd x))).differentiableWithinAt
  have hBΩ : L '' B ⊆ Ω := by
    rintro _ ⟨y, hy, rfl⟩
    show L.symm (L y) ∈ Ue
    rw [L.symm_apply_apply]
    exact hBU y hy
  have hLB : MeasurableSet (L '' B) := by
    rw [L.image_eq_preimage_symm]
    exact hLc.measurable hB
  have hQi : Isometry Q := AddMonoidHomClass.isometry_of_norm Q hQn
  have himg : Q '' (T '' B) = graphPt e F '' (L '' B) := by
    rw [Set.image_image, Set.image_image]
    exact Set.image_congr fun y hy => hQT y (hBU y hy)
  have hGA := GraphAreaHolomorphic.proof (AreaGraph.proof
    (AreaGraphBound.proof AreaGraphPiece.proof AreaGraphPartition.proof GraphJacContinuous.proof))
  have hfin : finrank ℝ (EuclideanSpace ℂ (Fin d)) = 2 * d := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  have : (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))).IsAddHaarMeasure := by
    have := isAddHaarMeasure_hausdorffMeasure (E := EuclideanSpace ℂ (Fin d))
    rwa [hfin] at this
  let Lr : EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin d) :=
    LinearMap.toContinuousLinearMap ((L : _ →ₗ[ℂ] _).restrictScalars ℝ)
  let Qr : EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (Q.restrictScalars ℝ)
  have hCV := lintegral_image_eq_lintegral_abs_det_fderiv_mul (μH[((2 * d : ℕ) : ℝ)]) hB
    (f := fun y => L y) (f' := fun _ => Lr) (fun y _ => Lr.hasFDerivAt.hasFDerivWithinAt) L.injective.injOn
    (fun x => ENNReal.ofReal (areaJacobian (fderiv ℝ (graphPt e F) x :
      EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n))))
  rw [← hQi.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg _)), himg,
    hGA d m n e Ω F hΩ hFd (L '' B) hBΩ hLB, hCV]
  refine setLIntegral_congr_fun hB fun y hy => ?_
  have hy' : y ∈ Ue := hBU y hy
  let Mt : EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap.comp
      ((fderiv ℝ s (WithLp.ofLp y)).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℂ)).toContinuousLinearMap)
  have hT : HasFDerivAt T Mt y :=
    (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp y
      (((hsd y hy').restrictScalars ℝ).hasFDerivAt.comp y (PiLp.hasFDerivAt_ofLp (𝕜 := ℝ) 2 y))
  have hx : L y ∈ Ω := hBΩ ⟨y, hy, rfl⟩
  have hFR : DifferentiableAt ℝ F (L y) := ((hFd.differentiableAt (hΩ.mem_nhds hx)).restrictScalars ℝ)
  have hG : HasFDerivAt (graphPt e F) (fderiv ℝ (graphPt e F) (L y)) (L y) :=
    (GraphAreaHolomorphic.differentiableAt_graphPt_real e hFR).hasFDerivAt
  have h1 : HasFDerivAt (fun z => Q (T z)) (Qr.comp Mt) y := Qr.hasFDerivAt.comp y hT
  have h2 : HasFDerivAt (fun z => graphPt e F (L z)) ((fderiv ℝ (graphPt e F) (L y)).comp Lr) y :=
    hG.comp y Lr.hasFDerivAt
  have hM : Qr.comp Mt = (fderiv ℝ (graphPt e F) (L y)).comp Lr :=
    h1.unique (h2.congr_of_eventuallyEq (Filter.eventually_of_mem (hUe.mem_nhds hy') fun z hz => hQT z hz))
  have hJ : sheetJac s (WithLp.ofLp y) =
      areaJacobian (Mt : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)) :=
    congrArg areaJacobian (LinearMap.ext fun v => rfl)
  have hJ2 : areaJacobian (Mt : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)) =
      areaJacobian (fderiv ℝ (graphPt e F) (L y) : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)) *
        |LinearMap.det (Lr : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin d))| := by
    have hQr : ∀ v, ‖(Qr : EuclideanSpace ℂ (Fin n) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)) v‖ = ‖v‖ := fun v => by
      simp only [Qr, ContinuousLinearMap.coe_coe, LinearMap.coe_toContinuousLinearMap',
        LinearMap.coe_restrictScalars]
      exact hQn v
    rw [← SheetImageAreaSet.areaJacobian_comp_of_norm _ hQr,
      ← SheetImageAreaSet.areaJacobian_comp_endo]
    rw [← ContinuousLinearMap.toLinearMap_comp, ← ContinuousLinearMap.toLinearMap_comp, hM]
  rw [hJ, hJ2, mul_comm (areaJacobian _), ENNReal.ofReal_mul (abs_nonneg _)]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceBranches
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets Filter Topology

theorem SliceBranches.proof (hI : IndefiniteRowSideFullHecke.ComplexSets.SliceImmersiveGeneral.Statement)
    (hB : IndefiniteRowSideFullHecke.ComplexSets.BranchProperAtPoint.Statement) (hM : SliceMatricesOpen.Statement)
    (hC : ImplicitCurve.Statement) : SliceBranches.Statement := by
  intro n d J W u p m γ ord hJ hdim hu hW hp hcov hsl hdisj hord U Λ hUo hUd hΛ
  obtain ⟨N₁, hN₁, hcov₁⟩ := hcov
  obtain ⟨V, hV, hVd⟩ := hI n d J W u p m γ hJ hdim hu hW hp hsl
  have hOp : interior (N₁ ∩ V) ∈ 𝓝 p := interior_mem_nhds.2 (inter_mem hN₁ hV)
  obtain ⟨y, hyO, hyW, hyU⟩ := mem_closure_iff_nhds.1 (hUd hp) _ hOp
  obtain ⟨q, ⟨hqO, hqU⟩, hqW, hqs⟩ := mem_closure_iff_nhds.1 (hVd ⟨hyW, (interior_subset hyO).2⟩)
    (interior (N₁ ∩ V) ∩ U) (inter_mem (isOpen_interior.mem_nhds hyO) (hUo.mem_nhds hyU))
  have hqN : N₁ ∈ 𝓝 q := mem_of_superset (mem_interior_iff_mem_nhds.1 hqO) fun x hx => hx.1
  choose s hs hs0 hsq hsinj using hqs
  obtain ⟨hGo, hGne⟩ := hM n d m (fun b => (γ b).toFun) s
    (fun b => (γ b).differentiableOn.differentiableAt (Metric.isOpen_ball.mem_nhds (hs b))) hsinj
  obtain ⟨L, hLG, hLΛ⟩ := (hΛ q ⟨hqW, hqU⟩).inter_open_nonempty _ hGo hGne
  choose r hr φ hφd hφ0 hφ P hP hPφ using fun b =>
    hC n d (γ b).toFun (γ b).radius L (s b) (γ b).differentiableOn (hs b) (hLG b)
  choose ε hεpos hεP using fun b =>
    hB n (d + 1) J u p q m γ hJ hdim hu ⟨N₁, hqN, hcov₁⟩ hdisj b (s b) (hs b) (hsq b) (P b) (hP b)
  have hφ0' : ∀ b, ∀ τ ∈ Metric.ball (0 : Fin 1 → ℂ) (r b), φ b τ 0 = τ 0 := fun b τ hτ => by
    rw [(hφ b τ hτ).2.1, hs0 b, zero_add]
  let c : Fin m → VarBranch (sliceIdeal J L q) 1 q := fun b =>
    { radius := r b
      radius_pos := hr b
      toFun := fun τ => (γ b).toFun (φ b τ)
      differentiableOn := (γ b).differentiableOn.comp (hφd b) fun τ hτ => (hφ b τ hτ).1
      injOn := fun τ hτ τ' hτ' h => by
        have h0 := congrArg (fun t => t 0) ((γ b).injOn (hφ b τ hτ).1 (hφ b τ' hτ').1 h)
        simp only [hφ0' b τ hτ, hφ0' b τ' hτ'] at h0
        funext i
        rwa [Subsingleton.elim i 0]
      map_zero := by simp only [hφ0 b, hsq b]
      mapsTo := fun τ hτ => by
        rw [zeroSet_sliceIdeal]
        exact ⟨(γ b).mapsTo (hφ b τ hτ).1, by rw [Set.mem_ofPred_eq, (hφ b τ hτ).2.2, hsq b]⟩ }
  have himg : ∀ b, (c b).image ⊆ (γ b).image := by
    rintro b _ ⟨τ, hτ, rfl⟩
    exact ⟨φ b τ, (hφ b τ hτ).1, rfl⟩
  refine ⟨q, ⟨hqW, hqU⟩, L, hLΛ, c, ⟨N₁ ∩ ⋂ b, Metric.ball q (ε b),
    inter_mem hqN (iInter_mem.2 fun b => Metric.ball_mem_nhds q (hεpos b)), ?_⟩,
    fun b b' hbb' x hx => hdisj b b' hbb' ⟨himg b hx.1, himg b' hx.2⟩, fun b => ?_⟩
  · rintro x ⟨hxs, hxN, hxε⟩
    rw [zeroSet_sliceIdeal] at hxs
    obtain ⟨b, t, ht, rfl⟩ : ∃ b, ∃ t ∈ Metric.ball 0 (γ b).radius, (γ b).toFun t = x := by
      simpa [VarBranch.image] using hcov₁ ⟨hxs.1, hxN⟩
    obtain ⟨τ, hτ, rfl⟩ := hPφ b t (hεP b t ht (Set.mem_iInter.1 hxε b))
      (by rw [hxs.2, hsq b])
    exact Set.mem_iUnion.2 ⟨b, τ, hτ, rfl⟩
  · obtain ⟨H, hHd, hH0, hHe⟩ := hord b
    refine ⟨fun τ => H (φ b τ), hHd.comp (hφd b) (fun τ hτ => (hφ b τ hτ).1),
      fun τ hτ => hH0 _ (hφ b τ hτ).1, fun τ hτ => ?_⟩
    show linEval u ((γ b).toFun (φ b τ)) = τ 0 ^ ord b * H (φ b τ)
    have h := hHe _ (hφ b τ hτ).1
    rw [hφ0' b τ hτ] at h
    exact h

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceReducedAwayZariski
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem eq_ker_eval_of_X_sub_C_mem {n : ℕ} (q : Fin n → ℂ) (P : Ideal (MvPolynomial (Fin n) ℂ))
    (hP : P.IsPrime) (h : ∀ k, X k - C (q k) ∈ P) : P = RingHom.ker (eval q) := by
  have hext : Ideal.Quotient.mk P = ((Ideal.Quotient.mk P).comp C).comp (eval q) := by
    refine MvPolynomial.ringHom_ext (fun c => by simp) (fun i => ?_)
    simp only [RingHom.comp_apply, eval_X]
    exact Ideal.Quotient.eq.2 (h i)
  have hle : RingHom.ker (eval q) ≤ P := by
    intro f hf
    rw [← Ideal.Quotient.eq_zero_iff_mem, hext]
    simp [RingHom.mem_ker.1 hf]
  have hmax : (RingHom.ker (eval q)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun c => ⟨C c, eval_C c⟩
  exact (hmax.eq_of_le hP.ne_top hle).symm

theorem SliceReducedAwayZariski.proof (hG : GenericFibreRadicalAway.Statement)
    (hB : SliceBundleRadicalAway.Statement) : SliceReducedAwayZariski.Statement := by
  intro n d J q hJ
  choose F hF0 hF using fun k : Fin n =>
    hG (Fin d × Fin n) n (universalSliceIdeal J d q) (X k - C (C (q k))) (hB n d J q hJ k)
  refine ⟨∏ k, F k, Finset.prod_ne_zero_iff.2 fun k _ => hF0 k, ?_⟩
  intro L hL P hP hIP hPq g hg
  rw [map_prod, Finset.prod_ne_zero_iff] at hL
  obtain ⟨k, hk⟩ : ∃ k, X k - C (q k) ∉ P := by
    by_contra h
    push Not at h
    exact hPq (eq_ker_eval_of_X_sub_C_mem q P hP h)
  have hk' := hF k _ (hL k (Finset.mem_univ k))
  rw [fibreIdeal_universalSliceIdeal] at hk'
  obtain ⟨m, hm⟩ := hk' g hg
  refine ⟨(X k - C (q k)) ^ m, fun h => hk (hP.mem_of_pow_mem m h), ?_⟩
  simpa using hm

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchIntDecompose
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def BranchIntDecompose.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u q : Fin n → ℂ) (m : ℕ)
    (γ : Fin m → VarBranch J (d + 1) q) (ord : Fin m → ℕ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    (∃ N ∈ 𝓝 q, zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) →
    (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | linEval u x = 0}) →
    (∀ b, VanishesToOrder (fun t => linEval u ((γ b).toFun t)) (γ b).radius (ord b)) →
      ∃ N ∈ 𝓝 q, ∀ (f : (Fin n → ℂ) → ℝ) (ψ : Fin (d + 1) → (Fin n → ℂ) → ℝ),
        ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ N →
        (∀ i, SmoothNear (zeroSet J) (ψ i)) →
          varInt J (d + 1) f ψ =
            ∑ b, ReciprocityTheory.AnForm.maInt (fun k => ψ k ∘ (γ b).toFun) (f ∘ (γ b).toFun)
              (Metric.ball 0 (γ b).radius)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveGermComponents
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def CurveGermComponents.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    ringKrullDim (curveLocalRing I q) = 1 →
      ∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet I ∩ N, ∃ W ∈ I.minimalPrimes,
        ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = 1 ∧ q ∈ zeroSet W ∧ x ∈ zeroSet W

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationQuotientLength
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

def CurveNormalisationQuotientLength.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), IsRadicalAt I q →
    ringKrullDim (curveLocalRing I q) = 1 →
    Module.length (curveLocalRing I q)
        (curveNormalisation I q ⧸
          LinearMap.range (Algebra.linearMap (curveLocalRing I q) (curveNormalisation I q))) ≠ ⊤

end GroundTheory.Heights₂.Heights
end

