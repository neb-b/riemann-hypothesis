module

public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0023
public import ReciprocityTheory.L2DbarEstimates.LeviForms.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0616
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0617
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHoloSectionAeEqOfBallCover
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.AeHoloGlue

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]

theorem mu_ne_zero_of_open (A : WeightedAtlas n Y ι La) {O : Set Y} (hO : IsOpen O)
    (hne : O.Nonempty) : A.mu O ≠ 0 := by
  obtain ⟨y, hy⟩ := hne
  have hW : IsOpen (O ∩ (A.chart (A.pick y)).source) := hO.inter (A.chart (A.pick y)).open_source
  have hWs : O ∩ (A.chart (A.pick y)).source ⊆ (A.chart (A.pick y)).source := Set.inter_subset_right
  have hS : IsOpen (A.chart (A.pick y) '' (O ∩ (A.chart (A.pick y)).source)) :=
    (A.chart (A.pick y)).isOpen_image_of_subset_source hW hWs
  have hSne : (A.chart (A.pick y) '' (O ∩ (A.chart (A.pick y)).source)).Nonempty :=
    ⟨_, Set.mem_image_of_mem _ ⟨hy, A.mem_pick y⟩⟩
  have hSt : A.chart (A.pick y) '' (O ∩ (A.chart (A.pick y)).source) ⊆ (A.chart (A.pick y)).target := by
    rintro _ ⟨x, hx, rfl⟩; exact (A.chart (A.pick y)).map_source hx.2
  intro h0
  have h1 : A.mu (O ∩ (A.chart (A.pick y)).source) = 0 := measure_mono_null Set.inter_subset_left h0
  rw [A.mu_chart _ _ hW.measurableSet hWs] at h1
  have hc : ContinuousOn (fun v => ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick y) ((A.chart (A.pick y)).symm v))))
      (A.chart (A.pick y) '' (O ∩ (A.chart (A.pick y)).source)) := by
    have := (A.smooth_ph A.kap (A.pick y)).continuousOn.mono hSt
    exact ENNReal.continuous_ofReal.comp_continuousOn (Real.continuous_exp.comp_continuousOn this)
  rw [lintegral_eq_zero_iff' (hc.aemeasurable hS.measurableSet)] at h1
  have h3 := ae_iff.mp h1
  have hu : {v | ¬ (fun v => ENNReal.ofReal (Real.exp (A.ph A.kap (A.pick y) ((A.chart (A.pick y)).symm v)))) v
      = (0 : V n → ℝ≥0∞) v} = Set.univ := by
    ext v; simp [ENNReal.ofReal_eq_zero, Real.exp_pos]
  rw [hu, Measure.restrict_apply_univ] at h3
  exact hS.measure_ne_zero volume hSne h3

theorem exists_null (A : WeightedAtlas n Y ι La) (i : ι) (c : V n) (r : ℝ) (u : V n → ℂ)
    (f : Y → ℂ) (h : u =ᵐ[volume.restrict (ball c r)] f ∘ (A.chart i).symm) :
    ∃ M : Set Y, A.mu M = 0 ∧ ∀ y ∈ (A.chart i).source, A.chart i y ∈ ball c r → y ∉ M →
      u (A.chart i y) = f y := by
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_ball] at h
  obtain ⟨T, hET, hTm, hT0⟩ := exists_measurable_superset_of_null (ae_iff.mp h)
  classical
  have hφ : Measurable ((A.chart i).source.piecewise (A.chart i) (fun _ => (0 : V n))) :=
    ContinuousOn.measurable_piecewise (A.chart i).continuousOn continuousOn_const
      (A.chart i).open_source.measurableSet
  refine ⟨(A.chart i).source ∩ (A.chart i).source.piecewise (A.chart i) (fun _ => (0 : V n)) ⁻¹' T,
    ?_, ?_⟩
  · have hm : MeasurableSet ((A.chart i).source ∩
        (A.chart i).source.piecewise (A.chart i) (fun _ => (0 : V n)) ⁻¹' T) :=
      (A.chart i).open_source.measurableSet.inter (hφ hTm)
    rw [A.mu_chart i _ hm Set.inter_subset_left]
    refine le_antisymm ?_ (by simp)
    calc _ ≤ ∫⁻ v in T, ENNReal.ofReal (Real.exp (A.ph A.kap i ((A.chart i).symm v))) := by
          apply lintegral_mono_set
          rintro _ ⟨x, ⟨hx1, hx2⟩, rfl⟩
          have : (A.chart i).source.piecewise (A.chart i) (fun _ => (0 : V n)) x = A.chart i x :=
            Set.piecewise_eq_of_mem _ _ _ hx1
          simpa [this] using hx2
      _ = 0 := setLIntegral_measure_zero _ _ hT0
  · intro y hy hb hM
    by_contra hne
    apply hM
    refine ⟨hy, ?_⟩
    show (A.chart i).source.piecewise (A.chart i) (fun _ => (0 : V n)) y ∈ T
    rw [Set.piecewise_eq_of_mem _ _ _ hy]
    apply hET
    simp only [Set.mem_setOf_eq]
    intro heq
    apply hne
    simpa [Function.comp, (A.chart i).left_inv hy] using heq hb

theorem continuousOn_g (A : WeightedAtlas n Y ι La) (la : La) (i j : ι) :
    ContinuousOn (A.g la i j) ((A.chart i).source ∩ (A.chart j).source) := by
  have h1 : ContinuousOn (A.g la i j ∘ (A.chart i).symm ∘ A.chart i)
      ((A.chart i).source ∩ (A.chart j).source) := by
    refine (A.holo_g la i j).continuousOn.comp ((A.chart i).continuousOn.mono Set.inter_subset_left) ?_
    intro y hy
    exact ⟨(A.chart i).map_source hy.1, by simpa [(A.chart i).left_inv hy.1] using hy.2⟩
  refine h1.congr ?_
  intro y hy
  simp [(A.chart i).left_inv hy.1]

theorem main : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La),
    ∀ (C : Cover A) (la : La) (f : ι → Y → ℂ) (u : Fin C.m → V n → ℂ),
    (∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source → f i y = A.g la i j y * f j y) →
    (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) →
    (∀ a, u a =ᵐ[volume.restrict (ball (C.c a) (C.r a))] f (C.idx a) ∘ (A.chart (C.idx a)).symm) →
    ∃ F : ι → Y → ℂ, A.IsSec la F ∧ ∀ᵐ y ∂A.mu, F (A.pick y) y = f (A.pick y) y := by
  intro n Y _ _ _ _ _ ι La _ A C la f u hf hu hae
  classical

  have hBo : ∀ a, IsOpen ((A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a)) :=
    fun a => (A.chart (C.idx a)).isOpen_inter_preimage isOpen_ball
  have hcov : ∀ y, ∃ a, y ∈ (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a) := by
    intro y
    by_contra hno
    push_neg at hno
    have h0 : ∀ a, C.chi a y = 0 := fun a => by
      by_contra hne
      exact hno a (C.supp a (subset_tsupport _ hne))
    have := C.sum_one y
    simp [h0] at this
  choose M hM0 hM using fun a => exists_null A (C.idx a) (C.c a) (C.r a) (u a) (f (C.idx a)) (hae a)
  have hM0' : A.mu (⋃ a, M a) = 0 := measure_iUnion_null hM0

  have hoff : ∀ a y, y ∈ (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a) →
      y ∉ ⋃ a, M a → u a (A.chart (C.idx a) y) = f (C.idx a) y := fun a y hy hn =>
    hM a y hy.1 hy.2 (fun h => hn (Set.mem_iUnion.mpr ⟨a, h⟩))
  have hcu : ∀ a, ContinuousOn (fun y => u a (A.chart (C.idx a) y))
      ((A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a)) := fun a =>
    (hu a).continuousOn.comp ((A.chart (C.idx a)).continuousOn.mono Set.inter_subset_left)
      (fun y hy => hy.2)

  have hagree : ∀ a b y, y ∈ (A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a) →
      y ∈ (A.chart (C.idx b)).source ∩ A.chart (C.idx b) ⁻¹' ball (C.c b) (C.r b) →
      u a (A.chart (C.idx a) y) = A.g la (C.idx a) (C.idx b) y * u b (A.chart (C.idx b) y) := by
    intro a b y hya hyb
    set D := ((A.chart (C.idx a)).source ∩ A.chart (C.idx a) ⁻¹' ball (C.c a) (C.r a)) ∩
      ((A.chart (C.idx b)).source ∩ A.chart (C.idx b) ⁻¹' ball (C.c b) (C.r b)) with hD
    have hcont : ContinuousOn (fun y => u a (A.chart (C.idx a) y) -
        A.g la (C.idx a) (C.idx b) y * u b (A.chart (C.idx b) y)) D :=
      ((hcu a).mono Set.inter_subset_left).sub
        (((continuousOn_g A la (C.idx a) (C.idx b)).mono
          (show D ⊆ (A.chart (C.idx a)).source ∩ (A.chart (C.idx b)).source from
            fun z hz => ⟨hz.1.1, hz.2.1⟩)).mul ((hcu b).mono Set.inter_subset_right))
    have hop := hcont.isOpen_inter_preimage ((hBo a).inter (hBo b)) (isOpen_compl_singleton (x := (0 : ℂ)))
    have hsub : D ∩ (fun y => u a (A.chart (C.idx a) y) -
        A.g la (C.idx a) (C.idx b) y * u b (A.chart (C.idx b) y)) ⁻¹' {0}ᶜ ⊆ ⋃ a, M a := by
      intro z ⟨hz, hz0⟩
      by_contra hn
      apply hz0
      simp only [Set.mem_singleton_iff]
      rw [hoff a z hz.1 hn, hoff b z hz.2 hn, hf _ _ z hz.1.1 hz.2.1]
      ring
    by_contra hne
    exact mu_ne_zero_of_open A hop ⟨y, ⟨hya, hyb⟩, by simpa [sub_eq_zero] using hne⟩
      (measure_mono_null hsub hM0')
  choose α hα using hcov
  refine ⟨fun i y => A.g la i (C.idx (α y)) y * u (α y) (A.chart (C.idx (α y)) y), ⟨?_, ?_⟩, ?_⟩
  ·
    intro i v hv
    have hvs : (A.chart i).symm v ∈ (A.chart i).source := (A.chart i).map_target hv.1
    set a0 := α ((A.chart i).symm v)
    have hO : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹'
        ((A.chart (C.idx a0)).source ∩ A.chart (C.idx a0) ⁻¹' ball (C.c a0) (C.r a0))) :=
      (A.chart i).isOpen_inter_preimage_symm (hBo a0)
    have hvO : v ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹'
        ((A.chart (C.idx a0)).source ∩ A.chart (C.idx a0) ⁻¹' ball (C.c a0) (C.r a0)) :=
      ⟨hv.1, hα _⟩
    have hOovl : (A.chart i).target ∩ (A.chart i).symm ⁻¹'
        ((A.chart (C.idx a0)).source ∩ A.chart (C.idx a0) ⁻¹' ball (C.c a0) (C.r a0)) ⊆
        ovl A.chart i (C.idx a0) := fun w hw => ⟨hw.1, hw.2.1⟩
    have hG : DifferentiableOn ℂ (fun w => A.g la i (C.idx a0) ((A.chart i).symm w) *
        u a0 ((A.chart (C.idx a0) ∘ (A.chart i).symm) w))
        ((A.chart i).target ∩ (A.chart i).symm ⁻¹'
          ((A.chart (C.idx a0)).source ∩ A.chart (C.idx a0) ⁻¹' ball (C.c a0) (C.r a0))) :=
      ((A.holo_g la i (C.idx a0)).mono hOovl).mul
        ((hu a0).comp ((A.holo_trans i (C.idx a0)).mono hOovl) (fun w hw => hw.2.2))
    have hloc : (fun w => A.g la i (C.idx a0) ((A.chart i).symm w) *
        u a0 ((A.chart (C.idx a0) ∘ (A.chart i).symm) w)) =ᶠ[𝓝 v]
        ((fun i y => A.g la i (C.idx (α y)) y * u (α y) (A.chart (C.idx (α y)) y)) i ∘
          (A.chart i).symm) := by
      filter_upwards [hO.mem_nhds hvO] with w hw
      have hws : (A.chart i).symm w ∈ (A.chart i).source := (A.chart i).map_target hw.1
      simp only [Function.comp]
      rw [hagree (α ((A.chart i).symm w)) a0 _ (hα _) hw.2, ← mul_assoc,
        ← A.g_cocycle la i _ _ _ hws (hα _).1 hw.2.1]
    exact ((hG.differentiableAt (hO.mem_nhds hvO)).congr_of_eventuallyEq hloc.symm).differentiableWithinAt
  ·
    intro i j y _ hi hj
    simp only
    rw [A.g_cocycle la i j (C.idx (α y)) y hi hj (hα y).1]
    ring
  ·
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hM0'] with y hy
    rw [hoff _ y (hα y) hy, ← hf _ _ y (A.mem_pick y) (hα y).1]

end GlobalTheory.AeHoloGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJacobianSectionCanonicalWeight
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.JacSec

noncomputable section

def jacM {n : ℕ} (f0 : V n → ℂ) (f : Fin n → V n → ℂ) (v : V n) : V n →L[ℂ] V n :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm : (Fin n → ℂ) →L[ℂ] V n).comp
    (ContinuousLinearMap.pi fun k => f0 v • fderiv ℂ (f k) v - f k v • fderiv ℂ f0 v)

theorem jacM_apply {n : ℕ} (f0 : V n → ℂ) (f : Fin n → V n → ℂ) (v ξ : V n) (k : Fin n) :
    (jacM f0 f v ξ).ofLp k = f0 v * fderiv ℂ (f k) v ξ - f k v * fderiv ℂ f0 v ξ := by
  simp [jacM]

theorem jacM_congr {n : ℕ} {f0 g0 : V n → ℂ} {f g : Fin n → V n → ℂ} {v : V n}
    (h0 : f0 =ᶠ[𝓝 v] g0) (h : ∀ k, f k =ᶠ[𝓝 v] g k) : jacM f0 f v = jacM g0 g v := by
  ext ξ k
  rw [jacM_apply, jacM_apply, h0.fderiv_eq, (h k).fderiv_eq, h0.eq_of_nhds, (h k).eq_of_nhds]

theorem jacM_trans {n : ℕ} (G : V n → ℂ) (Φ : V n → V n) (h0 : V n → ℂ) (h : Fin n → V n → ℂ)
    (v : V n) (hG : DifferentiableAt ℂ G v) (hΦ : DifferentiableAt ℂ Φ v)
    (hh0 : DifferentiableAt ℂ h0 (Φ v)) (hh : ∀ k, DifferentiableAt ℂ (h k) (Φ v)) :
    jacM (fun w => G w * h0 (Φ w)) (fun k w => G w * h k (Φ w)) v =
      (G v ^ 2) • (jacM h0 h (Φ v)).comp (fderiv ℂ Φ v) := by
  have d0 : fderiv ℂ (fun w => G w * h0 (Φ w)) v =
      G v • ((fderiv ℂ h0 (Φ v)).comp (fderiv ℂ Φ v)) + h0 (Φ v) • fderiv ℂ G v :=
    (hG.hasFDerivAt.mul (hh0.hasFDerivAt.comp v hΦ.hasFDerivAt)).fderiv
  have dk : ∀ k, fderiv ℂ (fun w => G w * h k (Φ w)) v =
      G v • ((fderiv ℂ (h k) (Φ v)).comp (fderiv ℂ Φ v)) + h k (Φ v) • fderiv ℂ G v := fun k =>
    (hG.hasFDerivAt.mul ((hh k).hasFDerivAt.comp v hΦ.hasFDerivAt)).fderiv
  ext ξ k
  rw [jacM_apply, d0, dk]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, jacM_apply,
    ContinuousLinearMap.add_apply, smul_eq_mul, PiLp.smul_apply]
  ring

theorem det_smul_V {n : ℕ} (c : ℂ) (M : V n →L[ℂ] V n) : (c • M).det = c ^ n * M.det := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_smul, LinearMap.det_smul,
    finrank_euclideanSpace_fin]

theorem jacM_det_diffAt {n : ℕ} {f0 : V n → ℂ} {f : Fin n → V n → ℂ} {U : Set (V n)}
    (hU : IsOpen U) (h0 : DifferentiableOn ℂ f0 U) (h : ∀ k, DifferentiableOn ℂ (f k) U)
    {v : V n} (hv : v ∈ U) : DifferentiableAt ℂ (fun w => (jacM f0 f w).det) v := by
  have c0 : ContDiffOn ℂ ∞ f0 U := ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ hU h0
  have ck : ∀ k, ContDiffOn ℂ ∞ (f k) U := fun k =>
    ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ hU (h k)
  have d0 : ContDiffOn ℂ ∞ (fderiv ℂ f0) U := c0.fderiv_of_isOpen hU (by simp)
  have dk : ∀ k, ContDiffOn ℂ ∞ (fderiv ℂ (f k)) U := fun k =>
    (ck k).fderiv_of_isOpen hU (by simp)
  have hn := hU.mem_nhds hv
  have hc : ContDiffAt ℂ ∞ (fun w => (jacM f0 f w).det) v := by
    simp_rw [flL_det_eq, jacM_apply]
    refine ContDiffAt.sum fun σ _ => contDiffAt_const.mul (contDiffAt_prod fun c _ => ?_)
    exact ((c0.contDiffAt hn).mul (((dk _).contDiffAt hn).clm_apply contDiffAt_const)).sub
      (((ck _).contDiffAt hn).mul ((d0.contDiffAt hn).clm_apply contDiffAt_const))
  exact hc.differentiableAt (by simp)

theorem zLoc_fderiv {n : ℕ} (f0 : V n → ℂ) (f : Fin n → V n → ℂ) (v : V n)
    (h0 : DifferentiableAt ℂ f0 v) (h : ∀ k, DifferentiableAt ℂ (f k) v) (hne : f0 v ≠ 0) :
    fderiv ℂ (fun w => (WithLp.toLp 2 (fun k => f k w / f0 w) : V n)) v =
      ((f0 v ^ 2)⁻¹) • jacM f0 f v := by
  have hinv : HasFDerivAt (fun w => (f0 w)⁻¹) (-((f0 v) ^ 2)⁻¹ • fderiv ℂ f0 v) v :=
    (hasDerivAt_inv hne).comp_hasFDerivAt v h0.hasFDerivAt
  have hk : ∀ k, HasFDerivAt (fun w => f k w / f0 w)
      (f k v • (-((f0 v) ^ 2)⁻¹ • fderiv ℂ f0 v) + (f0 v)⁻¹ • fderiv ℂ (f k) v) v := by
    intro k
    exact ((h k).hasFDerivAt.mul hinv).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun w => by simp [div_eq_mul_inv])
  have hpi := hasFDerivAt_pi.2 hk
  have hE := ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm :
    (Fin n → ℂ) →L[ℂ] V n).hasFDerivAt.comp v hpi
  rw [show (fun w => (WithLp.toLp 2 (fun k => f k w / f0 w) : V n)) =
    (((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm : (Fin n → ℂ) →L[ℂ] V n) ∘
      fun w k => f k w / f0 w) from rfl, hE.fderiv]
  ext ξ k
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, PiLp.smul_apply,
    jacM_apply, smul_eq_mul]
  simp
  field_simp
  ring

theorem jac_section : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (B : La) (t0 : ι → Y → ℂ) (t : Fin n → ι → Y → ℂ), A.IsSec B t0 → (∀ j, A.IsSec B (t j)) → ∃ J : ι → Y → ℂ, A.IsSec (A.kap + (2 * n) • B) J ∧ ∀ i y, y ∈ (A.chart i).source → t0 i y ≠ 0 → J i y = t0 i y ^ (2 * n) * (fderiv ℂ (A.zLoc t0 t i) (A.chart i y)).det := by
  intro n Y _ _ _ _ _ ι La _ A B t0 t h0 ht
  have hd0 : ∀ i, DifferentiableOn ℂ (t0 i ∘ (A.chart i).symm) (A.chart i).target := fun i => by
    simpa using h0.1 i
  have hdk : ∀ i k, DifferentiableOn ℂ (t k i ∘ (A.chart i).symm) (A.chart i).target :=
    fun i k => by simpa using (ht k).1 i
  refine ⟨fun i y => (jacM (t0 i ∘ (A.chart i).symm) (fun k => t k i ∘ (A.chart i).symm)
    (A.chart i y)).det, ⟨fun i => ?_, ?_⟩, ?_⟩
  · intro v hv
    have hvt : v ∈ (A.chart i).target := hv.1
    exact (jacM_det_diffAt (A.chart i).open_target (hd0 i) (hdk i) hvt).differentiableWithinAt.congr
      (fun w hw => by simp [(A.chart i).right_inv hw.1]) (by simp [(A.chart i).right_inv hvt])
  · intro i j y _ hi hj
    have hov : IsOpen (ovl A.chart i j) :=
      (A.chart i).isOpen_inter_preimage_symm (A.chart j).open_source
    have hmov : A.chart i y ∈ ovl A.chart i j :=
      ⟨(A.chart i).map_source hi, by simp [(A.chart i).left_inv hi, hj]⟩
    have hΦv : (A.chart j ∘ (A.chart i).symm) (A.chart i y) = A.chart j y := by
      simp [(A.chart i).left_inv hi]
    have hEv : ∀ s : ι → Y → ℂ, A.IsSec B s → s i ∘ (A.chart i).symm =ᶠ[𝓝 (A.chart i y)]
        fun w => (A.g B i j ∘ (A.chart i).symm) w *
          (s j ∘ (A.chart j).symm) ((A.chart j ∘ (A.chart i).symm) w) := by
      intro s hs
      filter_upwards [hov.mem_nhds hmov] with w hw
      have hsi : (A.chart i).symm w ∈ (A.chart i).source := (A.chart i).map_target hw.1
      simp only [Function.comp_apply]
      rw [(A.chart j).left_inv hw.2]
      exact hs.2 i j _ trivial hsi hw.2
    have hG : DifferentiableAt ℂ (A.g B i j ∘ (A.chart i).symm) (A.chart i y) :=
      (A.holo_g B i j).differentiableAt (hov.mem_nhds hmov)
    have hΦ : DifferentiableAt ℂ (A.chart j ∘ (A.chart i).symm) (A.chart i y) :=
      (A.holo_trans i j).differentiableAt (hov.mem_nhds hmov)
    have hjt : (A.chart j).target ∈ 𝓝 ((A.chart j ∘ (A.chart i).symm) (A.chart i y)) := by
      rw [hΦv]; exact (A.chart j).open_target.mem_nhds ((A.chart j).map_source hj)
    have key := jacM_trans (A.g B i j ∘ (A.chart i).symm) (A.chart j ∘ (A.chart i).symm)
      (t0 j ∘ (A.chart j).symm) (fun k => t k j ∘ (A.chart j).symm) (A.chart i y) hG hΦ
      ((hd0 j).differentiableAt hjt) (fun k => (hdk j k).differentiableAt hjt)
    rw [hΦv] at key
    have hcong := jacM_congr (hEv t0 h0) (fun k => hEv (t k) (ht k))
    have hdc : ((jacM (t0 j ∘ (A.chart j).symm) (fun k => t k j ∘ (A.chart j).symm)
        (A.chart j y)).comp (fderiv ℂ (A.chart j ∘ (A.chart i).symm) (A.chart i y))).det =
        (jacM (t0 j ∘ (A.chart j).symm) (fun k => t k j ∘ (A.chart j).symm) (A.chart j y)).det *
        (fderiv ℂ (A.chart j ∘ (A.chart i).symm) (A.chart i y)).det := LinearMap.det_comp _ _
    simp only
    rw [hcong, key, det_smul_V, hdc, A.g_add _ _ i j y hi hj, bsA_g_nsmul A B _ hi hj,
      A.g_kap i j y hi hj]
    simp only [Function.comp_apply, (A.chart i).left_inv hi]
    rw [← pow_mul]
    ring
  · intro i y hi hne
    have hyt : A.chart i y ∈ (A.chart i).target := (A.chart i).map_source hi
    have hn := (A.chart i).open_target.mem_nhds hyt
    have hne' : (t0 i ∘ (A.chart i).symm) (A.chart i y) ≠ 0 := by
      simpa [(A.chart i).left_inv hi] using hne
    have hz := zLoc_fderiv (t0 i ∘ (A.chart i).symm) (fun k => t k i ∘ (A.chart i).symm)
      (A.chart i y) ((hd0 i).differentiableAt hn) (fun k => (hdk i k).differentiableAt hn) hne'
    have hzl : A.zLoc t0 t i = fun w => (WithLp.toLp 2 (fun k =>
        (t k i ∘ (A.chart i).symm) w / (t0 i ∘ (A.chart i).symm) w) : V n) := rfl
    simp only
    rw [hzl, hz, det_smul_V]
    simp only [Function.comp_apply, (A.chart i).left_inv hi] at hne' ⊢
    rw [← mul_assoc, ← inv_pow, pow_mul, ← mul_pow]
    rw [show t0 i y ^ 2 * (t0 i y)⁻¹ ^ 2 = 1 by field_simp, one_pow, one_mul]

end

end GlobalTheory.JacSec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianShFactor
section
open GlobalTheory.EtC IsLocalRing

namespace GlobalTheory.NoethSHFactor

theorem exists_noetherian_sh_factor : ∀ (R A : Type) [CommRing R] [IsNoetherianRing R] [CommRing A], SH A →
    ∀ b : R →+* A, ∃ (C : Type) (_ : CommRing C), IsNoetherianRing C ∧ SH C ∧
      ∃ (f : R →+* C) (g : C →+* A), g.comp f = b := by
  intro R A _ _ _ hA b
  obtain ⟨hH, hsep⟩ := hA
  let p : Ideal R := (maximalIdeal A).comap b
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  let Rp := Localization.AtPrime p
  have hunit : ∀ y : p.primeCompl, IsUnit (b y) := by
    intro y
    by_contra h
    exact y.2 ((mem_maximalIdeal _).2 h)
  let b' : Rp →+* A := IsLocalization.lift (M := p.primeCompl) hunit
  have hb' : b'.comp (algebraMap R Rp) = b := IsLocalization.lift_comp hunit
  letI : Algebra Rp A := b'.toAlgebra
  haveI hloc : IsLocalHom (algebraMap Rp A) := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl x
    rw [IsLocalization.AtPrime.isUnit_mk'_iff]
    intro hr
    have h1 : IsLocalization.mk' Rp r s * algebraMap R Rp s = algebraMap R Rp r :=
      IsLocalization.mk'_spec Rp r s
    have h2 : IsUnit (b r) := by
      rw [← hb', RingHom.comp_apply, ← h1, map_mul]
      exact hx.mul (by rw [← RingHom.comp_apply, hb']; exact hunit s)
    exact (mem_maximalIdeal _).1 hr h2
  have hfactor :=
    _root_.GlobalTheory.StrictHensFactor.exists_factor_strictHenselisation Rp Rp A
      (Algebra.ofId Rp A)
  obtain ⟨D, _, _, _, c, w, hwc, P, _, φ, hφ, _, _⟩ := hfactor
  haveI : IsNoetherianRing Rp := IsLocalization.isNoetherianRing p.primeCompl Rp inferInstance
  haveI : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  letI : Algebra (Localization.AtPrime P) D := φ.toAlgebra
  have hD : IsNoetherianRing D :=
    GlobalTheory.StalkNoeth.isNoetherianRing_of_indEt (Localization.AtPrime P) D hφ.2.2.2
  refine ⟨D, inferInstance, hD, ⟨hφ.1, hφ.2.1⟩, (c : Rp →+* D).comp (algebraMap R Rp), (w : D →+* A), ?_⟩
  rw [← RingHom.comp_assoc]
  have hwc' : (w : D →+* A).comp (c : Rp →+* D) = b' :=
    congrArg AlgHom.toRingHom hwc
  rw [hwc', hb']

end GlobalTheory.NoethSHFactor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothCutoffSlopeThreeQuarters
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem exists_isCut (T : ℝ) : ∃ θ : ℝ → ℝ, IsCut T θ := by
  obtain ⟨χ, hχ⟩ : ∃ χ : ℝ → ℝ, ReciprocityTheory.L2DbarEstimates.I.IsCutoff χ :=
    ⟨_, ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff.isCutoff_chi⟩
  obtain ⟨hs, h1, h0, hb, hd⟩ := hχ
  set a : ℝ → ℝ := fun x => (x + T + 1) / 4 + 1 / 2 with ha
  have haS : ContDiff ℝ ∞ a := by
    simp only [ha]; fun_prop
  have hda : ∀ x, HasDerivAt a (1 / 4) x := by
    intro x
    have := (((hasDerivAt_id x).add_const T).add_const 1).div_const 4
    simpa [ha] using this.add_const (1 / 2)
  refine ⟨χ ∘ a, ?_, ?_, ?_, ?_, ?_⟩
  · exact hs.comp haS
  · intro x hx
    exact h1 _ (by simp only [ha]; linarith)
  · intro x hx
    exact h0 _ (by simp only [ha]; linarith)
  · intro x
    exact hb _
  · intro x
    have hχd : DifferentiableAt ℝ χ (a x) :=
      (hs.differentiable (by simp)) _
    have hD : HasDerivAt (χ ∘ a) (deriv χ (a x) * (1 / 4)) x :=
      hχd.hasDerivAt.comp x (hda x)
    rw [hD.deriv, abs_mul]
    have := hd (a x)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    linarith

theorem exists_isCut₂ : ∀ T : ℝ, ∃ θ : ℝ → ℝ, IsCut T θ := exists_isCut

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteStrictlyHenselianTateTwistAcyclicStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_strictlyHenselian_tateTwist_acyclic : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (T : Type) [CommRing T] [Algebra A T],
  Module.Finite A T → ∀ s i : ℤ, 0 < s → Subsingleton (Ht q (sp T) s i) := by
  first | (exact @GlobalTheory.EtC.GmStep.finite_sh_acyclic_twists) | (exact GlobalTheory.EtC.GmStep.finite_sh_acyclic_twists) | (intros; apply GlobalTheory.EtC.GmStep.finite_sh_acyclic_twists  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKernelIdealMulOfIdempotentsStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_kernelIdeal_mul_of_idempotents : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (G : PDivGroup p k) (u v : G ⟶ G), u + v = 𝟙 G → u ≫ v = 0 → v ≫ u = 0 → ∀ n : ℕ, Module.finrank k (G.A n ⧸ kerIdeal (u.app n)) * Module.finrank k (G.A n ⧸ kerIdeal (v.app n)) = p ^ (n * G.height) := by
  first | exact @GlobalTheory.PDivGroup.finrank_quot_kerIdeal_mul_of_idem | exact GlobalTheory.PDivGroup.finrank_quot_kerIdeal_mul_of_idem | (intros; apply GlobalTheory.PDivGroup.finrank_quot_kerIdeal_mul_of_idem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartEvalSquarePropertiesStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalChart_evalSquare_properties : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ n f, c.ev₂ n (inL f) = c.ev n f ⊗ₜ[O] 1 ∧ c.ev₂ n (inR f) = 1 ⊗ₜ[O] c.ev n f ∧ c.ev₂ n (subst c.μ f) = Coalgebra.comul (R := O) (c.ev n f) ∧ c.ev₂ n (cob1 c.μ f) = cobOne O (G.A n) (c.ev n f) := by
  first | exact @GlobalTheory.QLog.Chart.ev₂_eval | exact GlobalTheory.QLog.Chart.ev₂_eval | (intros; apply GlobalTheory.QLog.Chart.ev₂_eval <;> assumption)
end

