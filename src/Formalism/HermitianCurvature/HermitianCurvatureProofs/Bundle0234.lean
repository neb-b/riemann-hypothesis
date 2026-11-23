module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0228
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0221
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.XiBound
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0030
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BuiltBoundsCompactOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceCompactSupportCoefficient
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0211
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0151

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtInt
section
open MeasureTheory Filter Topology
open scoped ContDiff ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.LevelPointCoordinates

section fam

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X]
  [BorelSpace X]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

def UX (X : Type) [TopologicalSpace X] : Set (X × ℂ) := Set.univ ×ˢ {τ : ℂ | τ ≠ 0}

theorem isOpen_UX : IsOpen (UX X) := isOpen_univ.prod isOpen_ne_zero_complex

def Good (Φ : X → V1 E) : Prop :=
  ContDiffOn ℝ ∞ (fun q : X × ℂ => (Φ q.1 : ℂ → E) q.2) (UX X) ∧
    ∀ K : Set ℂ, IsCompact K → K ⊆ {τ | τ ≠ 0} →
      ∃ C : Set X, IsCompact C ∧ ∀ v, v ∉ C → ∀ τ ∈ K, (Φ v : ℂ → E) τ = 0

def IsInt (μ : Measure X) (ℓ : X → E →L[ℂ] E) (Φ : X → V1 E) (f : V1 E) : Prop :=
  ∀ τ : ℂ, τ ≠ 0 → (f : ℂ → E) τ = ∫ v, ℓ v ((Φ v : ℂ → E) τ) ∂μ

theorem good_cont_at {Φ : X → V1 E} (h : Good Φ) {τ : ℂ} (hτ : τ ≠ 0) :
    Continuous (fun v => (Φ v : ℂ → E) τ) :=
  h.1.continuousOn.comp_continuous (continuous_id.prodMk continuous_const) fun _ => ⟨Set.mem_univ _, hτ⟩

theorem partial_fderiv {Φ : X → V1 E} (h : Good Φ) (v : X) {τ : ℂ} (hτ : τ ≠ 0) :
    fderiv ℝ (Φ v : ℂ → E) τ =
      (fderiv ℝ (fun q : X × ℂ => (Φ q.1 : ℂ → E) q.2) (v, τ)).comp (ContinuousLinearMap.inr ℝ X ℂ) := by
  have hd : DifferentiableAt ℝ (fun q : X × ℂ => (Φ q.1 : ℂ → E) q.2) (v, τ) :=
    (h.1.differentiableOn (by simp)).differentiableAt (isOpen_UX.mem_nhds ⟨Set.mem_univ _, hτ⟩)
  have hi : HasFDerivAt (fun t : ℂ => (v, t)) (ContinuousLinearMap.inr ℝ X ℂ) τ := hasFDerivAt_prodMk_right v τ
  exact (hd.hasFDerivAt.comp τ hi).fderiv

theorem fd_contOn {Φ : X → V1 E} (h : Good Φ) :
    ContinuousOn (fun q : X × ℂ => fderiv ℝ (Φ q.1 : ℂ → E) q.2) (UX X) := by
  have h1 : ContinuousOn (fun q : X × ℂ =>
      (fderiv ℝ (fun q : X × ℂ => (Φ q.1 : ℂ → E) q.2) q).comp (ContinuousLinearMap.inr ℝ X ℂ)) (UX X) :=
    (h.1.continuousOn_fderiv_of_isOpen isOpen_UX (by simp)).clm_comp continuousOn_const
  exact h1.congr fun q hq => partial_fderiv h q.1 hq.2

theorem cd_partial {Φ : X → V1 E} (h : Good Φ) (w : ℂ) :
    ContDiffOn ℝ ∞ (fun q : X × ℂ => fderiv ℝ (Φ q.1 : ℂ → E) q.2 w) (UX X) := by
  have h1 : ContDiffOn ℝ ∞ (fun q : X × ℂ =>
      (fderiv ℝ (fun q : X × ℂ => (Φ q.1 : ℂ → E) q.2) q) (ContinuousLinearMap.inr ℝ X ℂ w)) (UX X) :=
    (h.1.fderiv_of_isOpen isOpen_UX (by simp)).clm_apply contDiffOn_const
  refine h1.congr fun q hq => ?_
  rw [partial_fderiv h q.1 hq.2]
  rfl

theorem fderiv_zero_of {Φ : X → V1 E} (h : Good Φ) {K : Set ℂ} (hK : IsCompact K) (hK0 : K ⊆ {τ | τ ≠ 0}) :
    ∃ C : Set X, IsCompact C ∧ ∀ v, v ∉ C → ∀ τ ∈ K, fderiv ℝ (Φ v : ℂ → E) τ = 0 := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK isOpen_ne_zero_complex hK0
  obtain ⟨C, hC, hz⟩ := h.2 L hL hLU
  refine ⟨C, hC, fun v hv τ hτ => ?_⟩
  have hev : (Φ v : ℂ → E) =ᶠ[𝓝 τ] fun _ => (0 : E) :=
    Filter.eventually_of_mem (isOpen_interior.mem_nhds (hKL hτ)) fun t ht => hz v hv t (interior_subset ht)
  rw [hev.fderiv_eq]
  exact fderiv_const_apply _

section int

variable (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (ℓ : X → E →L[ℂ] E)

theorem good_int {Φ : X → V1 E} (h : Good Φ) (hℓ : Continuous ℓ) {τ : ℂ} (hτ : τ ≠ 0) :
    Integrable (fun v => ℓ v ((Φ v : ℂ → E) τ)) μ := by
  obtain ⟨C, hC, hz⟩ := h.2 {τ} isCompact_singleton (Set.singleton_subset_iff.2 hτ)
  refine Continuous.integrable_of_hasCompactSupport (hℓ.clm_apply (good_cont_at h hτ)) ?_
  refine HasCompactSupport.intro hC fun v hv => ?_
  rw [hz v hv τ rfl, map_zero]

theorem fd_int {Φ : X → V1 E} (h : Good Φ) (hℓ : Continuous ℓ) {τ : ℂ} (hτ : τ ≠ 0) (w : ℂ) :
    Integrable (fun v => ℓ v (fderiv ℝ (Φ v : ℂ → E) τ w)) μ := by
  obtain ⟨C, hC, hz⟩ := fderiv_zero_of h isCompact_singleton (Set.singleton_subset_iff.2 hτ)
  have hc : Continuous (fun v => fderiv ℝ (Φ v : ℂ → E) τ) :=
    (fd_contOn h).comp_continuous (continuous_id.prodMk continuous_const) fun _ => ⟨Set.mem_univ _, hτ⟩
  refine Continuous.integrable_of_hasCompactSupport (hℓ.clm_apply (hc.clm_apply continuous_const)) ?_
  refine HasCompactSupport.intro hC fun v hv => ?_
  rw [hz v hv τ rfl]; simp

theorem rs_cont (hℓ : Continuous ℓ) : Continuous (fun v => (ℓ v).restrictScalars ℝ) :=
  (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).continuous.comp hℓ

theorem hasFDerivAt_int {Φ : X → V1 E} (h : Good Φ) (hℓ : Continuous ℓ) {τ0 : ℂ} (hτ0 : τ0 ≠ 0) :
    HasFDerivAt (fun τ => ∫ v, ℓ v ((Φ v : ℂ → E) τ) ∂μ)
      (∫ v, ((ℓ v).restrictScalars ℝ).comp (fderiv ℝ (Φ v : ℂ → E) τ0) ∂μ) τ0 := by
  have hn : 0 < ‖τ0‖ := norm_pos_iff.2 hτ0
  set r := ‖τ0‖ / 2 with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hK : IsCompact (Metric.closedBall τ0 r) := isCompact_closedBall _ _
  have hK0 : Metric.closedBall τ0 r ⊆ {τ | τ ≠ 0} := by
    intro τ hτ
    show τ ≠ 0
    rintro rfl
    rw [Metric.mem_closedBall, dist_zero_left] at hτ
    linarith
  have hB : ∀ τ ∈ Metric.ball τ0 r, τ ≠ 0 := fun τ hτ => hK0 (Metric.ball_subset_closedBall hτ)
  obtain ⟨C, hC, hz⟩ := fderiv_zero_of h hK hK0
  obtain ⟨Mf, hMf⟩ := (hC.prod hK).exists_bound_of_continuousOn
    ((fd_contOn h).mono fun q hq => ⟨Set.mem_univ _, hK0 hq.2⟩)
  obtain ⟨Ml, hMl⟩ := hC.exists_bound_of_continuousOn hℓ.continuousOn
  have hc0 : Continuous (fun v => fderiv ℝ (Φ v : ℂ → E) τ0) :=
    (fd_contOn h).comp_continuous (continuous_id.prodMk continuous_const) fun _ => ⟨Set.mem_univ _, hτ0⟩
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (𝕜 := ℝ)
    (F := fun τ v => ℓ v ((Φ v : ℂ → E) τ))
    (F' := fun τ v => ((ℓ v).restrictScalars ℝ).comp (fderiv ℝ (Φ v : ℂ → E) τ))
    (bound := Set.indicator C fun _ => Ml * Mf) (Metric.ball_mem_nhds τ0 hr0) ?_ (good_int μ ℓ h hℓ hτ0) ?_ ?_ ?_ ?_
  · filter_upwards [Metric.ball_mem_nhds τ0 hr0] with τ hτ
    exact (hℓ.clm_apply (good_cont_at h (hB τ hτ))).aestronglyMeasurable
  · exact ((rs_cont ℓ hℓ).clm_comp hc0).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun v τ hτ => ?_
    by_cases hv : v ∈ C
    · rw [Set.indicator_of_mem hv]
      have h1 := hMl v hv
      have h2 := hMf (v, τ) ⟨hv, Metric.ball_subset_closedBall hτ⟩
      calc ‖((ℓ v).restrictScalars ℝ).comp (fderiv ℝ (Φ v : ℂ → E) τ)‖
          ≤ ‖(ℓ v).restrictScalars ℝ‖ * ‖fderiv ℝ (Φ v : ℂ → E) τ‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ = ‖ℓ v‖ * ‖fderiv ℝ (Φ v : ℂ → E) τ‖ := by rw [ContinuousLinearMap.norm_restrictScalars]
        _ ≤ Ml * Mf := mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
    · rw [Set.indicator_of_notMem hv, hz v hv τ (Metric.ball_subset_closedBall hτ),
        ContinuousLinearMap.comp_zero, norm_zero]
  · exact (continuousOn_const.integrableOn_compact hC).integrable_indicator hC.measurableSet
  · refine Filter.Eventually.of_forall fun v τ hτ => ?_
    exact ((ℓ v).restrictScalars ℝ).hasFDerivAt.comp τ (differentiableAt_of_punctured_smooth (Φ v).2 (hB τ hτ)).hasFDerivAt

theorem fderiv_int {Φ : X → V1 E} (h : Good Φ) (hℓ : Continuous ℓ) {f : V1 E} (hf : IsInt μ ℓ Φ f) {τ0 : ℂ}
    (hτ0 : τ0 ≠ 0) (w : ℂ) :
    fderiv ℝ (f : ℂ → E) τ0 w = ∫ v, ℓ v (fderiv ℝ (Φ v : ℂ → E) τ0 w) ∂μ := by
  have hev : (f : ℂ → E) =ᶠ[𝓝 τ0] fun τ => ∫ v, ℓ v ((Φ v : ℂ → E) τ) ∂μ :=
    Filter.eventually_of_mem (isOpen_ne_zero_complex.mem_nhds hτ0) fun τ hτ => hf τ hτ
  rw [hev.fderiv_eq, (hasFDerivAt_int μ ℓ h hℓ hτ0).fderiv]
  have hc0 : Continuous (fun v => fderiv ℝ (Φ v : ℂ → E) τ0) :=
    (fd_contOn h).comp_continuous (continuous_id.prodMk continuous_const) fun _ => ⟨Set.mem_univ _, hτ0⟩
  obtain ⟨C, hC, hz⟩ := fderiv_zero_of h isCompact_singleton (Set.singleton_subset_iff.2 hτ0)
  have hI : Integrable (fun v => ((ℓ v).restrictScalars ℝ).comp (fderiv ℝ (Φ v : ℂ → E) τ0)) μ := by
    refine Continuous.integrable_of_hasCompactSupport ((rs_cont ℓ hℓ).clm_comp hc0) ?_
    refine HasCompactSupport.intro hC fun v hv => ?_
    rw [hz v hv τ0 rfl, ContinuousLinearMap.comp_zero]
  rw [ContinuousLinearMap.integral_apply hI]
  rfl

theorem dz_int {Φ : X → V1 E} (h : Good Φ) (hℓ : Continuous ℓ) {f : V1 E} (hf : IsInt μ ℓ Φ f) {τ0 : ℂ}
    (hτ0 : τ0 ≠ 0) : PBP.dz (f : ℂ → E) τ0 = ∫ v, ℓ v (PBP.dz (Φ v : ℂ → E) τ0) ∂μ := by
  unfold PBP.dz
  have hI2 : Integrable (fun v => Complex.I • ℓ v (fderiv ℝ (Φ v : ℂ → E) τ0 Complex.I)) μ :=
    (fd_int μ ℓ h hℓ hτ0 Complex.I).smul Complex.I
  rw [fderiv_int μ ℓ h hℓ hf hτ0, fderiv_int μ ℓ h hℓ hf hτ0, ← integral_smul, ← integral_sub
    (fd_int μ ℓ h hℓ hτ0 1) hI2, ← integral_smul]
  congr 1
  funext v
  rw [map_smul, map_sub, map_smul]

theorem dzb_int {Φ : X → V1 E} (h : Good Φ) (hℓ : Continuous ℓ) {f : V1 E} (hf : IsInt μ ℓ Φ f) {τ0 : ℂ}
    (hτ0 : τ0 ≠ 0) : PBP.dzb (f : ℂ → E) τ0 = ∫ v, ℓ v (PBP.dzb (Φ v : ℂ → E) τ0) ∂μ := by
  unfold PBP.dzb
  have hI2 : Integrable (fun v => Complex.I • ℓ v (fderiv ℝ (Φ v : ℂ → E) τ0 Complex.I)) μ :=
    (fd_int μ ℓ h hℓ hτ0 Complex.I).smul Complex.I
  rw [fderiv_int μ ℓ h hℓ hf hτ0, fderiv_int μ ℓ h hℓ hf hτ0, ← integral_smul, ← integral_add
    (fd_int μ ℓ h hℓ hτ0 1) hI2, ← integral_smul]
  congr 1
  funext v
  rw [map_smul, map_add (f := _), map_smul]

end int

end fam

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegralNormLeDecay
section
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

theorem norm_fsv (a t : ℂ) : ‖fsv a t‖ = 1 := by
  unfold fsv
  rw [Complex.norm_exp]
  have : (a * t - conj a * conj t).re = 0 := by
    simp [Complex.mul_re, Complex.sub_re, Complex.conj_re, Complex.conj_im]
  rw [this, Real.exp_zero]

theorem continuous_fsv₂ : Continuous (fun q : ℂ × ℂ => fsv q.1 q.2) := by
  unfold fsv
  exact Complex.continuous_exp.comp ((continuous_fst.mul continuous_snd).sub
    ((Complex.continuous_conj.comp continuous_fst).mul (Complex.continuous_conj.comp continuous_snd)))

theorem integrable_fsv_mul {φ : ℂ → ℂ} (hφ : Continuous φ) (hi : Integrable φ) (a : ℂ) :
    Integrable (fun t => fsv a t * φ t) := by
  refine hi.bdd_mul (c := 1) ?_ (Filter.Eventually.of_forall fun t => (norm_fsv a t).le)
  exact (continuous_fsv₂.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable

theorem continuous_transform {φ : ℂ → ℂ} (hφ : Continuous φ) (hi : Integrable φ) :
    Continuous (fun s : ℂ => ∫ t, fsv s t * φ t) := by
  refine continuous_of_dominated (bound := fun t => ‖φ t‖) (fun s => ?_) (fun s => ?_) hi.norm ?_
  · exact ((continuous_fsv₂.comp (continuous_const.prodMk continuous_id)).mul hφ).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by rw [norm_mul, norm_fsv, one_mul]
  · exact Filter.Eventually.of_forall fun t =>
      (continuous_fsv₂.comp (continuous_id.prodMk continuous_const)).mul continuous_const

theorem integrable_decay3' : Integrable (fun s : ℂ => ((1 + ‖s‖) ^ 3)⁻¹) := by
  have hd : Integrable (fun t : ℂ => (1 + ‖t‖) ^ (-(3 : ℝ))) volume := by
    refine integrable_one_add_norm ?_
    rw [Complex.finrank_real_complex]; norm_num
  refine hd.congr (Filter.Eventually.of_forall fun t => ?_)
  have h1 : (0 : ℝ) < 1 + ‖t‖ := by positivity
  simp only []
  rw [Real.rpow_neg h1.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem integral_norm_le_decay {Ξ : ℂ → ℂ} (hΞ : Continuous Ξ) {K : ℝ} (hK : ∀ s, ‖Ξ s‖ ≤ K * ((1 + ‖s‖) ^ 3)⁻¹) :
    Integrable Ξ ∧ ∫ s, ‖Ξ s‖ ≤ K * ∫ s : ℂ, ((1 + ‖s‖) ^ 3)⁻¹ := by
  have hint : Integrable Ξ :=
    Integrable.mono' (integrable_decay3'.const_mul K) hΞ.aestronglyMeasurable (Filter.Eventually.of_forall hK)
  refine ⟨hint, ?_⟩
  rw [← integral_const_mul]
  exact integral_mono hint.norm (integrable_decay3'.const_mul K) hK

theorem fsv_sigma {c : ℂ} (hc : c ≠ 0) :
    fsv (Complex.I * (Real.pi : ℂ) / (2 * c)) c = -1 ∧
      ‖Complex.I * (Real.pi : ℂ) / (2 * c)‖ = Real.pi / (2 * ‖c‖) := by
  constructor
  · unfold fsv
    have e1 : Complex.I * (Real.pi : ℂ) / (2 * c) * c = Complex.I * (Real.pi / 2 : ℝ) := by
      push_cast; field_simp
    have e2 : conj (Complex.I * (Real.pi : ℂ) / (2 * c)) * conj c = -(Complex.I * (Real.pi / 2 : ℝ)) := by
      rw [← map_mul, e1, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
    rw [e1, e2, sub_neg_eq_add, ← two_mul, show (2 : ℂ) * (Complex.I * ((Real.pi / 2 : ℝ) : ℂ)) =
      Real.pi * Complex.I by push_cast; ring, Complex.exp_pi_mul_I]
  · rw [norm_div, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_two, one_mul]

theorem rr_eq_form {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par} (p : KB.Pl P Wp Wq)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) (h : C.LPt)
    (hh : D.IsLocPt h j) :
    p.RR F j w h h = p.form j hj w (KB.slv p.T F j hj w h hh.2) (KB.slv p.T F j hj w h hh.2) := by
  unfold KB.Pl.RR D.RRplace
  rw [dite_eq_left ⟨hh, hh⟩, dite_eq_left hj]
  rfl

theorem bdd_of_tendsto {u : ℕ → ℂ} {x : ℂ} (hu : Tendsto u atTop (𝓝 x)) : ∃ B : ℝ, 0 ≤ B ∧ ∀ n, ‖u n‖ ≤ B := by
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto u hu)
  exact ⟨max B 0, le_max_right _ _, fun n => (hB _ ⟨n, rfl⟩).trans (le_max_left _ _)⟩

end Formalism.FourierDecayAlt.P.PBO
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PositivityBoundOfActual
section
namespace Formalism.FourierDecayAlt.P.PBASM

open Formalism.FourierDecayAlt NumberField Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem psd_of_rep {α ι H : Type} [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Y : Finset α)
    (U : ι → α → H) (K : α → α → ℂ) (hK : ∀ x y, K x y = ∑ k, inner ℂ (U k y) (U k x)) : TB.PSDOn Y K := by
  unfold TB.PSDOn
  have key : (Matrix.of fun x y : Y => K x y) = ∑ k, (Matrix.gram ℂ (fun x : Y => U k x)).transpose := by
    ext x y
    simp only [Matrix.of_apply, Matrix.sum_apply, Matrix.transpose_apply, Matrix.gram_apply, hK]
  rw [key]
  exact Matrix.posSemidef_sum _ fun k _ => (Matrix.posSemidef_gram ℂ _).transpose

theorem psd_smul {α : Type} (Y : Finset α) (k : α → α → ℂ) (a : ℝ) (ha : 0 ≤ a) (hk : TB.PSDOn Y k) :
    TB.PSDOn Y (fun x y => (a : ℂ) * k x y) := by
  rw [PBA.psd_iff_qf] at hk ⊢
  refine ⟨fun x hx y hy => ?_, fun c => ?_⟩
  · rw [hk.1 x hx y hy, map_mul, Complex.conj_ofReal]
  · have : PBA.qf Y (fun x y => (a : ℂ) * k x y) c = (a : ℂ) * PBA.qf Y k c := by
      unfold PBA.qf
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      ring
    rw [this, Complex.re_ofReal_mul]
    exact mul_nonneg ha (hk.2 c)

section top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

theorem rr_top_rep (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) :
    ∃ (ι : Type) (_ : Fintype ι) (U : ι → C.LPt → PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)),
      ∀ x y, p.RR F (P.r + 1) w x y = ∑ k, inner ℂ (U k y) (U k x) := by
  by_cases hw : w = []
  · refine ⟨Unit, inferInstance, fun _ x => if D.IsLocPt x (P.r + 1) then
      B.hsVec (D.vecV p.T.base p.ν' p.m₀ F x) else 0, fun x y => ?_⟩
    simp only [Fintype.univ_unit, Finset.sum_singleton]
    unfold KB.Pl.RR D.RRplace
    by_cases hx : D.IsLocPt x (P.r + 1)
    · by_cases hy : D.IsLocPt y (P.r + 1)
      · rw [dite_eq_left ⟨hx, hy⟩, dite_eq_right (by omega), if_pos rfl, if_pos hw]
        simp only [hx, hy, if_true, B.hsInner]
      · rw [dite_eq_right (fun h => hy h.2)]
        simp [hy]
    · rw [dite_eq_right (fun h => hx h.1)]
      simp [hx]
  · refine ⟨Wd.Ix (Fin w.length) × M.Ty P, inferInstance, fun k x => if D.IsLocPt x (P.r + 1) then
      ((Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w x k.1 k.2 : ℝ) : ℂ) •
        B.hsVec ((p.TP.E k.2).comp (D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w k.1 F) x)) else 0, fun x y => ?_⟩
    rw [Fintype.sum_prod_type]
    unfold KB.Pl.RR D.RRplace
    by_cases hx : D.IsLocPt x (P.r + 1)
    · by_cases hy : D.IsLocPt y (P.r + 1)
      · rw [dite_eq_left ⟨hx, hy⟩, dite_eq_right (by omega), if_pos rfl, if_neg hw]
        unfold Top.topOf
        refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun ρ _ => ?_
        simp only [hx, hy, if_true, B.hsInner, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
        push_cast
        ring
      · rw [dite_eq_right (fun h => hy h.2)]
        simp [hy]
    · rw [dite_eq_right (fun h => hx h.1)]
      simp [hx]

end top

section pos

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem gN_psdC (hA : P5.ThmPActualCpt) (hFP : ModuleFormPositivity.FormPosCpt) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))
    (hF : ∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) (v : Fin S.f) (ε : ℝ) (hε : 0 < ε) (j : ℕ)
    (hj : j ≤ S.G.r) (w : List C.Letter) (hw : KB.CutWord (D.parOf S v) (S.l + 1) w) (Y : Finset C.LPt) :
    TB.PSDOn Y (KB.gN (PBL.setC S p F) v ε j w) := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hv⟩ := hB'
  obtain ⟨hl0, -, -, -, -⟩ := hv v
  have hw' : KB.CutWord (D.parOf S v) (p v).l0 w := by rw [hl0]; exact hw
  have hgpos := PBL.g_pos_of_built hB
  have hu : ∀ h, PBL.CV ((p v).T.bs j) (PBL.uY S p F v ε j hj w Y h) := by
    intro h
    unfold PBL.uY
    split_ifs
    · unfold PBL.uB
      split_ifs with hh
      · exact PBL.cv_smul _ fun e => Formalism.FourierDecayAlt.P.slice_compact_support_coefficient _ _ (D.parOf S v) (p v) (F v ε) j hj w _
          ((PBD.isLocPt_toStd_iff _ _ hgpos h 1 j).2 hh) (hF v ε hε) e
      · exact PBL.cv_zero
    · exact PBL.cv_zero
  set c0 : ℝ := 1 / (PBL.ΓS S j * S.sizeAt v w) with hc0
  have hc0n : 0 ≤ c0 := by
    have := PBL.gam_pos hB j
    have := PBL.sizeAt_nonneg S v w
    positivity
  have hG := PBL.gram_psd (PBL.CV (S := Fin w.length) ((p v).T.bs j))
    (fun x y => (c0 : ℂ) * (p v).form j hj w x y) PBL.cv_zero (fun x y hx hy => PBL.cv_add hx hy)
    (fun c x hx => PBL.cv_smul c hx)
    (fun x₁ x₂ y c h₁ h₂ hy => by simp only [PBL.form_slC (p v) j hj w x₁ x₂ y c h₁ h₂ hy]; ring)
    (fun x y₁ y₂ c hx h₁ h₂ => by simp only [PBL.form_srC (p v) j hj w x y₁ y₂ c hx h₁ h₂]; ring)
    (fun x hx => mul_nonneg (by exact_mod_cast hc0n) (hFP hA _ _ (D.parOf S v) (p v) j hj w hw' x hx))
    Y (PBL.uY S p F v ε j hj w Y) hu
  refine PBL.psd_congr (fun x hx y hy => ?_) hG
  show (c0 : ℂ) * (p v).form j hj w (PBL.uY S p F v ε j hj w Y x) (PBL.uY S p F v ε j hj w Y y) = _
  rw [PBL.uY_mem S p F v ε j hj w Y x hx, PBL.uY_mem S p F v ε j hj w Y y hy, PBL.gN_uB hB F hF v ε hε j hj w x y]

theorem gramLoc_top_psd (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀)
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ)
    (w : List C.Letter) (Y : Finset C.LPt) :
    TB.PSDOn Y ((PBL.setC S p F).gramLoc v ε (S.G.r + 1) w) := by
  obtain ⟨ι, _, U, hU⟩ := rr_top_rep (p v) (F v ε) w
  set a : C.LPt → ℝ := fun x => √(PBL.nnS S x) / PBL.bS S x * √(1 / PBL.ΓS S (S.G.r + 1)) with ha
  have hΓ := PBL.gam_pos hB (S.G.r + 1)
  refine psd_of_rep Y (fun k x => ((a x : ℝ) : ℂ) • U k (PBL.stdS S x)) _ fun x y => ?_
  rw [PBL.gramLoc_setC hB, hU]
  simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hs : √(1 / PBL.ΓS S (S.G.r + 1)) * √(1 / PBL.ΓS S (S.G.r + 1)) = 1 / PBL.ΓS S (S.G.r + 1) :=
    Real.mul_self_sqrt (by positivity)
  have e1 : ((√(PBL.nnS S x) * √(PBL.nnS S y) : ℝ) : ℂ) *
      ((1 / (PBL.bS S x * PBL.bS S y * PBL.ΓS S (S.G.r + 1)) : ℝ) : ℂ) = ((a y : ℝ) : ℂ) * ((a x : ℝ) : ℂ) := by
    rw [ha]
    push_cast
    rw [show ((√(1 / PBL.ΓS S (S.G.r + 1)) : ℝ) : ℂ) = ((√(1 / PBL.ΓS S (S.G.r + 1)) : ℝ) : ℂ) from rfl]
    have hs' : ((√(1 / PBL.ΓS S (S.G.r + 1)) : ℝ) : ℂ) * ((√(1 / PBL.ΓS S (S.G.r + 1)) : ℝ) : ℂ) =
        1 / (PBL.ΓS S (S.G.r + 1) : ℂ) := by exact_mod_cast hs
    calc _ = (√(PBL.nnS S x) : ℂ) * (√(PBL.nnS S y) : ℂ) * ((PBL.bS S x : ℂ)⁻¹ * (PBL.bS S y : ℂ)⁻¹) *
          (1 / (PBL.ΓS S (S.G.r + 1) : ℂ)) := by rw [one_div, one_div, mul_inv, mul_inv]; ring
      _ = _ := by rw [← hs']; ring
  rw [← mul_assoc, e1]
  ring

end pos

theorem posB_of (hA : P5.ThmPActualCpt) (hFP : ModuleFormPositivity.FormPosCpt) : PosB := by
  intro Cb
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB F hF v ε hε i hi w Y
  change i ≤ S.G.r + 1 at hi
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGo, -⟩ := hB'
  rcases Nat.lt_or_ge i (S.G.r + 1) with hlt | hge
  · have hj : i ≤ S.G.r := by omega
    have hCI := PBCut.cutInside_of_built hB
    have hw := PBD.cutWord_of_adm S hGo hCI w v
    have hpsd := gN_psdC hA hFP hB F hF v ε hε i hj (w.1 v) hw Y
    have hsa := PBL.sizeAt_pos S hGo v (w.1 v) ⟨w, rfl⟩
    refine PBL.psd_congr (fun x _ y _ => ?_) (psd_smul Y _ _ hsa.le hpsd)
    show (S.sizeAt v (w.1 v) : ℂ) * KB.gN (PBL.setC S p F) v ε i (w.1 v) x y = _
    unfold KB.gN
    have : ((PBL.setC S p F).sizeAt v (w.1 v) : ℂ) = (S.sizeAt v (w.1 v) : ℂ) := rfl
    rw [this]
    have hne : (S.sizeAt v (w.1 v) : ℂ) ≠ 0 := by exact_mod_cast hsa.ne'
    field_simp
  · have hi' : i = S.G.r + 1 := by omega
    subst hi'
    exact gramLoc_top_psd hB F v ε (w.1 v) Y

end

end Formalism.FourierDecayAlt.P.PBASM

namespace Formalism.FourierDecayAlt.P

theorem positivity_bound : P5.ThmPActualCpt → PBASM.PosB := fun hA => PBASM.posB_of hA module_form_pos_compact_support

end Formalism.FourierDecayAlt.P
end

