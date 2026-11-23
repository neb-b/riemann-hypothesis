module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplificationAbsoluteSidePieceBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivity
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoFlagsGramNumberMulTopMinorNormLeTwoPow
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0356
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0012
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0005
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0323
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CellConv
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UniformBesselConstant
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0037
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.BFCell
public import Formalism.FormalDegreeBessel.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeAbsolutelyConvergentOperatorNormLe
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.AbsConv

variable {k r : ℕ}

theorem dmin_inv (z z' : Fin (2 * r + k + 1) → ℂ) {γ : Mat k r} (hγ : γ ∈ GG k r) (l : Fin (r + 2)) :
    Dmin k r z' z γ⁻¹ l = star (Dmin k r z z' γ l) := by
  unfold Dmin
  rw [(GlobalTheory.T.besselZhat_inv_and_regular_iff k r z z' γ hγ).1, ← Matrix.det_conjTranspose, Matrix.conjTranspose_submatrix]

theorem dr_inv (z z' : Fin (2 * r + k + 1) → ℂ) {γ : Mat k r} (hγ : γ ∈ GG k r) :
    Dr k r z' z γ⁻¹ = Dr k r z z' γ := by
  unfold Dr
  rw [dmin_inv z z' hγ, norm_star]

theorem twoFl_inv {z z' : Fin (2 * r + k + 1) → ℂ} {γ : Mat k r} (h : TwoFl k r z z' γ) : TwoFl k r z' z γ⁻¹ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h2, h1, h4, h3, isClosedSub_GG.2.2.2.2 _ h5, ?_, by rwa [dr_inv z z' h5]⟩
  unfold Gf at h6 ⊢
  rw [dmin_inv z z' h5, dmin_inv z z' h5, mul_comm (Tz k r z')]
  simpa only [Complex.star_def, Complex.normSq_conj] using h6

theorem deOK_inv {z z' : Fin (2 * r + k + 1) → ℂ} {γ : Mat k r} {De : ℝ} (hγ : γ ∈ GG k r)
    (h : DeOK k r z z' γ De) : DeOK k r z' z γ⁻¹ De := by
  refine ⟨h.1, fun l hl h0 => ?_⟩
  rw [dmin_inv z z' hγ] at h0 ⊢
  rw [norm_star]
  exact h.2 l hl fun h' => h0 (by rw [h', star_zero])

theorem continuous_lmul (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) :=
  continuous_const.matrix_mul (continuous_id (X := Mat k r))

theorem continuous_conj (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) :=
  (continuous_const.matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const

theorem lmul_inv_lmul {γ : Mat k r} (hγ : γ ∈ GG k r) (x : Mt k r) : lmulM γ⁻¹ (lmulM γ x) = x :=
  Matrix.nonsing_inv_mul_cancel_left γ (Matrix.of x) (isUnit_det_of_mem_GG hγ)

def lmulEquiv {γ : Mat k r} (hγ : γ ∈ GG k r) : Mt k r ≃ᵐ Mt k r where
  toFun := lmulM γ
  invFun := lmulM γ⁻¹
  left_inv := lmul_inv_lmul hγ
  right_inv x := Matrix.mul_nonsing_inv_cancel_left γ (Matrix.of x) (isUnit_det_of_mem_GG hγ)
  measurable_toFun := (continuous_lmul γ).measurable
  measurable_invFun := (continuous_lmul γ⁻¹).measurable

theorem quot_map {γ : Mat k r} (hγ : γ ∈ GG k r) {μG μR ν : Measure (Mt k r)} (hG : IsHaarOn (GG k r) μG)
    (h : IsQuotMeas μG μR ν) : IsQuotMeas μG (μR.map (conjM γ)) (ν.map (lmulEquiv hγ)) := by
  intro f hf
  rw [lintegral_map_equiv]
  have h1 := h (fun x => f (lmulM γ x)) (hf.comp (continuous_lmul γ).measurable)
  rw [← lintegral_map hf (continuous_lmul γ).measurable, hG.2.2.2 γ hγ] at h1
  rw [h1]
  refine lintegral_congr fun x => ?_
  have hm : Measurable fun s : Mt k r => f (rmulM (Matrix.of (lmulEquiv hγ x)) s) :=
    hf.comp (continuous_rmulM _).measurable
  refine Eq.trans ?_ (lintegral_map hm (continuous_conj γ).measurable).symm
  refine lintegral_congr fun s => ?_
  congr 1
  show γ * (Matrix.of s * Matrix.of x) = γ * Matrix.of s * γ⁻¹ * (γ * Matrix.of x)
  rw [Matrix.mul_assoc _ γ⁻¹, Matrix.nonsing_inv_mul_cancel_left γ (Matrix.of x) (isUnit_det_of_mem_GG hγ),
    Matrix.mul_assoc]

def Gs (k r : ℕ) : Set (Mt k r) := {x | Matrix.of x ∈ GG k r}

def ext0 (f : Mat k r → ℝ) : Mt k r → ℝ := Set.indicator (Gs k r) fun x => f (Matrix.of x)

theorem cochainExtendByZeroSubgroup_of_mem (f : Mat k r → ℝ) {x : Mt k r} (hx : Matrix.of x ∈ GG k r) : ext0 f x = f (Matrix.of x) :=
  Set.indicator_of_mem (s := Gs k r) hx _

theorem amplifierAbsConvExtendByZero_of_not_mem (f : Mat k r → ℝ) {x : Mt k r} (hx : Matrix.of x ∉ GG k r) : ext0 f x = 0 :=
  Set.indicator_of_notMem (s := Gs k r) hx _

theorem measurable_amplifierAbsConvExtendByZero {f : Mat k r → ℝ} (hf : ContinuousOn f (GG k r)) : Measurable (ext0 f) := by
  classical
  have hc : IsClosed (Gs k r) := isClosedSub_GG.2.1
  have h1 : ContinuousOn (fun x : Mt k r => f (Matrix.of x)) (Gs k r) := hf
  have := ContinuousOn.measurable_piecewise (g := fun _ => (0 : ℝ)) h1 continuousOn_const hc.measurableSet
  convert this using 1
  exact (Set.piecewise_eq_indicator).symm

def Kc (k r : ℕ) (De : ℝ) : ℝ :=
  (4 * r : ℝ) ^ (11 * r ^ 2) * De ^ (12 * r ^ 2) * (Real.pi * Real.exp 1 / ((k - 2 - r : ℕ) : ℝ)) ^ (r * (k - 2 - r)) *
    4 ^ (k - 2 - r) * ((r + 1) * 4 ^ (24 * r ^ 3 + 1))

theorem side {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {z z' : Fin (2 * r + k + 1) → ℂ} {π' : Mat k r → (Wq →L[ℂ] Wq)} {ψ' : Mat k r → ℂ}
    {μG μW' νS' μR νR : Measure (Mt k r)} {Φ' : Mat k r → Wq} {γ : Mat k r} {c κ s H₁ De : ℝ}
    (hr : 1 ≤ r) (hk : 2 * r + 6 ≤ k) (hκ : 0 < κ) (hs : 0 < s) (hH : 1 ≤ H₁)
    (h1 : OneSide z' π' ψ' μG μW' (ENNReal.ofReal κ • lebN k r) νS' Φ' c) (h2 : MomBd z' νS' Φ' (24 * r ^ 3 + 1) H₁)
    (h3 : TwoFl k r z z' γ) (h4 : DeOK k r z z' γ De) (h5 : NormR k r γ s μR) (h6 : IsQuotMeas μG μR νR)
    (w : Wq) (hw : ‖w‖ = 1) (i i' : ℕ) (y : ℝ) (hy : 0 < y) :
    ∫⁻ x in {x | ext0 (Sg k r z') x ≤ 2 ^ i' * H₁ ∧ (i' = 0 ∨ 2 ^ i' * H₁ / 2 < ext0 (Sg k r z') x) ∧
        ext0 (Sg k r z) (lmulM γ x) ≤ 2 ^ i * H₁ ∧ y < ext0 (Yv k r z z' γ) x ∧ ext0 (Yv k r z z' γ) x ≤ 2 * y},
      ENNReal.ofReal (ext0 (fun g => ‖⟪w, Φ' g⟫_ℂ‖) x ^ 2) ∂νR ≤
    ENNReal.ofReal (κ / s * Kc k r De * c * (2 ^ (i + i') * H₁) ^ (20 * r ^ 3) * y ^ (2 * (k - 2 - r)) *
      (((2 : ℝ) ^ i') ^ (2 * (24 * r ^ 3 + 1)))⁻¹) := by
  have p1 : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ one_le_two
  have p2 : (1 : ℝ) ≤ 2 ^ i' := one_le_pow₀ one_le_two
  have q1 : (2 : ℝ) ^ i * H₁ ≤ 2 ^ (i + i') * H₁ := by
    rw [pow_add]; gcongr; exact le_mul_of_one_le_right (by positivity) p2
  have q2 : (2 : ℝ) ^ i' * H₁ ≤ 2 ^ (i + i') * H₁ := by
    rw [pow_add]; gcongr; exact le_mul_of_one_le_left (by positivity) p1
  have hR : (1 : ℝ) ≤ 2 ^ (i + i') * H₁ := one_le_mul_of_one_le_of_one_le (one_le_pow₀ one_le_two) hH
  have key := (_root_.GlobalTheory.Amp.AbsSide.abs_side k r z z' π' ψ' μG μW' νS' μR νR Φ' γ c κ s H₁ De _ hr hk hκ hs hH h1 h2 h3 h4 h5 h6).2
    w hw i' _ y hR hy
  refine le_trans (lintegral_mono' (Measure.restrict_mono ?_ le_rfl) fun x => ?_) (key.trans (le_of_eq ?_))
  · rintro x ⟨a1, a2, a3, a4, a5⟩
    have hx : Matrix.of x ∈ GG k r := by
      by_contra hx
      rw [amplifierAbsConvExtendByZero_of_not_mem _ hx] at a4
      exact lt_asymm hy a4
    have hx' : Matrix.of (lmulM γ x) ∈ GG k r := isClosedSub_GG.2.2.2.1 _ h3.2.2.2.2.1 _ hx
    rw [cochainExtendByZeroSubgroup_of_mem _ hx] at a1 a2 a4 a5
    rw [cochainExtendByZeroSubgroup_of_mem _ hx'] at a3
    exact ⟨⟨hx, a1.trans q2, a3.trans q1, a4, a5⟩, a2⟩
  · by_cases hx : Matrix.of x ∈ GG k r
    · simp only [cochainExtendByZeroSubgroup_of_mem _ hx, le_refl]
    · simp [amplifierAbsConvExtendByZero_of_not_mem _ hx]
  · congr 1
    unfold fibVol Kc
    rw [mul_pow 2 y, pow_mul (2 : ℝ) 2]
    norm_num only
    ring

theorem max_bounds {r : ℕ} {S S' D De Y T : ℝ} (hr : 1 ≤ r) (hS : 1 ≤ S) (hDe : 1 ≤ De)
    (hD : D⁻¹ ≤ De) (hT : 0 ≤ T) (hT' : T ≤ max S S') (hY : Y ≤ T ^ r / D) :
    Y ≤ (r * max S S' ^ (2 * r - 1) * De) ^ r := by
  have hM : 1 ≤ max S S' := hS.trans (le_max_left _ _)
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h1 : max S S' ≤ r * max S S' ^ (2 * r - 1) :=
    (le_self_pow₀ hM (by omega)).trans (le_mul_of_one_le_left (by positivity) hr')
  calc Y ≤ T ^ r * De := hY.trans (by rw [div_eq_mul_inv]; gcongr)
    _ ≤ (r * max S S' ^ (2 * r - 1)) ^ r * De ^ r := by
        gcongr
        · exact hT'.trans h1
        · exact le_self_pow₀ hDe (by omega)
    _ = _ := (mul_pow _ _ _).symm

theorem abs_core : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (z z' : (Fin (2 * r + k + 1) → ℂ)) (π : Mat k r → (Wp →L[ℂ] Wp)) (π' : Mat k r → (Wq →L[ℂ] Wq)) (ψ ψ' : Mat k r → ℂ) (μG μW μW' νS νS' μR νR : Measure (Mt k r)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (γ : Mat k r) (c κ s H₁ De : ℝ), 1 ≤ r → 2 * r + 6 ≤ k → 0 < κ → 0 < s → 1 ≤ H₁ → OneSide z π ψ μG μW (ENNReal.ofReal κ • lebN k r) νS Φ c → OneSide z' π' ψ' μG μW' (ENNReal.ofReal κ • lebN k r) νS' Φ' c → MomBd z νS Φ (24 * r ^ 3 + 1) H₁ → MomBd z' νS' Φ' (24 * r ^ 3 + 1) H₁ → TwoFl k r z z' γ → DeOK k r z z' γ De → NormR k r γ s μR → IsQuotMeas μG μR νR → Integrable (fun x => (innerSL ℂ (Φ' (Matrix.of x))).smulRight (Φ (γ * Matrix.of x))) νR ∧ ‖(haveI := FiniteDimensional.complete ℂ Wp; ampJ νR c Φ Φ' γ)‖ ≤ κ / s * absBd k r H₁ De (Dr k r z z' γ) := by
  intro k r Wp _ _ _ Wq _ _ _ z z' π π' ψ ψ' μG μW μW' νS νS' μR νR Φ Φ' γ c κ s H₁ De hr hk hκ hs hH o1 o2 m1 m2
    tf de nr qm
  have hγ : γ ∈ GG k r := tf.2.2.2.2.1
  have hG : IsHaarOn (GG k r) μG := o1.2.2.2.2.2.1
  have hc : 0 < c := o1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have cΦ : ContinuousOn Φ (GG k r) := o1.2.2.2.2.2.2.2.2.2.2.2.2.1
  have cΦ' : ContinuousOn Φ' (GG k r) := o2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have tf' := twoFl_inv tf
  have de' := deOK_inv hγ de
  have nr' := (_root_.GlobalTheory.Amp.RootMeas.normR_facts k r γ s μR hs nr).2.2.2
  have qm' := quot_map hγ hG qm
  have hD0 : Dr k r z z' γ ≠ 0 := tf.2.2.2.2.2.2
  have hD : 0 < Dr k r z z' γ := lt_of_le_of_ne (norm_nonneg _) hD0.symm
  have hDe : (Dr k r z z' γ)⁻¹ ≤ De := de.2 ⟨r, by omega⟩ le_rfl (norm_ne_zero_iff.1 hD0)
  have hDe1 : 1 ≤ De := de.1
  have n1 := (_root_.GlobalTheory.Amp.AbsSide.abs_side k r z z' π' ψ' μG μW' νS' μR νR Φ' γ c κ s H₁ De _ hr hk hκ hs hH o2 m2 tf de nr qm).1
  have n2 := (_root_.GlobalTheory.Amp.AbsSide.abs_side k r z' z π ψ μG μW νS _ _ Φ γ⁻¹ c κ s H₁ De _ hr hk hκ hs hH o1 m1 tf' de' nr' qm').1
  rw [MeasurableEquiv.map_apply] at n2
  have a1 : ∀ᵐ x ∂νR, Matrix.of x ∈ GG k r ∧ Yv k r z z' γ (Matrix.of x) ≠ 0 := by
    filter_upwards [compl_mem_ae_iff.2 n1] with x hx
    simpa only [Set.mem_compl_iff, Set.mem_setOf_eq, not_or, not_not] using hx
  have a2 : ∀ᵐ x ∂νR, Yv k r z' z γ⁻¹ (γ * Matrix.of x) ≠ 0 := by
    filter_upwards [compl_mem_ae_iff.2 n2] with x hx
    exact fun h => hx (Or.inr h)
  have n0 : νR {x | Matrix.of x ∉ GG k r} = 0 := measure_mono_null (fun x hx => Or.inl hx) n1
  have hkk : 1 ≤ k - 2 - r := by omega
  have hK : 0 < κ / s * Kc k r De * c := by
    have : (0 : ℝ) < r := by exact_mod_cast hr
    have : (0 : ℝ) < ((k - 2 - r : ℕ) : ℝ) := by exact_mod_cast hkk
    unfold Kc
    positivity
  have me : Measurable (lmulM γ : Mt k r → Mt k r) := (continuous_lmul γ).measurable
  have main := GlobalTheory.T.integrable_and_norm_amplitude_le_of_pairings k r νR Φ Φ' γ c (κ / s * Kc k r De * c * 24 * (r : ℝ) ^ (2 * r) * H₁ ^ (24 * r ^ 3) *
    De ^ (2 * r) * (2 ^ r / Dr k r z z' γ) ^ (k - 2 - r)) hγ n0 cΦ cΦ' hc (by positivity) ?_
  · refine ⟨main.1, main.2.trans ?_⟩
    have := _root_.GlobalTheory.Amp.absArith k r H₁ De _ hr hk hH hDe1 hD
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ κ / s))
    unfold Kc
    field_simp
  intro v w hv hw
  have mA : Measurable (ext0 fun g => ‖⟪v, Φ g⟫_ℂ‖) := measurable_amplifierAbsConvExtendByZero (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const cΦ).norm
  have mB : Measurable (ext0 fun g => ‖⟪w, Φ' g⟫_ℂ‖) := measurable_amplifierAbsConvExtendByZero (ContinuousOn.inner (𝕜 := ℂ) continuousOn_const cΦ').norm
  have mS : ∀ z, Measurable (ext0 (Sg k r z)) := fun z => measurable_amplifierAbsConvExtendByZero (_root_.GlobalTheory.Amp.LenCont.lA_Sg_continuousOn k r z).2
  have mY : Measurable (ext0 (Yv k r z' z γ⁻¹)) := (_root_.GlobalTheory.Amp.YMeas.yv_measurable k r z' z γ⁻¹ tf'.2.2.2.2.1).1
  have mY' : Measurable (ext0 (Yv k r z z' γ)) := (_root_.GlobalTheory.Amp.YMeas.yv_measurable k r z z' γ hγ).1
  have dy := _root_.GlobalTheory.Dyadic.dyadic_summation (Mt k r) νR (fun x => ext0 (fun g => ‖⟪v, Φ g⟫_ℂ‖) (lmulM γ x))
    (ext0 fun g => ‖⟪w, Φ' g⟫_ℂ‖) (fun x => ext0 (Sg k r z) (lmulM γ x)) (ext0 (Sg k r z'))
    (fun x => ext0 (Yv k r z' z γ⁻¹) (lmulM γ x)) (ext0 (Yv k r z z' γ)) r (k - 2 - r) H₁ De (Dr k r z z' γ) _ _
    (mA.comp me) mB ((mS z).comp me) (mS z') (mY.comp me) mY' hr hkk hH hDe1 hD hK hK ?_ ?_
    (fun i i' y hy => side hr hk hκ hs hH o2 m2 tf de nr qm w hw i i' y hy)
  · rw [Real.sqrt_mul_self hK.le] at dy
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) dy
    filter_upwards [a1] with x hx
    have hx' : Matrix.of (lmulM γ x) ∈ GG k r := isClosedSub_GG.2.2.2.1 _ hγ _ hx.1
    rw [cochainExtendByZeroSubgroup_of_mem _ hx.1, cochainExtendByZeroSubgroup_of_mem _ hx']
    rfl
  · filter_upwards [a1, a2] with x hx hx2
    have hx' : γ * Matrix.of x ∈ GG k r := isClosedSub_GG.2.2.2.1 _ hγ _ hx.1
    have e1 : ∀ f : Mat k r → ℝ, ext0 f (lmulM γ x) = f (γ * Matrix.of x) := fun f => cochainExtendByZeroSubgroup_of_mem f hx'
    simp only [e1, cochainExtendByZeroSubgroup_of_mem _ hx.1]
    have s1 : 1 ≤ Sg k r z (γ * Matrix.of x) := ((_root_.GlobalTheory.Amp.LInv.lengths_basic k r z tf.1).2.2 _).1
    have s2 : 1 ≤ Sg k r z' (Matrix.of x) := ((_root_.GlobalTheory.Amp.LInv.lengths_basic k r z' tf.2.1).2.2 _).1
    obtain ⟨b1, b2, b3⟩ := _root_.GlobalTheory.Amp.YBound.dr_y_le k r z z' γ tf _ hx.1
    obtain ⟨-, b5, b6⟩ := _root_.GlobalTheory.Amp.YBound.dr_y_le k r z' z γ⁻¹ tf' _ hx'
    rw [Matrix.nonsing_inv_mul_cancel_left γ (Matrix.of x) (isUnit_det_of_mem_GG hγ), dr_inv z z' hγ] at b6
    refine ⟨norm_nonneg _, norm_nonneg _, s1, s2, lt_of_le_of_ne b5 hx2.symm, lt_of_le_of_ne b2 hx.2.symm, ?_, ?_,
      max_bounds hr s1 hDe1 hDe (zero_le_one.trans s2) (le_max_right _ _) b6,
      max_bounds hr s1 hDe1 hDe (zero_le_one.trans s1) (le_max_left _ _) b3⟩
    · rw [mul_comm (Yv k r z' z γ⁻¹ _)]
      exact _root_.GlobalTheory.Amp.LemA.Yv_mul_Yv_mul_Dr_le k r z z' γ tf _ hx.1
    · refine b1.trans ?_
      rw [show ∀ t : ℝ, t ^ (2 * r) = t ^ r * t ^ r from fun t => by ring]
      exact mul_le_mul (pow_le_pow_left₀ (zero_le_one.trans s2) (le_max_right _ _) _)
        (pow_le_pow_left₀ (zero_le_one.trans s1) (le_max_left _ _) _) (pow_nonneg (zero_le_one.trans s1) _)
        (pow_nonneg ((zero_le_one.trans s1).trans (le_max_left _ _)) _)
  · intro i i' y hy
    have h := side hr hk hκ hs hH o1 m1 tf' de' nr' qm' v hv i' i y hy
    rw [MeasurableEquiv.restrict_map, lintegral_map_equiv, add_comm i' i] at h
    refine le_trans (le_of_eq ?_) h
    congr 2
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rw [show lmulEquiv hγ x = lmulM γ x from rfl, lmul_inv_lmul hγ]

end GlobalTheory.Amp.AbsConv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselPeriodPositivityStatement
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_period_positivity : Hyps → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W) (h : ℝ) (l : A.H → W.Wp) (l' : A.H → W.Wq), haveI := FiniteDimensional.complete ℂ W.Wp; haveI := FiniteDimensional.complete ℂ W.Wq; 0 < θ → 0 < D.host.ka / gg D → 0 < Tr D w → 0 < Tr D w' → GoodW D τ w w' θ W → GoodS D lam A → GapAtLeast (epsSH D.R) lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z (psiS D W.z) A.σ W.π l → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z' (psiS D W.z') A.σ W.π' l' → (∀ x ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).sm, ∀ v ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).TK, Formalism.FourierDecayAlt.ThreeDimData.be W.z ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.π A.σ W.μW W.μN x v = (innerSL ℂ (l v)).smulRight (l x)) → (∀ x ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).sm, ∀ v ∈ (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).TK, Formalism.FourierDecayAlt.ThreeDimData.be W.z' ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) W.π' A.σ W.μW' W.μN x v = (innerSL ℂ (l' v)).smulRight (l' x)) → (∃ v, (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).KFin v ∧ l v ≠ 0) ∧ (∃ v, (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS).KFin v ∧ l' v ≠ 0) ∧ ∃ (w0 : A.H) (η : ℂ), PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam A.σ w0 ∧ ‖η‖ = PI.BesselPeriodGGP.fdegH W.μG A.σ w0 * Real.sqrt ((Module.finrank ℂ W.Wp : ℝ) * (Module.finrank ℂ W.Wq : ℝ)) ∧ ∀ (ν : Measure (Mt D.R.k D.R.rS)) (γ : MatKR D.R.k D.R.rS), γ ∈ UH (Hpk D.R.k D.R.rS) → ν {x | Matrix.of x ∉ UH (Hpk D.R.k D.R.rS)} = 0 → A.J ν γ = η • amp (⟨A.H, A.σ⟩ : Rep D.R.k D.R.rS) l l' w0 ν γ := by
  first | exact @GlobalTheory.AmpNormal.amp_eq_smul_normalised | exact GlobalTheory.AmpNormal.amp_eq_smul_normalised | (intros; apply GlobalTheory.AmpNormal.amp_eq_smul_normalised <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellQuotientNormalisesUnipotent
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

namespace GlobalTheory.BigConvLevi

open Formalism.FourierDecayAlt.P.TwoByOneBlock Formalism.FourierDecayAlt.P.BigCellHermitian

variable {k r : ℕ}

theorem hb_mul_self : Hb k * Hb k = 1 := by
  unfold Hb
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  split_ifs <;> norm_num

theorem isUnit_det_of_hb {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (h : μᴴ * Hb k * μ = Hb k) :
    IsUnit μ.det := by
  apply Matrix.isUnit_det_of_left_inverse (B := Hb k * μᴴ * Hb k)
  calc Hb k * μᴴ * Hb k * μ = Hb k * (μᴴ * Hb k * μ) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, hb_mul_self]

theorem conj_mem_of_levi (A B n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hAB : A * B = 1) (hA : A ∈ UH (Hpk k r)) (hB : B ∈ UH (Hpk k r))
    (hA1 : ∀ i j, ¬ mid k r j → A i j = if i = j then 1 else 0)
    (hB1 : ∀ i j, ¬ mid k r j → B i j = if i = j then 1 else 0)
    (hB3 : ∀ m j, mid k r j → ¬ mid k r m → B m j = 0)
    (hn : n ∈ Nset k r) : A * n * B ∈ Nset k r := by
  refine ⟨WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul hA hn.1) hB, ?_, ?_⟩
  · intro a i hai
    have hea : ¬ mid k r (eI k r a) := by
      have := a.isLt; simp only [mid, eI]; omega
    rw [Matrix.mul_apply, Finset.sum_eq_single (eI k r a)]
    · rw [hB1 _ _ hea, if_pos rfl, mul_one, Matrix.mul_apply, Finset.sum_eq_single (eI k r a)]
      · rw [hn.2.1 a (eI k r a) (by simp [eI]), if_pos rfl, mul_one, hA1 _ _ hea]
      · intro l _ hl
        by_cases hla : a.val ≤ l.val
        · rw [hn.2.1 a l hla, if_neg hl, mul_zero]
        · have hlm : ¬ mid k r l := by have := a.isLt; simp only [mid]; omega
          rw [hA1 i l hlm, if_neg (by rw [Fin.ext_iff]; omega), zero_mul]
      · simp
    · intro l _ hl
      rw [hB1 _ _ hea, if_neg hl, mul_zero]
    · simp
  · intro i j hj1 hj2 hi
    have hjm : mid k r j := ⟨hj1, hj2⟩
    rw [Matrix.mul_apply]
    have key : ∀ m, (A * n) i m * B m j = A i m * B m j := by
      intro m
      by_cases hm : mid k r m
      · congr 1
        rw [Matrix.mul_apply, Finset.sum_eq_single m]
        · rw [hn.2.2 m m hm.1 hm.2 hm.1, if_pos rfl, mul_one]
        · intro l _ hl
          by_cases hlr : r ≤ l.val
          · rw [hn.2.2 l m hm.1 hm.2 hlr, if_neg hl, mul_zero]
          · have hlm : ¬ mid k r l := by simp only [mid]; omega
            rw [hA1 i l hlm, if_neg (by rw [Fin.ext_iff]; omega), zero_mul]
        · simp
      · rw [hB3 m j hjm hm, mul_zero, mul_zero]
    rw [Finset.sum_congr rfl (fun m _ => key m), ← Matrix.mul_apply, hAB, Matrix.one_apply]

theorem cellQuot_props (c : Fin r → ℂ) (μ₁ μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hc : ∀ a, c a ≠ 0) (h₁ : μ₁ᴴ * Hb k * μ₁ = Hb k) (h : μᴴ * Hb k * μ = Hb k) :
    (bigCell k r c μ₁)⁻¹ * bigCell k r c μ ∈ UH (Hpk k r) ∧
    (∀ i j, ¬ mid k r j → ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ) i j = if i = j then 1 else 0) ∧
    (∀ m j, mid k r j → ¬ mid k r m → ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ) m j = 0) := by
  have hg₁ := big_cell_mem_holds k r c μ₁ hc h₁
  have hg := big_cell_mem_holds k r c μ hc h
  have u₁ := WeylGroupFacts.isUnit_of_uh hg₁
  have hμ₁ := isUnit_det_of_hb h₁
  refine ⟨WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hg₁) hg, ?_, ?_⟩
  · intro i j hj
    rw [Matrix.mul_apply, Finset.sum_congr rfl (fun l _ => by rw [bc_out_col c μ μ₁ l j hj]),
      ← Matrix.mul_apply, Matrix.nonsing_inv_mul _ u₁, Matrix.one_apply]
  · intro m j hj hm
    obtain ⟨t, rfl⟩ := mid_exists hj
    have e1 : (Pi.single (wI k r t) 1 : Fin (2 * r + k + 1) → ℂ) = jV k r (Pi.single t 1) := by
      funext i
      by_cases hi : mid k r i
      · obtain ⟨s, rfl⟩ := mid_exists hi
        rw [jV_wI]
        simp only [Pi.single_apply, wI_inj.eq_iff]
      · rw [jV_out _ hi, Pi.single_apply, if_neg (fun he : i = wI k r t => hi (he ▸ mid_wI t))]
    have col : ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ) m (wI k r t) =
        (((bigCell k r c μ₁)⁻¹ * bigCell k r c μ) *ᵥ Pi.single (wI k r t) 1) m := by
      rw [Matrix.mulVec_single_one]; rfl
    have back : ∀ v : Fin (k + 1) → ℂ,
        jV k r v = bigCell k r c μ₁ *ᵥ jV k r (μ₁⁻¹ *ᵥ v) := by
      intro v
      rw [bigCell_mulVec_jV, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hμ₁, Matrix.one_mulVec]
    rw [col, ← Matrix.mulVec_mulVec, e1, bigCell_mulVec_jV, back, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ u₁, Matrix.one_mulVec, jV_out _ hm]

theorem levi_conj_mem_iff : ∀ (k r : ℕ) (c : Fin r → ℂ) (μ₁ μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    (∀ a, c a ≠ 0) → μ₁ᴴ * Formalism.QuantumDeterminants.Hb k * μ₁ = Formalism.QuantumDeterminants.Hb k →
    μᴴ * Formalism.QuantumDeterminants.Hb k * μ = Formalism.QuantumDeterminants.Hb k →
    ∀ n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, n ∈ Formalism.QuantumDeterminants.Nset k r ↔
      (Formalism.QuantumDeterminants.bigCell k r c μ₁)⁻¹ * Formalism.QuantumDeterminants.bigCell k r c μ * n *
        ((Formalism.QuantumDeterminants.bigCell k r c μ₁)⁻¹ * Formalism.QuantumDeterminants.bigCell k r c μ)⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r := by
  intro k r c μ₁ μ hc h₁ h n
  have u₁ := WeylGroupFacts.isUnit_of_uh (big_cell_mem_holds k r c μ₁ hc h₁)
  have u := WeylGroupFacts.isUnit_of_uh (big_cell_mem_holds k r c μ hc h)
  obtain ⟨hA, hA1, hA3⟩ := cellQuot_props c μ₁ μ hc h₁ h
  obtain ⟨hB, hB1, hB3⟩ := cellQuot_props c μ μ₁ hc h h₁
  have hinv : ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ)⁻¹ = (bigCell k r c μ)⁻¹ * bigCell k r c μ₁ := by
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ u₁]
  have hAB : (bigCell k r c μ₁)⁻¹ * bigCell k r c μ * ((bigCell k r c μ)⁻¹ * bigCell k r c μ₁) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ u, Matrix.nonsing_inv_mul _ u₁]
  have hBA : (bigCell k r c μ)⁻¹ * bigCell k r c μ₁ * ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ u₁, Matrix.nonsing_inv_mul _ u]
  rw [hinv]
  constructor
  · exact conj_mem_of_levi _ _ n hAB hA hB hA1 hB1 hB3
  · intro hn'
    have := conj_mem_of_levi _ _ _ hBA hB hA hB1 hA1 hA3 hn'
    have e : (bigCell k r c μ)⁻¹ * bigCell k r c μ₁ *
        ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ * n * ((bigCell k r c μ)⁻¹ * bigCell k r c μ₁)) *
        ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ) = n := by
      calc _ = ((bigCell k r c μ)⁻¹ * bigCell k r c μ₁ * ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ)) * n *
            ((bigCell k r c μ)⁻¹ * bigCell k r c μ₁ * ((bigCell k r c μ₁)⁻¹ * bigCell k r c μ)) := by
            simp only [Matrix.mul_assoc]
        _ = n := by rw [hBA, Matrix.one_mul, Matrix.mul_one]
    rwa [e] at this

end GlobalTheory.BigConvLevi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BigCellTrivialStabiliserAndMeasures
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

namespace GlobalTheory.AmpTK

theorem bigCell_data : ∀ (k r : ℕ) (L : Formalism.MainNotions.S.LocBessel k r) (μG : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r)), 1 ≤ k → L.κN ≠ ⊤ → 0 < L.κN → L.c ≠ 0 → IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG → ∀ (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) → μᴴ * Formalism.QuantumDeterminants.Hb k * μ = Formalism.QuantumDeterminants.Hb k → Formalism.QuantumDeterminants.bigCell k r c μ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧ Formalism.MainNotions.S.IsRelStab L (Formalism.QuantumDeterminants.bigCell k r c μ) ∧ IsHaarOn (Formalism.MainNotions.S.RStab k r (Formalism.QuantumDeterminants.bigCell k r c μ)) (MeasureTheory.Measure.dirac (fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j)) ∧ Formalism.MainNotions.S.IsOrbQuot L (Formalism.QuantumDeterminants.bigCell k r c μ) (MeasureTheory.Measure.dirac (fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j)) (Formalism.MainNotions.S.pairMeas L) ∧ PI.BesselPeriodGGP.IsQuotMeas μG ((MeasureTheory.Measure.dirac (fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j)).map (fun x => fun i j => ((Formalism.QuantumDeterminants.bigCell k r c μ)⁻¹ * Matrix.of x * Formalism.QuantumDeterminants.bigCell k r c μ) i j)) μG := by
  intro k r L μG hk hκt hκ hc hG c μ hca hμ
  have hg : bigCell k r c μ ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.bigCellMem k r c μ hca hμ
  have hinv : (bigCell k r c μ)⁻¹ * bigCell k r c μ = 1 :=
    Matrix.nonsing_inv_mul _ (Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hg)
  have hR := GlobalTheory.AmpNorm.rStab_bigCell c μ hca hg
  set g := bigCell k r c μ
  have h1 : (Matrix.of fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j) = 1 := rfl
  refine ⟨hg, ?_, ⟨inferInstance, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro a ha
    rw [hR, Set.mem_singleton_iff] at ha
    rw [ha, mul_one, hinv]
    unfold psi
    rw [Model.ell_one k r L.z L.hz.1, Model.ell_one k r L.z' L.hz'.1]
  · exact IsProbabilityMeasure.ne_zero _
  · rw [Measure.dirac_apply]
    have : (fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j) ∉
        {x : Mt k r | Matrix.of x ∉ RStab k r g} := by
      intro h
      apply h
      rw [h1, hR]; rfl
    simp [Set.indicator_of_notMem this]
  · intro s hs
    rw [hR, Set.mem_singleton_iff] at hs
    subst hs
    have : (lmulM (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Mt k r → Mt k r) = id := by
      funext x; simp [lmulM]; rfl
    rw [this, Measure.map_id]
  · intro f hf
    have e : ∀ x : PairSp k r,
        (∫⁻ a, f (stabAct g (Matrix.of a) x) ∂(Measure.dirac
          (fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j))) = f x := by
      intro x
      rw [lintegral_dirac, h1]
      have : stabAct g 1 x = x := by
        unfold stabAct
        rw [mul_one, hinv]
        simp only [one_mul]
        rfl
      rw [this]
    simp_rw [e]
  · intro f hf
    rw [Measure.map_dirac, h1, mul_one, hinv]
    refine lintegral_congr fun x => ?_
    rw [lintegral_dirac, h1, one_mul]
    rfl

end GlobalTheory.AmpTK
end

