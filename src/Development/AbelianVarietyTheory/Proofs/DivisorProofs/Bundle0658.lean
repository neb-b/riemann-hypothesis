module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0643
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0648
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0628
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0549
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0548
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0640
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0649
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0508
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0642
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundarySymmCocycleMod
section
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory

namespace CobSymCoc

open GlobalTheory.Katz.CobCob

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ} {τ : Type}

theorem mvPowerSeriesMap_evalTwoGroups (φ : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    map φ (at2 c u v) = at2 (map φ c) (fun i => map φ (u i)) (fun i => map φ (v i)) := by
  unfold at2
  rw [map_subst (elim_has hu hv)]
  congr 1
  funext k
  cases k <;> rfl

theorem map_op (φ : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) :
    map φ (op μ u v i) = op (fun j => map φ (μ j)) (fun j => map φ (u j)) (fun j => map φ (v j)) i :=
  mvPowerSeriesMap_evalTwoGroups φ (μ i) hu hv

theorem map_threeGroupsFirstVariables (φ : R →+* S) : (fun j => map φ (x1 (R := R) (d := d) j)) = x1 := by
  funext j; exact map_X φ _
theorem map_threeGroupsSecondVariables (φ : R →+* S) : (fun j => map φ (x2 (R := R) (d := d) j)) = x2 := by
  funext j; exact map_X φ _
theorem map_threeGroupsThirdVariables (φ : R →+* S) : (fun j => map φ (x3 (R := R) (d := d) j)) = x3 := by
  funext j; exact map_X φ _

theorem map_assocL (φ : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (h : ∀ i, constantCoeff (μ i) = 0) :
    (fun i => map φ (op μ x1 (op μ x2 x3) i)) =
      op (fun j => map φ (μ j)) x1 (op (fun j => map φ (μ j)) x2 x3) := by
  funext i
  rw [map_op φ μ constantCoeff_threeGroupsFirstVariables (op_const h constantCoeff_threeGroupsSecondVariables constantCoeff_threeGroupsThirdVariables), map_threeGroupsFirstVariables]
  congr 1
  funext j
  rw [map_op φ μ constantCoeff_threeGroupsSecondVariables constantCoeff_threeGroupsThirdVariables, map_threeGroupsSecondVariables, map_threeGroupsThirdVariables]

theorem map_assocR (φ : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (h : ∀ i, constantCoeff (μ i) = 0) :
    (fun i => map φ (op μ (op μ x1 x2) x3 i)) =
      op (fun j => map φ (μ j)) (op (fun j => map φ (μ j)) x1 x2) x3 := by
  funext i
  rw [map_op φ μ (op_const h constantCoeff_threeGroupsFirstVariables constantCoeff_threeGroupsSecondVariables) constantCoeff_threeGroupsThirdVariables, map_threeGroupsThirdVariables]
  congr 1
  funext j
  rw [map_op φ μ constantCoeff_threeGroupsFirstVariables constantCoeff_threeGroupsSecondVariables, map_threeGroupsFirstVariables, map_threeGroupsSecondVariables]

end CobSymCoc


open CobSymCoc CobCob in
theorem cob_symCoc_mod : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (f : MvPowerSeries (Fin d) Q), DIn N f → In (RingHom.ker θ * N) (cob2 (up Q μ) (cob1 (up Q μ) f)) ∧ swap (cob1 (up Q μ) f) = cob1 (up Q μ) f := by
  intro p _ B O Q _ _ _ _ θ hF d μ hL N f hf
  have hM : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    simp only [up, constantCoeff_map, hL.const i, map_zero]
  obtain ⟨A, Bs, -⟩ := formalGroupLawCoboundaryTwo_coboundaryOne_alt Q d (up Q μ) hM f
  refine ⟨?_, ?_⟩
  · rw [A]
    have eL : op (up Q μ) x1 (op (up Q μ) x2 x3) = up Q (op μ x1 (op μ x2 x3)) :=
      (map_assocL (algebraMap B Q) μ hL.const).symm
    have eR : op (up Q μ) (op (up Q μ) x1 x2) x3 = up Q (op μ (op μ x1 x2) x3) :=
      (map_assocR (algebraMap B Q) μ hL.const).symm
    rw [eL, eR]
    refine GlobalTheory.T.subst_sub_subst_mem_mul_of_coeff_sub_mem p B O Q θ hF (RingHom.ker θ) ?_ (Fin d) (Fin d ⊕ (Fin d ⊕ Fin d)) N f _ _ hf
      (op_const hL.const constantCoeff_threeGroupsFirstVariables (op_const hL.const constantCoeff_threeGroupsSecondVariables constantCoeff_threeGroupsThirdVariables))
      (op_const hL.const (op_const hL.const constantCoeff_threeGroupsFirstVariables constantCoeff_threeGroupsSecondVariables) constantCoeff_threeGroupsThirdVariables) ?_
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := hF.pd x (RingHom.mem_ker.1 hx)
      exact ⟨y, RingHom.mem_ker.2 hy, hxy⟩
    · intro i α
      rw [RingHom.mem_ker, ← coeff_map, map_sub]
      have h1 := congrFun (map_assocL θ μ hL.const) i
      have h2 := congrFun (map_assocR θ μ hL.const) i
      rw [h1, h2, hL.law.assoc, sub_self, map_zero]
  · have hs : (fun i => swap (up Q μ i)) = up Q μ := by
      funext i
      have e : map (algebraMap B Q) (swap (μ i)) = swap (map (algebraMap B Q) (μ i)) := by
        unfold swap
        rw [mvPowerSeriesMap_evalTwoGroups (algebraMap B Q) (μ i) (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)]
        simp only [map_X]
      show swap (map (algebraMap B Q) (μ i)) = map (algebraMap B Q) (μ i)
      rw [← e, hL.comm i]
    rw [hs, sub_self] at Bs
    exact sub_eq_zero.1 Bs

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicValueDerivativeL2Ball
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

noncomputable section

theorem l2ball_sq_mul_vol_le {n : ℕ} {x : V n} {s : ℝ} (u : V n → ℂ)
    (hu : DifferentiableOn ℂ u (ball x s)) :
    ENNReal.ofReal (‖u x‖ ^ 2) * volume (ball (0 : V n) s) ≤
      ∫⁻ v in ball x s, ENNReal.ofReal (‖u v‖ ^ 2) := by
  have hu' : DifferentiableOn ℂ (fun y => u (x + y)) (ball 0 s) := by
    intro y hy
    have hxy : x + y ∈ ball x s := by simpa [mem_ball, dist_eq_norm] using hy
    exact ((hu.differentiableAt (isOpen_ball.mem_nhds hxy)).comp y
      ((differentiable_const x).add differentiable_id y)).differentiableWithinAt
  have hρm : Measurable fun t : ℝ => (Set.Iio s).indicator (fun _ => (1 : ℝ≥0∞)) t :=
    measurable_const.indicator measurableSet_Iio
  have h := ReciprocityTheory.L2DbarEstimates.mv n s _ _ hu' hρm
    (fun t ht => Set.indicator_of_notMem (by simpa using ht) _)
  have e1 : ∀ y : V n, (Set.Iio s).indicator (fun _ => (1 : ℝ≥0∞)) ‖y‖ =
      (ball (0 : V n) s).indicator 1 y := by
    intro y
    by_cases hy : ‖y‖ < s
    · rw [Set.indicator_of_mem (by simpa using hy), Set.indicator_of_mem (by simpa using hy)]; rfl
    · rw [Set.indicator_of_notMem (by simpa using hy), Set.indicator_of_notMem (by simpa using hy)]
  simp only [add_zero, e1] at h
  rw [lintegral_indicator_one measurableSet_ball] at h
  refine h.trans (le_of_eq ?_)
  rw [← lintegral_indicator measurableSet_ball,
    ← lintegral_add_left_eq_self (fun v => (ball x s).indicator (fun v => ENNReal.ofReal (‖u v‖ ^ 2)) v) x]
  refine lintegral_congr fun y => ?_
  by_cases hy : y ∈ ball (0 : V n) s
  · have hxy : x + y ∈ ball x s := by simpa [mem_ball, dist_eq_norm] using hy
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hxy]; simp
  · have hxy : x + y ∉ ball x s := by simpa [mem_ball, dist_eq_norm] using hy
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hxy]; simp

theorem norm_fderiv_le_of_ball {n : ℕ} {p : V n} {ρ R M : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (u : V n → ℂ) (hu : DifferentiableOn ℂ u (ball p R)) (hM : ∀ x ∈ ball p R, ‖u x‖ ≤ M) :
    ‖fderiv ℂ u p‖ ≤ M / ρ := by
  first
  | exact @_root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded
  | exact _root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded
  | (apply _root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded <;> assumption)
  | (intros; apply _root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FrechetDerivativeBound.norm_fderiv_le_of_bounded ..)

theorem l2_value_deriv_ball :
    ∀ (n : ℕ) (r : ℝ), 0 < r → ∃ C : ℝ, 0 ≤ C ∧ ∀ (p : V n) (u : V n → ℂ),
      DifferentiableOn ℂ u (ball p r) →
        ENNReal.ofReal (‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2) ≤
          ENNReal.ofReal C * ∫⁻ v in ball p r, ENNReal.ofReal (‖u v‖ ^ 2) := by
  intro n r hr
  set β : ℝ := (volume (ball (0 : V n) (r / 2))).toReal with hβdef
  have hβ : 0 < β := ENNReal.toReal_pos (measure_ball_pos volume _ (by linarith)).ne'
    measure_ball_lt_top.ne
  have hV : volume (ball (0 : V n) (r / 2)) = ENNReal.ofReal β :=
    (ENNReal.ofReal_toReal measure_ball_lt_top.ne).symm
  refine ⟨(1 + 16 / r ^ 2) / β, by positivity, fun p u hu => ?_⟩
  set I := ∫⁻ v in ball p r, ENNReal.ofReal (‖u v‖ ^ 2) with hIdef
  by_cases hI : I = ⊤
  · rw [hI, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']; exact le_top
  set J := I.toReal with hJ
  have hI' : I = ENNReal.ofReal J := (ENNReal.ofReal_toReal hI).symm
  have hx : ∀ x ∈ ball p (r / 2), ‖u x‖ ^ 2 ≤ J / β := by
    intro x hx
    have hsub : ball x (r / 2) ⊆ ball p r := by
      apply ball_subset_ball'
      rw [mem_ball] at hx; linarith
    have h2 := (l2ball_sq_mul_vol_le u (hu.mono hsub)).trans (lintegral_mono_set hsub)
    rw [hV, ← ENNReal.ofReal_mul (sq_nonneg _), ← hIdef, hI'] at h2
    rw [le_div_iff₀ hβ]
    exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).1 h2
  set M := Real.sqrt (J / β) with hMdef
  have hJβ : 0 ≤ J / β := div_nonneg ENNReal.toReal_nonneg hβ.le
  have hMx : ∀ x ∈ ball p (r / 2), ‖u x‖ ≤ M := by
    intro x hx'
    have := Real.sqrt_le_sqrt (hx x hx')
    rwa [Real.sqrt_sq (norm_nonneg _)] at this
  have hD := norm_fderiv_le_of_ball (ρ := r / 4) (by positivity) (by linarith) u
    (hu.mono (ball_subset_ball (by linarith))) hMx
  have hD2 : ‖fderiv ℂ u p‖ ^ 2 ≤ 16 / r ^ 2 * (J / β) := by
    have := pow_le_pow_left₀ (norm_nonneg _) hD 2
    refine this.trans (le_of_eq ?_)
    rw [div_pow, Real.sq_sqrt hJβ]; field_simp; ring
  have hp := hx p (mem_ball_self (by linarith))
  rw [hI', ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ‖u p‖ ^ 2 + ‖fderiv ℂ u p‖ ^ 2 ≤ J / β + 16 / r ^ 2 * (J / β) := add_le_add hp hD2
    _ = (1 + 16 / r ^ 2) / β * J := by ring

end

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HormanderEstimateOnBallConstLeviBound
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.HormanderBall

open ReciprocityTheory.ChartRestriction.G.AR.Up.HE

theorem measurable_wdb (n : ℕ) (j : Fin n) (g : V n → ℂ) : Measurable (wdb n j g) := by
  unfold wdb
  exact (((measurable_fderiv_apply_const ℝ g _).add
    ((measurable_fderiv_apply_const ℝ g _).const_mul _)).div_const _)

theorem norm_sum_mul_conj_sq_le {n : ℕ} (a ξ : Fin n → ℂ) :
    ‖∑ j, a j * (starRingEnd ℂ) (ξ j)‖ ^ 2 ≤ (∑ j, ‖a j‖ ^ 2) * ∑ j, ‖ξ j‖ ^ 2 := by
  have h1 : ‖∑ j, a j * (starRingEnd ℂ) (ξ j)‖ ≤ ∑ j, ‖a j‖ * ‖ξ j‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [norm_mul, Complex.norm_conj]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => ‖a j‖) (fun j => ‖ξ j‖)
  calc ‖∑ j, a j * (starRingEnd ℂ) (ξ j)‖ ^ 2 ≤ (∑ j, ‖a j‖ * ‖ξ j‖) ^ 2 := by
        gcongr
    _ ≤ _ := h2

theorem hormander_ball : ∀ (n : ℕ) (c : V n) (r t : ℝ) (φ : V n → ℝ) (F0 : V n → ℂ), 0 < t → ContDiffOn ℝ ∞ φ (ball c r) → ContDiffOn ℝ ∞ F0 (ball c r) → (∀ v ∈ ball c r, ∀ ξ : Fin n → ℂ, t * ∑ j, ‖ξ j‖ ^ 2 ≤ (leviV n (fun w => (φ w : ℂ)) v ξ).re) → ∃ F : V n → ℂ, DifferentiableOn ℂ F (ball c r) ∧ ∫⁻ v in ball c r, ENNReal.ofReal (‖F0 v - F v‖ ^ 2 * Real.exp (-φ v)) ≤ ENNReal.ofReal t⁻¹ * ∫⁻ v in ball c r, ENNReal.ofReal ((∑ j, ‖wdb n j F0 v‖ ^ 2) * Real.exp (-φ v)) := by
  intro n c r t φ F0 ht hφ hF0 hlevi
  have hU : IsOpen (ball c r) := isOpen_ball
  obtain ⟨X, hX⟩ := _root_.GlobalTheory.BallStein.ball_etaleStein n c r
  set h : V n → ℝ≥0∞ := fun v => ENNReal.ofReal (t⁻¹ * ∑ j, ‖wdb n j F0 v‖ ^ 2) with hhdef
  have hh : Measurable h := by
    refine ENNReal.measurable_ofReal.comp (Measurable.const_mul ?_ _)
    exact Finset.measurable_sum _ fun j _ => ((measurable_wdb n j F0).norm.pow_const 2)
  have hb : ∀ y ∈ ball c r, ∀ ξ : Fin n → ℂ,
      ENNReal.ofReal (‖∑ j, wdb n j F0 y * (starRingEnd ℂ) (ξ j)‖ ^ 2) ≤
        h y * ENNReal.ofReal (leviV n (fun w => (φ w : ℂ)) y ξ).re := by
    intro y hy ξ
    rw [hhdef, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ((norm_sum_mul_conj_sq_le _ _).trans ?_)
    have h1 := hlevi y hy ξ
    have h2 : ∑ j, ‖ξ j‖ ^ 2 ≤ t⁻¹ * (leviV n (fun w => (φ w : ℂ)) y ξ).re := by
      rw [le_inv_mul_iff₀ ht]; exact h1
    have h3 : 0 ≤ ∑ j, ‖wdb n j F0 y‖ ^ 2 := by positivity
    calc (∑ j, ‖wdb n j F0 y‖ ^ 2) * ∑ j, ‖ξ j‖ ^ 2
        ≤ (∑ j, ‖wdb n j F0 y‖ ^ 2) * (t⁻¹ * (leviV n (fun w => (φ w : ℂ)) y ξ).re) := by
          gcongr
      _ = _ := by ring
  obtain ⟨F, hF, hest⟩ := hormander n (ball c r) X (fun x => φ x.1) (fun x => F0 x.1)
    (fun x => h x.1)
    (by rw [hX]; exact smoothR_val hφ)
    (fun x ξ => by
      rw [hX, levi_val hU]
      exact le_trans (by positivity) (hlevi x.1 x.2 ξ))
    (by rw [hX]; exact smooth_val hF0)
    (hh.comp measurable_subtype_coe) (fun x ξ => by
      have := hb x.1 x.2 ξ
      rw [hX]
      show ENNReal.ofReal (‖dbarDot n Subtype.val (fun x : ball c r => F0 x.1) x ξ‖ ^ 2) ≤
        h x.1 * ENNReal.ofReal (Levi n Subtype.val (fun x : ball c r => φ x.1) x ξ).re
      simp only [dbarDot, db_val hU]
      rw [levi_val hU]
      exact this)
  refine ⟨ext0 F, differentiableOn_extendByZero hU (hX ▸ hF), ?_⟩
  have hest' : wint n Subtype.val (fun x : ball c r => F0 x.1 - F x) (fun x : ball c r => φ x.1) ≤
      ∫⁻ x, h x.1 * ENNReal.ofReal (Real.exp (-φ x.1)) ∂vol n (Subtype.val : ball c r → V n) := by
    rw [hX] at hest; exact hest
  have h4 : ∫⁻ v in ball c r, ENNReal.ofReal (‖F0 v - ext0 F v‖ ^ 2 * Real.exp (-φ v)) ≤
      ∫⁻ v in ball c r, h v * ENNReal.ofReal (Real.exp (-φ v)) := by
    rw [← lintegral_val hU, ← lintegral_val hU]
    simpa [wint, extendByZeroOnSubset_apply_coe] using hest'
  refine h4.trans (le_of_eq ?_)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_congr_fun hU.measurableSet fun v _ => ?_
  rw [hhdef, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  ring_nf

end GlobalTheory.HormanderBall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideAlt
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.AlgTau

theorem main : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (Λ : PeriodPair) (c Ω : ℂ) (τ : ℍ), 0 < d → δ ^ 2 = -(d : K) → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 𝔞 Λ → IsTauOf Λ c τ → Ω ^ 12 = latDisc Λ → (Ω * c / (2 * Real.pi * Complex.I)) ^ 12 = DD τ ∧ IsAlgebraic ℚ (jT τ) ∧ IsAlgebraic ℚ (G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2) ∧ ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), IsAlgebraic ℚ (wp N x τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2) := by
  intro K _ _ d δ ι 𝔞 Λ c Ω τ hd hδ hlat htau hΩ
  obtain ⟨-, hmul, him, -⟩ := _root_.GlobalTheory.LatOfMult.main K d δ ι 𝔞 Λ hd hδ hlat
  have hval := _root_.GlobalTheory.WpFam.TauVal.main Λ c Ω τ htau
  have halg := _root_.GlobalTheory.AlgebraicitySecondEisenstein.main Λ (ι δ) Ω hmul him hΩ
  refine ⟨(GlobalTheory.QFam.jT_eq_and_pow_twelve_eq_DD Λ c τ htau).2 Ω hΩ, ?_, ?_, ?_⟩
  · have hj : IsIntegral ℤ (jT τ) := _root_.GlobalTheory.JInt.main Λ c τ (ι δ) htau hmul him
    exact (hj.tower_top (A := ℚ)).isAlgebraic
  · rw [hval.1]; exact halg.1
  · intro N _ x
    rw [(hval.2 N x).1]
    have hN : (N : ℂ) * (c * tors N τ x) ∈ Λ.lattice := by
      have h1 := ((_root_.GlobalTheory.WpFam.homogeneity_of_isTauOf Λ c τ htau).1 ((N : ℂ) * tors N τ x)).2
        ((_root_.GlobalTheory.WpFam.TorsMem.main N τ).2.2.2.1 x)
      simpa [mul_left_comm] using h1
    exact (halg.2 N (c * tors N τ x) (Nat.pos_of_ne_zero (NeZero.ne N)) hN).1

end GlobalTheory.AlgTau
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinitesimalPointTrivial
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinitesimal_point_trivial : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (v : epsPtR x ⟶ o.A), spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ o.A).left → (∀ c ∈ w0 ^ r, v ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → v = 1 := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.TanKill.tan_eq_one_of_etPlace) | (exact GlobalTheory.UPel.HT.EtLev.TanKill.tan_eq_one_of_etPlace) | (intros; apply GlobalTheory.UPel.HT.EtLev.TanKill.tan_eq_one_of_etPlace  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfSurjectiveProjectiveConstRank
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem injective_of_surjective_of_rankAtStalk_eq : ∀ (B M : Type) [CommRing B] [AddCommGroup M] [Module B M] (g : ℕ) (f : M →ₗ[B] (Fin g → B)), Module.Finite B M → Module.Projective B M → (∀ p : PrimeSpectrum B, Module.rankAtStalk M p = g) → Function.Surjective f → Function.Injective f := by
  intro B M _ _ _ g f hf hp hr hs
  refine (Module.bijective_of_surjective_of_rankAtStalk_eq hs ?_).1
  intro m hm
  have : Nontrivial B := ⟨⟨0, 1, fun h => hm.ne_top (by rw [Ideal.eq_top_iff_one, ← h]; exact m.zero_mem)⟩⟩
  rw [hr, Module.rankAtStalk_eq_finrank_of_free]
  simp

end GlobalTheory.CechPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteRingOfModule
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EvP

theorem isAdicComplete_ring_of_module {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (p : ℕ) [h : IsAdicComplete (Ideal.span {(p : O)}) A] :
    IsAdicComplete (Ideal.span {(p : A)}) A := by
  have key : ∀ (n : ℕ) (x : A), x ∈ (Ideal.span {(p : A)} ^ n • ⊤ : Submodule A A) ↔
      x ∈ (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O A) := by
    intro n x
    rw [GlobalTheory.mem_span_singleton_pow_smul_top_iff_exists, GlobalTheory.mem_span_singleton_pow_smul_top_iff_exists]
    simp [Algebra.smul_def]
  exact
    { haus' := fun x hx => IsHausdorff.haus h.toIsHausdorff x fun n =>
        SModEq.sub_mem.2 ((key n _).1 (SModEq.sub_mem.1 (hx n)))
      prec' := fun f hf => by
        obtain ⟨L, hL⟩ := IsPrecomplete.prec h.toIsPrecomplete (f := f) fun {m n} hmn =>
          SModEq.sub_mem.2 ((key _ _).1 (SModEq.sub_mem.1 (hf hmn)))
        exact ⟨L, fun n => SModEq.sub_mem.2 ((key _ _).2 (SModEq.sub_mem.1 (hL n)))⟩ }

theorem constantCoeff_nmul {O : Type} [CommRing O] {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : ∀ j, constantCoeff (μ j) = 0) :
    ∀ (k : ℕ) (j : Fin d), constantCoeff (nmul μ k j) = 0 := by
  intro k
  induction k with
  | zero => intro j; rfl
  | succ k ihk =>
    intro j
    have hsucc : nmul μ (k + 1) j =
        subst (Sum.elim (nmul μ k) fun i => (X i : MvPowerSeries (Fin d) O)) (μ j) := by
      simp only [nmul, Function.iterate_succ_apply']
      rfl
    rw [hsucc]
    refine constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ?_) ?_ (hμ j) <;>
    · rintro (l | l)
      · simpa using ihk l
      · simp

theorem ev_subst_nmul_p : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (n : ℕ) (s : MvPowerSeries (Fin d) O), c.ev (n + 1) (subst (nmul c.μ p) s) = G.mulP n (c.ev n s) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c n s
  haveI : IsAdicComplete (Ideal.span {(p : O)}) (G.A (n + 1)) :=
    GlobalTheory.isAdicComplete_of_finite_projective _ _
  haveI : IsAdicComplete (Ideal.span {(p : G.A (n + 1))}) (G.A (n + 1)) :=
    isAdicComplete_ring_of_module (O := O) p
  have hT := (GlobalTheory.CEval.continuous_eval p O (G.A (n + 1)) (Fin d) (c.x (n + 1)) (c.nil (n + 1))).2
    (c.ev (n + 1)) (c.isEval (n + 1))
  let E' : MvPowerSeries (Fin d) O →ₐ[O] G.A (n + 1) :=
    (G.mulP n : G.A n →ₐ[O] G.A (n + 1)).comp (c.ev n)
  have hu : ∀ j, constantCoeff (nmul c.μ p j) = 0 :=
    constantCoeff_nmul c.μ (fun j => c.isLaw.const j) p
  have hE' : IsEval p (fun j => c.ev (n + 1) (nmul c.μ p j)) E' := by
    constructor
    · intro j
      show G.mulP n (c.ev n (X j)) = c.ev (n + 1) (nmul c.μ p j)
      rw [(c.isEval n).1 j, GlobalTheory.T.pDivGroupFormalChart_ev_natMultiple_eq_convPower p C v O hv G d c (n + 1) p j, ← c.res n j, mulP_res]
    · intro m
      obtain ⟨N, hN⟩ := (c.isEval n).2 m
      refine ⟨N, fun f hf => ?_⟩
      have := map_dvd (G.mulP n : G.A n →ₐ[O] G.A (n + 1)) (hN f hf)
      rwa [map_pow, map_natCast] at this
  exact hT.1 (Fin d) (nmul c.μ p) E' hu hE' s

end GlobalTheory.EvP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacterHarishChandraProductCuspidalGLOfRegulStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCharacter_harishChandraProductCuspidalGL_of_regular : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ), (∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1 ∧ Reg (Nat.card F) p.1 p.2) → ∀ n, n = deg L → IsChar ℂ ℂ (J θ L n) := by
  first | (exact @GlobalTheory.Shin.isChar_J_of_reg) | (exact GlobalTheory.Shin.isChar_J_of_reg) | (intros; apply GlobalTheory.Shin.isChar_J_of_reg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevIffIsEtLevOverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEtLev_iff_isEtLevOver' : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S T : Scheme.{0}) (s : S ⟶ Sp R) (t : T ⟶ S) (s₁ : T ⟶ Sp R) (o : Obj b N s) (o₁ : Obj b N s₁) (m : ObjMap o₁ o t) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (l : D.La → (𝟙_ (Over T) ⟶ o₁.A)), IsEtLev o₁ w0 r l ↔ IsEtLevOver o w0 r (T := Over.mk t) (fun y => ptOf m (l y)) := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.isEtLev_iff_isEtLevOver) | (exact GlobalTheory.UPel.HT.EtLev.isEtLev_iff_isEtLevOver) | (intros; apply GlobalTheory.UPel.HT.EtLev.isEtLev_iff_isEtLevOver  <;> assumption)
end

