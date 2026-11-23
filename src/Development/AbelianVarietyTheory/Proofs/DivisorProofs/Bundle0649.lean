module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0623
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0622
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupFormalChartEvNatMultipleEqConvPowerStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct WithConv Coalgebra

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivGroupFormalChart_ev_natMultiple_eq_convPower :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
      (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
      [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
      ∀ (G : GlobalTheory.PDivGroup p O) (d : ℕ) (c : GlobalTheory.QLog.Chart G d)
        (n k : ℕ) (i : Fin d),
        c.ev n (nmul c.μ k i) = PDiv.mulBy (R := O) (A := G.A n) k (c.x n i) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ G d c n k
  have : IsAdicComplete (Ideal.span {(p : O)}) (G.A n) :=
    GlobalTheory.isAdicComplete_of_finite_projective _ _
  have : IsAdicComplete (Ideal.span {(p : G.A n)}) (G.A n) :=
    GlobalTheory.NMul.isAdicComplete_ring_of_module (O := O) p
  have heval := ((_root_.GlobalTheory.CEval.continuous_eval
    p O (G.A n) (Fin d) (c.x n) (c.nil n)).2 (c.ev n) (c.isEval n)).1
  have hsucc (k : ℕ) (i : Fin d) : nmul c.μ (k + 1) i =
      subst (Sum.elim (nmul c.μ k) fun j => (X j : MvPowerSeries (Fin d) O)) (c.μ i) := by
    rw [nmul, Function.iterate_succ_apply']
    rfl
  have hconstant (k : ℕ) (i : Fin d) : constantCoeff (nmul c.μ k i) = 0 := by
    induction k generalizing i with
    | zero => rfl
    | succ k ih =>
      rw [hsucc]
      have hzero : ∀ j, constantCoeff
          (Sum.elim (nmul c.μ k) (fun i => (X i : MvPowerSeries (Fin d) O)) j) = 0 := by
        rintro (j | j)
        · exact ih j
        · exact constantCoeff_X j
      exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hzero) hzero
        (c.isLaw.const i)
  have hmul (k : ℕ) : (PDiv.mulBy (R := O) (A := G.A n) k : G.A n →ₐ[O] G.A n) =
      (toConv (AlgHom.id O (G.A n)) ^ k).ofConv :=
    PDiv.comp_mulBy_pts (AlgHom.id O (G.A n)) k
  induction k with
  | zero =>
    intro i
    have hzero : nmul c.μ 0 i = 0 := rfl
    change c.ev n (nmul c.μ 0 i) =
      (PDiv.mulBy (R := O) (A := G.A n) 0 : G.A n →ₐ[O] G.A n) (c.x n i)
    rw [hzero, map_zero, hmul]
    simp [c.aug n i]
  | succ k ih =>
    intro i
    let u := Sum.elim (nmul c.μ k) fun j => (X j : MvPowerSeries (Fin d) O)
    let lift : G.A n ⊗[O] G.A n →ₐ[O] G.A n :=
      Algebra.TensorProduct.lift (PDiv.mulBy (R := O) (A := G.A n) k : G.A n →ₐ[O] G.A n)
        (AlgHom.id O (G.A n)) fun _ _ => Commute.all _ _
    have hu : ∀ j, constantCoeff (u j) = 0 := by
      rintro (j | j)
      · exact hconstant k j
      · exact constantCoeff_X j
    have hlift : IsEval p (fun j => c.ev n (u j)) (lift.comp (c.ev₂ n)) := by
      constructor
      · rintro (j | j)
        · simp only [lift, u, AlgHom.comp_apply, (c.isEval₂ n).1 (Sum.inl j), Sum.elim_inl,
            Algebra.TensorProduct.lift_tmul, map_one, mul_one]
          exact (ih j).symm
        · simp only [lift, u, AlgHom.comp_apply, (c.isEval₂ n).1 (Sum.inr j), Sum.elim_inr,
            Algebra.TensorProduct.lift_tmul, map_one, one_mul, (c.isEval n).1 j]
          rfl
      · intro m
        obtain ⟨N, hN⟩ := (c.isEval₂ n).2 m
        refine ⟨N, fun f hf => ?_⟩
        simpa only [AlgHom.comp_apply, map_pow, map_natCast] using map_dvd lift (hN f hf)
    rw [hsucc, heval _ u _ hu hlift, AlgHom.comp_apply, c.comul n i]
    change lift (comul (R := O) (c.x n i)) =
      (PDiv.mulBy (R := O) (A := G.A n) (k + 1) : G.A n →ₐ[O] G.A n) (c.x n i)
    rw [hmul, pow_succ, AlgHom.convMul_apply]
    simp only [lift, hmul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointwiseAbsorptionTwisted
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem pointwise_absorption_twisted :
    ∀ (T x u g t k1 k2 E : ℝ), 0 ≤ u → 0 ≤ g → 0 < k2 → 0 < E → |t| ≤ 3 / 4 →
      wT T x / 8 ≤ (1 - k1 ^ 2 / k2) * E →
      ((-T - 1 ≤ x ∧ x ≤ -T + 1) → E / k2 ≤ 16 / 3 ∧ wT T x / 8 ≤ (1 - 5 * (k1 ^ 2 / k2)) * E) →
      (¬ (-T - 1 ≤ x ∧ x ≤ -T + 1) → t = 0) →
      (Real.sqrt (t ^ 2 * g ^ 2 / k2) + u * Real.sqrt (k1 ^ 2 / k2)) ^ 2 * E + u ^ 2 * (wT T x / 8)
        ≤ u ^ 2 * E + (if (-T - 1 ≤ x ∧ x ≤ -T + 1) then 15 / 4 * g ^ 2 else 0) := by
  intro T x u g t k1 k2 E hu hg hk2 hE ht hw hwin hoff
  have ha : 0 ≤ t ^ 2 * g ^ 2 / k2 := by positivity
  have hb : 0 ≤ k1 ^ 2 / k2 := by positivity
  have hA := Real.sq_sqrt ha
  have hB := Real.sq_sqrt hb
  have hA0 := Real.sqrt_nonneg (t ^ 2 * g ^ 2 / k2)
  have hB0 := Real.sqrt_nonneg (k1 ^ 2 / k2)
  by_cases h : (-T - 1 ≤ x ∧ x ≤ -T + 1)
  · rw [if_pos h]
    obtain ⟨h1, h2⟩ := hwin h
    have ht2 : t ^ 2 ≤ 9 / 16 := by
      have h0 : 0 ≤ |t| := abs_nonneg t
      have : |t| ^ 2 ≤ (3 / 4) ^ 2 := by nlinarith
      rw [sq_abs] at this
      linarith
    have haE : t ^ 2 * g ^ 2 / k2 * E ≤ 3 * g ^ 2 := by
      have e : t ^ 2 * g ^ 2 / k2 * E = t ^ 2 * g ^ 2 * (E / k2) := by ring
      rw [e]
      calc t ^ 2 * g ^ 2 * (E / k2) ≤ (9 / 16) * g ^ 2 * (16 / 3) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right ht2 (sq_nonneg g)) h1
              (by positivity) (by positivity)
        _ = 3 * g ^ 2 := by ring
    have key : (Real.sqrt (t ^ 2 * g ^ 2 / k2) + u * Real.sqrt (k1 ^ 2 / k2)) ^ 2
        ≤ 5 / 4 * (t ^ 2 * g ^ 2 / k2) + 5 * (k1 ^ 2 / k2) * u ^ 2 := by
      nlinarith [sq_nonneg (Real.sqrt (t ^ 2 * g ^ 2 / k2) / 2 - 2 * u * Real.sqrt (k1 ^ 2 / k2))]
    have k1' := mul_le_mul_of_nonneg_right key hE.le
    have k2' := mul_le_mul_of_nonneg_left h2 (sq_nonneg u)
    nlinarith
  · rw [if_neg h]
    have t0 := hoff h
    subst t0
    have z : Real.sqrt ((0:ℝ) ^ 2 * g ^ 2 / k2) = 0 := by simp
    rw [z]
    have k2' := mul_le_mul_of_nonneg_left hw (sq_nonneg u)
    have e : (0 + u * Real.sqrt (k1 ^ 2 / k2)) ^ 2 * E = u ^ 2 * (k1 ^ 2 / k2) * E := by
      rw [zero_add, mul_pow, hB]
    rw [e]
    nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientJetsFderivDetNeZero
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
namespace GlobalTheory

theorem quot_jets_det_ne_zero : ∀ n : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ (p : V n) (w0 : V n → ℂ) (w : Fin n → V n → ℂ), DifferentiableAt ℂ w0 p → (∀ j, DifferentiableAt ℂ (w j) p) → ‖w0 p - 1‖ ≤ ε → ‖fderiv ℂ (fun v => w0 v - 1) p‖ ≤ ε → (∀ j, ‖w j p‖ ≤ ε) → (∀ j, ‖fderiv ℂ (fun v : V n => w j v - (v j - p j)) p‖ ≤ ε) → w0 p ≠ 0 ∧ (fderiv ℂ (fun v : V n => (WithLp.toLp 2 (fun j => w j v / w0 v) : V n)) p).det ≠ 0 := by
  intro n
  refine ⟨1 / (4 * ((n : ℝ) + 1)), by positivity, ?_⟩
  intro p w0 w hw0 hw h0 hL0 hwp hLj
  set ε : ℝ := 1 / (4 * ((n : ℝ) + 1)) with hε
  have hεpos : 0 < ε := by positivity
  have hε4 : ε ≤ 1 / 4 := by
    rw [hε]; apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  set a := w0 p with ha_def
  have ha_norm : 3 / 4 ≤ ‖a‖ := by
    have h1 : ‖(1:ℂ)‖ ≤ ‖a‖ + ‖a - 1‖ := by
      have := norm_sub_le a (a - 1)
      simpa using this
    simp at h1
    linarith
  have ha : a ≠ 0 := by
    intro h; rw [h] at ha_norm; simp at ha_norm; linarith
  refine ⟨ha, ?_⟩
  set L0 := fderiv ℂ w0 p with hL0_def
  have hL0' : ‖L0‖ ≤ ε := by
    have := hL0; rwa [fderiv_sub_const] at this
  have hproj : ∀ j : Fin n, HasFDerivAt (fun v : V n => v j - p j) (EuclideanSpace.proj (𝕜 := ℂ) j) p := by
    intro j
    have := (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin n) j).hasFDerivAt (x := p)
    exact this.sub_const (p j)
  have hLj' : ∀ j : Fin n, ∀ ξ : V n, ‖fderiv ℂ (w j) p ξ - ξ j‖ ≤ ε * ‖ξ‖ := by
    intro j ξ
    have hd : fderiv ℂ (fun v : V n => w j v - (v j - p j)) p
        = fderiv ℂ (w j) p - EuclideanSpace.proj (𝕜 := ℂ) j :=
      ((hw j).hasFDerivAt.sub (hproj j)).fderiv
    have := (fderiv ℂ (fun v : V n => w j v - (v j - p j)) p).le_opNorm ξ
    rw [hd] at this
    have h2 := hLj j
    rw [hd] at h2
    calc ‖fderiv ℂ (w j) p ξ - ξ j‖ = ‖(fderiv ℂ (w j) p - EuclideanSpace.proj (𝕜 := ℂ) j) ξ‖ := by simp
      _ ≤ _ := this
      _ ≤ ε * ‖ξ‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  set F : V n → V n := fun v => (WithLp.toLp 2 (fun j => w j v / w0 v) : V n) with hF
  have hq : ∀ j : Fin n, HasFDerivAt (fun v => w j v / w0 v)
      (w j p • ((-(a ^ 2)⁻¹) • L0) + a⁻¹ • fderiv ℂ (w j) p) p := by
    intro j
    have hinv : HasFDerivAt (fun v => (w0 v)⁻¹) ((-(a ^ 2)⁻¹) • L0) p :=
      (hasDerivAt_inv ha).comp_hasFDerivAt p hw0.hasFDerivAt
    have := HasFDerivAt.mul (hw j).hasFDerivAt hinv
    have e : (fun v => w j v / w0 v) = (w j * fun v => (w0 v)⁻¹) := by
      funext v; simp [div_eq_mul_inv]
    rw [e]; exact this
  have hFd : DifferentiableAt ℂ F p := by
    rw [differentiableAt_piLp]
    intro j
    simpa [hF] using (hq j).differentiableAt
  set D := fderiv ℂ F p with hD
  have hDj : ∀ j : Fin n, ∀ ξ : V n, (D ξ) j = w j p * ((-(a ^ 2)⁻¹) * L0 ξ) + a⁻¹ * fderiv ℂ (w j) p ξ := by
    intro j ξ
    have h1 : HasFDerivAt (fun v => EuclideanSpace.proj (𝕜 := ℂ) j (F v)) ((EuclideanSpace.proj (𝕜 := ℂ) j).comp D) p :=
      (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin n) j).hasFDerivAt.comp p hFd.hasFDerivAt
    have h2 : (fun v => EuclideanSpace.proj (𝕜 := ℂ) j (F v)) = fun v => w j v / w0 v := by
      funext v; simp [hF]
    rw [h2] at h1
    have := congrArg (fun T : V n →L[ℂ] ℂ => T ξ) (h1.unique (hq j))
    simpa using this
  have hinj : ∀ ξ : V n, D ξ = 0 → ξ = 0 := by
    intro ξ hξ
    have hcoord : ∀ j : Fin n, ‖ξ j‖ ≤ 2 * ε * ‖ξ‖ := by
      intro j
      have e := hDj j ξ
      rw [hξ] at e
      simp only [PiLp.zero_apply] at e
      have e2 : a * fderiv ℂ (w j) p ξ = w j p * L0 ξ := by
        have : a ^ 2 * (w j p * ((-(a ^ 2)⁻¹) * L0 ξ) + a⁻¹ * fderiv ℂ (w j) p ξ) = 0 := by
          rw [← e]; ring
        field_simp at this
        linear_combination this
      have hL0ξ : ‖L0 ξ‖ ≤ ε * ‖ξ‖ := (L0.le_opNorm ξ).trans (mul_le_mul_of_nonneg_right hL0' (norm_nonneg _))
      have e3 : ‖a‖ * ‖fderiv ℂ (w j) p ξ‖ ≤ ε * (ε * ‖ξ‖) := by
        rw [← norm_mul, e2, norm_mul]
        exact mul_le_mul (hwp j) hL0ξ (norm_nonneg _) hεpos.le
      have e4 : ‖fderiv ℂ (w j) p ξ‖ ≤ ε * ‖ξ‖ := by
        by_contra hc
        push_neg at hc
        have : (3/4) * (ε * ‖ξ‖) < ‖a‖ * ‖fderiv ℂ (w j) p ξ‖ := by
          calc (3/4) * (ε * ‖ξ‖) ≤ ‖a‖ * (ε * ‖ξ‖) := mul_le_mul_of_nonneg_right ha_norm (by positivity)
            _ < ‖a‖ * ‖fderiv ℂ (w j) p ξ‖ := mul_lt_mul_of_pos_left hc (by linarith)
        have : ε * (ε * ‖ξ‖) ≤ (3/4) * (ε * ‖ξ‖) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        linarith
      have e5 := hLj' j ξ
      have : ‖ξ j‖ ≤ ‖fderiv ℂ (w j) p ξ‖ + ‖fderiv ℂ (w j) p ξ - ξ j‖ := by
        have := norm_sub_le (fderiv ℂ (w j) p ξ) (fderiv ℂ (w j) p ξ - ξ j)
        simpa using this
      linarith
    have hsq : ‖ξ‖ ^ 2 ≤ (n : ℝ) * (2 * ε * ‖ξ‖) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      calc ∑ i, ‖ξ.ofLp i‖ ^ 2 ≤ ∑ _i : Fin n, (2 * ε * ‖ξ‖) ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            exact pow_le_pow_left₀ (norm_nonneg _) (hcoord i) 2
        _ = (n : ℝ) * (2 * ε * ‖ξ‖) ^ 2 := by simp
    have hc : (n : ℝ) * (2 * ε) ^ 2 ≤ 1 / 4 := by
      rw [hε]
      have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
      rw [show (2 * (1 / (4 * ((n:ℝ) + 1)))) ^ 2 = 1 / (4 * ((n:ℝ)+1)^2) by field_simp; ring]
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have : ‖ξ‖ ^ 2 ≤ (1/4) * ‖ξ‖ ^ 2 := by
      calc ‖ξ‖ ^ 2 ≤ (n : ℝ) * (2 * ε * ‖ξ‖) ^ 2 := hsq
        _ = ((n : ℝ) * (2 * ε) ^ 2) * ‖ξ‖ ^ 2 := by ring
        _ ≤ (1/4) * ‖ξ‖ ^ 2 := mul_le_mul_of_nonneg_right hc (by positivity)
    have : ‖ξ‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖ξ‖]
    simpa using this
  intro hdet
  have h := (LinearMap.det_eq_zero_iff_ker_ne_bot (f := (D : V n →ₗ[ℂ] V n))).1 hdet
  apply h
  rw [LinearMap.ker_eq_bot']
  intro m hm
  exact hinj m hm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShellMass
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

noncomputable section

namespace GlobalTheory.ShellMass

theorem shell_mass : ∀ (n : ℕ), 1 ≤ n → ∀ (p : V n) (O : Set (V n)) (Z : V n → V n) (lam : V n → ℝ), IsOpen O → p ∈ O → DifferentiableOn ℂ Z O → Z p = 0 → (fderiv ℂ Z p).det ≠ 0 → ContinuousOn lam O → ∀ (φ : V n → ℝ) (l τ : ℝ), ContinuousOn φ O → 0 < l → 0 < τ → ∃ ρ : ℝ, 0 < ρ ∧ ball p ρ ⊆ O ∧ ∀ b : ℝ, ∫⁻ v in ball p ρ ∩ {v | Z v ≠ 0 ∧ b - l ≤ ((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))) ∧ ((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))) ≤ b}, ENNReal.ofReal (Real.exp (-φ v) * Real.exp (-((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))))) ≤ ENNReal.ofReal ((1 + τ) * (Real.pi ^ n / ((n - 1).factorial : ℝ) * (l / n)) * (Real.exp (-φ p + n * lam p) / ‖(fderiv ℂ Z p).det‖ ^ 2)) := by
  classical
  intro n hn p O Z lam hO hpO hZ hZp hdet hlam φ l τ hφ hl hτ
  have hZc : ContDiffOn ℂ ∞ Z O := by
    refine contDiffOn_piLp' (p := 2) fun i => ?_
    have hd : DifferentiableOn ℂ (fun x => Z x i) O :=
      (EuclideanSpace.proj i : V n →L[ℂ] ℂ).differentiable.comp_differentiableOn hZ
    have ha : AnalyticOnNhd ℂ (fun x => Z x i) O := fun z hz =>
      ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.analyticAt_of_diffOn hO hd hz
    exact ha.contDiffOn hO.uniqueDiffOn
  have hZa : ContDiffAt ℂ ∞ Z p := hZc.contDiffAt (hO.mem_nhds hpO)
  set E0 := (fderiv ℂ Z p).toContinuousLinearEquivOfDetNeZero hdet
  have hs : HasStrictFDerivAt Z (E0 : V n →L[ℂ] V n) p := by
    simpa [E0] using hZa.hasStrictFDerivAt_fderiv (by norm_cast)
  set e := hs.toOpenPartialHomeomorph Z
  have he : (e : V n → V n) = Z := rfl
  have hpe : p ∈ e.source := hs.mem_toOpenPartialHomeomorph_source
  have hdetc : ContinuousOn (fun v => (fderiv ℂ Z v).det) O :=
    ContinuousLinearMap.continuous_det.comp_continuousOn
      (hZc.continuousOn_fderiv_of_isOpen hO (by norm_cast))
  set D : V n → ℝ := fun v => ‖(fderiv ℂ Z v).det‖ ^ 2 with hD
  have hDc : ContinuousAt D p := ((hdetc.continuousAt (hO.mem_nhds hpO)).norm).pow 2
  have hD0 : 0 < D p := pow_pos (norm_pos_iff.2 hdet) 2
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  set c := l / n with hcdef
  have hc : 0 < c := div_pos hl hnr
  have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ), 0 < η ∧ Real.exp (2 * η) * (c + 2 * η) < (1 + τ) * c := by
    refine Filter.Eventually.and eventually_mem_nhdsWithin (nhdsWithin_le_nhds ?_)
    have ht : Tendsto (fun η : ℝ => Real.exp (2 * η) * (c + 2 * η)) (𝓝 0)
        (𝓝 (Real.exp (2 * 0) * (c + 2 * 0))) :=
      ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
        (continuous_const.add (continuous_const.mul continuous_id))).tendsto 0
    simp only [mul_zero, Real.exp_zero, one_mul, add_zero] at ht
    exact ht.eventually (gt_mem_nhds (by nlinarith))
  obtain ⟨η, hη, hηc⟩ := hev.exists
  have hlamc : ContinuousAt lam p := hlam.continuousAt (hO.mem_nhds hpO)
  have hgc : ContinuousAt (fun v => -φ v + (n : ℝ) * lam v) p :=
    ((hφ.continuousAt (hO.mem_nhds hpO)).neg).add (continuousAt_const.mul hlamc)
  have h1 : ∀ᶠ v in 𝓝 p, v ∈ O := hO.mem_nhds hpO
  have h2 : ∀ᶠ v in 𝓝 p, v ∈ e.source := e.open_source.mem_nhds hpe
  have h3 : ∀ᶠ v in 𝓝 p, lam v ∈ ball (lam p) η := hlamc.eventually (ball_mem_nhds _ hη)
  have h4 : ∀ᶠ v in 𝓝 p, (-φ v + (n : ℝ) * lam v) ∈ ball (-φ p + (n : ℝ) * lam p) η :=
    hgc.eventually (ball_mem_nhds _ hη)
  have h5 : ∀ᶠ v in 𝓝 p, D p * Real.exp (-η) < D v := by
    refine hDc.eventually (lt_mem_nhds ?_)
    have : Real.exp (-η) < 1 := (Real.exp_lt_exp.2 (by linarith : -η < 0)).trans_eq Real.exp_zero
    nlinarith
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and (h2.and (h3.and (h4.and h5))))
  have hbO : ball p ρ ⊆ O := fun v hv => (hball v hv).1
  have hinj : Set.InjOn Z (ball p ρ) := by
    rw [← he]; exact e.injOn.mono fun v hv => (hball v hv).2.1
  refine ⟨ρ, hρ, hbO, ?_⟩
  intro b
  set a1 := Real.exp ((b - l) / n + lam p - η) with ha1
  set a2 := Real.exp (b / n + lam p + η) with ha2
  have ha1p : 0 < a1 := Real.exp_pos _
  have h21 : a2 / a1 = Real.exp (c + 2 * η) := by
    rw [ha1, ha2, ← Real.exp_sub, hcdef]; congr 1; ring
  have ha12 : a1 ≤ a2 := by
    rw [ha1, ha2]; refine Real.exp_le_exp.2 ?_
    have : (b - l) / n ≤ b / n := div_le_div_of_nonneg_right (by linarith) hnr.le
    linarith
  set Ann := {w : V n | a1 ≤ ‖w‖ ^ 2 ∧ ‖w‖ ^ 2 ≤ a2} with hAnn
  have hAnnm : MeasurableSet Ann :=
    ((isClosed_le continuous_const (continuous_norm.pow 2)).inter
      (isClosed_le (continuous_norm.pow 2) continuous_const)).measurableSet
  set K := Real.exp (2 * η) * (Real.exp (-φ p + n * lam p) / ‖(fderiv ℂ Z p).det‖ ^ 2) with hK
  have hK0 : 0 ≤ K := by positivity
  have hfm' : Measurable fun w : V n => ENNReal.ofReal ((‖w‖ ^ 2) ^ (-(n : ℝ))) :=
    ((measurable_norm.pow_const 2).pow_const _).ennreal_ofReal
  set f : V n → ℝ≥0∞ := fun w => ENNReal.ofReal K *
      Ann.indicator (fun w => ENNReal.ofReal ((‖w‖ ^ 2) ^ (-(n : ℝ)))) w with hfdef
  have hfm : Measurable f := measurable_const.mul (hfm'.indicator hAnnm)
  set Zb : V n → V n := (ball p ρ).piecewise Z (fun _ => 0) with hZb
  have hZbm : Measurable Zb :=
    ContinuousOn.measurable_piecewise (hZ.continuousOn.mono hbO) continuousOn_const measurableSet_ball
  set G : V n → ℝ≥0∞ := fun v => ENNReal.ofReal (D v) * f (Zb v) with hG
  have hGm : Measurable G := by
    refine Measurable.mul ?_ (hfm.comp hZbm)
    refine Measurable.ennreal_ofReal ?_
    exact ((ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℂ Z)).norm).pow_const 2

  have hpt : ∀ v ∈ ball p ρ ∩ {v | Z v ≠ 0 ∧ b - l ≤ ((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))) ∧
      ((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))) ≤ b},
      ENNReal.ofReal (Real.exp (-φ v) * Real.exp (-((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))))) ≤ G v := by
    rintro v ⟨hvb, hv0, hvl, hvu⟩
    obtain ⟨-, -, hv3, hv4, hv5⟩ := hball v hvb
    rw [mem_ball, Real.dist_eq, abs_lt] at hv3 hv4
    set s := ‖Z v‖ ^ 2 with hsdef
    have hsp : 0 < s := pow_pos (norm_pos_iff.2 hv0) 2
    have hlog : Real.log (s * Real.exp (-lam v)) = Real.log s - lam v := by
      rw [Real.log_mul hsp.ne' (Real.exp_pos _).ne', Real.log_exp]; ring
    rw [hlog] at hvl hvu ⊢
    have hl1 : (b - l) / n ≤ Real.log s - lam v := by rw [div_le_iff₀ hnr]; linarith
    have hl2 : Real.log s - lam v ≤ b / n := by rw [le_div_iff₀ hnr]; linarith
    have hA : Z v ∈ Ann := by
      refine ⟨?_, ?_⟩
      · exact (Real.exp_le_exp.2 (by linarith)).trans_eq (Real.exp_log hsp)
      · exact (Real.exp_log hsp).symm.trans_le (Real.exp_le_exp.2 (by linarith))
    have hZbv : Zb v = Z v := Set.piecewise_eq_of_mem _ _ _ hvb
    simp only [hG, hfdef, hZbv, Set.indicator_of_mem hA]
    rw [← ENNReal.ofReal_mul hK0, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hsn : s ^ (-(n : ℝ)) = Real.exp (-(n : ℝ) * Real.log s) := by
      rw [Real.rpow_def_of_pos hsp]; ring_nf
    have heq : Real.exp (-φ v) * Real.exp (-((n : ℝ) * (Real.log s - lam v))) =
        Real.exp (-φ v + (n : ℝ) * lam v) * s ^ (-(n : ℝ)) := by
      rw [hsn, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    rw [heq]
    have hexp : Real.exp (-φ v + (n : ℝ) * lam v) ≤ D v * K := by
      have e1 : Real.exp (-φ v + (n : ℝ) * lam v) ≤ Real.exp (-φ p + n * lam p + η) :=
        Real.exp_le_exp.2 (by linarith)
      have e2 : Real.exp (-φ p + n * lam p + η) = D p * Real.exp (-η) * K := by
        rw [hK, show ‖(fderiv ℂ Z p).det‖ ^ 2 = D p from rfl, div_eq_mul_inv]
        have hDi : D p * (D p)⁻¹ = 1 := mul_inv_cancel₀ hD0.ne'
        have hx : Real.exp (-φ p + n * lam p + η) =
            Real.exp (-η) * Real.exp (2 * η) * Real.exp (-φ p + n * lam p) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        rw [hx]
        linear_combination (-(Real.exp (-η) * Real.exp (2 * η) * Real.exp (-φ p + n * lam p))) * hDi
      rw [e2] at e1
      exact e1.trans (mul_le_mul_of_nonneg_right hv5.le hK0)
    have hsn0 : 0 ≤ s ^ (-(n : ℝ)) := Real.rpow_nonneg hsp.le _
    calc Real.exp (-φ v + (n : ℝ) * lam v) * s ^ (-(n : ℝ)) ≤ D v * K * s ^ (-(n : ℝ)) :=
          mul_le_mul_of_nonneg_right hexp hsn0
      _ = D v * (K * s ^ (-(n : ℝ))) := by ring
  have hcov := ReciprocityTheory.L2DbarEstimates.I.cov n (ball p ρ) Z f isOpen_ball (hZ.mono hbO) hinj hfm
  have hpol := ReciprocityTheory.L2DbarEstimates.I.polar n hn a1 a2 ha1p ha12
  calc _ ≤ ∫⁻ v in ball p ρ ∩ {v | Z v ≠ 0 ∧ b - l ≤ ((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))) ∧
        ((n : ℝ) * Real.log (‖Z v‖ ^ 2 * Real.exp (-lam v))) ≤ b}, G v := setLIntegral_mono hGm hpt
    _ ≤ ∫⁻ v in ball p ρ, G v := lintegral_mono_set Set.inter_subset_left
    _ = ∫⁻ w in Z '' ball p ρ, f w := by
        rw [hcov]
        refine setLIntegral_congr_fun measurableSet_ball (fun v hv => ?_)
        simp only [hG, hD, Set.piecewise_eq_of_mem _ _ _ hv, hZb]
    _ ≤ ∫⁻ w, f w := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal K * ENNReal.ofReal (Real.pi ^ n / ((n - 1).factorial : ℝ) * Real.log (a2 / a1)) := by
        rw [hfdef, lintegral_const_mul _ (hfm'.indicator hAnnm), lintegral_indicator hAnnm, hpol]
    _ ≤ _ := by
        rw [← ENNReal.ofReal_mul hK0]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [h21, Real.log_exp, hK]
        have hP : 0 ≤ Real.pi ^ n / ((n - 1).factorial : ℝ) := by positivity
        have hE : 0 ≤ Real.exp (-φ p + n * lam p) / ‖(fderiv ℂ Z p).det‖ ^ 2 := by positivity
        calc Real.exp (2 * η) * (Real.exp (-φ p + n * lam p) / ‖(fderiv ℂ Z p).det‖ ^ 2) *
              (Real.pi ^ n / ((n - 1).factorial : ℝ) * (c + 2 * η))
            = (Real.pi ^ n / ((n - 1).factorial : ℝ) * (Real.exp (-φ p + n * lam p) / ‖(fderiv ℂ Z p).det‖ ^ 2)) *
              (Real.exp (2 * η) * (c + 2 * η)) := by ring
          _ ≤ (Real.pi ^ n / ((n - 1).factorial : ℝ) * (Real.exp (-φ p + n * lam p) / ‖(fderiv ℂ Z p).det‖ ^ 2)) *
              ((1 + τ) * c) := mul_le_mul_of_nonneg_left hηc.le (mul_nonneg hP hE)
          _ = _ := by rw [hcdef]; ring

end GlobalTheory.ShellMass
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstGroupLawEqMulOfDualTateCharacter
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
open TensorProduct

namespace GlobalTheory.QLog.Chart

theorem subst_μ_eq_inL_mul_inR : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d)
    (χ : G.dual.Tate) (u : MvPowerSeries (Fin d) O), (∀ n, c.ev n u = charElem χ n) →
    subst c.μ u = inL u * inR u := by
  intro p _ O _ _ _ G d c χ u hu
  set D := subst c.μ u - inL u * inR u with hD
  have hev : ∀ n, c.ev₂ n D = 0 := by
    intro n
    obtain ⟨h1, h2, h3, -⟩ := ev₂_eval p O G d c n u
    rw [hD, map_sub, map_mul, h1, h2, h3, hu n, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
      (isGroupLikeElem_charElem χ n).comul_eq_tmul_self, sub_self]
  rw [← sub_eq_zero, ← hD]
  ext α
  rw [map_zero]
  refine IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := Ideal.span {(p : O)})) _ fun m => ?_
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, sub_zero]
  obtain ⟨n, hn⟩ := c.ker m (α.degree + 1)
  exact _root_.GlobalTheory.KerTensor.ker_tensor p O (G.A n) (G.A n) (Fin d) (Fin d) (c.x n) (c.x n) (c.ev n) (c.ev n) (c.ev₂ n) m
    (α.degree + 1) (c.isEval n) (c.isEval n) (c.isEval₂ n) (c.surj n) (c.surj n) hn hn D (hev n) α
    (Nat.lt_succ_self _)

end GlobalTheory.QLog.Chart
end
end

