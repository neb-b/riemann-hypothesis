module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.UnitTestFunctions.LiftUnit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentsOfPrimePowerRootOfUnity
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0173
public import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundaryTermGood
section
noncomputable section

open MeasureTheory Filter Topology Metric PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.RgEisLeft

lemma gauss_strip (b c : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, b ≤ z.re → z.re ≤ c →
    ‖Complex.exp (z ^ 2)‖ * (1 + ‖z‖) ^ 4 ≤ C := by
  set X := max |b| |c| with hX
  have hX0 : 0 ≤ X := le_trans (abs_nonneg _) (le_max_left _ _)
  refine ⟨8 * Real.exp ((1 + X) ^ 2 + X ^ 2), by positivity, fun z hb hc => ?_⟩
  have hx : |z.re| ≤ X := by
    rw [abs_le]
    constructor
    · have h1 := neg_abs_le b
      have h2 := le_max_left |b| |c|
      linarith
    · have h1 := le_abs_self c
      have h2 := le_max_right |b| |c|
      linarith
  have hn : ‖Complex.exp (z ^ 2)‖ = Real.exp (z.re ^ 2 - z.im ^ 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [pow_two, Complex.mul_re]
  have hz : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
  obtain ⟨t, ht⟩ : ∃ t, t = 1 + ‖z‖ := ⟨_, rfl⟩
  rw [← ht, hn]
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hta : t ≤ (1 + X) + |z.im| := by linarith
  have ht2 : t ^ 2 ≤ 2 * (1 + X) ^ 2 + 2 * z.im ^ 2 := by
    have h1 : t ^ 2 ≤ ((1 + X) + |z.im|) ^ 2 := pow_le_pow_left₀ ht0 hta 2
    have h2 : |z.im| ^ 2 = z.im ^ 2 := sq_abs _
    nlinarith [sq_nonneg ((1 + X) - |z.im|)]
  have h4 : t ^ 4 ≤ 8 * Real.exp (t ^ 2 / 2) := by
    have h1 := Real.quadratic_le_exp_of_nonneg (x := t ^ 2 / 2) (by positivity)
    have h2 : t ^ 4 = 8 * ((t ^ 2 / 2) ^ 2 / 2) := by ring
    have h3 : 0 ≤ t ^ 2 / 2 := by positivity
    linarith
  have hx2 : z.re ^ 2 ≤ X ^ 2 := by
    rw [← sq_abs z.re]
    exact pow_le_pow_left₀ (abs_nonneg _) hx 2
  calc Real.exp (z.re ^ 2 - z.im ^ 2) * t ^ 4
      ≤ Real.exp (z.re ^ 2 - z.im ^ 2) * (8 * Real.exp (t ^ 2 / 2)) := by gcongr
    _ = 8 * Real.exp (z.re ^ 2 - z.im ^ 2 + t ^ 2 / 2) := by rw [Real.exp_add]; ring
    _ ≤ 8 * Real.exp ((1 + X) ^ 2 + X ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)

lemma leftGood_of {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℂ → E}
    (hd : DifferentiableOn ℂ A {z | z.re < 1 / 2})
    (hb : ∀ b c : ℝ, c < 1 / 2 → ∃ M : ℝ, ∀ z : ℂ, b ≤ z.re → z.re ≤ c → ‖A z‖ ≤ M * (1 + ‖z‖) ^ 2) :
    LeftGood (fun z => (Complex.exp (z ^ 2) * (z - 1)) • A z) (1 / 2) ∧
    LeftGood (fun z => z • (Complex.exp (z ^ 2) * (z - 1)) • A z) (1 / 2) := by
  have hd1 : DifferentiableOn ℂ (fun z => (Complex.exp (z ^ 2) * (z - 1)) • A z) {z | z.re < 1 / 2} :=
    DifferentiableOn.smul
      (by fun_prop : Differentiable ℂ fun z : ℂ => Complex.exp (z ^ 2) * (z - 1)).differentiableOn hd
  have hd2 : DifferentiableOn ℂ (fun z => z • (Complex.exp (z ^ 2) * (z - 1)) • A z) {z | z.re < 1 / 2} :=
    DifferentiableOn.smul differentiableOn_id hd1
  have key : ∀ b c : ℝ, c < 1 / 2 → ∃ B : ℝ, ∀ z : ℂ, b ≤ z.re → z.re ≤ c →
      ‖(Complex.exp (z ^ 2) * (z - 1)) • A z‖ * (1 + ‖z‖) ≤ B := by
    intro b c hc
    obtain ⟨M, hM⟩ := hb b c hc
    obtain ⟨C, hC0, hC⟩ := gauss_strip b c
    refine ⟨|M| * C, fun z h1 h2 => ?_⟩
    have hA : ‖A z‖ ≤ |M| * (1 + ‖z‖) ^ 2 :=
      (hM z h1 h2).trans (by gcongr; exact le_abs_self M)
    have hz1 : ‖z - 1‖ ≤ 1 + ‖z‖ := by
      have := norm_sub_le z 1
      simp only [norm_one] at this
      linarith
    have ht : 0 ≤ 1 + ‖z‖ := by positivity
    rw [norm_smul, norm_mul]
    calc ‖Complex.exp (z ^ 2)‖ * ‖z - 1‖ * ‖A z‖ * (1 + ‖z‖)
        ≤ ‖Complex.exp (z ^ 2)‖ * (1 + ‖z‖) * (|M| * (1 + ‖z‖) ^ 2) * (1 + ‖z‖) := by gcongr
      _ = |M| * (‖Complex.exp (z ^ 2)‖ * (1 + ‖z‖) ^ 4) := by ring
      _ ≤ |M| * C := by
          gcongr
          exact hC z h1 h2
  refine ⟨⟨hd1, fun b c hc => ?_⟩, ⟨hd2, fun b c hc => ?_⟩⟩
  · obtain ⟨B, hB⟩ := key b c hc
    refine ⟨B, fun z h1 h2 => le_trans ?_ (hB z h1 h2)⟩
    have : 1 ≤ 1 + ‖z‖ := by simp
    exact le_mul_of_one_le_right (norm_nonneg _) this
  · obtain ⟨B, hB⟩ := key b c hc
    refine ⟨B, fun z h1 h2 => le_trans ?_ (hB z h1 h2)⟩
    rw [norm_smul, mul_comm]
    have : ‖z‖ ≤ 1 + ‖z‖ := by simp
    gcongr

theorem differentiableOn_integral {T E : Type} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
    [BorelSpace T] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [SecondCountableTopology E] (μ : Measure T) [IsFiniteMeasure μ] {r : T → E} (hr : Continuous r)
    {ζ : ℂ → T → ℂ} (hζ : LeftFam ζ) :
    DifferentiableOn ℂ (fun z => ∫ κ, ζ z κ • r κ ∂μ) {z | z.re < 1 / 2} := by
  have hopen : IsOpen {z : ℂ | z.re < 1 / 2} := isOpen_lt Complex.continuous_re continuous_const
  intro z₀ hz₀
  have hz₀' : z₀.re < 1 / 2 := hz₀
  obtain ⟨ε, hε⟩ : ∃ ε, ε = (1 / 2 - z₀.re) / 4 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hball : ∀ w ∈ closedBall z₀ (2 * ε), w.re < 1 / 2 ∧ z₀.re - 2 * ε ≤ w.re ∧ w.re ≤ z₀.re + 2 * ε ∧
      ‖w‖ ≤ ‖z₀‖ + 2 * ε := by
    intro w hw
    have h1 : ‖w - z₀‖ ≤ 2 * ε := by simpa [dist_eq_norm] using hw
    have h2 : |(w - z₀).re| ≤ ‖w - z₀‖ := Complex.abs_re_le_norm _
    have h3 := abs_le.mp (h2.trans h1)
    have h4 : ‖w‖ ≤ ‖z₀‖ + ‖w - z₀‖ := by
      have := norm_add_le z₀ (w - z₀)
      simpa using this
    simp only [Complex.sub_re] at h3
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  have hsub : closedBall z₀ (2 * ε) ⊆ {z : ℂ | z.re < 1 / 2} := fun w hw => (hball w hw).1
  obtain ⟨M, hM⟩ := hζ.strip (z₀.re - 2 * ε) (z₀.re + 2 * ε) (by rw [hε]; linarith)
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = |M| * (1 + (‖z₀‖ + 2 * ε)) ^ 2 := ⟨_, rfl⟩
  have hbd : ∀ w ∈ closedBall z₀ (2 * ε), ∀ t, ‖ζ w t‖ ≤ B := by
    intro w hw t
    obtain ⟨-, h2, h3, h4⟩ := hball w hw
    refine (hM w h2 h3 t).trans ?_
    rw [hB]
    gcongr
    exact le_abs_self M
  obtain ⟨R, hR⟩ := isCompact_univ.exists_bound_of_continuousOn hr.continuousOn
  have hR' : ∀ t, ‖r t‖ ≤ R := fun t => hR t (Set.mem_univ t)
  have hcont : ∀ z : ℂ, z.re < 1 / 2 → Continuous (ζ z) := by
    intro z hz
    have h := hζ.cont.comp_continuous (f := fun t : T => (z, t)) (by fun_prop)
      (fun t => ⟨hz, Set.mem_univ t⟩)
    exact h
  have hmeasF : ∀ z : ℂ, z.re < 1 / 2 → AEStronglyMeasurable (fun κ => ζ z κ • r κ) μ := fun z hz =>
    ((hcont z hz).measurable.aestronglyMeasurable).smul hr.aestronglyMeasurable
  have hdiff : ∀ (t : T) (z : ℂ), z.re < 1 / 2 → HasDerivAt (ζ · t) (deriv (ζ · t) z) z := fun t z hz =>
    (((hζ.hol t) z hz).differentiableAt (hopen.mem_nhds hz)).hasDerivAt
  have hd0 : Measurable fun t => deriv (ζ · t) z₀ := by
    let h : ℕ → ℂ := fun n => ((ε / (n + 1) : ℝ) : ℂ)
    have hh0 : ∀ n, h n ≠ 0 := fun n => by
      have : ε / ((n : ℝ) + 1) ≠ 0 := by positivity
      exact Complex.ofReal_ne_zero.mpr this
    have hhs : ∀ n, z₀ + h n ∈ closedBall z₀ (2 * ε) := by
      intro n
      have h1 : ε / ((n : ℝ) + 1) ≤ ε := div_le_self hε0.le (by simp)
      have h2 : 0 ≤ ε / ((n : ℝ) + 1) := by positivity
      simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, h, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg h2]
      linarith
    have hlim : Tendsto h atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall hh0⟩
      have h1 : Tendsto (fun n : ℕ => ε / ((n : ℝ) + 1)) atTop (𝓝 0) := by
        have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ε
        simpa [div_eq_mul_inv] using h0
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
      simpa [h, Function.comp_def] using h2
    refine measurable_of_tendsto_metrizable
      (f := fun (n : ℕ) t => (h n)⁻¹ • (ζ (z₀ + h n) t - ζ z₀ t)) (fun n => ?_) ?_
    · have hc : Continuous fun t => (h n)⁻¹ • (ζ (z₀ + h n) t - ζ z₀ t) :=
        (continuous_const_smul (h n)⁻¹).comp
          (show Continuous fun t => ζ (z₀ + h n) t - ζ z₀ t from
            (hcont _ (hsub (hhs n))).sub (hcont _ hz₀'))
      exact hc.measurable
    · rw [tendsto_pi_nhds]
      intro t
      exact (hasDerivAt_iff_tendsto_slope_zero.mp (hdiff t z₀ hz₀')).comp hlim
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℂ)
    (F := fun z κ => ζ z κ • r κ) (F' := fun z κ => deriv (ζ · κ) z • r κ) (x₀ := z₀)
    (s := ball z₀ ε) (bound := fun _ => B / ε * R)
    (ball_mem_nhds z₀ hε0)
    (by
      filter_upwards [hopen.mem_nhds hz₀] with z hz using hmeasF z hz)
    (by
      refine Integrable.of_bound (hmeasF z₀ hz₀') (B * R) (Eventually.of_forall fun t => ?_)
      rw [norm_smul]
      have h1 := hbd z₀ (mem_closedBall_self (by positivity)) t
      have h0 : 0 ≤ B := (norm_nonneg _).trans h1
      exact mul_le_mul h1 (hR' t) (norm_nonneg _) h0)
    (hd0.aestronglyMeasurable.smul hr.aestronglyMeasurable)
    (Eventually.of_forall fun t z hz => by
      have hz' : dist z z₀ < ε := hz
      have hsph : closedBall z ε ⊆ closedBall z₀ (2 * ε) := by
        intro w hw
        have h1 : dist w z ≤ ε := hw
        have h2 := dist_triangle w z z₀
        show dist w z₀ ≤ 2 * ε
        linarith
      have hder : ‖deriv (ζ · t) z‖ ≤ B / ε :=
        Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hε0
          (((hζ.hol t).mono hsub).mono hsph |>.diffContOnCl_ball subset_rfl)
          (fun w hw => hbd w (hsph (sphere_subset_closedBall hw)) t)
      rw [norm_smul]
      exact mul_le_mul hder (hR' t) (norm_nonneg _) ((norm_nonneg _).trans hder))
    (integrable_const _)
    (Eventually.of_forall fun t z hz => by
      have hz' : z ∈ closedBall z₀ (2 * ε) := by
        have : dist z z₀ < ε := hz
        show dist z z₀ ≤ 2 * ε
        linarith
      exact (hdiff t z (hsub hz')).smul_const (r t))
  exact hmain.2.differentiableAt.differentiableWithinAt

theorem bGood : BGood := by
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hH hP ζ hζ
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  haveI : ProperSpace (W →L[ℂ] W) := FiniteDimensional.proper ℂ _
  haveI : IsProbabilityMeasure μ := hP
  obtain ⟨R, hR⟩ := (isCompact_univ (X := K)).exists_bound_of_continuousOn hρ.continuousOn
  refine leftGood_of (A := fun z => avg μ ρ (ζ z)) (differentiableOn_integral μ hρ hζ) ?_
  intro b c hc
  obtain ⟨M, hM⟩ := hζ.strip b c hc
  refine ⟨|M| * |R|, fun z h1 h2 => ?_⟩
  have hpt : ∀ κ : K, ‖ζ z κ • ρ κ‖ ≤ |M| * |R| * (1 + ‖z‖) ^ 2 := by
    intro κ
    rw [norm_smul]
    have h3 : ‖ζ z κ‖ ≤ |M| * (1 + ‖z‖) ^ 2 :=
      (hM z h1 h2 κ).trans (by gcongr; exact le_abs_self M)
    have h4 : ‖ρ κ‖ ≤ |R| := (hR κ (Set.mem_univ κ)).trans (le_abs_self R)
    calc ‖ζ z κ‖ * ‖ρ κ‖ ≤ (|M| * (1 + ‖z‖) ^ 2) * |R| :=
          mul_le_mul h3 h4 (norm_nonneg _) (by positivity)
      _ = |M| * |R| * (1 + ‖z‖) ^ 2 := by ring
  have := norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall hpt)
  simpa [avg] using this

end GlobalTheory.CompanionTheory.RgEisLeft
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BumpProfileEqZeroOfLtHalf
section
open PositivityTheory.RgEis PositivityTheory.RgEis.TF

noncomputable section

namespace GlobalTheory.CompanionTheory.TestFun

theorem contDiff_mul_of_vanish {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : E → ℝ} (hN : ContDiff ℝ (⊤ : ℕ∞) N) {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ0 : ∀ s, s < 1 / 2 → φ s = 0) {H : E → ℝ}
    (hH : ∀ y, 0 < N y → ContDiffAt ℝ (⊤ : ℕ∞) H y) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => φ (N y) * H y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : 0 < N y
  · exact (hφ.comp hN).contDiffAt.mul (hH y hy)
  · have hlt : N y < 1 / 2 := by linarith [not_lt.mp hy]
    have hev : ∀ᶠ z in nhds y, N z < 1 / 2 :=
      hN.continuous.continuousAt.eventually (gt_mem_nhds hlt)
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hev] with z hz
    simp [hφ0 _ hz]

def sqSum {ι : Type} [Fintype ι] (y : ι → ℝ) : ℝ := ∑ j, y j ^ 2

theorem sqSum_contDiff {ι : Type} [Fintype ι] : ContDiff ℝ (⊤ : ℕ∞) (sqSum (ι := ι)) := by
  unfold sqSum
  exact ContDiff.sum fun j _ => (contDiff_apply ℝ (fun _ => ℝ) j).pow 2

theorem sqSum_smul {ι : Type} [Fintype ι] (t : ℝ) (v : ι → ℝ) :
    sqSum (t • v) = t ^ 2 * sqSum v := by
  unfold sqSum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by simp [mul_pow]

theorem sq_le_sqSum {ι : Type} [Fintype ι] (y : ι → ℝ) (j : ι) : y j ^ 2 ≤ sqSum y := by
  unfold sqSum
  exact Finset.single_le_sum (f := fun j => y j ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)

theorem hasCompactSupport_of_sqSum {ι : Type} [Fintype ι] {F : (ι → ℝ) → ℝ}
    (h : ∀ y, 2 < sqSum y → F y = 0) : HasCompactSupport F := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ι → ℝ) 2) ?_
  intro y hy
  apply h
  have hn : (2 : ℝ) < ‖y‖ := by simpa [mem_closedBall_zero_iff] using hy
  have : ∃ j, 2 < |y j| := by
    by_contra hc
    push Not at hc
    have : ‖y‖ ≤ 2 := (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun j => by
      simpa [Real.norm_eq_abs] using hc j
    linarith
  obtain ⟨j, hj⟩ := this
  have h4 : (2 : ℝ) ^ 2 < y j ^ 2 := by
    rw [← sq_abs (y j)]
    exact pow_lt_pow_left₀ hj (by norm_num) (by norm_num)
  linarith [sq_le_sqSum y j]

def phi0 : ContDiffBump (1 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

theorem bumpProfile_one : phi0 1 = 1 :=
  phi0.one_of_mem_closedBall (by simp [phi0])

theorem bumpProfile_eq_zero_of_lt_half (s : ℝ) (hs : s < 1 / 2) : phi0 s = 0 := by
  refine phi0.zero_of_le_dist ?_
  show (1 / 2 : ℝ) ≤ dist s 1
  rw [Real.dist_eq, abs_sub_comm]
  exact le_trans (by linarith) (le_abs_self _)

theorem bumpProfile_eq_zero_of_two_lt (s : ℝ) (hs : 2 < s) : phi0 s = 0 := by
  refine phi0.zero_of_le_dist ?_
  show (1 / 2 : ℝ) ≤ dist s 1
  rw [Real.dist_eq]
  exact le_trans (by linarith) (le_abs_self _)

theorem bumpProfile_contDiff : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => phi0 s) := phi0.contDiff

def bumpAt (δ : ℝ) (hδ : 0 < δ) : ContDiffBump (1 : ℝ) :=
  ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩

theorem bumpAt_one (δ : ℝ) (hδ : 0 < δ) : bumpAt δ hδ 1 = 1 :=
  (bumpAt δ hδ).one_of_mem_closedBall (by simp [bumpAt]; linarith)

theorem bumpAt_ne (δ : ℝ) (hδ : 0 < δ) {s : ℝ} (h : bumpAt δ hδ s ≠ 0) : 1 - δ < s := by
  by_contra hc
  refine h ((bumpAt δ hδ).zero_of_le_dist ?_)
  show δ ≤ dist s 1
  rw [Real.dist_eq, abs_sub_comm]
  exact le_trans (by linarith [not_lt.mp hc]) (le_abs_self _)

def angular {ι : Type} [Fintype ι] (i₀ : ι) (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (y : ι → ℝ) : ℝ :=
  bumpAt δ hδ (y i₀ ^ 2 / sqSum y) * (y i₀ / Real.sqrt (sqSum y)) ^ m

theorem angular_contDiffAt {ι : Type} [Fintype ι] (i₀ : ι) (m : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (y : ι → ℝ) (hy : 0 < sqSum y) : ContDiffAt ℝ (⊤ : ℕ∞) (angular i₀ m δ hδ) y := by
  have hN : ContDiffAt ℝ (⊤ : ℕ∞) (sqSum (ι := ι)) y := sqSum_contDiff.contDiffAt
  have hc : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => y i₀) y := (contDiff_apply ℝ (fun _ => ℝ) i₀).contDiffAt
  have hq : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => y i₀ ^ 2 / sqSum y) y :=
    (hc.pow 2).div hN hy.ne'
  have hbc : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => bumpAt δ hδ s) := (bumpAt δ hδ).contDiff
  have hb : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => bumpAt δ hδ (y i₀ ^ 2 / sqSum y)) y :=
    ContDiff.comp_contDiffAt (g := fun s : ℝ => bumpAt δ hδ s)
      (f := fun y : ι → ℝ => y i₀ ^ 2 / sqSum y) y hbc hq
  have hs : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => Real.sqrt (sqSum y)) y := hN.sqrt hy.ne'
  exact hb.mul ((hc.div hs (Real.sqrt_pos.2 hy).ne').pow m)

def bigF {ι : Type} [Fintype ι] (i₀ : ι) (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (y : ι → ℝ) : ℝ :=
  phi0 (sqSum y) * angular i₀ m δ hδ y

def smallF (m : ℕ) (t : ℝ) : ℝ := phi0 (t ^ 2) * (t / Real.sqrt (t ^ 2)) ^ m

theorem smallF_contDiff (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (smallF m) := by
  refine contDiff_mul_of_vanish (N := fun t : ℝ => t ^ 2) (contDiff_id.pow 2) bumpProfile_contDiff
    bumpProfile_eq_zero_of_lt_half (H := fun t => (t / Real.sqrt (t ^ 2)) ^ m) ?_
  intro y hy
  have hN : ContDiffAt ℝ (⊤ : ℕ∞) (fun t : ℝ => t ^ 2) y := (contDiff_id.pow 2).contDiffAt
  exact (contDiffAt_id.div (hN.sqrt hy.ne') (Real.sqrt_pos.2 hy).ne').pow m

theorem smallF_compact (m : ℕ) : HasCompactSupport (smallF m) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) 2) ?_
  intro t ht
  have hn : (2 : ℝ) < |t| := by simpa [mem_closedBall_zero_iff] using ht
  have h4 : (2 : ℝ) ^ 2 < t ^ 2 := by
    rw [← sq_abs t]
    exact pow_lt_pow_left₀ hn (by norm_num) (by norm_num)
  simp [smallF, bumpProfile_eq_zero_of_two_lt (t ^ 2) (by linarith)]

theorem bigF_unit {ι : Type} [Fintype ι] (i₀ : ι) (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (v : ι → ℝ)
    (hv : sqSum v = 1) : bigF i₀ m δ hδ v = bumpAt δ hδ (v i₀ ^ 2) * v i₀ ^ m := by
  simp [bigF, angular, hv, bumpProfile_one]

theorem bigF_smul {ι : Type} [Fintype ι] (i₀ : ι) (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (v : ι → ℝ)
    (hv : sqSum v = 1) (t : ℝ) :
    bigF i₀ m δ hδ (t • v) = smallF m t * bigF i₀ m δ hδ v := by
  rw [bigF_unit i₀ m δ hδ v hv]
  have hN : sqSum (t • v) = t ^ 2 := by rw [sqSum_smul, hv, mul_one]
  by_cases ht : t = 0
  · subst ht
    have h0 : sqSum (0 : ι → ℝ) = 0 := by simp [sqSum]
    simp [bigF, smallF, h0, bumpProfile_eq_zero_of_lt_half 0 (by norm_num)]
  · have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
    have hq : (t • v) i₀ ^ 2 / sqSum (t • v) = v i₀ ^ 2 := by
      rw [hN, Pi.smul_apply, smul_eq_mul, mul_pow]
      field_simp
    have hr : (t • v) i₀ / Real.sqrt (sqSum (t • v)) = t / Real.sqrt (t ^ 2) * v i₀ := by
      rw [hN, Pi.smul_apply, smul_eq_mul]
      ring
    simp only [bigF, angular, smallF]
    rw [hq, hr, hN, mul_pow]
    ring

theorem realBump : RealBump := by
  intro ι _ _ i₀ m δ hδ
  have hone : sqSum (Pi.single i₀ (1 : ℝ) : ι → ℝ) = 1 := by
    unfold sqSum
    rw [Finset.sum_eq_single i₀]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  refine ⟨bigF i₀ m δ hδ, smallF m, ?_, ?_, smallF_contDiff m, smallF_compact m, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_mul_of_vanish sqSum_contDiff bumpProfile_contDiff bumpProfile_eq_zero_of_lt_half
      (angular_contDiffAt i₀ m δ hδ)
  · refine hasCompactSupport_of_sqSum fun y hy => ?_
    simp [bigF, bumpProfile_eq_zero_of_two_lt _ hy]
  · rw [bigF_unit i₀ m δ hδ _ hone]
    simp [bumpAt_one]
  · simp [smallF, bumpProfile_one]
  · intro t ht
    refine mul_nonneg phi0.nonneg (pow_nonneg (div_nonneg ht (Real.sqrt_nonneg _)) m)
  · intro t
    simp only [smallF, neg_sq, neg_div, neg_pow t]
    ring_nf
  · intro v hv
    have hv' : sqSum v = 1 := hv
    refine ⟨bigF_smul i₀ m δ hδ v hv', ?_, ?_⟩
    · intro h
      rw [bigF_unit i₀ m δ hδ v hv'] at h
      exact bumpAt_ne δ hδ (left_ne_zero_of_mul h)
    · intro h
      rw [bigF_unit i₀ m δ hδ v hv']
      exact mul_nonneg (bumpAt δ hδ).nonneg (pow_nonneg h.le m)

end GlobalTheory.CompanionTheory.TestFun
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentsOfPrimePowerRootOfUnityStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotents_of_prime_power_root_of_unity : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), R.Val (l : A.U) → ∀ (n : ℕ) (ζ : OC l), IsPrimitiveRoot ζ (l ^ n) → ∀ z : A.U, z ^ l ^ n = 1 → ∃ e : ZMod (l ^ n) → A.A, (haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩; CompleteOrthogonalIdempotents e) ∧ ∀ c, A.sharp (e c) * (z - A.oC ζ ^ c.val) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RootsLC.exists_idempotents_of_root_of_unity | exact GlobalTheory.CompanionTheory.RootsLC.exists_idempotents_of_root_of_unity | (intros; apply GlobalTheory.CompanionTheory.RootsLC.exists_idempotents_of_root_of_unity <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzExistsRealMajorant
section
open scoped SchwartzMap

namespace GlobalTheory.CompanionTheory.SchwartzMaj

theorem exists_nonneg_schwartz_majorant (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : SchwartzMap E ℂ) :
    ∃ F : SchwartzMap E ℂ, ∀ x, (F x).im = 0 ∧ ‖f x‖ ≤ (F x).re := by
  obtain ⟨Φ, r, hΦ, hr⟩ := GlobalTheory.CompanionTheory.EisRk1.exists_schwartz_majorant f
  refine ⟨Φ, fun x => ?_⟩
  rw [hΦ x]
  exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; exact hr x⟩

end GlobalTheory.CompanionTheory.SchwartzMaj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaCIntNeg
section
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.AdelicThetaSeries

theorem thetaC_neg {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : (ι → 𝔸[k]) → ℂ) (h : GL ι 𝔸[k]) :
    thetaC (fun x ↦ F (-x)) h = thetaC F h := by
  unfold thetaC
  rw [← (Equiv.neg (ι → k)).tsum_eq (fun ξ => F ((h : Matrix ι ι 𝔸[k]) *ᵥ ratV ξ))]
  refine tsum_congr fun ξ => ?_
  have hr : ratV (-ξ) = -ratV ξ := by
    funext i
    simp [ratV]
  simp only [Equiv.neg_apply, hr, Matrix.mulVec_neg]

theorem thetaCInt_neg : ∀ {k : Type} [Field k] [NumberField k], ∀ {ι : Type} [Fintype ι]
    [DecidableEq ι], ∀ (w : InfinitePlace k) (F : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k),
    thetaCInt w (fun x ↦ F (-x)) ω = thetaCInt w F ω := by
  intro k _ _ ι _ _ w F ω
  funext t
  unfold thetaCInt
  simp only [thetaC_neg]

end GlobalTheory.CompanionTheory.AdelicThetaSeries
end

