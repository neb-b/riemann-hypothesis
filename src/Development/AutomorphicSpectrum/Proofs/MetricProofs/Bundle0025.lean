module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0023
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle0004
public import ReciprocityTheory.AnalyticForms.LeviForms.RegChartC
public import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalLeviPshRegularization
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizationGlueC2Explicit
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RefineAdaptedAtlasWithGradient
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0021
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothOnOfChartLeviNonneg
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0024
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SiegelOfRiemann
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SymplecticPolydiscPeriodBasis
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import Development.WeilBound.CoreStatements.PluriharmonicCharts.XPerInt

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ContinuousHermitianMatrixFamilyStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_hermitian_matrix_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (X : Type) [TopologicalSpace X] (R : X → RiemLat E g Λ) (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ), (∀ x, (R x).form = form) → (∀ v, Continuous fun x => (R x).P v) → Continuous fun x => (R x).Hm := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.continuous_Hm | exact GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.continuous_Hm | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.HmCont.continuous_Hm <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsExtendLinearIndependentOfSpanStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extend_linearIndependent_of_span : ∀ (g m r : ℕ) (w : Fin r → Fin g → ℂ) (b : Fin m → Fin g → ℂ), LinearIndependent ℂ w → LinearIndependent ℂ b → (∀ a, w a ∈ Submodule.span ℂ (Set.range b)) → ∃ (k : ℕ) (J : Fin k → Fin m), r + k = m ∧ LinearIndependent ℂ (Fin.append w (fun j => b (J j))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Exchange.exists_completion_by_members | exact GlobalTheory.CompanionTheory.Ar.Exchange.exists_completion_by_members | (intros; apply GlobalTheory.CompanionTheory.Ar.Exchange.exists_completion_by_members <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GlobalRegularizationStatementHolds
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem regGlobalStatement_holds : RegGlobalStatement := by
  intro e X _ _ _ A B Θ L s n m W hΘ hΘpos hL hS hSNC hs hAd th ph C₅ hSW hGB
  obtain ⟨B', x, hAd', hGB', hsrc⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Giv.refine_adapted_atlas A B L th s ph C₅ hs hAd hGB
  obtain ⟨hAB, h2, hcov, M, hM⟩ := hAd'
  choose S mm hm1 hbd hrl using hM
  have hcl : IsClosed (bdry s) := LeviFormBoundaryTopology.isClosed_bdry hS
  obtain ⟨hth, hphs, hpsh, hb⟩ := hSW
  obtain ⟨C₅', hC₅'0, hconv⟩ := _root_.GlobalTheory.CompanionTheory.Metric.BoundConv.bound_conv C₅ M
  obtain ⟨hlogd, hmono, hle, htend, hsmall, hmin⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.epsT_numerics
  have hrWge : ∀ y, Real.exp 1 ≤ rW L s y := rW_ge L s hs
  have h2le : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hball : ∀ j, ∀ z ∈ ball (0 : Fin e → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv (S j),
      z ∈ (B'.chart j).target ∧ (B'.chart j).symm z ∉ bdry s := by
    intro j z hz
    have hzt : z ∈ (B'.chart j).target := h2 j (ball_subset_closedBall hz.1)
    exact ⟨hzt, fun hzb => hz.2 ((hbd j z hzt).1 hzb)⟩
  have hq : ∀ j, ContDiffOn ℝ ∞ (fun z => th.φ (x j) ((B'.chart j).symm z)) (ball (0 : Fin e → ℂ) 2) :=
    fun j => (smoothOn_of_compatible hAB (th.isOpen_U (x j)) (hth.1 (x j)) j).mono fun z hz =>
      ⟨h2 j (ball_subset_closedBall hz),
        hsrc j ((B'.chart j).map_target (h2 j (ball_subset_closedBall hz)))⟩
  have hphj : ∀ j, ContDiffOn ℝ ∞ (ph ∘ (B'.chart j).symm)
      (ball (0 : Fin e → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv (S j)) :=
    fun j => (smoothOn_of_compatible hAB hcl.isOpen_compl hphs j).mono fun z hz => hball j z hz
  have hlevi : ∀ j, ReciprocityTheory.AnForm.A.IsLeviPsh (ball (0 : Fin e → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv (S j))
      (fun z => (fun z => th.φ (x j) ((B'.chart j).symm z)) z + (ph ∘ (B'.chart j).symm) z) := by
    intro j
    refine ⟨(((hq j).mono Set.diff_subset).add (hphj j)).of_le h2le, fun z hz w => ?_⟩
    exact _root_.GlobalTheory.CompanionTheory.LeviChart.levi_nonneg_of_compat_fixedBase A B' th ph (bdry s)ᶜ (x j) j hAB hth hcl.isOpen_compl hphs hpsh (hsrc j) z (hball j z hz) w
  have hbnd : ∀ j, ∀ z ∈ ball (0 : Fin e → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv (S j),
      -C₅' * Real.log (rLoc (S j) (mm j) z) ≤ (ph ∘ (B'.chart j).symm) z ∧
        (ph ∘ (B'.chart j).symm) z ≤ C₅' := by
    intro j z hz
    obtain ⟨-, hzb⟩ := hball j z hz
    have hr := hrl j z (ball_subset_closedBall hz.1) hzb
    have hrl' := RegularChartScaling.rLoc_ge (S j) (mm j) (RegularChartScaling.norm_coord_le_of_ball le_rfl hz.1)
    exact (hconv _ _ (ph ((B'.chart j).symm z)) 0 (hrWge _) hrl' hr).1 (hb _ hzb).1 (hb _ hzb).2
  have hgrad : ∀ j, ∀ z ∈ ball (0 : Fin e → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv (S j),
      ‖fderiv ℝ (ph ∘ (B'.chart j).symm) z‖ ≤
        C₅' * rLoc (S j) (mm j) z ^ C₅' * Real.exp (rLoc (S j) (mm j) z / 2) := by
    intro j z hz
    have hz2 : z ∈ ball (0 : Fin e → ℂ) 2 \ ReciprocityTheory.AnForm.A.coordDiv (S j) :=
      ⟨ball_subset_ball (by norm_num) hz.1, hz.2⟩
    obtain ⟨-, hzb⟩ := hball j z hz2
    have hr := hrl j z (ball_subset_closedBall hz2.1) hzb
    have hrl' := RegularChartScaling.rLoc_ge (S j) (mm j) (RegularChartScaling.norm_coord_le_of_ball le_rfl hz2.1)
    exact (hconv _ _ 0 _ (hrWge _) hrl' hr).2 (hGB' j z hz.1 hzb)
  have hch := fun j => _root_.GlobalTheory.CompanionTheory.Ar.Giv.regularise_one_chart e (S j) (mm j) (fun z => th.φ (x j) ((B'.chart j).symm z))
    (ph ∘ (B'.chart j).symm) C₅' M (hm1 j) (hq j) (hphj j) (hlevi j) (hbnd j) (hgrad j)
  choose Cj tj g hCj1 htj0 htje hgt hgC2 using hch

  obtain ⟨C', t', ht'0, hcmp⟩ := GlobalTheory.T.glued_local_regularizations_on_atlas A B' L th s ph C₅ M x S mm hAB h2 hsrc hs hcl hbd hrl
    ⟨hth, hphs, hpsh, hb⟩
  set Cm : ℝ := 1 + ∑ j, |Cj j| with hCmdef
  have hCm : ∀ j, Cj j ≤ Cm := fun j => by
    have h1 := Finset.single_le_sum (f := fun j => |Cj j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    have h2' := le_abs_self (Cj j)
    linarith
  have hCm1 : 1 ≤ Cm := by
    have : 0 ≤ ∑ j, |Cj j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  set Cl : ℝ := |C'| + Cm with hCldef
  have hCl1 : 1 ≤ Cl := by have := abs_nonneg C'; linarith
  have hClj : ∀ j, Cj j ≤ Cl := fun j => by have := abs_nonneg C'; linarith [hCm j]
  obtain ⟨a, ha0, ha⟩ := hsmall Cl
  obtain ⟨tm, htm0, htm⟩ := hmin B'.n tj htj0
  set t₀ : ℝ := min (min tm t') (min a (Real.exp (-Real.exp 1))) with ht₀def
  have ht₀0 : 0 < t₀ := lt_min (lt_min htm0 ht'0) (lt_min ha0 (Real.exp_pos _))
  have ht₀j : ∀ j, t₀ ≤ tj j := fun j => ((min_le_left _ _).trans (min_le_left _ _)).trans (htm j)
  have ht₀' : t₀ ≤ t' := (min_le_left _ _).trans (min_le_right _ _)
  have ht₀a : t₀ ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have ht₀e : t₀ ≤ Real.exp (-Real.exp 1) := (min_le_right _ _).trans (min_le_right _ _)
  have hLL : ∀ t, 0 < t → t ≤ t₀ → 0 ≤ Real.log (Real.log (1 / t)) := fun t ht htt => by
    have := (log_inv_bounds ht (htt.trans ht₀e)).2; linarith

  have hy54 : ∀ j, ∀ y ∈ chartBall B' j (5 / 4), B'.chart j y ∈ ball (0 : Fin e → ℂ) (5 / 4) ∧
      B'.chart j y ∈ closedBall (0 : Fin e → ℂ) 2 ∧ (B'.chart j).symm (B'.chart j y) = y := by
    intro j y hy
    exact ⟨hy.2, ball_subset_closedBall (ball_subset_ball (by norm_num) hy.2), (B'.chart j).left_inv hy.1⟩
  have hsand : ∀ t, 0 < t → t ≤ t₀ → ∀ j, ∀ y ∈ chartBall B' j (5 / 4),
      polyMaxOff (S j) (fun z => th.φ (x j) ((B'.chart j).symm z) + ph ((B'.chart j).symm z))
          (B'.chart j y) t - epsT (Cj j) t ≤ th.φ (x j) y + g j t (B'.chart j y) ∧
        th.φ (x j) y + g j t (B'.chart j y) ≤ polyMaxOff (S j)
          (fun z => th.φ (x j) ((B'.chart j).symm z) + ph ((B'.chart j).symm z)) (B'.chart j y) t := by
    intro t ht htt j y hy
    obtain ⟨hz, -, hsy⟩ := hy54 j y hy
    have h := ((hgt j t ht (htt.trans (ht₀j j))).2.2.2.2.1 (B'.chart j y) hz)
    have h' : polyMaxOff (S j) (fun z => th.φ (x j) ((B'.chart j).symm z) + ph ((B'.chart j).symm z))
          (B'.chart j y) t - epsT (Cj j) t ≤ th.φ (x j) ((B'.chart j).symm (B'.chart j y)) + g j t (B'.chart j y) ∧
        th.φ (x j) ((B'.chart j).symm (B'.chart j y)) + g j t (B'.chart j y) ≤ polyMaxOff (S j)
          (fun z => th.φ (x j) ((B'.chart j).symm z) + ph ((B'.chart j).symm z)) (B'.chart j y) t := h
    rw [hsy] at h'
    exact h'
  have hloc : ∀ t, 0 < t → t ≤ t₀ → ∀ j, ∀ y ∈ chartBall B' j (5 / 4),
      (g j t ∘ B'.chart j) y ≤ Cl ∧ -Cl * Real.log (Real.log (1 / t)) ≤ (g j t ∘ B'.chart j) y ∧
        (y ∉ bdry s → ph y ≤ (g j t ∘ B'.chart j) y ∧
          (rW L s y ≤ Real.log (1 / t) → (g j t ∘ B'.chart j) y ≤ ph y + t ^ ((1 : ℝ) / 3))) := by
    intro t ht htt j y hy
    obtain ⟨hz, hz2, hsy⟩ := hy54 j y hy
    obtain ⟨-, -, hgb, hgn, -, -⟩ := hgt j t ht (htt.trans (ht₀j j))
    obtain ⟨hb1, hb2⟩ := hgb _ hz
    have hll := hLL t ht htt
    refine ⟨hb1.trans (hClj j), le_trans ?_ hb2, fun hyb => ?_⟩
    · have := mul_le_mul_of_nonneg_right (hClj j) hll
      show -Cl * _ ≤ -Cj j * _
      linarith
    · have hzt : B'.chart j y ∈ (B'.chart j).target := h2 j hz2
      have hzc : B'.chart j y ∉ ReciprocityTheory.AnForm.A.coordDiv (S j) := fun hc =>
        hyb (hsy ▸ (hbd j _ hzt).2 hc)
      obtain ⟨hn1, hn2⟩ := hgn _ ⟨hz, hzc⟩
      have hr := hrl j _ hz2 (by rw [hsy]; exact hyb)
      rw [hsy] at hr
      simp only [Function.comp_apply, hsy] at hn1 hn2 ⊢
      refine ⟨hn1, fun hrw => hn2 ?_⟩
      have := (abs_le.1 hr).1
      linarith
  have hmono' : ∀ t t', 0 < t → t ≤ t' → t' ≤ t₀ → ∀ j, ∀ y ∈ chartBall B' j (5 / 4),
      (g j t ∘ B'.chart j) y ≤ (g j t' ∘ B'.chart j) y + epsT Cl t' := by
    intro t t'' ht htt' ht'' j y hy
    obtain ⟨hz, -, -⟩ := hy54 j y hy
    have h := (hgt j t ht ((htt'.trans ht'').trans (ht₀j j))).2.2.2.2.2 t'' htt' (ht''.trans (ht₀j j)) _ hz
    have := epsT_le_epsT (hClj j) (ht.trans_le htt') (ht''.trans ht₀e)
    simp only [Function.comp_apply]
    linarith

  obtain ⟨K, hK0, hgl⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Giv.regularization_glue_C2 A B' Θ th s ph hAB hcov h2 hΘ hΘpos hth hcl hphs
  have hback : ∀ t, 0 < t → t ≤ t₀ → ∀ j, A.SmoothOn (chartBall B' j (5 / 4)) (g j t ∘ B'.chart j) ∧
      IsPshOn A (chartBall B' j (5 / 4)) (th + LocPot.ofFun (g j t ∘ B'.chart j)) := by
    intro t ht htt j
    obtain ⟨hgs, hglevi, -⟩ := hgt j t ht (htt.trans (ht₀j j))
    exact _root_.GlobalTheory.CompanionTheory.Metric.PshBack.smoothOn_isPshOn_chartBack A B' th (x j) j (ball (0 : Fin e → ℂ) (5 / 4)) (g j t) hAB hth (hsrc j) isOpen_ball
      (fun z hz => h2 j (ball_subset_closedBall (ball_subset_ball (by norm_num) hz))) hgs hglevi.2
  have hov : ∀ t, 0 < t → t ≤ t₀ → ∀ j k, ∀ y ∈ chartBall B' j (5 / 4) ∩ chartBall B' k (5 / 4),
      |(g j t ∘ B'.chart j) y - (g k t ∘ B'.chart k) y| ≤ epsT Cl t := by
    intro t ht htt j k y hy
    obtain ⟨sj1, sj2⟩ := hsand t ht htt j y hy.1
    obtain ⟨sk1, sk2⟩ := hsand t ht htt k y hy.2
    have hc := abs_le.1 (hcmp t ht (htt.trans ht₀') j k y hy)
    have hte := htt.trans ht₀e
    have e1 := epsT_le_epsT (hCm j) ht hte
    have e2 := epsT_le_epsT (hCm k) ht hte
    have e3 := epsT_le_epsT (le_abs_self C') ht hte
    have e4 : epsT Cl t = epsT |C'| t + epsT Cm t := by
      simp only [hCldef, epsT]; ring
    simp only [Function.comp_apply]
    rw [abs_le]
    constructor <;> linarith [hc.1, hc.2]
  obtain ⟨F, hF, hFC2⟩ := hgl t₀ (epsT Cl) (fun t j => g j t ∘ B'.chart j) ht₀0 (htend Cl)
    (fun t ht htt => ⟨hle Cl t hCl1 ht (htt.trans ht₀e), ha t ht (htt.trans ht₀a),
      fun j => (hback t ht htt j).1,
      ⟨Cl + Cl * Real.log (Real.log (1 / t)), fun j y hy => by
        obtain ⟨h1, h2', -⟩ := hloc t ht htt j y hy
        have := mul_nonneg (by linarith : (0 : ℝ) ≤ Cl) (hLL t ht htt)
        rw [abs_le]; constructor <;> linarith⟩,
      fun j => (hback t ht htt j).2, hov t ht htt⟩)
    (fun j K' hK' hK'c => by
      have hsub : K' ⊆ ball (0 : Fin e → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv (S j) := by
        intro z hz
        have hzt : z ∈ (B'.chart j).target :=
          h2 j (ball_subset_closedBall (ball_subset_ball (by norm_num) (hK' hz).1))
        exact ⟨(hK' hz).1, fun hc => (hK' hz).2 ((hbd j z hzt).2 hc)⟩
      exact _root_.GlobalTheory.CompanionTheory.Metric.ChartPullBack.C2_tendsto_chart_pullback (B'.chart j) (g j) (ph ∘ (B'.chart j).symm) K'
        (fun z hz => h2 j (ball_subset_closedBall (ball_subset_ball (by norm_num) (hK' hz).1)))
        (hgC2 j K' hsub hK'c))
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.CompanionTheory.Ar.RegFin.isRegFamily_of_glue A B' Θ L th s ph C₅ K Cl t₀ (fun t j => g j t ∘ B'.chart j) F hΘ hΘpos hth hs hcov
    (fun y hy => (hb y hy).1) hK0 hCl1 ht₀0 ht₀e hF hloc hmono'
  exact ⟨C, t₀, F, hC, hFC2⟩

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicLocalQuotientMapStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_local_quotient_map : ∀ (g' k g n : ℕ) (U : Set (Fin n → ℂ)) (e : Fin k → (Fin n → ℂ) → Fin g → ℂ) (t₀ : Fin n → ℂ), IsOpen U → t₀ ∈ U → k + g' = g → (∀ i, DifferentiableOn ℂ (e i) U) → LinearIndependent ℂ (fun i => e i t₀) → ∃ V : Set (Fin n → ℂ), IsOpen V ∧ t₀ ∈ V ∧ V ⊆ U ∧ ∃ q : (Fin n → ℂ) → (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ), (∀ x, DifferentiableOn ℂ (fun t => q t x) V) ∧ ∀ t ∈ V, Function.Surjective (q t) ∧ LinearMap.ker (q t) = Submodule.span ℂ (Set.range fun i => e i t) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.QuotHol.exists_holomorphic_quotient | exact GlobalTheory.CompanionTheory.Metric.QuotHol.exists_holomorphic_quotient | (intros; apply GlobalTheory.CompanionTheory.Metric.QuotHol.exists_holomorphic_quotient <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasurableCuspWeightFamilyStatement
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_cusp_weight_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (X : Type) [MeasurableSpace X] (R : X → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ), (∀ x, (R x).form = form) → (∀ I, Measurable fun x => (R x).nz σ I) → (∀ x, BddAbove {y | ∃ I, (R x).IsCusp I ∧ y = -Real.log ((R x).nz σ I)}) → Measurable fun x => (R x).cuspW σ := by
  intro E _ _ _ g Λ _ _ Ψ _ X _ R σ form hform hnz _
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact measurable_of_empty _
  have : Module.Free ℤ Λ := (R x₀).free
  have : Module.Finite ℤ Λ := (R x₀).fin
  have : Countable (Submodule (𝓞 E) Λ) := by
    have : Countable Λ :=
      (Module.finBasis ℤ Λ).equivFun.toEquiv.injective.countable
    have : Countable (Submodule ℤ Λ) := by
      have hspan : Function.Surjective (fun s : Finset Λ => Submodule.span ℤ (s : Set Λ)) := by
        intro N
        obtain ⟨s, hs⟩ := (IsNoetherian.noetherian N : N.FG)
        exact ⟨s, hs⟩
      exact hspan.countable
    exact (Submodule.restrictScalars_injective ℤ (𝓞 E) Λ).countable
  let C : Submodule (𝓞 E) Λ → Prop := fun I =>
    I ≠ ⊥ ∧ GroundTheory.Heights₂.Heights.LowerBoundFree.IsSaturated I ∧
      GroundTheory.Heights₂.Heights.LowerBoundFree.IsIsoSub form I
  have hC (x : X) (I : Submodule (𝓞 E) Λ) : (R x).IsCusp I ↔ C I := by
    simp only [RiemLat.IsCusp, C, hform x]
  have hset (x : X) : {y | ∃ I, (R x).IsCusp I ∧ y = -Real.log ((R x).nz σ I)} =
      Set.range fun I : {I // C I} => -Real.log ((R x).nz σ I.1) := by
    ext y
    constructor
    · rintro ⟨I, hI, rfl⟩
      exact ⟨⟨I, (hC x I).1 hI⟩, rfl⟩
    · rintro ⟨I, rfl⟩
      exact ⟨I.1, (hC x I.1).2 I.2, rfl⟩
  have hsup : Measurable fun x => ⨆ I : {I // C I}, -Real.log ((R x).nz σ I.1) :=
    Measurable.iSup fun I => (Real.measurable_log.comp (hnz I.1)).neg
  have heq : (fun x => (R x).cuspW σ) =
      fun x => max 0 (⨆ I : {I // C I}, -Real.log ((R x).nz σ I.1)) := by
    funext x
    simp only [RiemLat.cuspW, hset x, iSup]
  rw [heq]
  exact measurable_const.max hsup
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereDifferenceTendstoZero
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem an_two_weights_close : ConvergenceSignedStatement → ∀ (e : ℕ) (σ : Type) (S : AnSys e (σ ⊕ σ)) (d : σ → S.X → ℝ), (∀ a, S.A.Smooth (d a)) → (∀ a, ∀ y ∈ S.open', S.ph (Sum.inl a) y = S.ph (Sum.inr a) y + d a y) → ∀ (a : σ) (w : Fin e → σ ⊕ σ), Tendsto (fun t => mInt S.A (fun i => S.potT (w i) t) (fun x => S.phT (Sum.inl a) t x - S.phT (Sum.inr a) t x - d a x)) (𝓝[>] 0) (𝓝 0) :=
  @PositivityTheory.Xgp.t_an_two

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.NormDegreeStepZero
section
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Decomp

theorem normDegree_step_zero {K : Type} [Field K] [NumberField K] {E : HermitianBundle.{0} K} {r : ℕ}
    (A : SatFlag E r) : E.normDegree (A.F 0) = 0 := by
  have h : A.F 0 = ⊥ := (Submodule.finrank_eq_zero (R := 𝓞 K) (S := A.F 0)).mp (A.rank 0)
  rw [HermitianBundle.normDegree, h, HermitianBundle.degree_bot, zero_div]

theorem lamDeg_eq : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (Ψ : Type) [Fintype Ψ] (j k : ℕ) (A : FlagPair E Ψ (j + 1) (k + 1)) (lam : Ψ → Fin (j + 1 + (k + 1)) → ℝ), A.lamDeg lam = ∑ τ, ((∑ i : Fin j, (lam τ (Fin.castAdd (k + 1) i.castSucc) - lam τ (Fin.castAdd (k + 1) i.succ)) * (-E.normDegree ((A.W τ).F i.succ.castSucc))) + (lam τ (Fin.castAdd (k + 1) (Fin.last j)) - lam τ (Fin.natAdd (j + 1) 0)) * (-E.normDegree (A.W τ).top) + (∑ i : Fin k, (lam τ (Fin.natAdd (j + 1) i.castSucc) - lam τ (Fin.natAdd (j + 1) i.succ)) * (-E.normDegree ((A.S τ).F i.rev.succ.castSucc))) - lam τ (Fin.natAdd (j + 1) 0) * A.flatDeg τ) := by
  intro K _ _ E Ψ _ j k A lam
  unfold FlagPair.lamDeg
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hW := GlobalTheory.CompanionTheory.AbelFlag.abel_summation_flag j (fun i => lam τ (Fin.castAdd (k + 1) i))
    (fun i => E.normDegree ((A.W τ).F i)) (normDegree_step_zero (A.W τ))
  have hS := GlobalTheory.CompanionTheory.DualFlag.abel_sum_rev k (fun i => lam τ (Fin.natAdd (j + 1) i))
    (fun i => E.normDegree ((A.S τ).F i)) (normDegree_step_zero (A.S τ))
  simp only [SatFlag.grDeg, FlagPair.flatDeg, SatFlag.top]
  linear_combination hW + hS

end GlobalTheory.CompanionTheory.Ar.Decomp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeLeRankMulSlope
section
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.DegSlope

private lemma degreeWith_bot {K : Type} [Field K] [NumberField K] (E : HermitianBundle.{0} K)
    {r : ℕ} (f : Fin r → ↥(⊥ : Submodule (𝓞 K) E.carrier)) : E.degreeWith ⊥ f = 0 := by
  unfold HermitianBundle.degreeWith
  have h0 : ∀ i, ((f i : E.carrier)) = 0 := fun i => (Submodule.mem_bot _).1 (f i).2
  have hcard : Nat.card (↥(⊥ : Submodule (𝓞 K) E.carrier) ⧸ Submodule.span (𝓞 K) (Set.range f)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Quotient.inductionOn₂' a b (fun x y => congrArg _ (Subsingleton.elim x y))⟩, ⟨0⟩⟩
  have hdet : ∀ σ : K →+* ℂ, Real.log ‖E.gramDet σ (fun i => ((f i : E.carrier)))‖ = 0 := by
    intro σ
    unfold HermitianBundle.gramDet
    simp only [h0, TensorProduct.tmul_zero, inner_zero_left]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp
    · haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
      have hc : (@inner ℂ _ (E.metric.form σ).toInner (0 : Fibre σ E.carrier) (0 : Fibre σ E.carrier)) = 0 := by
        have h : @inner ℂ _ (E.metric.form σ).toInner ((0 : Fibre σ E.carrier) + 0) 0 =
            @inner ℂ _ (E.metric.form σ).toInner (0 : Fibre σ E.carrier) 0 +
              @inner ℂ _ (E.metric.form σ).toInner (0 : Fibre σ E.carrier) 0 :=
          (E.metric.form σ).add_left 0 0 0
        rw [add_zero] at h
        linear_combination -h
      have hdet0 : (Matrix.of fun (_ : Fin r) (_ : Fin r) =>
          (@inner ℂ _ (E.metric.form σ).toInner (0 : Fibre σ E.carrier) (0 : Fibre σ E.carrier))).det = 0 := by
        rw [show (Matrix.of fun (_ : Fin r) (_ : Fin r) =>
            (@inner ℂ _ (E.metric.form σ).toInner (0 : Fibre σ E.carrier) (0 : Fibre σ E.carrier))) = 0 from
          Matrix.ext fun _ _ => hc]
        exact Matrix.det_zero
      have hgoal : Real.log ‖(Matrix.of fun (_ : Fin r) (_ : Fin r) =>
          (@inner ℂ _ (E.metric.form σ).toInner (0 : Fibre σ E.carrier) (0 : Fibre σ E.carrier))).det‖ = 0 := by
        rw [hdet0, norm_zero, Real.log_zero]
      exact hgoal
  rw [hcard]
  simp [hdet]

theorem normDegree_le_rank_mul_of_slopeMax_le : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (μ : ℝ), E.slopeMax ≤ (μ : EReal) → ∀ F : Submodule (𝓞 K) E.carrier, E.normDegree F ≤ E.rank F * μ := by
  intro K _ _ E μ hμ F
  by_cases hF : F = ⊥
  · subst hF
    have hr : E.rank ⊥ = 0 := by
      simp [HermitianBundle.rank]
    rw [hr, Nat.cast_zero, zero_mul]
    unfold HermitianBundle.normDegree HermitianBundle.degree
    rw [degreeWith_bot, zero_div]
  · have hpos : 0 < E.rank F := by
      unfold HermitianBundle.rank
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hF
      exact Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨x, hx⟩, by simpa using hx0⟩
    have h1 : (E.slope F : EReal) ≤ E.slopeMax :=
      le_iSup₂ (f := fun G (_ : G ≠ ⊥) => (E.slope G : EReal)) F hF
    have h2 : E.slope F ≤ μ := EReal.coe_le_coe_iff.1 (h1.trans hμ)
    unfold HermitianBundle.slope at h2
    rw [div_le_iff₀ (by exact_mod_cast hpos)] at h2
    linarith

end GlobalTheory.CompanionTheory.Ar.DegSlope
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PeriodMatrixLocalTrivialization
section
open Matrix Metric GroundTheory.Heights₂.Heights.Regular GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_periodPolydisc_frame : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : LogPeriods n a g Λ), ∃ (Q : PeriodPolydisc n a g) (A : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), (∀ i j, DifferentiableOn ℂ (fun z => A z i j) (ball 0 1)) ∧ (A 0).det ≠ 0 ∧ ∀ w ∈ logCover L.a_le, A (expCover a w) * L.H (expCover a w) * (A (expCover a w))ᴴ = (((Q.τ w).map Complex.im)⁻¹).map Complex.ofReal := by
  intro n a g Λ _ L
  obtain ⟨bas, Q, A, T0, hsym, hAd, hdet, -, -, hAP, hQP⟩ := exists_markedPeriods_frame n a g Λ L
  refine ⟨Q, A, hAd, hdet, fun w hw => ?_⟩
  let Am : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i => L.P w (bas (.inl i))
  let Bm : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i => L.P w (bas (.inr i))
  have hAm : Am = A (expCover a w) := by
    ext i k
    exact hAP w hw i k
  obtain ⟨h1, -, -, h4⟩ := siegel_of_riemann g Am Bm (L.H (expCover a w)) (L.herm w hw)
    (L.pos w hw) (fun i j => ⟨(L.im w hw (bas (.inl i)) (bas (.inl j))).trans (by simp [(hsym i j).1]),
      (L.im w hw (bas (.inr i)) (bas (.inr j))).trans (by simp [(hsym i j).2.1]),
      (L.im w hw (bas (.inl i)) (bas (.inr j))).trans (by
        rw [(hsym i j).2.2]; split_ifs <;> simp)⟩)
  have hB : Bm = Q.τ w * Am := by
    ext j k
    have h := congrFun (hQP w hw j) k
    rw [Finset.sum_apply] at h
    simpa [Am, Bm, Matrix.mul_apply] using h
  have hτ : Bm * Am⁻¹ = Q.τ w := by
    rw [hB, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h1), Matrix.mul_one]
  rw [← hAm, h4, hτ]

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PtsIntegralConjLineEq
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

namespace GlobalTheory.CompanionTheory.Ar.Tw

theorem ptsIntegral_conjLine : PtsIndepStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Q : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι), IsArithVar Q (e + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSectionOn Q A s → ptsIntegral Q (pot fun j => conjLine (L j)) (logNorm (conjLine A) s) = ptsIntegral Q (pot L) (logNorm A s) := by
  intro hI K _ ι _ Q e L A s hQ hL hA hs
  exact GlobalTheory.CompanionTheory.Ar.Cmp.arInt_conj
    (fun K _ ι _ P e Ψ L A s hP hΨ hL hA hs => sheetIndep K ι P e Ψ L A s hP hΨ hL hA hs) hI
    (fun K _ ι _ P e hP => goodProjExists K ι P e hP) K ι Q e L A s hQ hL hA hs

end GlobalTheory.CompanionTheory.Ar.Tw
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.UniformisedPotentialIntegralFormula
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem proportional_on_uniformised : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (U : Set X) (th : Ψ × Fin N → LocPot X) (ph : Ψ × Fin N → X → ℝ), j ≤ N → e = antisymDegree Ψ N → IsOpen U → IsNull A Uᶜ → (∀ p, IsPotential A (th p)) → (∀ p, A.SmoothOn U (ph p)) → IsUniformised A U j (fun p => th p + LocPot.ofFun (ph p)) → (∀ w : Fin e → Ψ × Fin N, MIntegrable A (fun i => th (w i) + LocPot.ofFun (ph (w i))) (fun _ => 1)) → ∃ v : ℝ, 0 < v ∧ toWt (formPoly e fun w => mInt A (fun i => th (w i) + LocPot.ofFun (ph (w i))) (fun _ => 1)) = C v * antisymDelta Ψ N :=
  @PositivityTheory.Xgp.t_per_int

end GlobalTheory.CompanionTheory.Ar.PB
end

