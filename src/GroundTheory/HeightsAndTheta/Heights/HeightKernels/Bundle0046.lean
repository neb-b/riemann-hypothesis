module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import ReciprocityTheory.ThetaQuasiPeriods.PeriodLattice
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Assembly
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0044
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0015
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0042
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0040
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualCurvePoint
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0031
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0045
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0014
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ChartCutoffParts
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0039
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0004

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.Assembly
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

theorem CoordConeArithVar.full : CoordConeArithVar.Statement :=
  CoordConeArithVar.proof IntDomainDim.full

theorem GrassArithVar.full : GrassArithVar.Statement := GrassArithVar.proof CoordConeArithVar.full

theorem RootArithVar.full : RootArithVar.Statement := RootArithVar.proof CoordConeArithVar.full

theorem DualArithVar.full : DualArithVar.Statement := DualArithVar.proof CoordConeArithVar.full

theorem FsLineSemipositive.full : FsLineSemipositive.Statement :=
  FsLineSemipositive.proof FsLineSmooth.proof FsLineLevi.proof

theorem RootPointConj.full : RootPointConj.Statement := RootPointConj.proof RootAnchorNonzero.proof

theorem RootPointsFinite.full : RootPointsFinite.Statement :=
  RootPointsFinite.proof RootAnchorNonzero.proof

theorem RootLogNormBound.full : RootLogNormBound.Statement :=
  RootLogNormBound.proof RootAnchorNonzero.proof RootPointConj.full PlueckerKernel.full

theorem RootHeight.full : RootHeight.Statement :=
  RootHeight.proofNE RootArithVar.full RootDivSuppEmpty.proof RootLogNormBound.full
    RootPointsFinite.full PtsIntegralZeroLowerNE.proof MultiHomogMemCoord.proof FsLineSmooth.proof

theorem RootDense.full : RootDense.Statement :=
  RootDense.proof MultiHomogMemCoord.proof RootsOfUnityDense.full

theorem GrassHeightBound.full : GrassHeightBound.Statement :=
  GrassHeightBound.proof GrassArithVar.full RootArithVar.full FsLineSemipositive.full
    NefOfNonneg.proof FsConjInvariant.proof GrassLeRoot.proof RootHeight.full RootDense.full

theorem DualStdMassAt.full : DualStdMassAt.Statement :=
  DualStdMassAt.proof DualPtsOnPlane.proof DualPtsOfPlane.proof

theorem DualPointLineDegree.ofOpen (hVI : VertRIndex.Statement) (hSN : SectionIndexNorm.Statement) :
    DualPointLineDegree.Statement :=
  DualPointLineDegree.proof DualCurvePoint.proof PointDegCPos.proof PointArInt.proof
    (PointVertR.proof hVI hSN) DualLineIndex.proof DualLineSemipositive.proof

theorem DualTopBound.ofOpen (hEnergy : DualMetricEnergy.Statement)
    (hBasis : DualTopBasisChange.Statement) (hStacked : DualTopStacked.Statement)
    (hSDeg : DualStackedDegree.Statement) (hBC : DualStdBaseChange.Statement)
    (hGL : GrassLinesProj.Statement) (hCharts : DualGeomDegCharts.Statement)
    (hGChart : GrassGeomDegChart.Statement) (hMass : ChartMassInvariant.Statement) :
    DualTopBound.Statement :=
  DualTopBound.proof DualLatticeBasisExists.proof DualEmbBijective.proof
    (DualTopMetricChange.proof Telescope.proof hEnergy)
    (DualTopLatticeChange.proof (DualTopSubLattice.proof hBasis hStacked hSDeg))
    (DualTopStandard.proof hBC hGL) (DualGeomDegStandard.proof hCharts hGChart hMass)
    GrassHeightBound.full

theorem DualGeomDegPos.ofOpen (hDeg : DegreeStatement) (hInd : PtsIndepStatement) :
    DualGeomDegPos.Statement :=
  DualGeomDegPos.proof hDeg hInd DualArithVar.full DualLineSemipositive.proof DualPtsOnPlane.proof
    DualStdMassAt.full

theorem LineOfLargeDegreeFromZ.ofOpen (hVI : VertRIndex.Statement) (hSN : SectionIndexNorm.Statement)
    (hEnergy : DualMetricEnergy.Statement)
    (hBasis : DualTopBasisChange.Statement) (hStacked : DualTopStacked.Statement)
    (hSDeg : DualStackedDegree.Statement) (hBC : DualStdBaseChange.Statement)
    (hGL : GrassLinesProj.Statement) (hCharts : DualGeomDegCharts.Statement)
    (hGChart : GrassGeomDegChart.Statement) (hMass : ChartMassInvariant.Statement)
    (hDeg : DegreeStatement) (hInd : PtsIndepStatement) :
    LineOfLargeDegreeFromZ.Statement :=
  LineOfLargeDegreeFromZ.proofDual DualLatticeBasisExists.proof DualEmbBijective.proof
    DualArithVar.full DualLineSemipositive.proof NefOfNonneg.proof DualLineConj.proof
    (DualPointLineDegree.ofOpen hVI hSN)
    (DualTopBound.ofOpen hEnergy hBasis hStacked hSDeg hBC hGL hCharts hGChart hMass)
    (DualGeomDegPos.ofOpen hDeg hInd)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartDiffEnergy
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix MeasureTheory Filter Topology
open scoped ComplexOrder

noncomputable section

namespace ChartEnergyDifferenceBound

theorem cross_le {u U χ a p G : ℝ} (hU : |u| ≤ U) (hχ : 0 ≤ χ) (hp : 0 ≤ p) (hG : 0 ≤ G)
    (ha : |a| ≤ Real.sqrt p * Real.sqrt G) :
    -(u * (χ * a + χ * a)) ≤ 2 * U ^ 2 * p + χ * χ * G / 2 := by
  have hsp := Real.sq_sqrt hp
  have hsG := Real.sq_sqrt hG
  have h0 : 0 ≤ |u| := abs_nonneg u
  have hua : -(u * a) ≤ |u| * |a| := by
    rw [← abs_mul]
    exact neg_le_abs _
  have h1 : -(u * (χ * a + χ * a)) ≤ 2 * χ * (|u| * |a|) := by
    nlinarith [mul_le_mul_of_nonneg_left hua hχ]
  have hb : |u| * |a| ≤ U * (Real.sqrt p * Real.sqrt G) := mul_le_mul hU ha (abs_nonneg a) (h0.trans hU)
  have h2 : 2 * χ * (|u| * |a|) ≤ 2 * χ * (U * (Real.sqrt p * Real.sqrt G)) :=
    mul_le_mul_of_nonneg_left hb (by positivity)
  have h3 : 2 * χ * (U * (Real.sqrt p * Real.sqrt G)) ≤ 2 * U ^ 2 * p + χ * χ * G / 2 := by
    nlinarith [sq_nonneg (2 * U * Real.sqrt p - χ * Real.sqrt G)]
  linarith

end ChartEnergyDifferenceBound

open ChartIntegrationByPartsSymmetry ChartEnergyDifferenceBound

theorem ChartDiffEnergy.proof (hE : ChartCutoffEnergy.Statement) : ChartDiffEnergy.Statement := by
  intro n A B T hA hB hT
  set φ : Fin n → (Fin (n + 1) → ℂ) → ℝ := fun i => hermChartPot (T i) with hφdef
  set u : (Fin (n + 1) → ℂ) → ℝ := fun y => hermChartPot A y - hermChartPot B y with hudef
  have hφ3 : ∀ i, ContDiff ℝ 3 (φ i) := fun i => contDiff_hermChartPot_of_le 3 (hT i)
  have hφ2 : ∀ i, ContDiff ℝ 2 (φ i) := fun i => contDiff_hermChartPot_of_le 2 (hT i)
  have hu3 : ContDiff ℝ 3 u := (contDiff_hermChartPot_of_le 3 hA).sub (contDiff_hermChartPot_of_le 3 hB)
  have hu1 : ContDiff ℝ 1 u := hu3.of_le (by norm_num)
  have hGc : Continuous (gradDens φ u u) := continuous_gradDens hφ2 hu1 hu1
  have hG0 : ∀ y, 0 ≤ gradDens φ u u y := gradDens_chart_nonneg hT u
  obtain ⟨U, hU⟩ := ChartEnergyIntegrableAlt.pot_sub_bound HermFormCompare.proof hA hB
  have hUa : ∀ y, |u y| ≤ U := fun y => by
    have := hU y
    rwa [Real.norm_eq_abs] at this
  obtain ⟨K, hK⟩ := hE n T hT
  have hI : Integrable (fun y => u y * maDens (Fin.cons u φ) y) :=
    integrable_pot_mul_maDensity hA hB hA hB hT
  set I : ℝ := ∫ y, |u y * maDens (Fin.cons u φ) y| with hIdef
  have hψG : ∀ k : ℕ, Integrable (fun y => chartCutoff k y * chartCutoff k y * gradDens φ u u y) := fun k =>
    (((contDiff_chartCutoff k 0).continuous.mul (contDiff_chartCutoff k 0).continuous).mul
      hGc).integrable_of_hasCompactSupport (hasCompactSupport_chartCutoff k).mul_right.mul_right
  have hX : ∀ k : ℕ, ∫ y, chartCutoff k y * chartCutoff k y * gradDens φ u u y ≤ 2 * I + 4 * U ^ 2 * K := by
    intro k
    set χ : (Fin (n + 1) → ℂ) → ℝ := chartCutoff k with hχdef
    have hχ3 : ContDiff ℝ 3 χ := contDiff_chartCutoff k 3
    have hχ1 : ContDiff ℝ 1 χ := contDiff_chartCutoff k 1
    have hψ3 : ContDiff ℝ 3 (fun y => χ y * χ y) := hχ3.mul hχ3
    have hψc : HasCompactSupport (fun y => χ y * χ y) := (hasCompactSupport_chartCutoff k).mul_right
    obtain ⟨i1, i2, i3, heq⟩ := parts_cutoff hφ3 hψ3 hψc hu3 hu3
    have hP : Integrable (gradDens φ χ χ) :=
      (continuous_gradDens hφ2 hχ1 hχ1).integrable_of_hasCompactSupport
        (hasCompactSupport_gradDens_left φ χ (hasCompactSupport_chartCutoff k))
    have hL : ∀ y, gradDens φ (fun y => χ y * χ y) u y = χ y * gradDens φ χ u y + χ y * gradDens φ χ u y :=
      fun y => (gradDensLeibniz_thm n φ χ χ u y (hχ1.differentiable one_ne_zero y)
        (hχ1.differentiable one_ne_zero y)).1
    have hpt : ∀ y, -(χ y * χ y * u y * maDens (Fin.cons u φ) y) - u y * gradDens φ (fun y => χ y * χ y) u y ≤
        |u y * maDens (Fin.cons u φ) y| + (2 * U ^ 2 * gradDens φ χ χ y + χ y * χ y * gradDens φ u u y / 2) := by
      intro y
      rw [hL y]
      have h0 : 0 ≤ χ y := chartCutoff_nonneg k y
      have h1 : χ y ≤ 1 := chartCutoff_le_one k y
      have hψ0 : 0 ≤ χ y * χ y := mul_nonneg h0 h0
      have hψ1 : χ y * χ y ≤ 1 := by nlinarith
      have ht := neg_abs_le (u y * maDens (Fin.cons u φ) y)
      have ht0 := abs_nonneg (u y * maDens (Fin.cons u φ) y)
      have ha : -(χ y * χ y * u y * maDens (Fin.cons u φ) y) ≤ |u y * maDens (Fin.cons u φ) y| := by
        nlinarith [mul_nonneg hψ0 (by linarith : 0 ≤ |u y * maDens (Fin.cons u φ) y| + u y * maDens (Fin.cons u φ) y),
          mul_nonneg (by linarith : 0 ≤ 1 - χ y * χ y) ht0]
      have hb := cross_le (hUa y) h0 (gradDens_chart_nonneg hT χ y) (hG0 y) (abs_gradDens_chart_le hT χ u y)
      linarith
    have i1n : Integrable (fun y => -(χ y * χ y * u y * maDens (Fin.cons u φ) y)) := i1.neg
    have iL : Integrable (fun y => -(χ y * χ y * u y * maDens (Fin.cons u φ) y) -
        u y * gradDens φ (fun y => χ y * χ y) u y) := i1n.sub i3
    have iA : Integrable (fun y => |u y * maDens (Fin.cons u φ) y|) := hI.abs
    have iP : Integrable (fun y => 2 * U ^ 2 * gradDens φ χ χ y) := hP.const_mul _
    have iG : Integrable (fun y => χ y * χ y * gradDens φ u u y / 2) := i2.div_const 2
    have iPG : Integrable (fun y => 2 * U ^ 2 * gradDens φ χ χ y + χ y * χ y * gradDens φ u u y / 2) := iP.add iG
    have iR : Integrable (fun y => |u y * maDens (Fin.cons u φ) y| +
        (2 * U ^ 2 * gradDens φ χ χ y + χ y * χ y * gradDens φ u u y / 2)) := iA.add iPG
    have hXeq : ∫ y, χ y * χ y * gradDens φ u u y =
        ∫ y, (-(χ y * χ y * u y * maDens (Fin.cons u φ) y) - u y * gradDens φ (fun y => χ y * χ y) u y) := by
      rw [integral_sub i1n i3, integral_neg]
      linarith
    have hmono := integral_mono iL iR hpt
    rw [← hXeq, integral_add iA iPG, integral_add iP iG, integral_const_mul, integral_div] at hmono
    have hKk : 2 * U ^ 2 * ∫ y, gradDens φ χ χ y ≤ 2 * U ^ 2 * K :=
      mul_le_mul_of_nonneg_left (hK k) (by positivity)
    linarith
  set f : ℕ → (Fin (n + 1) → ℂ) → ENNReal :=
    fun k y => ENNReal.ofReal (chartCutoff k y * chartCutoff k y * gradDens φ u u y) with hfdef
  have hmono : ∀ y, Monotone fun k => f k y := by
    intro y a b hab
    apply ENNReal.ofReal_le_ofReal
    have h1 := chartCutoff_mono y hab
    have h0 := chartCutoff_nonneg a y
    exact mul_le_mul_of_nonneg_right (mul_le_mul h1 h1 h0 (h0.trans h1)) (hG0 y)
  have htend : ∀ y, Tendsto (fun k => f k y) atTop (𝓝 (ENNReal.ofReal (gradDens φ u u y))) := by
    intro y
    have h := ((tendsto_chartCutoff y).mul (tendsto_chartCutoff y)).mul_const (gradDens φ u u y)
    rw [one_mul, one_mul] at h
    exact (ENNReal.continuous_ofReal.tendsto _).comp h
  have hfm : ∀ k, AEMeasurable (f k) volume := fun k => (hψG k).1.aemeasurable.ennreal_ofReal
  have hlim := lintegral_tendsto_of_tendsto_of_monotone hfm (Eventually.of_forall hmono)
    (Eventually.of_forall htend)
  have hbd : ∀ k, ∫⁻ y, f k y ≤ ENNReal.ofReal (2 * I + 4 * U ^ 2 * K) := by
    intro k
    have hnn : ∀ y, 0 ≤ chartCutoff k y * chartCutoff k y * gradDens φ u u y := fun y =>
      mul_nonneg (mul_nonneg (chartCutoff_nonneg k y) (chartCutoff_nonneg k y)) (hG0 y)
    rw [hfdef, ← ofReal_integral_eq_lintegral_ofReal (hψG k) (Eventually.of_forall hnn)]
    exact ENNReal.ofReal_le_ofReal (hX k)
  refine ⟨hGc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hG0)]
  exact lt_of_le_of_lt (le_of_tendsto' hlim hbd) ENNReal.ofReal_lt_top

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartIbpCutoff
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix MeasureTheory Filter Topology
open ChartIntegrationByPartsSymmetry
open scoped ComplexOrder

noncomputable section

namespace ChartIntegrationByPartsCutoff

variable {n : ℕ}

theorem sqrt_mul_sqrt_le {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 < ε) :
    Real.sqrt a * Real.sqrt b ≤ ε * a + b / (4 * ε) := by
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  have h3 := sq_nonneg (2 * ε * Real.sqrt a - Real.sqrt b)
  have h4 : 0 < 4 * ε := by positivity
  have key : 4 * ε * (Real.sqrt a * Real.sqrt b) ≤ 4 * ε * (ε * a + b / (4 * ε)) := by
    rw [mul_add, mul_div_cancel₀ _ h4.ne']
    have e : (2 * ε * Real.sqrt a - Real.sqrt b) ^ 2 =
        4 * ε * (ε * a) + b - 4 * ε * (Real.sqrt a * Real.sqrt b) := by
      rw [sub_sq, mul_pow, mul_pow, h1, h2]
      ring
    linarith
  exact le_of_mul_le_mul_left key h4

def outer (n k : ℕ) : Set (Fin (n + 1) → ℂ) := {y | ((k : ℝ) + 1) ^ 2 ≤ ∑ i, ‖y i‖ ^ 2}

theorem measurableSet_outer (k : ℕ) : MeasurableSet (outer n k) :=
  (isClosed_le continuous_const (continuous_finsetSum _ fun i _ =>
    (continuous_norm.comp (continuous_apply i)).pow 2)).measurableSet

theorem tendsto_integral_outer {g : (Fin (n + 1) → ℂ) → ℝ} (hg : Integrable g) :
    Tendsto (fun k : ℕ => ∫ y, (outer n k).indicator g y) atTop (𝓝 0) := by
  have h0 : (∫ _y : Fin (n + 1) → ℂ, (0 : ℝ)) = 0 := integral_zero _ _
  rw [← h0]
  refine tendsto_integral_of_dominated_convergence (fun y => ‖g y‖)
    (fun k => (hg.indicator (measurableSet_outer k)).aestronglyMeasurable) hg.norm
    (fun k => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
  · rw [Set.indicator]
    split_ifs
    · exact le_rfl
    · simp
  · obtain ⟨N, hN⟩ := exists_nat_gt (∑ i, ‖y i‖ ^ 2)
    refine tendsto_atTop_of_eventually_const (i₀ := N) fun k hk => ?_
    have hk' : (N : ℝ) ≤ k := by exact_mod_cast hk
    have : ¬ y ∈ outer n k := by
      simp only [outer, Set.mem_ofPred_eq, not_le]
      nlinarith
    simp [Set.indicator_of_notMem this]

theorem tendsto_boundary {T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ} (hT : ∀ i, (T i).PosDef)
    {u w : (Fin (n + 1) → ℂ) → ℝ} {W : ℝ} (hW : ∀ y, ‖w y‖ ≤ W)
    (hE : Integrable (gradDens (fun i => hermChartPot (T i)) u u)) {K : ℝ}
    (hK : ∀ k : ℕ, ∫ y, gradDens (fun i => hermChartPot (T i)) (chartCutoff k) (chartCutoff k) y ≤ K) :
    Tendsto (fun k : ℕ => ∫ y, w y * gradDens (fun i => hermChartPot (T i)) (chartCutoff k) u y) atTop (𝓝 0) := by
  set φ : Fin n → (Fin (n + 1) → ℂ) → ℝ := fun i => hermChartPot (T i) with hφdef
  have h2 : ∀ i, ContDiff ℝ 2 (φ i) := fun i => contDiff_hermChartPot_of_le 2 (hT i)
  have hone : ((1 : ℕ) : WithTop ℕ∞) ≤ 3 := by norm_num
  have hW0 : 0 ≤ W := (norm_nonneg _).trans (hW 0)
  set t : ℕ → ℝ := fun k => ∫ y, (outer n k).indicator (gradDens φ u u) y with htdef
  have ht0 : ∀ k, 0 ≤ t k := fun k => integral_nonneg fun y =>
    Set.indicator_nonneg (fun y _ => gradDens_chart_nonneg hT u y) y
  set ε : ℕ → ℝ := fun k => Real.sqrt (t k + 1 / ((k : ℝ) + 1)) with hεdef
  have hεpos : ∀ k, 0 < ε k := fun k => Real.sqrt_pos.mpr (by have := ht0 k; positivity)
  have htε : ∀ k, t k ≤ ε k ^ 2 := fun k => by
    rw [hεdef, Real.sq_sqrt (by have := ht0 k; positivity)]
    have : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := by positivity
    linarith
  have hbound : ∀ k, |∫ y, w y * gradDens φ (chartCutoff k) u y| ≤ W * (ε k * (K + 1 / 4)) := by
    intro k
    have hχ3 := contDiff_chartCutoff (D := n + 1) k 3
    have hcc := hasCompactSupport_chartCutoff (D := n + 1) k
    have hiχ : Integrable (gradDens φ (chartCutoff k) (chartCutoff k)) :=
      (continuous_gradDens h2 (hχ3.of_le hone) (hχ3.of_le hone)).integrable_of_hasCompactSupport
        (hasCompactSupport_gradDens_left φ _ hcc)
    have hiO : Integrable ((outer n k).indicator (gradDens φ u u)) := hE.indicator (measurableSet_outer k)
    have hpt : ∀ y, ‖w y * gradDens φ (chartCutoff k) u y‖ ≤
        W * (ε k * gradDens φ (chartCutoff k) (chartCutoff k) y +
          (outer n k).indicator (gradDens φ u u) y / (4 * ε k)) := by
      intro y
      rw [norm_mul]
      have hnn := gradDens_chart_nonneg hT (chartCutoff k) y
      by_cases hy : y ∈ outer n k
      · rw [Set.indicator_of_mem hy]
        have hcs : ‖gradDens φ (chartCutoff k) u y‖ ≤
            ε k * gradDens φ (chartCutoff k) (chartCutoff k) y + gradDens φ u u y / (4 * ε k) :=
          (abs_gradDens_chart_le hT (chartCutoff k) u y).trans
            (sqrt_mul_sqrt_le hnn (gradDens_chart_nonneg hT u y) (hεpos k))
        exact mul_le_mul (hW y) hcs (norm_nonneg _) hW0
      · have hlt : ∑ i, ‖y i‖ ^ 2 < ((k : ℝ) + 1) ^ 2 := by simpa [outer] using hy
        rw [gradDens_chartCutoff_left φ u hlt, Set.indicator_of_notMem hy, norm_zero, mul_zero, zero_div,
          add_zero]
        exact mul_nonneg hW0 (mul_nonneg (hεpos k).le hnn)
    have hint : Integrable fun y => W * (ε k * gradDens φ (chartCutoff k) (chartCutoff k) y +
        (outer n k).indicator (gradDens φ u u) y / (4 * ε k)) :=
      ((hiχ.const_mul (ε k)).add (hiO.div_const (4 * ε k))).const_mul W
    have h1 := norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
    rw [Real.norm_eq_abs] at h1
    refine h1.trans ?_
    rw [integral_const_mul, integral_add (hiχ.const_mul _) (hiO.div_const _), integral_const_mul, integral_div]
    refine mul_le_mul_of_nonneg_left ?_ hW0
    have hq : t k / (4 * ε k) ≤ ε k / 4 := by
      rw [div_le_div_iff₀ (by have := hεpos k; positivity) (by norm_num)]
      nlinarith [htε k, hεpos k]
    have := mul_le_mul_of_nonneg_left (hK k) (hεpos k).le
    change ε k * _ + t k / (4 * ε k) ≤ _
    nlinarith
  have htt : Tendsto t atTop (𝓝 0) := tendsto_integral_outer hE
  have hinv : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hε : Tendsto ε atTop (𝓝 0) := by
    have := ((htt.add hinv).sqrt)
    simpa [hεdef] using this
  have hB : Tendsto (fun k => W * (ε k * (K + 1 / 4))) atTop (𝓝 0) := by
    simpa using (hε.mul_const (K + 1 / 4)).const_mul W
  exact squeeze_zero_norm (fun k => (hbound k).trans_eq' (Real.norm_eq_abs _)) hB

end ChartIntegrationByPartsCutoff


open ChartIntegrationByPartsCutoff in
theorem ChartIbpCutoff.proof (hE : ChartCutoffEnergy.Statement) (hD : ChartDiffEnergy.Statement) :
    ChartIbpCutoff.Statement := by
  intro n A B C D T hA hB hC hD' hT
  set φ : Fin n → (Fin (n + 1) → ℂ) → ℝ := fun i => hermChartPot (T i) with hφdef
  set u : (Fin (n + 1) → ℂ) → ℝ := fun y => hermChartPot A y - hermChartPot B y with hudef
  set w : (Fin (n + 1) → ℂ) → ℝ := fun y => hermChartPot C y - hermChartPot D y with hwdef
  have h3 : ∀ i, ContDiff ℝ 3 (φ i) := fun i => contDiff_hermChartPot_of_le 3 (hT i)
  have hu : ContDiff ℝ 3 u := (contDiff_hermChartPot_of_le 3 hA).sub (contDiff_hermChartPot_of_le 3 hB)
  have hw : ContDiff ℝ 3 w := (contDiff_hermChartPot_of_le 3 hC).sub (contDiff_hermChartPot_of_le 3 hD')
  obtain ⟨Wu, hWu⟩ := ChartEnergyIntegrableAlt.pot_sub_bound HermFormCompare.proof hA hB
  obtain ⟨Ww, hWw⟩ := ChartEnergyIntegrableAlt.pot_sub_bound HermFormCompare.proof hC hD'
  obtain ⟨K, hK⟩ := hE n T hT
  have key : ∀ k : ℕ, (∫ y, chartCutoff k y * (u y * maDensity (Fin.cons w φ) y - w y * maDensity (Fin.cons u φ) y))
      = (∫ y, w y * gradDens φ (chartCutoff k) u y) - ∫ y, u y * gradDens φ (chartCutoff k) w y := by
    intro k
    obtain ⟨i1, -, -, e1⟩ := parts_cutoff h3 (contDiff_chartCutoff k 3) (hasCompactSupport_chartCutoff k) hu hw
    obtain ⟨i2, -, -, e2⟩ := parts_cutoff h3 (contDiff_chartCutoff k 3) (hasCompactSupport_chartCutoff k) hw hu
    have hsplit : ∀ y, chartCutoff k y * (u y * maDensity (Fin.cons w φ) y - w y * maDensity (Fin.cons u φ) y) =
        chartCutoff k y * u y * maDens (Fin.cons w φ) y - chartCutoff k y * w y * maDens (Fin.cons u φ) y :=
      fun y => by change _ = _ * _ * maDensity _ y - _ * _ * maDensity _ y; ring
    simp_rw [hsplit]
    rw [integral_sub i1 i2, e1, e2]
    simp_rw [show ∀ y, gradDens φ w u y = gradDens φ u w y from gradDens_chart_comm hT w u]
    ring
  refine Tendsto.congr (fun k => (key k).symm) ?_
  rw [← sub_zero (0 : ℝ)]
  exact (tendsto_boundary hT hWw (hD n A B T hA hB hT) hK).sub (tendsto_boundary hT hWu (hD n C D T hC hD' hT) hK)

end

end GroundTheory.Heights₂.Heights
end

