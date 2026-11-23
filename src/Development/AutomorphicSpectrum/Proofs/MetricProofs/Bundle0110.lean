module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement
public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvergenceStatementHolds
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0083
public import ReciprocityTheory.AnalyticForms.LeviForms.ConvExpandStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDensityNonnegOffNullSet
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0102
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PModelFibreSumAeSheet
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.LintegralFibSum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0097
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0063
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0034
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0103
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0048
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameChangeRegular
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockLUFactorization
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.LU

variable {N j : ℕ}

theorem mem_stepCols_stepOf (hj : j ≤ N) (a b : Fin N) :
    a ∈ stepCols N j (stepOf N j b) ↔ a ≤ b ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) := by
  have ha := a.2
  have hb := b.2
  rw [Fin.le_def, stepCols, Finset.mem_filter]
  have hv : ((stepOf N j b : Fin N) : ℕ) = if N - j ≤ (b : ℕ) then (b : ℕ) - (N - j) else (b : ℕ) + j := rfl
  generalize ((stepOf N j b : Fin N) : ℕ) = i at hv ⊢
  simp only [Finset.mem_univ, true_and]
  split_ifs at hv ⊢ <;> omega

theorem det_subtype_eq_minorIJ (G : Matrix (Fin N) (Fin N) ℂ) (C : Finset (Fin N)) (P : Fin N → Prop)
    [Fintype {a // P a}] [DecidableEq {a // P a}] (hP : ∀ a, a ∈ C ↔ P a) :
    (G.submatrix (Subtype.val : {a // P a} → Fin N) Subtype.val).det = minorIJ G C C := by
  let e : Fin C.card ≃ {a // P a} := (C.orderIsoOfFin rfl).toEquiv.trans (Equiv.subtypeEquivRight hP)
  rw [minorIJ, dite_eq_left rfl, ← Matrix.det_submatrix_equiv_self e
    (G.submatrix (Subtype.val : {a // P a} → Fin N) Subtype.val)]
  rfl

theorem minor_stepOf_ne_zero (hj : j ≤ N) {G : Matrix (Fin N) (Fin N) ℂ} (hG : IsBlockDiag j G) (hd : G.det ≠ 0)
    (hs : ∀ i : Fin N, IsProperStep N j i → minorIJ G (stepCols N j i) (stepCols N j i) ≠ 0) (b : Fin N) :
    minorIJ G (stepCols N j (stepOf N j b)) (stepCols N j (stepOf N j b)) ≠ 0 := by
  by_cases hp : IsProperStep N j (stepOf N j b)
  · exact hs _ hp
  have hb := b.2
  have hlast : (b : ℕ) + 1 = N ∨ (b : ℕ) + 1 = N - j := by
    simp only [IsProperStep, stepOf, not_and_or, not_not] at hp
    split_ifs at hp <;> omega
  have hD := GlobalTheory.CompanionTheory.Ar.PB.CPts.detFac_ne_zero hj (⟨N - 1, by omega⟩ : Fin N) hG hd
  rw [detFac, if_pos (by simp only; omega), if_pos (by simp only; omega)] at hD
  by_cases h : N - j ≤ (b : ℕ)
  · have e : stepCols N j (stepOf N j b) = wIdx N j := by
      ext a
      have ha := a.2
      rw [mem_stepCols_stepOf hj, Fin.le_def]
      simp only [wIdx, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [e]
    exact left_ne_zero_of_mul hD
  · have e : stepCols N j (stepOf N j b) = omIdx N j := by
      ext a
      have ha := a.2
      rw [mem_stepCols_stepOf hj, Fin.le_def]
      simp only [omIdx, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [e]
    exact right_ne_zero_of_mul hD

theorem exists_lower_upper : ∀ (N j : ℕ) (G : Matrix (Fin N) (Fin N) ℂ), j ≤ N → IsBlockDiag j G → G.det ≠ 0 →
    (∀ i : Fin N, IsProperStep N j i → minorIJ G (stepCols N j i) (stepCols N j i) ≠ 0) →
    ∃ L U : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j L ∧ IsLowerUni L ∧ IsBlockDiag j U ∧ U.BlockTriangular id ∧
      (∀ c, U c c ≠ 0) ∧ G = L * U := by
  intro N j G hj hG hd hs
  have hu : ∀ b : Fin N, IsUnit (G.submatrix
      (Subtype.val : {a : Fin N // a ≤ b ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)} → Fin N) Subtype.val).det := fun b => by
    rw [det_subtype_eq_minorIJ G (stepCols N j (stepOf N j b)) _ fun a => mem_stepCols_stepOf hj a b]
    exact (minor_stepOf_ne_zero hj hG hd hs b).isUnit
  obtain ⟨B, hB, hBt, hL⟩ := hG.exists_upper hu
  have hdB : B.det ≠ 0 := fun h => by
    have := hL.det
    rw [Matrix.det_mul, h, mul_zero] at this
    exact zero_ne_one this
  have huB : IsUnit B.det := hdB.isUnit
  letI := Matrix.invertibleOfIsUnitDet B huB
  refine ⟨G * B, B⁻¹, hG.mul hB, hL, hB.inv huB, blockTriangular_inv_of_blockTriangular hBt, fun c => ?_, ?_⟩
  · have h1 : (B⁻¹).det ≠ 0 := (Matrix.isUnit_nonsing_inv_det B huB).ne_zero
    rw [Matrix.det_of_upperTriangular (blockTriangular_inv_of_blockTriangular hBt)] at h1
    exact (Finset.prod_ne_zero_iff.1 h1) c (Finset.mem_univ c)
  · rw [Matrix.mul_nonsing_inv_cancel_right _ _ huB]

end GlobalTheory.CompanionTheory.Ar.PB.WMan.LU
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExpandMInt
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric.ExpandMInt

theorem expand_mInt : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (U : Set X) (P : Fin e → LocPot X) (f : Fin e → X → ℝ) (Θ : LocPot X) (g : X → ℝ), IsOpen U → (∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Uᶜ) = 0) → (∀ i, IsPotential A (P i)) → IsPotential A Θ → (∀ i, A.SmoothOn U (f i)) → (∀ T : Finset (Fin e), MIntegrable A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) + LocPot.ofFun (if i ∈ T then f i else 0) + Θ) g) → MIntegrable A (fun i => P i + LocPot.ofFun (f i)) g ∧ mInt A (fun i => P i + LocPot.ofFun (f i)) g = ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) * mInt A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) + LocPot.ofFun (if i ∈ T then f i else 0) + Θ) g := by
  intro e X _ _ _ A U P f Θ g hU hnull hP hΘ hf hT

  have hae : ∀ j, ∀ᵐ y ∂(volume : Measure (Fin e → ℂ)), y ∈ (A.chart j).target →
      locDens A (fun i => P i + LocPot.ofFun (f i)) j y =
        ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) *
          locDens A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) +
            LocPot.ofFun (if i ∈ T then f i else 0) + Θ) j y := by
    intro j
    rw [ae_iff]
    refine measure_mono_null (fun y hy => ?_) (hnull j)
    simp only [Set.mem_ofPred_eq, Classical.not_imp] at hy
    refine ⟨hy.1, fun hyU => hy.2 ?_⟩
    exact _root_.GlobalTheory.CompanionTheory.Ar.Giv.locDens_expand_ofFun A U P f Θ hU hP hΘ hf j y ⟨hy.1, hyU⟩
  refine ⟨?_, ?_⟩
  · intro j K hK hKc
    have hsum : IntegrableOn (fun y => ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) *
        (g ((A.chart j).symm y) * locDens A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) +
            LocPot.ofFun (if i ∈ T then f i else 0) + Θ) j y)) K :=
      integrable_finsetSum _ fun T _ => (hT T j K hK hKc).const_mul _
    refine hsum.congr_fun_ae ?_
    filter_upwards [ae_restrict_of_ae (hae j), ae_restrict_mem hKc.measurableSet] with y hy hyK
    rw [hy (hK hyK), Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    ring
  · unfold mInt
    split_ifs with h
    · unfold integralWith
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp_rw [← integral_const_mul]
      rw [← integral_finsetSum _ fun T _ => (integrableOn_weight A h.some _ g (hT T) j).const_mul _]
      refine setIntegral_congr_ae (A.chart j).open_target.measurableSet ?_
      filter_upwards [hae j] with y hy hyt
      rw [hy hyt, Finset.mul_sum]
      refine Finset.sum_congr rfl fun T _ => ?_
      ring
    · simp

end GlobalTheory.CompanionTheory.Metric.ExpandMInt
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteFibresOfAnalyticLocalDiffeoStatement
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_fibres_of_analytic_local_diffeo : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (q : X → Fin e → ℂ) (S : Set X) (G : X → ℝ), (∀ j, volume ((A.chart j).target ∩ (A.chart j).symm ⁻¹' S) = 0) → (∀ x ∉ S, ∀ j, x ∈ (A.chart j).source → AnalyticAt ℂ (q ∘ (A.chart j).symm) (A.chart j x) ∧ LinearMap.det (fderiv ℂ (q ∘ (A.chart j).symm) (A.chart j x) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0) → (∀ y, (q ⁻¹' {y} \ S).Finite) → (∀ x ∉ S, ∀ i k, x ∈ (A.chart k).source → ContDiffAt ℝ 2 ((Φ i).φ x ∘ (A.chart k).symm) (A.chart k x)) → (∀ j, AEStronglyMeasurable (fun u => G ((A.chart j).symm u) * locDens A Φ j u) (volume.restrict (A.chart j).target)) → ∀ Pt : ChartPartition A, ∫⁻ y, ENNReal.ofReal (∑ᶠ x ∈ q ⁻¹' {y} \ S, |G x * pushDens A Φ q x|) = ∑ j, ∫⁻ u in (A.chart j).target, ENNReal.ofReal |Pt.χ j ((A.chart j).symm u) * G ((A.chart j).symm u) * locDens A Φ j u| := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Push.lintegral_absFibre_eq | exact GlobalTheory.CompanionTheory.Ar.Giv.Push.lintegral_absFibre_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Push.lintegral_absFibre_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartEighth
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan

theorem continuousWithinAt_valAt_of_regAt {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] {x : (Σ k, ι k) → Ω} {zb : (Σ k, ι k) → ℂ} (hz : zb ∈ mcPts (mCoordIdeal x)) {s : Ω}
    (hs : RegAt x (mCoordIdeal zb) s) : ContinuousWithinAt (valAt x s) (mcPts (mCoordIdeal x)) zb := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  have hy := GlobalTheory.CompanionTheory.Ar.PB.ValRing.aeval_ne_zero_of_notMem hz hh hn
  have h0 := GlobalTheory.CompanionTheory.Ar.PB.ValRing.eval_ne_zero_of_notMem hh hn
  have cg : Continuous fun w : (Σ k, ι k) → ℂ => eval w (map (Int.castRingHom ℂ) g) :=
    MvPolynomial.continuous_eval _
  have ch : Continuous fun w : (Σ k, ι k) → ℂ => eval w (map (Int.castRingHom ℂ) h) :=
    MvPolynomial.continuous_eval _
  have hnear : valAt x s =ᶠ[𝓝[mcPts (mCoordIdeal x)] zb]
      fun w => eval w (map (Int.castRingHom ℂ) g) / eval w (map (Int.castRingHom ℂ) h) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ch.continuousAt.eventually_ne h0)] with w hw hw0
    exact valAt_eq hw ⟨d, g, h, hg, hh, hy, heq, hw0, rfl⟩
  have hat : valAt x s zb = eval zb (map (Int.castRingHom ℂ) g) / eval zb (map (Int.castRingHom ℂ) h) :=
    valAt_eq hz ⟨d, g, h, hg, hh, hy, heq, h0, rfl⟩
  exact (cg.continuousAt.div ch.continuousAt h0).continuousWithinAt.congr_of_eventuallyEq hnear hat

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem twMinor_continuousWithinAt (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {Z : Type}
    [TopologicalSpace Z] {S : Set Z} {z₀ : Z} {β : Z → (Σ k, baseIdx ι M.blk k) → ℂ} {P : Z → (Σ k, ι k) → ℂ}
    (hβ : ContinuousWithinAt β S z₀) (hS : Set.MapsTo β S (mcPts (mCoordIdeal M.x)))
    (hz : β z₀ ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal (β z₀)))
    (hP : ContinuousWithinAt P S z₀) (i : Fin N) (k : K) (g : Matrix (Fin N) (Fin N) ℂ) (J : Finset (Fin N)) :
    ContinuousWithinAt (fun z => twMinor M F (β z) i k g (P z) J) S z₀ := by
  simp only [twMinor, pluck]
  refine tendsto_finsetSum _ fun I _ => Tendsto.const_mul _ (tendsto_finsetSum _ fun m _ => Tendsto.mul ?_ ?_)
  · exact ContinuousWithinAt.comp (g := valAt M.x (F.u' I ⟨k, m⟩))
      (continuousWithinAt_valAt_of_regAt hz (hG.2.1 _ _).2) hβ hS
  · exact ((continuous_apply (⟨k, m⟩ : Σ k, ι k)).continuousAt.comp_continuousWithinAt hP)

theorem wRho_continuousOn : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ContinuousOn (wRho M Rb τ k₀ ca cb F kb r h ε) (wO M Rb τ a k₀ ca cb F kb V r h) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε H
  obtain ⟨hb, hab, hk, hca, hcb, hy, hF, hB, horb, hr, hh⟩ := H
  obtain ⟨hVo, hVt, -, -, hbl⟩ := hB
  have hbase : Set.MapsTo (baseOf M k₀) (wO M Rb τ a k₀ ca cb F kb V r h) (mcPts (mCoordIdeal M.x)) := fun z hz =>
    GlobalTheory.CompanionTheory.Ar.PB.CPts.base_mem M (GlobalTheory.CompanionTheory.Ar.PB.CPts.comp_mem_mcPts (GlobalTheory.CompanionTheory.Ar.PB.WSq.Pts.isBlockMap_v₀ k₀)
      (algebraMap Φ (RatFunc Φ)) (funext fun _ => rfl) hz.1)
  have cB : Continuous (baseOf M k₀) := continuous_pi fun q => continuous_apply _
  have cF : Continuous (fstPt (ι := ι) k₀) := continuous_pi fun q => continuous_apply _
  have cS : Continuous (sndPt (ι := ι) k₀) := continuous_pi fun q => continuous_apply _
  have hgood : ∀ z ∈ wO M Rb τ a k₀ ca cb F kb V r h, M.GoodAt F (mCoordIdeal (baseOf M k₀ z)) := by
    intro z hz
    have h3 := (hbl _ hz.2.2.1).2.2
    rw [(Rb.A.chart kb).left_inv hz.2.1] at h3
    have e := orbit_trans (orbit_symm (horb _ (hbase hz))) h3.2
    rw [GlobalTheory.CompanionTheory.Ar.PB.CovMap.mCoordIdeal_eq_of_sameOrbit e]
    exact h3.1
  have cLow : ∀ (P : ((Σ o : Option K, ι (o.getD k₀)) → ℂ) → (Σ k, ι k) → ℂ), Continuous P → ∀ (τ' : Ψ) (a' b' : Fin N),
      ∀ z ∈ wO M Rb τ a k₀ ca cb F kb V r h, (∀ k, M.blk (τ', stepOf N j b') = some k →
        twMinor M F (baseOf M k₀ z) (stepOf N j b') k (h τ')⁻¹ (P z) (stepCols N j (stepOf N j b')) ≠ 0) →
      ContinuousWithinAt (fun z => lowRead M F (baseOf M k₀ z) h (P z) τ' a' b')
        (wO M Rb τ a k₀ ca cb F kb V r h) z := by
    intro P hP τ' a' b' z hz hne
    have cT := fun (k : K) (J : Finset (Fin N)) => twMinor_continuousWithinAt M F cB.continuousWithinAt hbase (hbase hz)
      (hgood z hz) hP.continuousWithinAt (stepOf N j b') k (h τ')⁻¹ J
    cases e : M.blk (τ', stepOf N j b') with
    | none =>
      simp only [lowRead, e, Option.elim_none]
      exact continuousWithinAt_const
    | some k =>
      simp only [lowRead, e, Option.elim_some]
      exact (cT k _).div (cT k _) (hne k e)
  have hst : stepOf N j ca = a := by
    apply Fin.ext
    have h1 := a.2
    have h2 := ca.2
    have h3 := M.j_le
    simp only [stepOf, lastCol] at hca ⊢
    split_ifs at hca ⊢ <;> omega
  intro z hz
  have hz₄ : ∀ p k, M.blk p = some k →
      twMinor M F (baseOf M k₀ z) p.2 k (h p.1)⁻¹ (fstPt k₀ z) (stepCols N j p.2) ≠ 0 := hz.2.2.2.1
  have hz₅ : twMinor M F (baseOf M k₀ z) a k₀ (h τ)⁻¹ (sndPt k₀ z) (stepCols N j a) ≠ 0 := hz.2.2.2.2
  refine continuousWithinAt_pi.2 fun i => ?_
  rcases e : ε.symm i with l | q | u
  · simp only [wRho, e]
    have c2 : ContinuousWithinAt (r ∘ baseOf M k₀) (wO M Rb τ a k₀ ca cb F kb V r h) z :=
      ContinuousWithinAt.comp (hr _ (hbase hz)) cB.continuousWithinAt hbase
    have c3 : ContinuousAt (fun x => Rb.A.chart kb x l) ((r ∘ baseOf M k₀) z) :=
      (continuous_apply l).continuousAt.comp ((Rb.A.chart kb).continuousAt hz.2.1)
    exact ContinuousAt.comp_continuousWithinAt (g := fun x => Rb.A.chart kb x l) c3 c2
  · simp only [wRho, e]
    exact cLow (fstPt k₀) cF q.1.1 q.1.2.1 q.1.2.2 z hz fun k e' => hz₄ (q.1.1, stepOf N j q.1.2.2) k e'
  · simp only [wRho, e]
    refine (cLow (sndPt k₀) cS τ cb ca z hz fun k e' => ?_).sub (cLow (fstPt k₀) cF τ cb ca z hz fun k e' => ?_)
    · rw [hst] at e' ⊢
      obtain rfl : k₀ = k := Option.some.inj (hk.symm.trans e')
      exact hz₅
    · exact hz₄ (τ, stepOf N j ca) k e'

end Flag

end GlobalTheory.CompanionTheory.Ar.PB.WMan
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartTenth
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto

section Scale

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ}

def normScale (M : FlagModel y Ψ N j) (c : NonPluckerBlocks M.blk → ℂ) : Option K → ℂ
  | some k => if h : ∀ p, M.blk p ≠ some k then c ⟨k, h⟩ else 1
  | none => 1

theorem normScale_ne (M : FlagModel y Ψ N j) {c : NonPluckerBlocks M.blk → ℂ} (hc : ∀ k, c k ≠ 0) (o : Option K) :
    normScale M c o ≠ 0 := by
  cases o with
  | none => exact one_ne_zero
  | some k =>
    by_cases h : ∀ p, M.blk p ≠ some k
    · show dite _ _ _ ≠ 0
      rw [dite_eq_left h]
      exact hc ⟨k, h⟩
    · show dite _ _ _ ≠ 0
      rw [dite_eq_right h]
      exact one_ne_zero

theorem normScale_base (M : FlagModel y Ψ N j) (c : NonPluckerBlocks M.blk → ℂ) (k : NonPluckerBlocks M.blk) :
    normScale M c (some k.1) = c k := by
  simp [normScale, k.2]

theorem normScale_step (M : FlagModel y Ψ N j) (c : NonPluckerBlocks M.blk → ℂ) {p : Ψ × Fin N} {k : K}
    (hp : M.blk p = some k) : normScale M c (some k) = 1 := by
  have h : ¬ ∀ p, M.blk p ≠ some k := fun h => h p hp
  show dite _ _ _ = 1
  rw [dite_eq_right h]

end Scale

theorem norm : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ z ∈ wO M Rb τ a k₀ ca cb F kb V r h, baseOf M k₀ z ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt F (mCoordIdeal (baseOf M k₀ z)) ∧ SameOrbit (bl (Rb.A.chart kb (r (baseOf M k₀ z)))) (baseOf M k₀ z) ∧ ∃ (h' : Ψ → Matrix (Fin N) (Fin N) ℂ) (t' : ℂ), (∀ τ', IsBlockDiag j (h' τ') ∧ (h' τ').det ≠ 0) ∧ (∀ p k, M.blk p = some k → ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k, fstPt k₀ z ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (baseOf M k₀ z) * minorIJ (h' p.1) I (stepCols N j p.2)) ∧ ∃ α : ℂ, α ≠ 0 ∧ ∀ m : ι k₀, sndPt k₀ z ⟨k₀, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k₀, m⟩ I) (baseOf M k₀ z) * minorIJ (h' τ * (1 + Matrix.single cb ca t')) I (stepCols N j a) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h hctx z hzO
  obtain ⟨hb, hba, hk₀, hca, hcb, hAV, hF, hBC, hr, -, -⟩ := hctx
  obtain ⟨hz, hsrc, hV₀, -, -⟩ := hzO
  have z₀ : fstPt k₀ z ∈ mcPts (mCoordIdeal y) :=
    CPts.comp_mem_mcPts (Pts.isBlockMap_v₀ k₀) (algebraMap Φ (RatFunc Φ)) (funext fun _ => rfl) hz
  have hbm : baseOf M k₀ z ∈ mcPts (mCoordIdeal M.x) := CPts.base_mem M z₀
  obtain ⟨hblm, hbl1, hblG, horb⟩ := hBC.2.2.2.2 _ hV₀
  rw [(Rb.A.chart kb).left_inv hsrc] at horb
  have horbit : SameOrbit (bl (Rb.A.chart kb (r (baseOf M k₀ z)))) (baseOf M k₀ z) :=
    orbit_trans (orbit_symm horb) (hr _ hbm)
  have hG : M.GoodAt F (mCoordIdeal (baseOf M k₀ z)) := by
    rwa [← CovMap.mCoordIdeal_eq_of_sameOrbit horbit]
  refine ⟨hbm, hG, horbit, ?_⟩
  obtain ⟨c, hc, hce⟩ := id horbit
  let z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ := fun q => normScale M c q.1 * z q
  have hz' : z' ∈ mcPts (wP M τ a k₀ ca cb) :=
    mcPts_smul (CoordinateConeArithVar.isMultiHomogIdeal _) _ (normScale_ne M hc) hz
  have hbase : basePart M.blk (fstPt k₀ z') = bl (Rb.A.chart kb (r (baseOf M k₀ z))) := by
    rw [hce]
    funext q
    show normScale M c (some q.1.1) * z _ = c q.1 * z _
    rw [normScale_base]
  have hval : ∀ s : M.Ω, valAt M.x s (basePart M.blk (fstPt k₀ z')) = valAt M.x s (baseOf M k₀ z) := fun s => by
    rw [hbase]
    exact CovMap.LocImg.valAt_orbit horbit hbm s
  obtain ⟨h', t', H, H'⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Pts.main K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hba hk₀ hca hcb hAV F z' hF
    (by rw [hbase]; exact hblm) (by rw [hbase]; exact hblG) (by rw [hbase]; exact hbl1)).1 hz'
  refine ⟨h', t', H.2.1, fun p k hp => ?_, ?_⟩
  · obtain ⟨α, hα, e⟩ := H.2.2 p k hp
    refine ⟨α, hα, fun m => ?_⟩
    have e' := e m
    simp only [hval] at e'
    rw [← e']
    show z _ = normScale M c (some k) * z _
    rw [normScale_step M c hp, one_mul]
  · obtain ⟨α, hα, e⟩ := H'.2.2 (τ, a) k₀ hk₀
    refine ⟨α, hα, fun m => ?_⟩
    have e' := e m
    rw [Pts.basePart_snd M hk₀] at e'
    simp only [hval, Function.update_self] at e'
    rw [← e', Pts.snd_self, Pts.snd_self]
    show z _ = 1 * z _
    rw [one_mul]

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartThird
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Mem

theorem blockDiag_transvection {N j : ℕ} {ca cb : Fin N} (hc : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j) (t : ℂ) :
    IsBlockDiag j (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) := fun x y hxy => by
  have h1 : (1 : Matrix (Fin N) (Fin N) ℂ) x y = 0 := Matrix.one_apply_ne fun e => hxy (by rw [e])
  have h2 : Matrix.single cb ca t x y = 0 := by
    rw [Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact hxy hc.symm
  rw [Matrix.add_apply, h1, h2, add_zero]

theorem det_transvection' {N : ℕ} {ca cb : Fin N} (hc : ca ≠ cb) (t : ℂ) :
    (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ).det = 1 :=
  Matrix.det_transvection_of_ne cb ca hc.symm t

theorem cols_same_block {N j : ℕ} {a b ca cb : Fin N} (hb : (b : ℕ) = a + 1) (hbj : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) : (ca : ℕ) < N - j ↔ (cb : ℕ) < N - j := by
  have := b.2
  have := cb.2
  unfold lastCol at hca
  split_ifs at hca <;> omega

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ w ∈ wD ε V, wPhi M F bl h ε k₀ τ ca cb w ∈ mcPts (wP M τ a k₀ ca cb) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hW w hw
  obtain ⟨-, hE⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.WMan.Exact.chart_exact K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hW
  obtain ⟨hHB, hbase, hX⟩ := hE w hw
  obtain ⟨hb, hbj, hblk, hca, hcb, hvar, hF, hBC, -, -, -⟩ := hW
  obtain ⟨hmc, hnorm, hgood, -⟩ := hBC.2.2.2.2 (wB ε w) hw
  have hbase' : basePart M.blk (fstPt k₀ (wPhi M F bl h ε k₀ τ ca cb w)) = bl (wB ε w) := hbase
  have hc : ca ≠ cb := fun e => by rw [e] at hcb; omega
  refine (_root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Pts.main K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hbj hblk hca hcb hvar F
    (wPhi M F bl h ε k₀ τ ca cb w) hF (by rw [hbase']; exact hmc) (by rw [hbase']; exact hgood)
    (by rw [hbase']; exact hnorm)).2 ⟨fun τ' => wH h ε τ' w, wT ε w, ?_, ?_⟩
  · refine ⟨(hX τ a).1.1, hHB, fun p k hk => ⟨1, one_ne_zero, fun m => ?_⟩⟩
    rw [one_mul]
    exact (hX p.1 p.2).1.2 k hk m
  · refine ⟨(hX τ a).2.1, fun τ' => ?_, fun p k hk => ⟨1, one_ne_zero, fun m => ?_⟩⟩
    · by_cases e : τ' = τ
      · subst e
        rw [Function.update_self]
        refine ⟨(hHB τ').1.mul (blockDiag_transvection (cols_same_block hb hbj hca hcb) _), ?_⟩
        rw [Matrix.det_mul, det_transvection' hc, mul_one]
        exact (hHB τ').2
      · rw [Function.update_of_ne e]
        exact hHB τ'
    · rw [one_mul]
      have hm := (hX p.1 p.2).2.2 k hk m
      by_cases e : p.1 = τ
      · rw [if_pos e] at hm
        rw [e, Function.update_self]
        rw [e] at hm
        exact hm
      · rw [if_neg e] at hm
        rw [Function.update_of_ne e]
        exact hm

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Mem
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericDegreeOfArithSystemStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_degree_of_arith_system : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → GenDegStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.genDeg_of_system | exact GlobalTheory.CompanionTheory.Ar.Giv.genDeg_of_system | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.genDeg_of_system <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameChangeRegularStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_frame_change_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → FramesOK (aOf 𝔐 bW bO φ) x₀ m := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.frames_main | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.frames_main | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.frames_main <;> assumption)
end

