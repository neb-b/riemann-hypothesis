module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0039
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0061
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingWeight
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0059
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Assembly
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaHolomorphic

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IteratedDerivBoundGaussianGrowth
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Sl

theorem norm_iteratedDeriv_zero_le_of_gaussian_growth
    (f : ℂ → ℂ) (M lam : ℝ) (n n' i : ℕ) (hf : Differentiable ℂ f) (hlam : 0 < lam)
    (hn : 1 ≤ n) (hn' : 1 ≤ n') (hi : i ≤ n')
    (hb : ∀ τ, ‖f τ‖ ≤ M * Real.exp (n * ‖τ‖ ^ 2 * lam ^ 2 / 2)) :
    ‖iteratedDeriv i f 0‖ ≤ Real.sqrt (Real.exp 1 * n * n') ^ i * lam ^ i * M := by
  have h0 : ‖f 0‖ ≤ M := by simpa using hb 0
  have hM : 0 ≤ M := (norm_nonneg _).trans h0
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simpa using h0
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hi0' : (0 : ℝ) < i := by exact_mod_cast hi0
  have hlam2 : (0 : ℝ) < lam ^ 2 := pow_pos hlam 2
  have hq : (0 : ℝ) < i / (n * lam ^ 2) := div_pos hi0' (mul_pos hn0 hlam2)
  set R : ℝ := Real.sqrt (i / (n * lam ^ 2)) with hR
  have hR2 : R ^ 2 = i / (n * lam ^ 2) := Real.sq_sqrt hq.le
  have hRpos : 0 < R := Real.sqrt_pos.2 hq
  have hsph : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖f z‖ ≤ M * Real.exp (i / 2) := by
    intro z hz
    have hz' : ‖z‖ = R := mem_sphere_zero_iff_norm.1 hz
    have e : (n : ℝ) * ‖z‖ ^ 2 * lam ^ 2 / 2 = i / 2 := by
      rw [hz', hR2]
      field_simp
    calc ‖f z‖ ≤ M * Real.exp (n * ‖z‖ ^ 2 * lam ^ 2 / 2) := hb z
      _ = M * Real.exp (i / 2) := by rw [e]
  have hC := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le i hRpos hf.diffContOnCl hsph
  refine hC.trans ?_
  have hA : 0 ≤ (i.factorial : ℝ) * (M * Real.exp (i / 2)) / R ^ i :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hM (Real.exp_pos _).le)) (pow_nonneg hRpos.le _)
  have hB : 0 ≤ Real.sqrt (Real.exp 1 * n * n') ^ i * lam ^ i * M :=
    mul_nonneg (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (pow_nonneg hlam.le _)) hM
  refine (pow_le_pow_iff_left₀ hA hB two_ne_zero).1 ?_
  have hs1 : (Real.sqrt (Real.exp 1 * n * n') ^ i) ^ 2 = (Real.exp 1 * n * n') ^ i := by
    rw [← pow_mul, mul_comm i 2, pow_mul, Real.sq_sqrt (by positivity)]
  have hs2 : (R ^ i) ^ 2 = (i / (n * lam ^ 2)) ^ i := by
    rw [← pow_mul, mul_comm i 2, pow_mul, hR2]
  have hs3 : Real.exp (i / 2) ^ 2 = Real.exp 1 ^ i := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have key : ((i.factorial : ℝ)) ^ 2 ≤ ((i : ℝ) * n') ^ i := by
    have h1 : (i.factorial : ℝ) ≤ (i : ℝ) ^ i := by exact_mod_cast Nat.factorial_le_pow i
    have h2 : ((i : ℝ) ^ i) ^ 2 ≤ ((i : ℝ) * n') ^ i := by
      rw [← pow_mul, mul_comm i 2, pow_mul, sq]
      exact pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hi) hi0'.le) i
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) h1 2).trans h2
  have hin : (i : ℝ) ^ i ≠ 0 := pow_ne_zero _ hi0'.ne'
  have hnl : ((n : ℝ) * lam ^ 2) ^ i ≠ 0 := pow_ne_zero _ (mul_pos hn0 hlam2).ne'
  have lhs : ((i.factorial : ℝ) * (M * Real.exp (i / 2)) / R ^ i) ^ 2 =
      (M ^ 2 * Real.exp 1 ^ i * (n : ℝ) ^ i * (lam ^ 2) ^ i) * (i.factorial : ℝ) ^ 2 / (i : ℝ) ^ i := by
    rw [div_pow, mul_pow, mul_pow, hs3, hs2, div_pow]
    field_simp
    ring
  have rhs : (Real.sqrt (Real.exp 1 * n * n') ^ i * lam ^ i * M) ^ 2 =
      (M ^ 2 * Real.exp 1 ^ i * (n : ℝ) ^ i * (lam ^ 2) ^ i) * ((i : ℝ) * n') ^ i / (i : ℝ) ^ i := by
    rw [mul_pow, mul_pow, hs1]
    field_simp
    ring
  rw [lhs, rhs]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left key (by positivity)) (pow_nonneg hi0'.le _)

end GlobalTheory.CompanionTheory.Ar.Sl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionMapLocallyAnalytic
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap

section Orbit

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P : Ideal (MRing ι)} {D e : ℕ} (R : AnLogRes P ⊤ D) {Y : Type*} [TopologicalSpace Y]
  (B : FinHolAtlas e Y) {V : Y → Set Y} {μ : Y → Y → (Σ k, ι k) → ℂ} {h : Y → R.X}

theorem continuous_of_orbit_of_ne (hVo : ∀ y, IsOpen (V y)) (hVm : ∀ y, y ∈ V y)
    (hμ : ∀ y q, B.HoloOn (V y) fun u => μ y u q) (hne : ∀ y k, ∃ i, μ y y ⟨k, i⟩ ≠ 0)
    (hc : ∀ y y', ∀ u ∈ V y ∩ V y', SameOrbit (μ y u) (μ y' u))
    (hh : ∀ y, SameOrbit (R.lift (h y) (h y)) (μ y y)) : Continuous h := by
  rw [continuous_iff_continuousAt]
  intro y
  rw [ContinuousAt, tendsto_iff_ultrafilter]
  intro F hF
  obtain ⟨x, -, hx⟩ := isCompact_univ.ultrafilter_le_nhds (F.map h) (by simp)
  have hth : Tendsto h F (𝓝 x) := hx
  have hUx : ∀ᶠ y' in (F : Filter Y), h y' ∈ R.U x := hth ((R.isOpen_U x).mem_nhds (R.mem_U x))
  have hVy : ∀ᶠ y' in (F : Filter Y), y' ∈ V y := hF ((hVo y).mem_nhds (hVm y))
  have hcr : ∀ k (i i' : ι k), R.lift x x ⟨k, i⟩ * μ y y ⟨k, i'⟩ =
      R.lift x x ⟨k, i'⟩ * μ y y ⟨k, i⟩ := by
    intro k i i'
    have t1 : ∀ q, Tendsto (fun y' => R.lift x (h y') q) F (𝓝 (R.lift x x q)) := fun q =>
      (Proj.continuousAt_of_holoOn R.A (R.holo x q) (R.mem_U x)).tendsto.comp hth
    have t2 : ∀ q, Tendsto (fun y' => μ y y' q) F (𝓝 (μ y y q)) := fun q =>
      (Proj.continuousAt_of_holoOn B (hμ y q) (hVm y)).tendsto.mono_left hF
    refine tendsto_nhds_unique ((t1 ⟨k, i⟩).mul (t2 ⟨k, i'⟩))
      (((t1 ⟨k, i'⟩).mul (t2 ⟨k, i⟩)).congr' ?_)
    filter_upwards [hUx, hVy] with y' h1 h2
    exact Proj.orbit_cross (Proj.local_orbit R hVm hc hh h1 h2) k i' i
  have hxy : SameOrbit (R.lift x x) (μ y y) :=
    Proj.orbit_of_cross (R.mem x x (R.mem_U x)).1 (hne y) hcr
  have hxe : x = h y :=
    R.inj x (h y) (Proj.not_mem_mcPts_top _) (Proj.orbit_trans hxy (Proj.orbit_symm (hh y)))
  rw [← hxe]
  exact hx

end Orbit

theorem holoMap_of_local_analytic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (P J : Ideal (MRing ι)) (P' J' : Ideal (MRing ι')) (D D' : ℕ) (R : AnLogRes P J D) (R' : AnLogRes P' J' D') (g : R'.X → R.X), J = ⊤ → (∀ x, ∃ (V : Set ((Σ k, ι' k) → ℂ)) (f : ((Σ k, ι' k) → ℂ) → (Σ k, ι k) → ℂ), IsOpen V ∧ R'.lift x x ∈ V ∧ AnalyticOnNhd ℂ f V ∧ ∀ z' ∈ V ∩ mcPts P', ∀ x', SameOrbit z' (R'.lift x' x') → SameOrbit (f z') (R.lift (g x') (g x'))) → HoloMap R'.A R.A g := by
  intro K _ ι _ K' _ ι' _ P J P' J' D D' R R' g hJ hg
  subst hJ
  choose Vs f hVs hxV hf hcomp using hg
  have hcl : ∀ y, ContinuousOn (R'.lift y) (R'.U y) := fun y =>
    continuousOn_pi.2 fun p x hx =>
      (Proj.continuousAt_of_holoOn R'.A (R'.holo y p) hx).continuousWithinAt
  let V : R'.X → Set R'.X := fun y => R'.U y ∩ R'.lift y ⁻¹' Vs y
  let μ : R'.X → R'.X → (Σ k, ι k) → ℂ := fun y u => f y (R'.lift y u)
  have hVo : ∀ y, IsOpen (V y) := fun y =>
    (hcl y).isOpen_inter_preimage (R'.isOpen_U y) (hVs y)
  have hVm : ∀ y, y ∈ V y := fun y => ⟨R'.mem_U y, hxV y⟩
  have hμ : ∀ y q, R'.A.HoloOn (V y) fun u => μ y u q := by
    rintro y q j w ⟨hw, hwV⟩
    have h1 : AnalyticAt ℂ (fun w' => R'.lift y ((R'.A.chart j).symm w')) w :=
      AnalyticAt.pi fun p => R'.holo y p j w ⟨hw, hwV.1⟩
    have h2 : AnalyticAt ℂ (f y ∘ fun w' => R'.lift y ((R'.A.chart j).symm w')) w :=
      AnalyticAt.comp (hf y _ hwV.2) h1
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι k) => ℂ) q).analyticAt _ |>.comp h2
  have hor : ∀ y, ∀ u ∈ V y, SameOrbit (μ y u) (R.lift (g u) (g u)) := fun y u hu =>
    hcomp y _ ⟨hu.2, R'.mem y u hu.1⟩ u (R'.compat y u u ⟨hu.1, R'.mem_U u⟩)
  have hc : ∀ y y', ∀ u ∈ V y ∩ V y', SameOrbit (μ y u) (μ y' u) := fun y y' u hu =>
    Proj.orbit_trans (hor y u hu.1) (Proj.orbit_symm (hor y' u hu.2))
  have hh : ∀ y, SameOrbit (R.lift (g y) (g y)) (μ y y) := fun y =>
    Proj.orbit_symm (hor y y (hVm y))
  have hne : ∀ y k, ∃ i, μ y y ⟨k, i⟩ ≠ 0 := fun y k => by
    obtain ⟨i, hi⟩ := (R.mem (g y) (g y) (R.mem_U _)).1 k
    exact ⟨i, Proj.orbit_ne (hh y) hi⟩
  have hcont : Continuous g := continuous_of_orbit_of_ne R R'.A hVo hVm hμ hne hc hh
  exact ⟨hcont, Proj.analytic_of_orbit R R'.A hVo hVm hμ hc hh hcont⟩

end GlobalTheory.CompanionTheory.Ar.PB.CovMap
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MultAtTwistQuadEqStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multAt_twist_quad_eq : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (J W : Ideal (MRing ι)), W ∈ J.minimalPrimes → (twist p W).IsPrime → multAt (J.map inc ⊔ Ideal.span {quad p}) (twist p W) = multAt J W := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.multAt_twist | exact GlobalTheory.CompanionTheory.Ar.Tw.multAt_twist | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.multAt_twist <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralUniqueEmbedding
section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
open GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight

section SlopeTestRemainingChoices

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

noncomputable def conjugateProjection {e : ℕ} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) where
  toFun w := star (Ψ (star w))
  map_add' a b := by simp only [star_add, map_add (f := _)]
  map_smul' c w := by
    simp only [star_smul, map_smul, RingHom.id_apply, star_star]

theorem conjugateProjection_star {e : ℕ} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (w : ((k : K) → ι k) → ℂ) : conjugateProjection Ψ (star w) = star (Ψ w) := by
  change star (Ψ (star (star w))) = _
  rw [star_star]

theorem isSectionOn_one_of_degree_zero {P : Ideal (MRing ι)} {d : ℕ} {A : HermLine ι}
    (hP : IsArithVar P d) (hA : A.a = 0) : IsSectionOn P A 1 := by
  refine ⟨0, fun k => by simp [hA], ?_, ?_⟩
  · intro m hm k
    have hm0 : m = 0 := by
      classical
      have := MvPolynomial.support_one (R := ℤ) (σ := Σ k, ι k) ▸ hm
      simpa using this
    simp [hm0]
  · exact (Ideal.ne_top_iff_one P).1 hP.2.1.1.ne_top


open Classical in
theorem logNorm_one_eq_indicator {Ω F : Type} [Field Ω] [Field F] [Algebra F Ω] {y : (Σ k, ι k) → Ω}
    {P : Ideal (MRing ι)} {tg : F →+* ℂ} {B : HermLine ι}
    (huniq : ∀ z ∈ mcPts P, ∃! s : F →+* ℂ, LiesOver y s z)
    (hB : ∀ z ∈ mcPts P, ∀ s : F →+* ℂ, LiesOver y s z → B.h z = if s = tg then Real.exp (-1) else 1) :
    ∀ z ∈ mcPts P, logNorm B 1 z = ({z | LiesOver y tg z}.indicator fun _ => (1 : ℝ)) z := by
  classical
  intro z hz
  obtain ⟨s, hs, hs'⟩ := huniq z hz
  have hone : ‖eval z (map (Int.castRingHom ℂ) (1 : MRing ι))‖ = 1 := by simp
  unfold logNorm
  rw [hone, hB z hz s hs]
  by_cases hst : s = tg
  · subst hst
    rw [Set.indicator_of_mem (show z ∈ {z | LiesOver y s z} from hs), if_pos rfl, one_div,
      Real.log_inv, Real.log_exp, neg_neg]
  · rw [Set.indicator_of_notMem (fun h => hst (hs' tg h).symm), if_neg hst]
    simp

end SlopeTestRemainingChoices

theorem conjugate_pieces_same_mass :
    ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin D → HermLine ι) (sg : F →+* ℂ), IsArithVar (mCoordIdeal y) (D + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsConjInvariantH (L j)) → (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) → ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y (ComplexEmbedding.conjugate sg) z}.indicator fun _ => (1 : ℝ)) = ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) := by
  intro hRes K _ ι _ Ω _ F _ _ _ y D L sg hP hL hC huniq
  classical
  have hpos : ∀ tg s : F →+* ℂ, 0 < (if s = tg then Real.exp (-1) else (1 : ℝ)) := by
    intro tg s
    split_ifs
    · exact Real.exp_pos _
    · exact one_pos
  obtain ⟨B, hBa, hBs, hB⟩ := exists_smooth_weight_const_near_embeddings K ι Ω F y
    (fun s => if s = sg then Real.exp (-1) else 1) (hpos sg) huniq
  obtain ⟨B', hBa', hBs', hB'⟩ := exists_smooth_weight_const_near_embeddings K ι Ω F y
    (fun s => if s = ComplexEmbedding.conjugate sg then Real.exp (-1) else 1)
    (hpos (ComplexEmbedding.conjugate sg)) huniq
  have hBv : ∀ z ∈ mcPts (mCoordIdeal y), ∀ s : F →+* ℂ, LiesOver y s z →
      B.h z = if s = sg then Real.exp (-1) else 1 := fun z hz s hs => (hB z hz s hs).self_of_nhds
  have hBv' : ∀ z ∈ mcPts (mCoordIdeal y), ∀ s : F →+* ℂ, LiesOver y s z →
      B'.h z = if s = ComplexEmbedding.conjugate sg then Real.exp (-1) else 1 :=
    fun z hz s hs => (hB' z hz s hs).self_of_nhds
  rw [← GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts (mCoordIdeal y)
      (fun _ _ _ => rfl) (logNorm_one_eq_indicator huniq hBv'),
    ← GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts (mCoordIdeal y)
      (fun _ _ _ => rfl) (logNorm_one_eq_indicator huniq hBv)]
  by_cases hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ), IsGoodProj (mCoordIdeal y) Ψ
  · obtain ⟨Ψ, hΨ⟩ := hex
    have hstar : ∀ z ∈ mcPts (mCoordIdeal y), B'.h (star z) = B.h z := by
      intro z hz
      obtain ⟨s, hs, -⟩ := huniq z hz
      have hzc : star z ∈ mcPts (mCoordIdeal y) := conjVec_mem_mcPts hz
      have hsc : LiesOver y (ComplexEmbedding.conjugate s) (star z) := liesOver_conjVec hs
      have hiff : ComplexEmbedding.conjugate s = ComplexEmbedding.conjugate sg ↔ s = sg :=
        ⟨fun h => by simpa using congrArg ComplexEmbedding.conjugate h, fun h => by rw [h]⟩
      rw [hBv' _ hzc _ hsc, hBv z hz s hs]
      simp only [hiff]
    obtain ⟨hΨ', hI⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegralAt_conj K ι (mCoordIdeal y) D Ψ (conjugateProjection Ψ) L B B' hP hΨ
      (conjugateProjection_star Ψ) hL hC hBa hBs hBa' hBs' hstar
    rw [ptsIntegral_eq_at hRes resBridge hP hΨ' hL hBs' (isSectionOn_one_of_degree_zero hP hBa'),
      ptsIntegral_eq_at hRes resBridge hP hΨ hL hBs (isSectionOn_one_of_degree_zero hP hBa), hI]
  · unfold ptsIntegral
    rw [dite_eq_right hex, dite_eq_right hex]

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SemicharacterThetaCharacteristic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.Ar.Nform

theorem exists_half_canMult : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (bs : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (χ : Λ → ℂ),
    (∀ l l' : Λ, χ (l + l') = χ l * χ l' * Complex.exp (Real.pi * Complex.I *
      (((∑ i, (bs.repr l (Sum.inr i) * bs.repr l' (Sum.inl i) - bs.repr l (Sum.inl i) * bs.repr l' (Sum.inr i)) : ℤ) : ℝ) : ℂ))) →
    (∀ l, χ l ^ 2 = 1) →
    ∃ a c : Fin g → ℝ, (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ (∀ i, c i = 0 ∨ c i = 1 / 2) ∧
      ∀ x, χ x = GlobalTheory.CanTh.canMult a c (fun i => bs.repr x (Sum.inl i)) (fun i => bs.repr x (Sum.inr i)) := by
  intro g Λ bs χ hχ hsq
  classical
  have hpm : ∀ l, χ l = 1 ∨ χ l = -1 := fun l =>
    mul_self_eq_one_iff.mp (by rw [← sq]; exact hsq l)
  have hexp : ∀ k : ℤ, Complex.exp (↑Real.pi * Complex.I * ((k : ℝ) : ℂ)) = (-1) ^ k := by
    intro k
    rw [Complex.ofReal_intCast, mul_comm, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  have hhalf : Complex.exp (2 * ↑Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ)) = -1 := by
    rw [show (2 : ℂ) * ↑Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ) = ↑Real.pi * Complex.I by
      push_cast; ring, Complex.exp_pi_mul_I]
  have hhalf' : Complex.exp (-(2 * ↑Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ))) = -1 := by
    rw [Complex.exp_neg, hhalf]
    norm_num
  have hsame : ∀ j k : Fin g ⊕ Fin g, bs.repr (bs j) k = if j = k then 1 else 0 := by
    intro j k
    rw [Module.Basis.repr_self, Finsupp.single_apply]
  have hsingle : ∀ i : Fin g, (fun k => bs.repr (bs (Sum.inl i)) (Sum.inl k)) = Pi.single i 1 ∧
      (fun k => bs.repr (bs (Sum.inl i)) (Sum.inr k)) = 0 ∧
      (fun k => bs.repr (bs (Sum.inr i)) (Sum.inl k)) = 0 ∧
      (fun k => bs.repr (bs (Sum.inr i)) (Sum.inr k)) = Pi.single i 1 := by
    intro i
    refine ⟨funext fun k => ?_, funext fun k => ?_, funext fun k => ?_, funext fun k => ?_⟩ <;>
      by_cases hk : k = i
    · subst hk; simp [hsame]
    · simp [hsame, Pi.single_apply, hk, Ne.symm hk]
    · simp [hsame]
    · simp [hsame]
    · simp [hsame]
    · simp [hsame]
    · subst hk; simp [hsame]
    · simp [hsame, Pi.single_apply, hk, Ne.symm hk]
  have hdot : ∀ (a : Fin g → ℝ) (i : Fin g),
      (a ⬝ᵥ fun k => (((Pi.single i 1 : Fin g → ℤ) k : ℤ) : ℝ)) = a i := by
    intro a i
    simp [dotProduct, Pi.single_apply]
  have hdot0 : ∀ a : Fin g → ℝ, (a ⬝ᵥ fun k => (((0 : Fin g → ℤ) k : ℤ) : ℝ)) = 0 := by
    intro a
    simp [dotProduct]
  have hC_inl : ∀ (a c : Fin g → ℝ) (i : Fin g),
      GlobalTheory.CanTh.canMult a c (fun k => bs.repr (bs (Sum.inl i)) (Sum.inl k))
        (fun k => bs.repr (bs (Sum.inl i)) (Sum.inr k)) =
        Complex.exp (2 * ↑Real.pi * Complex.I * ((a i : ℝ) : ℂ)) := by
    intro a c i
    obtain ⟨h1, h2, -, -⟩ := hsingle i
    rw [h1, h2]
    simp only [GlobalTheory.CanTh.canMult, dotProduct_zero, hdot, hdot0]
    congr 1
    push_cast
    ring
  have hC_inr : ∀ (a c : Fin g → ℝ) (i : Fin g),
      GlobalTheory.CanTh.canMult a c (fun k => bs.repr (bs (Sum.inr i)) (Sum.inl k))
        (fun k => bs.repr (bs (Sum.inr i)) (Sum.inr k)) =
        Complex.exp (-(2 * ↑Real.pi * Complex.I * ((c i : ℝ) : ℂ))) := by
    intro a c i
    obtain ⟨-, -, h3, h4⟩ := hsingle i
    rw [h3, h4]
    simp only [GlobalTheory.CanTh.canMult, zero_dotProduct, hdot, hdot0]
    congr 1
    push_cast
    ring
  obtain ⟨a, ha⟩ : ∃ a : Fin g → ℝ, a = fun i => if χ (bs (Sum.inl i)) = 1 then 0 else 1 / 2 :=
    ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Fin g → ℝ, c = fun i => if χ (bs (Sum.inr i)) = 1 then 0 else 1 / 2 :=
    ⟨_, rfl⟩
  refine ⟨a, c, fun i => ?_, fun i => ?_, ?_⟩
  · simp only [ha]
    split_ifs <;> norm_num
  · simp only [hc]
    split_ifs <;> norm_num
  have hχ0 : ∀ l, χ l ≠ 0 := by
    intro l h
    have h' := hsq l
    rw [h] at h'
    norm_num at h'
  have hψ0 : ∀ l : Λ, GlobalTheory.CanTh.canMult a c (fun i => bs.repr l (Sum.inl i))
      (fun i => bs.repr l (Sum.inr i)) ≠ 0 := by
    intro l
    simp only [GlobalTheory.CanTh.canMult]
    exact Complex.exp_ne_zero _
  have hψ : ∀ l l' : Λ,
      GlobalTheory.CanTh.canMult a c (fun i => bs.repr (l + l') (Sum.inl i))
                   (fun i => bs.repr (l + l') (Sum.inr i)) =
        GlobalTheory.CanTh.canMult a c (fun i => bs.repr l (Sum.inl i))
                     (fun i => bs.repr l (Sum.inr i)) *
          GlobalTheory.CanTh.canMult a c (fun i => bs.repr l' (Sum.inl i))
            (fun i => bs.repr l' (Sum.inr i)) *
          Complex.exp (Real.pi * Complex.I *
            (((∑ i, (bs.repr l (Sum.inr i) * bs.repr l' (Sum.inl i) -
              bs.repr l (Sum.inl i) * bs.repr l' (Sum.inr i)) : ℤ) : ℝ) : ℂ)) := by
    intro l l'
    have hm : (fun i => bs.repr (l + l') (Sum.inl i)) =
        (fun i => bs.repr l (Sum.inl i)) + (fun i => bs.repr l' (Sum.inl i)) := by
      funext i
      simp [map_add (f := _)]
    have hn : (fun i => bs.repr (l + l') (Sum.inr i)) =
        (fun i => bs.repr l (Sum.inr i)) + (fun i => bs.repr l' (Sum.inr i)) := by
      funext i
      simp [map_add (f := _)]
    rw [hm, hn, GlobalTheory.HolTheta.canMult_add, hexp, Finset.sum_sub_distrib]
    rfl
  have hbasis : ∀ j : Fin g ⊕ Fin g, χ (bs j) =
      GlobalTheory.CanTh.canMult a c (fun i => bs.repr (bs j) (Sum.inl i))
        (fun i => bs.repr (bs j) (Sum.inr i)) := by
    rintro (i | i)
    · rw [hC_inl]
      rcases hpm (bs (Sum.inl i)) with h | h
      · simp [ha, h]
      · have h' : χ (bs (Sum.inl i)) ≠ 1 := by rw [h]; norm_num
        simp only [ha, h', if_false]
        rw [h, hhalf]
    · rw [hC_inr]
      rcases hpm (bs (Sum.inr i)) with h | h
      · simp [hc, h]
      · have h' : χ (bs (Sum.inr i)) ≠ 1 := by rw [h]; norm_num
        simp only [hc, h', if_false]
        rw [h, hhalf']
  exact GlobalTheory.HolTheta.eq_of_cocycle bs
    (fun l l' => Complex.exp (Real.pi * Complex.I *
      (((∑ i, (bs.repr l (Sum.inr i) * bs.repr l' (Sum.inl i) -
        bs.repr l (Sum.inl i) * bs.repr l' (Sum.inr i)) : ℤ) : ℝ) : ℂ)))
    (ψ := fun l => GlobalTheory.CanTh.canMult a c (fun i => bs.repr l (Sum.inl i))
      (fun i => bs.repr l (Sum.inr i)))
    (fun _ _ => Complex.exp_ne_zero _) hχ0 hψ0 hχ hψ hbasis

end GlobalTheory.CompanionTheory.Ar.Nform
end

