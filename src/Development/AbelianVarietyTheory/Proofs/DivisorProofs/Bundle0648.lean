module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0015
public import ReciprocityTheory.L2DbarEstimates.Imports
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0617
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemDomOfOrth
section
noncomputable section

namespace GlobalTheory.SUChartSection

open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def gsU (X : Data E r) (w : V (nd X)) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  FrameDegreeData.uMat (PoinPf.Gw X w τ)

def gsS (X : Data E r) (w : V (nd X)) (τ : X.Ψ) (k : Fin r) : ℝ :=
  (Real.sqrt |(((gsU X w τ)ᵀ * PoinPf.Gw X w τ * (gsU X w τ).map (starRingEnd ℂ)) k k).re|)⁻¹

def gsB (X : Data E r) (w : V (nd X)) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  gsU X w τ * Matrix.diagonal fun k => ((gsS X w τ k : ℝ) : ℂ)

def yM (X : Data E r) (w : V (nd X)) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  mat (nmat X w) τ * gsB X w τ

def yF (X : Data E r) (w : V (nd X)) : X.Ψ → Fin r → Fin r → ℂ := fun τ a b => yM X w τ a b

def dY (X : Data E r) : V (nd X) →L[ℝ] (X.Ψ → Fin r → Fin r → ℂ) := fderiv ℝ (yF X) 0

def secM (X : Data E r) (x : Frame X.Ψ r) (w : V (nd X)) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  mat x τ * yM X w τ * (mat x τ)⁻¹

theorem gram_cpt (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (w : V (nd X)) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (cpt X x w) τ) = PoinPf.Gw X w τ := by
  show gram τ.1 X.Gm (mat x τ * mat (nmat X w) τ) = _
  rw [FrameDegreeData.gram_mul, hx τ]
  rfl

theorem bOf_cpt (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (w : V (nd X)) :
    FrameDegreeData.bOf X (cpt X x w) = fun τ => gsB X w τ := by
  funext τ
  simp only [FrameDegreeData.bOf, FrameDegreeData.uOf, gram_cpt X hx, gsB, gsU]
  refine congrArg (fun d => FrameDegreeData.uMat (PoinPf.Gw X w τ) * Matrix.diagonal d) ?_
  funext k
  simp only [FrameDegreeData.sOf, FrameDegreeData.dOf, FrameDegreeData.uOf, FrameDegreeData.gram_mul, gram_cpt X hx, gsS, gsU]

theorem det_ne_of_orth (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) : (mat x τ).det ≠ 0 := by
  intro h0
  have h1 := congrArg Matrix.det (hx τ)
  rw [FrameDegreeData.gram_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul,
    Matrix.det_diagonal] at h1
  refine Finset.prod_ne_zero_iff.2 (fun a _ => ?_) h1.symm
  exact_mod_cast PoinPf.sgn_ne _ _

theorem mem_dom_of_orth (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) : x ∈ X.dom := by
  intro τ
  refine ⟨det_ne_of_orth X hx τ, fun i => ?_⟩
  have h := PoinPf.dmin_cpt_orth X hx 0 τ i
  rw [PoinPf.cpt_zero, PoinPf.Gw_zero, PoinPf.lminor_Jd] at h
  rw [h, Complex.ofReal_re]
  exact mul_self_pos.2 (PoinPf.psgn_ne _ _)

theorem exists_ball (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) :
    ∃ R > 0, ∀ w ∈ Metric.ball (0 : V (nd X)) R, cpt X x w ∈ X.dom := by
  obtain ⟨R, hR, h⟩ := PoinPf.good_ball X 0
  exact ⟨R, hR, fun w hw => PoinPf.cpt_mem_dom X (mem_dom_of_orth X hx) hx (h w hw).1 (h w hw).2.1⟩

theorem gsU_zero (X : Data E r) (τ : X.Ψ) : gsU X 0 τ = 1 := by
  ext j c
  simp only [gsU, PoinPf.Gw_zero, FrameDegreeData.uMat, Matrix.of_apply, Matrix.one_apply]
  split_ifs with h1 h2
  · rfl
  · have : FrameDegreeData.rowc (PoinPf.Jd X) c = 0 := by
      funext m
      simp only [FrameDegreeData.rowc, PoinPf.Jd, Pi.zero_apply]
      rw [Matrix.diagonal_apply_ne]
      intro hc
      have : ((Fin.castLE c.isLt.le m : Fin r) : ℕ) < c := m.isLt
      rw [← hc] at this
      exact lt_irrefl _ this
    rw [this, Matrix.zero_vecMul, Pi.zero_apply, neg_zero]
  · rfl

theorem gsB_zero (X : Data E r) (τ : X.Ψ) : gsB X 0 τ = 1 := by
  have hS : ∀ k, gsS X 0 τ k = 1 := by
    intro k
    simp only [gsS, gsU_zero, Matrix.transpose_one, Matrix.one_mul, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.mul_one, PoinPf.Gw_zero, PoinPf.Jd, Matrix.diagonal_apply_eq, Complex.ofReal_re, PoinPf.abs_sgn,
      Real.sqrt_one, inv_one]
  rw [gsB, gsU_zero, Matrix.one_mul]
  simp only [hS, Complex.ofReal_one, Matrix.diagonal_one]

theorem yM_zero (X : Data E r) (τ : X.Ψ) : yM X 0 τ = 1 := by
  rw [yM, PoinPf.nmat_zero, gsB_zero, Matrix.one_mul]

theorem secM_zero (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) : secM X x 0 τ = 1 := by
  rw [secM, yM_zero, Matrix.mul_one, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (det_ne_of_orth X hx τ))]

theorem gsB_lower (X : Data E r) (w : V (nd X)) (τ : X.Ψ) {a b : Fin r} (h : b < a) : gsB X w τ a b = 0 := by
  rw [gsB, Matrix.mul_diagonal, gsU, FrameDegreeData.uMat_upper _ h, zero_mul]

theorem gsB_diag (X : Data E r) (w : V (nd X)) (τ : X.Ψ) (a : Fin r) :
    gsB X w τ a a = ((gsS X w τ a : ℝ) : ℂ) := by
  rw [gsB, Matrix.mul_diagonal, gsU, FrameDegreeData.uMat_diag, one_mul]

end GlobalTheory.SUChartSection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyAtlasBallPartitionCover
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem nonempty_cover : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y]
    (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), Nonempty (Cover A) := by
  intro n Y _ _ _ _ _ _ ι La _ A
  classical
  have hε : ∀ x : Y, ∃ ε > 0, ball (A.chart (A.pick x) x) ε ⊆ (A.chart (A.pick x)).target :=
    fun x => Metric.isOpen_iff.1 (A.chart (A.pick x)).open_target _
      ((A.chart (A.pick x)).map_source (A.mem_pick x))
  choose ε hε0 hεb using hε
  let b : ∀ x : Y, ContDiffBump (A.chart (A.pick x) x) := fun x =>
    ⟨ε x / 4, ε x / 2, by linarith [hε0 x], by linarith [hε0 x]⟩
  let β : Y → Y → ℝ := fun x => A.chiC (A.pick x) (b x)
  let K0 : Y → Set (V n) := fun x => closedBall (A.chart (A.pick x) x) (ε x / 2)
  have hK0t : ∀ x, K0 x ⊆ (A.chart (A.pick x)).target := fun x =>
    (closedBall_subset_ball (by linarith [hε0 x])).trans (hεb x)
  have hbs : ∀ x u, (b x) u ≠ 0 → u ∈ K0 x := by
    intro x u hu
    have : u ∈ Function.support (b x) := hu
    rw [(b x).support_eq] at this
    exact ball_subset_closedBall this
  have hβs : ∀ x, A.SmoothFn (β x) := fun x =>
    A.chiC_smooth (b x).contDiff (hbs x) (isCompact_closedBall _ _) (hK0t x)
  have hβ0 : ∀ x y, 0 ≤ β x y := by
    intro x y
    show 0 ≤ A.chiC _ _ y
    unfold WeightedAtlas.chiC
    split_ifs
    · exact (b x).nonneg
    · exact le_rfl
  let U : Y → Set Y := fun x =>
    (A.chart (A.pick x)).source ∩ (A.chart (A.pick x)) ⁻¹' ball (A.chart (A.pick x) x) (ε x / 2)
  have hUo : ∀ x, IsOpen (U x) := fun x =>
    (A.chart (A.pick x)).continuousOn.isOpen_inter_preimage (A.chart (A.pick x)).open_source
      isOpen_ball
  have hUx : ∀ x, x ∈ U x := fun x => ⟨A.mem_pick x, by exact Set.mem_preimage.mpr (mem_ball_self (by linarith [hε0 x]))⟩
  have hUpos : ∀ x y, y ∈ U x → 0 < β x y := by
    rintro x y ⟨hy, hyb⟩
    show 0 < A.chiC _ _ y
    rw [A.chiC_of_mem hy]
    exact (b x).pos_of_mem_ball hyb
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo
    (fun y _ => Set.mem_iUnion.2 ⟨y, hUx y⟩)
  let pt : Fin t.card → Y := fun a => (t.equivFin.symm a).1
  let S : Y → ℝ := fun y => ∑ a, β (pt a) y
  have hS : ∀ y, 0 < S y := by
    intro y
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    have hpt : pt (t.equivFin ⟨x, hxt⟩) = x := by simp [pt]
    have h1 : β (pt (t.equivFin ⟨x, hxt⟩)) y ≤ S y :=
      Finset.single_le_sum (f := fun a => β (pt a) y) (fun a _ => hβ0 (pt a) y)
        (Finset.mem_univ _)
    rw [hpt] at h1
    linarith [hUpos x y hyx]
  have hSs : A.SmoothFn S := by
    intro j
    have : (S ∘ (A.chart j).symm) = fun v => ∑ a, β (pt a) ((A.chart j).symm v) := rfl
    rw [this]
    exact ContDiffOn.sum fun a _ => hβs (pt a) j
  refine ⟨{
    m := t.card
    idx := fun a => A.pick (pt a)
    c := fun a => A.chart (A.pick (pt a)) (pt a)
    r := fun a => 3 * ε (pt a) / 4
    chi := fun a y => β (pt a) y / S y
    r_pos := fun a => by have := hε0 (pt a); positivity
    sub := fun a => (closedBall_subset_ball (by linarith [hε0 (pt a)])).trans (hεb (pt a))
    smooth := ?_
    supp := ?_
    nonneg := fun a y => div_nonneg (hβ0 _ y) (hS y).le
    sum_one := fun y => by rw [← Finset.sum_div]; exact div_self (hS y).ne' }⟩
  · intro a j v hv
    exact ((hβs (pt a) j v hv).div (hSs j v hv) (hS _).ne')
  · intro a
    set x := pt a
    have hKc : IsClosed ((A.chart (A.pick x)).symm '' K0 x) :=
      (A.isCompact_chartImage (isCompact_closedBall _ _) (hK0t x)).isClosed
    refine (closure_minimal ?_ hKc).trans ?_
    · intro y hy
      have hy' : β x y ≠ 0 := fun h0 => hy (by simp only [h0, zero_div])
      by_contra hK
      exact hy' (A.chiC_eq_zero (hbs x) hK)
    · rintro _ ⟨u, hu, rfl⟩
      refine ⟨(A.chart (A.pick x)).map_target (hK0t x hu), ?_⟩
      simp only [Set.mem_preimage]
      rw [(A.chart (A.pick x)).right_inv (hK0t x hu)]
      exact mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hu) (by linarith [hε0 x]))

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFderivLeOfBoundedGen
section
namespace GlobalTheory.FrechetDerivativeBound

theorem norm_fderiv_le_of_bounded_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p : E} {ρ R M : ℝ} (hρ : 0 < ρ) (hR : ρ < R) (u : E → ℂ)
    (hu : DifferentiableOn ℂ u (Metric.ball p R))
    (hM : ∀ x ∈ Metric.ball p R, ‖u x‖ ≤ M) : ‖fderiv ℂ u p‖ ≤ M / ρ := by
  have hp : p ∈ Metric.ball p R := Metric.mem_ball_self (hρ.trans hR)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM p hp)
  refine ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg hM0 hρ.le) ?_
  intro v hv
  have hmem : ∀ t ∈ Metric.closedBall (0 : ℂ) ρ, p + t • v ∈ Metric.ball p R := by
    intro t ht
    rw [mem_closedBall_zero_iff] at ht
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hv, mul_one]
    exact ht.trans_lt hR
  have hline : ∀ t : ℂ, HasDerivAt (fun s : ℂ => p + s • v) v t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const v).const_add p
  have hd : DifferentiableOn ℂ (fun t : ℂ => u (p + t • v)) (Metric.closedBall 0 ρ) :=
    hu.comp (fun t _ => (hline t).differentiableAt.differentiableWithinAt) hmem
  have hdc : DiffContOnCl ℂ (fun t : ℂ => u (p + t • v)) (Metric.ball 0 ρ) := by
    apply DifferentiableOn.diffContOnCl
    rwa [closure_ball _ hρ.ne']
  have hup : DifferentiableAt ℂ u p := hu.differentiableAt (Metric.isOpen_ball.mem_nhds hp)
  have hder : HasDerivAt (fun t : ℂ => u (p + t • v)) (fderiv ℂ u p v) 0 := by
    have h1 : HasFDerivAt u (fderiv ℂ u p) (p + (0 : ℂ) • v) := by
      simpa using hup.hasFDerivAt
    exact h1.comp_hasDerivAt (0 : ℂ) (hline 0)
  rw [← hder.deriv]
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hdc
    (fun z hz => hM _ (hmem z (Metric.sphere_subset_closedBall hz)))

theorem norm_fderiv_le_of_bounded {n : ℕ} {p : ReciprocityTheory.L2DbarEstimates.V n} {ρ R M : ℝ}
    (hρ : (0 : ℝ) < ρ) (hR : ρ < R) (u : ReciprocityTheory.L2DbarEstimates.V n → ℂ)
    (hu : DifferentiableOn ℂ u (Metric.ball p R))
    (hM : ∀ x ∈ Metric.ball p R, ‖u x‖ ≤ M) : ‖fderiv ℂ u p‖ ≤ M / ρ :=
  norm_fderiv_le_of_bounded_gen hρ hR u hu hM

end GlobalTheory.FrechetDerivativeBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthNormLogBoundIffOrthBound
section
open scoped ComplexOrder Matrix
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.BrNormCompare

open GlobalTheory.IndefiniteRowSideFullHecke

theorem gramSum_eq_sumGram {K : Type} [Field K] {N n : ℕ} (hN : N = n + 1) (G' : Matrix (Fin n) (Fin n) K) (g : K) :
    OrthogonalNormSquareSum.gramSum hN G' g = ScaledCoisometryNorms.sumGram N G' g := by
  ext a b
  simp only [OrthogonalNormSquareSum.gramSum, ScaledCoisometryNorms.sumGram, Matrix.of_apply]
  by_cases ha : a.1 < n
  · simp [ha]
  · by_cases hb : b.1 < n
    · simp [ha, hb]
    · have h1 : a = Br.iL hN := Fin.ext (by have := a.2; simp only [Br.iL]; omega)
      have h2 : b = Br.iL hN := Fin.ext (by have := b.2; simp only [Br.iL]; omega)
      rw [dite_eq_right ha, dite_eq_right ha, if_neg hb, if_neg hb, if_pos ⟨h1, h2⟩]

theorem length_eq {K : Type} [Field K] [StarRing K] (s : K →+* ℂ) (hs : ∀ x : K, s (star x) = star (s x)) (g t : K) :
    s (star t * g * t) = ((‖s t‖ ^ 2 : ℝ) : ℂ) * s g := by
  rw [map_mul, map_mul, hs, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  simp only [Complex.star_def]
  ring

section

variable {K : Type} [Field K] [StarRing K] {ι : Type} [Fintype ι] {N n : ℕ}

theorem isScaledCoisometry_iff (s : K →+* ℂ) (lam : ι → DomWeight N) (G : ι → Matrix (Fin N) (Fin N) K)
    (sg : ι → DomWeight n) (G' : ι → Matrix (Fin n) (Fin n) K) (P : VV K lam →ₗ[K] VV K sg) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    OrthogonalNormSquareSum.IsScaledCoisometry s lam G sg G' P ρ ↔ 0 < ρ ^ 2 ∧ ScaledCoisometryNorms.IsScaledCoisometry s lam sg G G' P (ρ ^ 2) := by
  unfold OrthogonalNormSquareSum.IsScaledCoisometry ScaledCoisometryNorms.IsScaledCoisometry
  refine and_congr_left' ⟨fun h => pow_pos h 2, fun h => lt_of_le_of_ne hρ ?_⟩
  rintro rfl
  simp at h

theorem factor_nonneg (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) {T : ℝ} (hT : 0 < T) :
    0 ≤ OrthogonalNormSquareSum.factor hN lam sg T :=
  mul_nonneg (mul_nonneg (Real.rpow_nonneg hT.le _) (abs_nonneg _)) (Real.sqrt_nonneg _)

theorem prod_factor_sq (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) {T : ℝ} (hT : 0 < T) :
    (∏ τ, OrthogonalNormSquareSum.factor hN (lam τ) (sg τ) T) ^ 2 = ScaledCoisometryNorms.brSq hN lam sg T := by
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun τ _ => OrthogonalNormSquareSum.factor_sq hN _ _ hT

theorem const_eq (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n) {T : ℝ} (hT : 0 < T) :
    T ^ (-∑ τ, Br.nBr (lam τ) (sg τ)) * OrthogonalNormSquareSum.orthNormSq hN lam sg = ScaledCoisometryNorms.brSq hN lam sg T :=
  (ScaledCoisometryNorms.brSq_eq hN lam sg hT).symm

theorem whole_iff (s : K →+* ℂ) (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n)
    (G : ι → Matrix (Fin N) (Fin N) K) (G' : ι → Matrix (Fin n) (Fin n) K) (t : ι → K) {T : ℝ} (hT : 0 < T) :
    (OrthogonalNormSquareSum.IsScaledCoisometry s lam G sg G' (Br.brAt hN lam sg t) (∏ τ, OrthogonalNormSquareSum.factor hN (lam τ) (sg τ) T) ∧
      OrthogonalNormSquareSum.HasOpNormSq s lam G sg G' (Br.brAt hN lam sg t)
        (T ^ (-∑ τ, Br.nBr (lam τ) (sg τ)) * OrthogonalNormSquareSum.orthNormSq hN lam sg)) ↔
    ScaledCoisometryNorms.NormConcl s hN lam sg G G' t T := by
  rw [isScaledCoisometry_iff s lam G sg G' _ (Finset.prod_nonneg fun τ _ => factor_nonneg hN _ _ hT),
    prod_factor_sq hN lam sg hT, const_eq hN lam sg hT, and_assoc]
  rfl

theorem single_iff (s : K →+* ℂ) (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n)
    (G : Matrix (Fin N) (Fin N) K) (G' : Matrix (Fin n) (Fin n) K) (t : K) {T : ℝ} (hT : 0 < T) :
    OrthogonalNormSquareSum.IsScaledCoisometry s (fun _ : Unit => lam) (fun _ => G) (fun _ : Unit => sg) (fun _ => G')
        (Br.brAt hN (fun _ : Unit => lam) (fun _ : Unit => sg) fun _ => t) (OrthogonalNormSquareSum.factor hN lam sg T) ↔
      0 < ScaledCoisometryNorms.brSq hN (fun _ : Unit => lam) (fun _ : Unit => sg) T ∧
        ScaledCoisometryNorms.IsScaledCoisometry s (fun _ : Unit => lam) (fun _ : Unit => sg) (fun _ => G) (fun _ => G')
          (Br.brAt hN (fun _ : Unit => lam) (fun _ : Unit => sg) fun _ => t)
          (ScaledCoisometryNorms.brSq hN (fun _ : Unit => lam) (fun _ : Unit => sg) T) := by
  rw [isScaledCoisometry_iff _ _ _ _ _ _ (factor_nonneg hN lam sg hT), ← prod_factor_sq hN _ _ hT]
  simp

end

theorem lastMapNorm_iff_brNorm : OrthogonalNormSquareSum.LastMapNorm ↔ ScaledCoisometryNorms.BrNorm := by
  constructor
  · intro h K _ _ s hs ι _ N n hN lam sg h1 h2 G' hG g t T hT ht
    have := (h K s hs ι N n hN lam sg h1 h2 G' hG T hT g t fun τ => by rw [length_eq s hs, ht τ]).2
    rw [whole_iff s hN lam sg _ G' t hT] at this
    simpa only [gramSum_eq_sumGram] using this
  · intro h K _ _ s hs ι _ N n hN lam sg h1 h2 G' hG T hT g t ht
    have ht' : ∀ τ, ((‖s (t τ)‖ ^ 2 : ℝ) : ℂ) * s (g τ) = (T : ℂ) := fun τ => by rw [← length_eq s hs, ht τ]
    refine ⟨fun τ => ?_, ?_⟩
    · have := h K s hs Unit N n hN (fun _ => lam τ) (fun _ => sg τ) (fun _ => h1 τ) (fun _ => h2 τ) (fun _ => G' τ)
        (fun _ => hG τ) (fun _ => g τ) (fun _ => t τ) T hT (fun _ => ht' τ)
      rw [single_iff s hN _ _ _ _ _ hT, gramSum_eq_sumGram]
      exact ⟨this.1, this.2.1⟩
    · rw [whole_iff s hN lam sg _ G' t hT]
      simpa only [gramSum_eq_sumGram] using h K s hs ι N n hN lam sg h1 h2 G' hG g t T hT ht'

theorem last_ineq {ι : Type} [Fintype ι] {N n : ℕ} (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n)
    (h1 : ∀ τ, Br.Interlace hN (lam τ) (sg τ)) (a : ℝ) (ha : ∀ τ, (((lam τ).spread : ℤ) : ℝ) ≤ 2 * a) :
    ∑ τ, (2 * ((N : ℝ) - 1) * ((OrthogonalNormSquareSum.dOne hN (lam τ) (sg τ) : ℤ) : ℝ) + (N : ℝ) * ((N : ℝ) - 1) / 2) * Real.log (2 * a) ≤
      2 * ∑ τ, ((N : ℝ) * ((OrthogonalNormSquareSum.dOne hN (lam τ) (sg τ) : ℤ) : ℝ) + (N : ℝ) ^ 2) * Real.log (2 * a) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun τ _ => ?_
  have hd : (0 : ℤ) ≤ OrthogonalNormSquareSum.dOne hN (lam τ) (sg τ) := by
    refine Finset.sum_nonneg fun i _ => le_min ?_ (Finset.sum_nonneg fun j _ => (h1 τ j).1)
    have := h1 τ i
    simp only [Br.aBr, Br.bBr] at this
    omega
  have hs : (1 : ℤ) ≤ (lam τ).spread := by
    have hpos : 0 < N := by omega
    have := (lam τ).anti (show (⟨0, hpos⟩ : Fin N) ≤ ⟨N - 1, by omega⟩ from Fin.mk_le_mk.mpr (Nat.zero_le _))
    simp only [DomWeight.spread, dif_pos hpos]
    omega
  have hd' : (0 : ℝ) ≤ ((OrthogonalNormSquareSum.dOne hN (lam τ) (sg τ) : ℤ) : ℝ) := by exact_mod_cast hd
  have hs' : (1 : ℝ) ≤ (((lam τ).spread : ℤ) : ℝ) := by exact_mod_cast hs
  have hl : 0 ≤ Real.log (2 * a) := Real.log_nonneg (hs'.trans (ha τ))
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hl
  nlinarith [sq_nonneg (N : ℝ)]

end GlobalTheory.BrNormCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupChartIntegralAdditiveSeriesEqZero
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.IntAdd

theorem formalGroupLawCoboundaryOne_map_coefficients {R S : Type} [CommRing R] [CommRing S] {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (h : ∀ i, constantCoeff (μ i) = 0) (r : R →+* S)
    (f : MvPowerSeries (Fin d) R) :
    map r (cob1 μ f) = cob1 (fun i => map r (μ i)) (map r f) := by
  unfold cob1 inL inR
  rw [map_sub, map_sub, map_subst (hasSubst_of_constantCoeff_zero h),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  simp only [map_X]

theorem eq_zero_of_cob1_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ s : MvPowerSeries (Fin d) O, cob1 (up E c.μ) (map (algebraMap O E) s) = 0 → s = 0 := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ G d c E _ _ hF s hs
  have h0 : cob1 c.μ s = 0 := by
    have hm := formalGroupLawCoboundaryOne_map_coefficients c.μ c.isLaw.const (algebraMap O E) s
    have hup : (fun i => map (algebraMap O E) (c.μ i)) = up E c.μ := rfl
    rw [hup, hs] at hm
    ext α
    apply hF.inj
    have := congrArg (coeff α) hm
    rw [coeff_map] at this
    rw [this]; simp
  have hp : (p : O) ≠ 0 := by
    intro h
    exact one_ne_zero (hF.sat 1 (by rw [h, zero_mul]))
  have hev : ∀ n, c.ev n s = 0 := fun n =>
    G.eq_zero_of_cobOne_eq_zero hp n (by
      rw [← (Chart.ev₂_eval p O G d c n s).2.2.2, h0, map_zero])
  ext α
  rw [coeff_zero]
  refine hF.eq_zero_of_forall_pow_dvd fun m => ?_
  obtain ⟨n, hn⟩ := c.ker m (α.degree + 1)
  exact hn s (hev n) α (Nat.lt_succ_self _)

end GlobalTheory.QLog.IntAdd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSectionCutoffMulHolomorphic
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem smooth_cutoff_mul_sec : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (W : Set Y) (χ : Y → ℝ) (h : ι → Y → ℂ), IsOpen W → A.SmoothFn χ → tsupport χ ⊆ W → A.IsSecOn la W h → A.IsSSec la (fun i y => (χ y : ℂ) * h i y) := by
  intro n Y _ _ _ _ _ ι La _ A la W χ h hW hχ hsupp hh
  have hzero : ∀ y, y ∉ W → χ y = 0 := fun y hy =>
    Function.notMem_support.1 (fun hs => hy (hsupp (subset_tsupport χ hs)))
  refine ⟨fun i => ?_, fun i j y hi hj => ?_⟩
  · intro v hv
    refine ContDiffAt.contDiffWithinAt ?_
    set e := A.chart i
    have hvn : e.target ∈ 𝓝 v := e.open_target.mem_nhds hv
    have hχv : ContDiffAt ℝ ∞ (fun v => ((χ (e.symm v) : ℝ) : ℂ)) v :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp v ((hχ i).contDiffAt hvn)
    by_cases hy : e.symm v ∈ W
    · have hU : IsOpen (e.target ∩ e.symm ⁻¹' W) := e.isOpen_inter_preimage_symm hW
      have hh' : ContDiffAt ℝ ∞ (h i ∘ e.symm) v :=
        hyq_contDiffAt_of_holo hU (hh.1 i) ⟨hv, hy⟩
      exact hχv.mul hh'
    · have hnt : e.symm v ∉ tsupport χ := fun ht => hy (hsupp ht)
      have hev : χ =ᶠ[𝓝 (e.symm v)] 0 := notMem_tsupport_iff_eventuallyEq.1 hnt
      have hev' : ∀ᶠ v' in 𝓝 v, χ (e.symm v') = 0 := (e.continuousAt_symm hv).eventually hev
      refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [hev'] with v' hv'
      simp [hv']
  · by_cases hy : y ∈ W
    · show (χ y : ℂ) * h i y = A.g la i j y * ((χ y : ℂ) * h j y)
      rw [hh.2 i j y hy hi hj]; ring
    · show (χ y : ℂ) * h i y = A.g la i j y * ((χ y : ℂ) * h j y)
      simp [hzero y hy]

end GlobalTheory
end

