module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianChartScalarInvariance
section
open UpperTheory.V.Lit.Geo
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Lit.Bor
open scoped ContDiff

private theorem scal_mem {E : Type} [Field E] [NumberField E] {a : ℕ} {y : Lie E a} (hy : y ∈ invSet E a) :
    sc (Matrix.of y) • y ∈ invSet E a := by
  have hc : sc (Matrix.of y) ≠ 0 := (Real.exp_pos _).ne'
  have hy' : IsUnit (Matrix.of y) := hy
  have h : IsUnit (sc (Matrix.of y) • Matrix.of y) := by
    rw [Algebra.smul_def]
    exact ((IsUnit.mk0 _ hc).map (algebraMap ℝ (Matrix (Fin a) (Fin a) (Cinf E)))).mul hy'
  exact h

private theorem chart_eq {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (ha : 1 ≤ a)
    (L : AddSubgroup (Fin a → Af E)) (P : (Fin a → Cinf E) → ℂ) (g : GA E a) {y : Lie E a} (hy : y ∈ invSet E a) :
    chart (gsum L (pg P)) g y = msum (fun v : lat L g => pt (rt g) v.1) P (sc (Matrix.of y) • y) := by
  obtain ⟨u, hu⟩ := hy
  obtain rfl : y = toL u.val := hu.symm
  rw [chart_val, (UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℂ (pg P)).2.1 g u]
  refine tsum_congr fun v => congrArg (pg P) ?_
  exact (Matrix.vecMul_smul _ _ _).symm

theorem UpperTheory.hermitian_chart_scalar_invariance :
    ThSm := by
  intro E _ _ _ a ha L hL P hP
  obtain ⟨N, hN⟩ := UpperTheory.geometry_of_numbers_lattice_estimate E a ha L hL
  obtain ⟨hs, h1, hd, -⟩ := UpperTheory.deriv_similitudeChar_at_one_eq_trace E a
  have hS : ContDiffOn ℝ ∞ (fun y : Lie E a => sc (Matrix.of y) • y) (invSet E a) := hs.smul contDiffOn_id
  refine ⟨⟨gsum L (pg P), fun g => ?_⟩, rfl, fun X => ?_⟩
  · exact ((UpperTheory.smooth_sum_left_right_mul_order E a _ _ N (hN g) P hP).comp hS fun y hy => scal_mem hy).congr
      fun y hy => chart_eq ha L P g hy
  · have ho : oneL E a ∈ invSet E a := isUnit_one
    have hn : invSet E a ∈ nhds (oneL E a) := isOpen_invSet.mem_nhds ho
    have h1' : sc (Matrix.of (oneL E a)) = 1 := h1
    have hsd : DifferentiableAt ℝ (fun y : Lie E a => sc (Matrix.of y)) (oneL E a) :=
      (hs.contDiffAt hn).differentiableAt (by simp)
    have hSd := hsd.hasFDerivAt.smul (hasFDerivAt_id (oneL E a))
    let Z : Lie E a := X + (-ell E a X) • oneL E a
    let T : (Fin a → Cinf E) →ₗ[ℝ] (Fin a → Cinf E) := (Matrix.vecMulLinear (Matrix.of Z)).restrictScalars ℝ
    obtain ⟨Q, hQ, hT⟩ := (UpperTheory.quadratic_form_gradient_formula E a P hP).2.2 T
    refine ⟨Q, hQ, funext fun g => ?_⟩
    obtain ⟨-, hF, hF'⟩ := UpperTheory.sum_der E a _ _ N (hN g) P hP _ ho
    have e : chart (gsum L (pg P)) g =ᶠ[nhds (oneL E a)]
        msum (fun v : lat L g => pt (rt g) v.1) P ∘ fun y : Lie E a => sc (Matrix.of y) • y :=
      Filter.eventually_of_mem hn fun y hy => chart_eq ha L P g hy
    have hF1 : HasFDerivAt (msum (fun v : lat L g => pt (rt g) v.1) P)
        (fderiv ℝ (msum (fun v : lat L g => pt (rt g) v.1) P) (oneL E a)) (sc (Matrix.of (oneL E a)) • oneL E a) := by
      rw [h1', one_smul]
      exact hF.hasFDerivAt
    have hc := HasFDerivAt.comp (f := fun y : Lie E a => sc (Matrix.of y) • y) (oneL E a) hF1 hSd
    change fderiv ℝ (chart (gsum L (pg P)) g) (oneL E a) X = _
    rw [e.fderiv_eq, hc.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, h1', one_smul, hd, id]
    rw [hF']
    refine tsum_congr fun v => ?_
    rw [← hT]
    have e1 : pt (rt g) v.1 ᵥ* Matrix.of (oneL E a) = pt (rt g) v.1 := Matrix.vecMul_one _
    rw [e1]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianPointEmbeddingInjective
section
open UpperTheory.V.Lit.Geo

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor in
private theorem pt_injective {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (g : GA E a) :
    Function.Injective (pt g) := by
  intro v v' h
  have hu : IsUnit (GeneralLinearGroup.map (pInf E) g).val := Units.isUnit _
  have h1 : vInf v = vInf v' := Matrix.vecMul_injective_of_isUnit hu h
  funext i
  have h2 : ((pInf E).comp (algebraMap E (Ad E))) (v i) = ((pInf E).comp (algebraMap E (Ad E))) (v' i) := congrFun h1 i
  exact ((pInf E).comp (algebraMap E (Ad E))).injective h2

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor in
theorem UpperTheory.hermitian_point_embedding_injective :
    GradA := by
  intro E _ _ _ a ha L hL
  obtain ⟨c, hc, hlow⟩ := UpperTheory.geometric_side_comparison
  obtain ⟨N, hN⟩ := UpperTheory.geometry_of_numbers_lattice_estimate E a ha L hL
  obtain ⟨C, -, hC⟩ := UpperTheory.moment_bound_of_pointwise_moments N 1
  have hD : (0 : ℝ) < (a : ℝ) * Fintype.card (InfinitePlace E) := by
    have h1 : (0 : ℝ) < a := by exact_mod_cast ha
    have h2 : (0 : ℝ) < Fintype.card (InfinitePlace E) := by exact_mod_cast Fintype.card_pos
    exact mul_pos h1 h2
  refine ⟨c / ((a : ℝ) * Fintype.card (InfinitePlace E)), div_pos hc hD, fun g hg => ?_⟩
  have hell : ell E a (toL (mom L g).1) = trF (mom L g).1 1 / ((a : ℝ) * Fintype.card (InfinitePlace E)) := by
    simp only [trF, mul_one, Matrix.trace, Matrix.diag, Finset.sum_apply, Complex.re_sum]
    rfl
  rw [hell]
  refine div_le_div_of_nonneg_right ?_ hD.le
  rw [UpperTheory.hermitian_space_moment_identity E a ha L hL g 1, le_div_iff₀ (by linarith)]
  simp only [(UpperTheory.geometric_side_quadraticForm_identity E a).1]
  let φ : lat L g →+ EuclideanSpace ℂ (Fin a × InfinitePlace E) :=
    ((euc (E := E) (a := a)).toLinearMap.toAddMonoidHom.comp (pt (rt g))).comp (lat L g).subtype
  have hφ : ∀ v : lat L g, ‖φ v‖ ^ 2 = qf (pt (rt g) v.1) := fun v => norm_euc_sq _
  have hinj : Function.Injective φ := fun v v' h =>
    Subtype.ext (pt_injective (rt g) ((euc (E := E) (a := a)).injective h))
  have hs0 : Summable fun v : lat L g => Real.exp (-Real.pi * qf (pt (rt g) v.1)) := by
    simpa only [one_mul] using ((hN g).2 1 1 one_pos le_rfl).1
  have hs1 : Summable fun v : lat L g => qf (pt (rt g) v.1) * Real.exp (-Real.pi * qf (pt (rt g) v.1)) := by
    refine ((hC _ _ (hN g)).1.sub hs0).congr fun v => ?_
    ring
  have := hlow (lat L g) _ φ hinj
  simp only [hφ] at this
  exact this hs0 hs1 hg
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpaceGradientEstimate
section
open UpperTheory.V.Lit.Geo

private theorem gradB_pt {z n W q c : ℝ} (hc : 0 < c) (hq : 0 ≤ q)
    (h1 : n ^ 2 ≤ z) (h2 : z ≤ W * q) (h3 : z = 0 ∨ c ≤ n) :
    z ≤ W ^ 2 / c ^ 2 * (1 + q) ^ 2 := by
  have hc2 : 0 < c ^ 2 := by positivity
  rcases h3 with h | h
  · rw [h]; positivity
  · have hz : c ^ 2 ≤ z := (pow_le_pow_left₀ hc.le h 2).trans h1
    have hz0 : 0 ≤ z := hc2.le.trans hz
    rw [div_mul_eq_mul_div, le_div_iff₀ hc2]
    have a1 : z * c ^ 2 ≤ z * z := mul_le_mul_of_nonneg_left hz hz0
    have a2 : z * z ≤ (W * q) * (W * q) := mul_self_le_mul_self hz0 h2
    have a3 : q ^ 2 ≤ (1 + q) ^ 2 := by nlinarith
    have a4 : W ^ 2 * q ^ 2 ≤ W ^ 2 * (1 + q) ^ 2 := mul_le_mul_of_nonneg_left a3 (sq_nonneg W)
    nlinarith

theorem UpperTheory.hermitian_space_gradient_estimate :
    GradB := by
  intro E _ _ _ a ha L hL
  obtain ⟨N, hN⟩ := UpperTheory.geometry_of_numbers_lattice_estimate E a ha L hL
  obtain ⟨C, hC0, hC⟩ := UpperTheory.moment_bound_of_pointwise_moments N 2
  refine ⟨C, fun g w c hc hsep => ?_⟩
  obtain ⟨hs, hle⟩ := hC _ _ (hN g)
  have hTh : 1 ≤ Th L g := ((UpperTheory.hermitian_space_geometric_estimate E a ha L hL).1 g).1
  have hTh0 : 0 < Th L g := lt_of_lt_of_le one_pos hTh
  have hR := (UpperTheory.traceForm_cauchy_schwarz_cmDatum E a w).2.2
  rw [UpperTheory.hermitian_space_moment_identity E a ha L hL g, div_le_iff₀ hTh0]
  have hK : 0 ≤ qf w ^ 2 / c ^ 2 := by positivity
  have hpt : ∀ v : lat L g, quad (Matrix.vecMulVec w (star w)) (pt (rt g) v.1) * gauss (pt (rt g) v.1) ≤
      qf w ^ 2 / c ^ 2 * ((1 + qf (pt (rt g) v.1)) ^ 2 * Real.exp (-Real.pi * qf (pt (rt g) v.1))) := by
    intro v
    obtain ⟨r1, r2, r3⟩ := hR (pt (rt g) v.1)
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right
      (gradB_pt hc (qf_nonneg _) r1 r2 ((hsep v.1 v.2).imp r3 id)) (Real.exp_pos _).le
  have hnn : ∀ v : lat L g, 0 ≤ quad (Matrix.vecMulVec w (star w)) (pt (rt g) v.1) * gauss (pt (rt g) v.1) :=
    fun v => mul_nonneg ((sq_nonneg _).trans (hR _).1) (Real.exp_pos _).le
  have hs2 := hs.mul_left (qf w ^ 2 / c ^ 2)
  have hs1 := Summable.of_nonneg_of_le hnn hpt hs2
  refine (hs1.tsum_le_tsum hpt hs2).trans ?_
  rw [tsum_mul_left]
  refine (mul_le_mul_of_nonneg_left hle hK).trans (le_of_eq ?_)
  change _ * (C * Th L g) = _
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianTraceFormEntryEstimate
section
open UpperTheory.V.Lit.Geo

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

private theorem entry_le {E : Type} [Field E] [NumberField E] {a : ℕ} (M : Matrix (Fin a) (Fin a) (Cinf E))
    (i j : Fin a) (w : InfinitePlace E) : ‖M i j w‖ ≤ ‖toL M‖ :=
  (norm_le_pi_norm (toL M i j) w).trans ((norm_le_pi_norm (toL M i) j).trans (norm_le_pi_norm (toL M) i))

private theorem abs_trF_le {E : Type} [Field E] [NumberField E] {a : ℕ} (M p : Matrix (Fin a) (Fin a) (Cinf E)) :
    |trF M p| ≤ Fintype.card (InfinitePlace E) * (a * (a * (‖toL M‖ * ‖toL p‖))) := by
  unfold trF
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (a * (a * (‖toL M‖ * ‖toL p‖))) ?_).trans (by simp)
  intro w _
  refine (Complex.abs_re_le_norm _).trans ?_
  have h : (M * p).trace w = ∑ i, ∑ j, M i j w * p j i w := by
    simp [Matrix.trace, Matrix.mul_apply, Finset.sum_apply]
  rw [h]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (a * (‖toL M‖ * ‖toL p‖)) ?_).trans (by simp)
  intro i _
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (‖toL M‖ * ‖toL p‖) ?_).trans (by simp)
  intro j _
  rw [norm_mul]
  exact mul_le_mul (entry_le M i j w) (entry_le p j i w) (norm_nonneg _) (norm_nonneg _)

private theorem trF_add_smul {E : Type} [Field E] [NumberField E] {a : ℕ} (M p p' : Matrix (Fin a) (Fin a) (Cinf E))
    (c : ℝ) : trF M (p + c • p') = trF M p + c * trF M p' := by
  unfold trF
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul]
  simp

theorem UpperTheory.hermitian_trace_form_entry_estimate :
    FnTaylor := by
  intro E _ _ _ a ha L hL
  obtain ⟨N, hN⟩ := UpperTheory.geometry_of_numbers_lattice_estimate E a ha L hL
  obtain ⟨C₁, hC₁, hT⟩ := UpperTheory.two_sided_bound_of_pointwise_bounds N
  obtain ⟨C₂, ε₂, hC₂, hε₂, hS⟩ := UpperTheory.second_order_taylor_remainder_bound E a
  obtain ⟨-, ⟨B, hB, hBd⟩, -⟩ := UpperTheory.hermitian_trace_form_estimate E a ha L hL
  obtain ⟨hq1, hqa, hqh, hqc, hqb, -⟩ := UpperTheory.geometric_side_quadraticForm_identity E a
  obtain ⟨-, -, -, hsc, -⟩ := UpperTheory.deriv_similitudeChar_at_one_eq_trace E a
  set K : ℝ := C₂ + (1 + C₂) * a with hK
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hK0 : 0 ≤ K := by positivity
  set D : ℝ := ‖toL (1 : Matrix (Fin a) (Fin a) (Cinf E))‖ + 1 with hD
  have hD0 : 0 ≤ D := by positivity
  set n : ℝ := (Fintype.card (InfinitePlace E) : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  refine ⟨C₁ * K ^ 2 + Real.pi * (C₂ * (n * (a * (a * (B * D))))), min ε₂ (min 1 (1 / (4 * (K + 1)))),
    by positivity, by positivity, ?_⟩
  intro g Y h hl hY hh
  set y := ‖toL Y‖ with hy
  have hy0 : 0 ≤ y := norm_nonneg _
  have hy2 : y ≤ ε₂ := hY.trans (min_le_left _ _)
  have hy1 : y ≤ 1 := hY.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hy3 : y ≤ 1 / (4 * (K + 1)) := hY.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hKy : K * y ≤ 1 / 4 := by
    rw [le_div_iff₀ (by positivity)] at hy3
    nlinarith only [hy3, hy0]
  have hs := hS Y hy2
  rw [hl, add_zero, ← hy] at hs
  set s := sc (1 + Y) with hsdef
  have hs1 : |s - 1| ≤ C₂ * y := hs.trans (mul_le_mul_of_nonneg_left (by nlinarith only [hy0, hy1]) hC₂)
  have hs2 : |s - 1| ≤ C₂ := hs1.trans (by nlinarith only [hy1, hC₂])
  have hs3 : |s| ≤ 1 + C₂ := by
    have := abs_le.1 hs2
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  set p := Y + (s - 1) • (1 + Y) with hp
  have hquad : ∀ x, quad p x = (s - 1) * qf x + s * quad Y x := by
    intro x
    rw [hp, (hqa _ _ 0 x).1, (hqa _ 0 (s - 1) x).2, (hqa _ _ 0 x).1, hq1]
    ring
  have hu : ∀ x, |quad p x| ≤ K * y * qf x := by
    intro x
    have hx := qf_nonneg x
    rw [hquad]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hx]
    have h1 : |s - 1| * qf x ≤ C₂ * y * qf x := mul_le_mul_of_nonneg_right hs1 hx
    have h2 : |s| * |quad Y x| ≤ (1 + C₂) * (a * y * qf x) :=
      mul_le_mul hs3 (hqb Y x) (abs_nonneg _) (by positivity)
    calc _ ≤ C₂ * y * qf x + (1 + C₂) * (a * y * qf x) := add_le_add h1 h2
      _ = K * y * qf x := by rw [hK]; ring
  haveI : Nonempty (lat L g) := ⟨0⟩
  have key := hT (lat L g) (fun v => qf (pt (rt g) v.1)) (fun v => quad p (pt (rt g) v.1)) (K * y) (hN g)
    (by positivity) hKy (fun v => hu _)
  have e1 : fn L (g * infGL E a h) =
      Real.log (∑' v : lat L g, Real.exp (-Real.pi * (qf (pt (rt g) v.1) + quad p (pt (rt g) v.1)))) := by
    unfold fn Th
    rw [(UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℝ gauss).2.1 g h]
    congr 1
    refine tsum_congr fun v => ?_
    unfold gauss
    rw [hqc, hqh, ← hsc h, hh, ← hsdef, hquad, (hqa _ _ 0 _).1, hq1]
    congr 2
    ring
  have e2 := UpperTheory.hermitian_space_moment_identity E a ha L hL g p
  have key' : |fn L (g * infGL E a h) - fn L g + Real.pi * trF (mom L g).1 p| ≤
      C₁ * (K * y) ^ 2 := by
    rw [e1, e2]
    exact key
  rw [hp, trF_add_smul] at key'
  have h1 : ‖toL (1 + Y)‖ ≤ D := by
    have : toL (1 + Y) = toL 1 + toL Y := rfl
    rw [this]
    exact (norm_add_le _ _).trans (by rw [hD]; linarith)
  have h2 : |trF (mom L g).1 (1 + Y)| ≤ n * (a * (a * (B * D))) := by
    refine (abs_trF_le _ _).trans ?_
    have := mul_le_mul (hBd g).1 h1 (norm_nonneg _) hB.le
    gcongr
  have h3 : |Real.pi * ((s - 1) * trF (mom L g).1 (1 + Y))| ≤
      Real.pi * (C₂ * y ^ 2 * (n * (a * (a * (B * D))))) := by
    rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hs h2 (abs_nonneg _) (by positivity)) Real.pi_pos.le
  have h4 := abs_le.1 key'
  have h5 := abs_le.1 h3
  rw [abs_le]
  constructor <;> linarith only [h4.1, h4.2, h5.1, h5.2]

end
end

