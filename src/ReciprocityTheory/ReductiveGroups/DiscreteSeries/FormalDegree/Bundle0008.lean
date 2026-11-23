module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0007
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.ProdShcSqEqJacPow
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.JacBaseA

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FiPmatEqFiOneSmulPmat
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem wS_nonneg' {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n)
    (S : {S : Finset (Fin n) // S.card = i}) : 0 ≤ wS z hi S := by
  unfold wS
  positivity

theorem fi_eq_lse {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) (t : ℝ) :
    Fi ((t : ℂ) • pmat z) i = Real.log (∑ S, wS z hi S * Real.exp (t * yS z S.1)) := by
  unfold Fi
  rw [lemma3a z hi t]
  congr 1
  have h : (∑ S, ((wS z hi S : ℝ) : ℂ) * Complex.exp ((t * yS z S.1 : ℝ) : ℂ)) =
      ((∑ S, wS z hi S * Real.exp (t * yS z S.1) : ℝ) : ℂ) := by
    push_cast
    simp only [Complex.ofReal_exp, Complex.ofReal_mul]
  rw [h, Complex.ofReal_re]

theorem fi_pmat_eq_fi_one_smul_pmat {ε : Fin n → Bool} (z : PCoord ε → ℂ) (i : ℕ) :
    Fi (pmat z) i = Fi (((1 : ℝ) : ℂ) • pmat z) i := by
  rw [Complex.ofReal_one, one_smul]

theorem fi_convex {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) :
    ConvexOn ℝ Set.univ (fun t : ℝ => Fi ((t : ℂ) • pmat z) i) := by
  have h : (fun t : ℝ => Fi ((t : ℂ) • pmat z) i) =
      fun t : ℝ => Real.log (∑ S, wS z hi S * Real.exp (t * yS z S.1)) := by
    funext t
    exact fi_eq_lse z hi t
  rw [h]
  exact lse_convexOn (wS z hi) (fun S => yS z S.1) (wS_nonneg' z hi) (lemma3b z hi)

theorem fi_zero (i : ℕ) : Fi (0 : Matrix (Fin n) (Fin n) ℂ) i = 0 := by
  unfold Fi Del
  rw [NormedSpace.exp_zero]
  split_ifs with h
  · rw [Matrix.submatrix_one _ (Fin.castLE_injective h)]
    simp
  · simp

theorem fi_nonneg {ε : Fin n → Bool} (z : PCoord ε → ℂ) (i : ℕ) : 0 ≤ Fi (pmat z) i := by
  by_cases hi : i ≤ n
  · rw [fi_pmat_eq_fi_one_smul_pmat, fi_eq_lse z hi]
    apply Real.log_nonneg
    have h := lse_one_le (wS z hi) (fun S => yS z S.1) (wS_nonneg' z hi) (lemma3b z hi) (lemma3c z hi)
    simpa only [one_mul] using h
  · unfold Fi Del
    rw [dite_eq_right hi]
    simp

theorem fi_lower {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) {ep : ℝ}
    (h1 : rhoP z ≤ ep) (h2 : ep ≤ 1) : Vi (pmat z) i / 2 * (1 - ep) ≤ Fi (pmat z) i := by
  have hr : 0 ≤ rhoP z := by
    unfold rhoP
    positivity
  rw [fi_pmat_eq_fi_one_smul_pmat, fi_eq_lse z hi, ← lemma3d z hi]
  have h := lse_lower (wS z hi) (fun S => yS z S.1) (wS_nonneg' z hi) (lemma3b z hi) (lemma3c z hi)
    (hr.trans h1) h2 (fun S => by
      have := abs_sum_pev_le z S.1
      unfold yS
      linarith)
  simpa only [one_mul] using h

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.JacAll
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem jall_pmat_add {ε : Fin n → Bool} (z w : PCoord ε → ℂ) : pmat (z + w) = pmat z + pmat w := by
  ext a b
  simp only [pmat, Pi.add_apply, Matrix.add_apply]
  split_ifs <;> simp

theorem jall_pmat_smul {ε : Fin n → Bool} (c : ℝ) (z : PCoord ε → ℂ) :
    pmat (c • z) = (c : ℂ) • pmat z := by
  ext a b
  simp only [pmat, Pi.smul_apply, Matrix.smul_apply]
  split_ifs <;> simp [Complex.real_smul, star_mul', Complex.conj_ofReal]

def adKL {ε : Fin n → Bool} (k : KG ε) : (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ) where
  toFun := adK k
  map_add' z w := by
    funext ab
    simp only [adK, jall_pmat_add, Matrix.mul_add, Matrix.add_mul, Pi.add_apply, Matrix.add_apply]
  map_smul' c z := by
    funext ab
    simp only [adK, jall_pmat_smul, Matrix.mul_smul, Matrix.smul_mul, Pi.smul_apply, Matrix.smul_apply,
      RingHom.id_apply, Complex.real_smul, smul_eq_mul]

theorem jall_adK_inv {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) : adK k⁻¹ (adK k z) = z := by
  have hk := toMK_facts k
  have h : pmat (adK k⁻¹ (adK k z)) = pmat z := by
    rw [pmat_adK, pmat_adK, toMK_inv, Matrix.conjTranspose_conjTranspose]
    calc (toMK k)ᴴ * (toMK k * pmat z * (toMK k)ᴴ) * toMK k
        = ((toMK k)ᴴ * toMK k) * pmat z * ((toMK k)ᴴ * toMK k) := by simp only [Matrix.mul_assoc]
      _ = pmat z := by rw [hk.1, Matrix.one_mul, Matrix.mul_one]
  rw [← pact_pmat_coords (adK k⁻¹ (adK k z)), h, pact_pmat_coords]

theorem jall_abs_det_adKL {ε : Fin n → Bool} (k : KG ε) : |LinearMap.det (adKL k)| = 1 := by
  have hinj : Function.Injective (adKL k) := fun x y hxy => by
    have := congrArg (adK k⁻¹) hxy
    simpa only [adKL, LinearMap.coe_mk, AddHom.coe_mk, jall_adK_inv] using this
  have hmp := adK_measurePreserving k
  have hcs : IsCompact ((adKL k) '' Metric.closedBall (0 : PCoord ε → ℂ) 1) :=
    (isCompact_closedBall 0 1).image (LinearMap.continuous_of_finiteDimensional _)
  have h1 : volume ((adK k) ⁻¹' ((adKL k) '' Metric.closedBall (0 : PCoord ε → ℂ) 1)) =
      volume ((adKL k) '' Metric.closedBall (0 : PCoord ε → ℂ) 1) :=
    hmp.measure_preimage hcs.isClosed.measurableSet.nullMeasurableSet
  have hpre : (adK k) ⁻¹' ((adKL k) '' Metric.closedBall (0 : PCoord ε → ℂ) 1) =
      Metric.closedBall (0 : PCoord ε → ℂ) 1 := Set.preimage_image_eq _ hinj
  rw [hpre, MeasureTheory.Measure.addHaar_image_linearMap] at h1
  have hpos : volume (Metric.closedBall (0 : PCoord ε → ℂ) 1) ≠ 0 :=
    (Metric.measure_closedBall_pos volume 0 one_pos).ne'
  have hfin : volume (Metric.closedBall (0 : PCoord ε → ℂ) 1) ≠ ⊤ :=
    (isCompact_closedBall (0 : PCoord ε → ℂ) 1).measure_lt_top.ne
  have h2 : ENNReal.ofReal |LinearMap.det (adKL k)| = 1 := by
    have h3 : 1 * volume (Metric.closedBall (0 : PCoord ε → ℂ) 1) =
        ENNReal.ofReal |LinearMap.det (adKL k)| * volume (Metric.closedBall (0 : PCoord ε → ℂ) 1) := by
      rw [one_mul]; exact h1
    exact ((ENNReal.mul_left_inj hpos hfin).mp h3).symm
  exact ENNReal.ofReal_eq_one.mp h2

def jdetA {ε : Fin n → Bool} (g : Matrix (Fin n) (Fin n) ℂ) (z : PCoord ε → ℂ) : ℝ :=
  LinearMap.det ((fderiv ℝ (actR (ε := ε) g) z : (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) :
    (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ))

theorem jall_diff {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (z : PCoord ε → ℂ) :
    DifferentiableAt ℝ (actR (ε := ε) g) z := by
  first
  | exact (JacB.actR_contDiff' hg).differentiable one_ne_zero z
  | exact (JacB.actR_contDiff' hg).differentiable le_rfl z

theorem jall_chain {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hh : inUJ ε h)
    (z : PCoord ε → ℂ) : jdetA (g * h) z = jdetA h (actR g z) * jdetA g z := by
  unfold jdetA
  have hfun : actR (ε := ε) (g * h) = actR h ∘ actR g := funext (actR_mul hg hh)
  rw [hfun, fderiv_comp z (jall_diff hh (actR g z)) (jall_diff hg z)]
  exact LinearMap.det_comp _ _

theorem jall_fderiv_K {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) :
    fderiv ℝ (actR (ε := ε) (toMK k)) z = LinearMap.toContinuousLinearMap (adKL k⁻¹) := by
  have e : actR (ε := ε) (toMK k) = ⇑(LinearMap.toContinuousLinearMap (adKL k⁻¹)) := by
    funext w
    rw [actR_K]
    rfl
  rw [e]
  exact ContinuousLinearMap.fderiv _

theorem jall_abs_jdetA_K {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) :
    |jdetA (toMK k) z| = 1 := by
  unfold jdetA
  rw [jall_fderiv_K]
  exact jall_abs_det_adKL k⁻¹

theorem jall_inUJ_K {ε : Fin n → Bool} (k : KG ε) : inUJ ε (toMK k) := by
  first
  | exact k.1.2
  | exact k.val.property
  | exact k.2.1

theorem jall_actR_K_zero {ε : Fin n → Bool} (k : KG ε) : actR (ε := ε) (toMK k) 0 = 0 := by
  have hp0 : pmat (0 : PCoord ε → ℂ) = 0 := by
    ext a b
    simp [pmat]
  apply actR_of_eq_polarM (k := k)
  simp only [polarM, hp0, NormedSpace.exp_zero, Matrix.one_mul, Matrix.mul_one]

theorem jacAll {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (z : PCoord ε → ℂ) :
    |LinearMap.det ((fderiv ℝ (actR (ε := ε) g) z : (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) :
      (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ))| * Jac (actR g z) = Jac z := by
  have hp0 : pmat (0 : PCoord ε → ℂ) = 0 := by
    ext a b
    simp [pmat]
  obtain ⟨k, hk⟩ := actR_spec hg z
  set w := actR g z with hw
  have hEz := exp_pmat_inUJ z
  have hEw := exp_pmat_inUJ w
  have hK := jall_inUJ_K k
  have h0z : actR (ε := ε) (NormedSpace.exp (pmat z)) 0 = z := by
    apply actR_of_eq_polarM (k := 1)
    simp only [polarM, hp0, NormedSpace.exp_zero, Matrix.one_mul]
    first
    | rfl
    | (rw [show toMK (1 : KG ε) = 1 from rfl, Matrix.one_mul])
    | simp
  have hc1 := jall_chain hEz hg 0
  rw [h0z] at hc1
  have hc2 := jall_chain hK hEw 0
  rw [jall_actR_K_zero] at hc2
  have hmul : NormedSpace.exp (pmat z) * g = toMK k * NormedSpace.exp (pmat w) := by
    rw [hk]; rfl
  rw [hmul, hc2] at hc1
  have hab : |jdetA g z| * |jdetA (ε := ε) (NormedSpace.exp (pmat z)) 0| = |jdetA (ε := ε) (NormedSpace.exp (pmat w)) 0| := by
    have := congrArg abs hc1
    rw [abs_mul, abs_mul, jall_abs_jdetA_K, mul_one] at this
    rw [this, mul_comm]
  have hbZ : |jdetA (ε := ε) (NormedSpace.exp (pmat z)) 0| * Jac z = 1 := JacB.jacBase' z
  have hcW : |jdetA (ε := ε) (NormedSpace.exp (pmat w)) 0| * Jac w = 1 := JacB.jacBase' w
  show |jdetA g z| * Jac w = Jac z
  linear_combination (-(|jdetA g z| * Jac w)) * hbZ + (Jac w * Jac z) * hab + Jac z * hcW

end ReciprocityTheory.ChartRestriction.DS
end
end

