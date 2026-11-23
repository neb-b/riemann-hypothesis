module

public import ReciprocityTheory.SemistableReduction.Bundle0015
public import ReciprocityTheory.SemistableReduction.Bundle0010
public import ReciprocityTheory.SemistableReduction.Bundle0003
public import ReciprocityTheory.SemistableReduction.Bundle0016

@[expose] public section

-- bundled from ReciprocityTheory.SemistableReduction.SphereTorus
section
namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory

theorem sphereTorus_holds (hInt : SphereLogIntegrableStatement) (hBasic : TorusMeanBasicStatement) :
    SphereLeTorusStatement := by
  intro B n a f hn hf hhom
  haveI : IsProbabilityMeasure (sphereProb n) := isProbabilityMeasure_sphereProb hn
  haveI : IsProbabilityMeasure (blockSphereProb B n) := by
    unfold blockSphereProb; infer_instance
  haveI : IsProbabilityMeasure ((volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)) :=
    ⟨by simp⟩
  haveI : IsProbabilityMeasure (torusProb (Fin B × Fin n)) := by
    unfold torusProb; infer_instance

  have hh : Integrable (fun z => Real.log ‖MvPolynomial.eval (blockPoint z) f‖)
      (blockSphereProb B n) := hInt B n a f hf hhom

  have hslice : ∀ θ : Fin B × Fin n → ℝ,
      Integrable (fun z => Real.log ‖MvPolynomial.eval
        (fun p => blockPoint z p * torusPoint θ p) f‖) (blockSphereProb B n) ∧
      ∫ z, Real.log ‖MvPolynomial.eval (fun p => blockPoint z p * torusPoint θ p) f‖
        ∂(blockSphereProb B n) = blockSphereMean B n f ∧
      ∫ z, ‖Real.log ‖MvPolynomial.eval (fun p => blockPoint z p * torusPoint θ p) f‖‖
        ∂(blockSphereProb B n) =
        ∫ z, ‖Real.log ‖MvPolynomial.eval (blockPoint z) f‖‖ ∂(blockSphereProb B n) := by
    intro θ
    have hmp := measurePreserving_blockRot (B := B) (n := n) θ
    have e : ∀ z, (fun p => blockPoint z p * torusPoint θ p) = blockPoint (blockRot θ z) := by
      intro z; rw [blockPoint_blockRot]
    simp only [e]
    refine ⟨?_, ?_, ?_⟩
    · have h1 : Integrable (fun z => Real.log ‖MvPolynomial.eval (blockPoint z) f‖)
          (Measure.map (blockRot θ) (blockSphereProb B n)) := by
        rw [hmp.map_eq]; exact hh
      exact h1.comp_measurable hmp.measurable
    · have hA : AEStronglyMeasurable (fun z => Real.log ‖MvPolynomial.eval (blockPoint z) f‖)
          (Measure.map (blockRot θ) (blockSphereProb B n)) := by
        rw [hmp.map_eq]; exact hh.aestronglyMeasurable
      have h2 := integral_map hmp.measurable.aemeasurable hA
      rw [hmp.map_eq] at h2
      exact h2.symm
    · have hA : AEStronglyMeasurable (fun z => ‖Real.log ‖MvPolynomial.eval (blockPoint z) f‖‖)
          (Measure.map (blockRot θ) (blockSphereProb B n)) := by
        rw [hmp.map_eq]; exact hh.norm.aestronglyMeasurable
      have h2 := integral_map hmp.measurable.aemeasurable hA
      rw [hmp.map_eq] at h2
      exact h2.symm

  have hcont : Continuous (fun q : BlockSphere B n × (Fin B × Fin n → ℝ) =>
      MvPolynomial.eval (fun p => blockPoint q.1 p * torusPoint q.2 p) f) := by
    refine (MvPolynomial.continuous_eval f).comp (continuous_pi fun p => ?_)
    refine Continuous.mul ?_ ?_
    · unfold blockPoint spherePoint
      fun_prop
    · unfold torusPoint
      fun_prop
  have hgm : AEStronglyMeasurable (fun q : BlockSphere B n × (Fin B × Fin n → ℝ) =>
      Real.log ‖MvPolynomial.eval (fun p => blockPoint q.1 p * torusPoint q.2 p) f‖)
      ((blockSphereProb B n).prod (torusProb (Fin B × Fin n))) :=
    (Real.measurable_log.comp hcont.norm.measurable).aestronglyMeasurable
  have hgi : Integrable (fun q : BlockSphere B n × (Fin B × Fin n → ℝ) =>
      Real.log ‖MvPolynomial.eval (fun p => blockPoint q.1 p * torusPoint q.2 p) f‖)
      ((blockSphereProb B n).prod (torusProb (Fin B × Fin n))) := by
    rw [integrable_prod_iff' hgm]
    refine ⟨Filter.Eventually.of_forall fun θ => (hslice θ).1, ?_⟩
    simp only [fun θ => (hslice θ).2.2]
    exact integrable_const _

  have hae : ∀ᵐ z ∂(blockSphereProb B n), ∀ p, blockPoint z p ≠ 0 := by
    rw [ae_iff]
    simpa [not_forall] using blockSphereProb_coord_zero (B := B) (n := n)
  calc blockSphereMean B n f
      = ∫ θ, ∫ z, Real.log ‖MvPolynomial.eval (fun p => blockPoint z p * torusPoint θ p) f‖
          ∂(blockSphereProb B n) ∂(torusProb (Fin B × Fin n)) := by
        simp only [fun θ => (hslice θ).2.1]
        simp
    _ = ∫ z, ∫ θ, Real.log ‖MvPolynomial.eval (fun p => blockPoint z p * torusPoint θ p) f‖
          ∂(torusProb (Fin B × Fin n)) ∂(blockSphereProb B n) :=
        (integral_integral_swap hgi).symm
    _ = ∫ z, scaledTorusMean (blockPoint z) f ∂(blockSphereProb B n) := rfl
    _ ≤ ∫ _z, torusMean f ∂(blockSphereProb B n) := by
        refine integral_mono_ae hgi.integral_prod_left (integrable_const _) ?_
        filter_upwards [hae] with z hz
        exact scaledTorusMean_le_torusMean hBasic f hf (blockPoint z) hz (norm_blockPoint_le z)
    _ = torusMean f := by simp

end ReciprocityTheory.MultiplicativeHeights
end

-- bundled from ReciprocityTheory.SemistableReduction.TorusMeanD
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Real Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma slice_abs_integral_le (f : MvPolynomial ι ℂ) (i : ι) (θ : ι → ℝ) :
    ∫ t, ‖tmLog f (update θ i t)‖ ∂unitIntervalMeasure ≤
      2 * posLog (∑ s ∈ f.support, ‖f.coeff s‖) +
        ∑ k ∈ Finset.range (f.support.sup (fun s => s i) + 1), |tmLog (coeffIn i k f) θ| := by
  have hu : ∀ t, tmLog f (update θ i t) =
      Real.log ‖(tmSlice i (torusPoint θ) f).eval (circPt t)‖ := tmLog_update f θ i
  have hL : 0 ≤ posLog (∑ s ∈ f.support, ‖f.coeff s‖) := posLog_nonneg
  have hI : Integrable (fun t => tmLog f (update θ i t)) unitIntervalMeasure := by
    simp_rw [hu]; exact integrableOn_log_circ _
  have h1 : ∫ t, ‖tmLog f (update θ i t)‖ ∂unitIntervalMeasure ≤
      ∫ t, (2 * posLog (∑ s ∈ f.support, ‖f.coeff s‖) - tmLog f (update θ i t)) ∂unitIntervalMeasure := by
    refine integral_mono hI.norm ((integrable_const _).sub hI) fun t => ?_
    have := tmLog_le f (update θ i t)
    simp only [Real.norm_eq_abs]
    rcases abs_cases (tmLog f (update θ i t)) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  have h2 : ∫ t, (2 * posLog (∑ s ∈ f.support, ‖f.coeff s‖) - tmLog f (update θ i t)) ∂unitIntervalMeasure =
      2 * posLog (∑ s ∈ f.support, ‖f.coeff s‖) -
        (tmSlice i (torusPoint θ) f).logMahlerMeasure := by
    rw [integral_sub (integrable_const _) hI, integral_const]
    simp_rw [hu]
    rw [integral_log_circ]
    simp
  have h3 : |Real.log ‖(tmSlice i (torusPoint θ) f).leadingCoeff‖| ≤
      ∑ k ∈ Finset.range (f.support.sup (fun s => s i) + 1), |tmLog (coeffIn i k f) θ| := by
    rw [Polynomial.leadingCoeff, tmSlice_coeff]
    by_cases hn : (tmSlice i (torusPoint θ) f).natDegree < f.support.sup (fun s => s i) + 1
    · exact Finset.single_le_sum (f := fun k => |tmLog (coeffIn i k f) θ|)
        (fun k _ => abs_nonneg _) (Finset.mem_range.mpr hn)
    · rw [coeffIn_eq_zero_of_lt i f _ (by omega)]
      simp only [map_zero, norm_zero, Real.log_zero, abs_zero]
      exact Finset.sum_nonneg fun k _ => abs_nonneg _
  have h4 := log_norm_leadingCoeff_le (tmSlice i (torusPoint θ) f)
  have h5 := neg_abs_le (Real.log ‖(tmSlice i (torusPoint θ) f).leadingCoeff‖)
  linarith

lemma integrable_log_abs_on_torus (S : Finset ι) :
    ∀ f : MvPolynomial ι ℂ, f.vars ⊆ S → Integrable (tmLog f) (torusProb ι) := by
  induction S using Finset.induction_on with
  | empty =>
    intro f hS
    have : tmLog f = fun _ => Real.log ‖MvPolynomial.constantCoeff f‖ := by
      funext θ; simp [tmLog, eval_const_of_vars_empty f hS]
    rw [this]; exact integrable_const _
  | insert i S' hi ih =>
    intro f hS
    have hsub : ∀ k, (coeffIn i k f).vars ⊆ S' := by
      intro k j hj
      have h1 := vars_coeffIn_subset i k f hj
      rw [Finset.mem_erase] at h1
      have h2 := hS h1.2
      rw [Finset.mem_insert] at h2
      exact h2.resolve_left h1.1
    have hmeas : AEStronglyMeasurable (tmLog f ∘ tmUpd i) ((torusProb ι).prod unitIntervalMeasure) :=
      ((measurable_tmLog f).comp (measurable_tmUpd i)).aestronglyMeasurable
    rw [← tm_integrable_comp i (measurable_tmLog f).aestronglyMeasurable,
      integrable_prod_iff hmeas]
    refine ⟨Filter.Eventually.of_forall fun θ => ?_, ?_⟩
    · show Integrable (fun t => tmLog f (update θ i t)) unitIntervalMeasure
      simp_rw [tmLog_update]
      exact integrableOn_log_circ _
    · have hG : Integrable (fun θ => 2 * posLog (∑ s ∈ f.support, ‖f.coeff s‖) +
          ∑ k ∈ Finset.range (f.support.sup (fun s => s i) + 1), |tmLog (coeffIn i k f) θ|)
          (torusProb ι) :=
        (integrable_const _).add (integrable_finsetSum _ fun k _ => (ih _ (hsub k)).abs)
      refine hG.mono' hmeas.norm.integral_prod_right' (Filter.Eventually.of_forall fun θ => ?_)
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact slice_abs_integral_le f i θ

lemma tm_int (f : MvPolynomial ι ℂ) : Integrable (tmLog f) (torusProb ι) :=
  integrable_log_abs_on_torus Finset.univ f (Finset.subset_univ _)

lemma tm_ae_ne (f : MvPolynomial ι ℂ) (hf : f ≠ 0) :
    ∀ᵐ θ ∂(torusProb ι), MvPolynomial.eval (torusPoint θ) f ≠ 0 := by
  rw [ae_iff]; simpa using tm_null f hf

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.Unipotent
section
namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField Polynomial

theorem unip_conj_pow {r : ℕ} (Q M : Matrix (Fin r) (Fin r) ℂ) (hQ : Q.det ≠ 0) (n : ℕ) :
    (Q * M * Q⁻¹) ^ n = Q * M ^ n * Q⁻¹ := by
  have hinv : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q (isUnit_iff_ne_zero.mpr hQ)
  have hinv' : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.mpr hQ)
  induction n with
  | zero => simp [hinv']
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    calc Q * M ^ n * Q⁻¹ * (Q * M * Q⁻¹) = Q * M ^ n * (Q⁻¹ * Q) * M * Q⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = Q * (M ^ n * M) * Q⁻¹ := by rw [hinv, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem unip_trace_conj {r : ℕ} (Q M : Matrix (Fin r) (Fin r) ℂ) (hQ : Q.det ≠ 0) :
    (Q * M * Q⁻¹).trace = M.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul Q (isUnit_iff_ne_zero.mpr hQ), Matrix.one_mul]

theorem unip_trace_map {K : Type*} [Field K] {r : ℕ} (σ : K →+* ℂ) (M : Matrix (Fin r) (Fin r) K) :
    (M.map σ).trace = σ M.trace := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

theorem unip_map_pow {K : Type*} [Field K] {r : ℕ} (σ : K →+* ℂ) (M : Matrix (Fin r) (Fin r) K)
    (n : ℕ) : (M.map σ) ^ n = (M ^ n).map σ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, pow_succ, Matrix.map_mul]

theorem unip_trace_aeval_one {K : Type*} [Field K] {r : ℕ} (γ : Matrix (Fin r) (Fin r) K)
    (hγ : ∀ k, k ≤ r → (γ ^ k).trace = r) (P : K[X]) (hP : P.natDegree ≤ r) :
    (aeval γ P).trace = r * P.eval 1 := by
  have hlt : P.natDegree < r + 1 := Nat.lt_succ_of_le hP
  rw [Polynomial.aeval_eq_sum_range' hlt, Matrix.trace_sum, Polynomial.eval_eq_sum_range' hlt,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [Matrix.trace_smul, hγ k hk', smul_eq_mul, one_pow, mul_one, mul_comm]

theorem unipotent_holds : UnipotentStatement := by
  intro K _ _ r g γ Q hT hg hQ hA
  set A : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ := fun σ => Q σ * γ.map σ * (Q σ)⁻¹ with hAdef
  have hc : 0 ≤ Real.exp (2 / (3 * (r : ℝ))) := (Real.exp_pos _).le
  have htrA : ∀ σ n, ((A σ) ^ n).trace = σ ((γ ^ n).trace) := by
    intro σ n
    simp only [hAdef]
    rw [unip_conj_pow _ _ (hQ σ), unip_trace_conj _ _ (hQ σ), unip_map_pow, unip_trace_map]
  have htrB : ∀ σ n, n ≤ r → ‖((A σ) ^ n).trace‖ ≤ r * Real.exp (1 / 3) := by
    intro σ n hn
    have hd : ∀ i, ‖((A σ) ^ n) i i‖ ≤ Real.exp (1 / 3) := by
      intro i
      have h1 := unip_diag_sq_le (A σ) _ hc (hA σ) n i
      have h2 : Real.exp (2 / (3 * (r : ℝ))) ^ n ≤ Real.exp (1 / 3) ^ 2 := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        rcases Nat.eq_zero_or_pos r with hr | hr
        · subst hr
          have : n = 0 := by omega
          subst this; norm_num
        · have hr' : (0 : ℝ) < r := by exact_mod_cast hr
          have hn' : (n : ℝ) ≤ r := by exact_mod_cast hn
          calc (n : ℝ) * (2 / (3 * r)) = (2 / 3) * ((n : ℝ) / r) := by field_simp
            _ ≤ (2 / 3) * 1 := by gcongr; exact (div_le_one hr').mpr hn'
            _ = ((2 : ℕ) : ℝ) * (1 / 3) := by norm_num
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.exp_pos _).le two_ne_zero).mp (h1.trans h2)
    calc ‖((A σ) ^ n).trace‖ = ‖∑ i, ((A σ) ^ n) i i‖ := rfl
      _ ≤ ∑ i, ‖((A σ) ^ n) i i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin r, Real.exp (1 / 3) := Finset.sum_le_sum (fun i _ => hd i)
      _ = r * Real.exp (1 / 3) := by simp
  have hT1 : ∀ n, 1 ≤ n → n ≤ r → (γ ^ n).trace = r := by
    intro n h1 h2
    obtain ⟨z, hz⟩ := hT n h1 h2
    by_cases hz0 : z = 0
    · rw [hz0] at hz
      simp only [map_zero, mul_zero] at hz
      exact sub_eq_zero.mp (by simpa using hz)
    · exfalso
      obtain ⟨σ, hσ⟩ := NumberField.exists_conjugate_one_le_norm hz0
      have e1 : σ ((γ ^ n).trace - r) = (g : ℂ) * σ z := by rw [hz, map_mul, map_natCast]
      rw [map_sub, map_natCast, ← htrA σ n] at e1
      have hn1 : ‖((A σ) ^ n).trace - r‖ ≤ r * Real.exp (1 / 3) + r := by
        refine (norm_sub_le _ _).trans ?_
        rw [Complex.norm_natCast]
        linarith [htrB σ n h2]
      rw [e1, norm_mul, Complex.norm_natCast] at hn1
      have : (g : ℝ) ≤ g * ‖σ z‖ := le_mul_of_one_le_right (Nat.cast_nonneg _) hσ
      nlinarith
  have hTall : ∀ k, k ≤ r → (γ ^ k).trace = r := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp [Matrix.trace_one]
    · exact hT1 k h hk
  have hN : ∀ k, 1 ≤ k → k ≤ r → ((γ - 1) ^ k).trace = 0 := by
    intro k h1 h2
    have := unip_trace_aeval_one γ hTall ((X - C 1) ^ k)
      (by rw [natDegree_pow, natDegree_X_sub_C, mul_one]; exact h2)
    simp only [map_pow, map_sub, aeval_X, map_one, eval_pow, eval_sub, eval_X, eval_one,
      sub_self] at this
    rw [this, zero_pow (by omega : k ≠ 0), mul_zero]
  refine ⟨unip_pow_card_eq_zero (γ - 1) hN, fun σ => ?_⟩
  have hinv' : Q σ * (Q σ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hQ σ))
  have heq : Q σ * (γ.map σ - 1) * (Q σ)⁻¹ = A σ - 1 := by
    simp only [hAdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hinv']
  rw [heq, unip_hs_sub_one]
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simp
  have htr1 : (A σ).trace = r := by
    have h7 := htrA σ 1
    rw [pow_one] at h7
    rw [h7, hT1 1 le_rfl hr, map_natCast]
  rw [htr1, Complex.natCast_re]
  have h5 := unip_hs_le (A σ) _ (hA σ)
  have h6 := unip_exp_bound r hr
  nlinarith

end ReciprocityTheory.MultiplicativeHeights
end

