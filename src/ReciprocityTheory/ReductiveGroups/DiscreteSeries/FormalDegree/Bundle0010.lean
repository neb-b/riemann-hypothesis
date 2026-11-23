module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0008
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0007
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.IntegrableOfContinuousCompact

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.SCoefGeTwoOfHc
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem sCoef_ge_one {lam : Fin n → ℝ} (hlam : Antitone lam) {i : ℕ} (hi : i + 1 < n) :
    1 ≤ sCoef lam i := by
  have h : lam ⟨i + 1, hi⟩ ≤ lam ⟨i, by omega⟩ := hlam (Fin.mk_le_mk.mpr (Nat.le_succ i))
  simp only [sCoef, dif_pos hi]
  linarith

theorem fi_scale {ε : Fin n → Bool} (z : PCoord ε → ℂ) {i : ℕ} (hi : i ≤ n) {t : ℝ} (ht : 1 ≤ t) :
    t * Fi (pmat z) i ≤ Fi ((t : ℂ) • pmat z) i := by
  have hc := fi_convex z hi
  have ht0 : 0 < t := by linarith
  have h : Fi (((1 / t * t + (1 - 1 / t) * 0 : ℝ) : ℂ) • pmat z) i ≤
      1 / t * Fi (((t : ℝ) : ℂ) • pmat z) i + (1 - 1 / t) * Fi (((0 : ℝ) : ℂ) • pmat z) i :=
    hc.2 (Set.mem_univ t) (Set.mem_univ (0 : ℝ)) (show (0 : ℝ) ≤ 1 / t by positivity)
      (show (0 : ℝ) ≤ 1 - 1 / t by rw [sub_nonneg, div_le_one ht0]; exact ht)
      (show 1 / t + (1 - 1 / t) = (1 : ℝ) by ring)
  have e1 : 1 / t * t + (1 - 1 / t) * 0 = 1 := by rw [mul_zero, add_zero, one_div_mul_cancel ht0.ne']
  have e0 : Fi (((0 : ℝ) : ℂ) • pmat z) i = 0 := by simp [fi_zero]
  rw [e1, e0, Complex.ofReal_one, one_smul, mul_zero, add_zero] at h
  calc t * Fi (pmat z) i ≤ t * (1 / t * Fi ((t : ℂ) • pmat z) i) := mul_le_mul_of_nonneg_left h ht0.le
    _ = Fi ((t : ℂ) • pmat z) i := by rw [← mul_assoc, mul_one_div_cancel ht0.ne', one_mul]

theorem ph_nonneg {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) (z : PCoord ε → ℂ) :
    0 ≤ Ph lam (pmat z) := by
  unfold Ph
  refine Finset.sum_nonneg fun i hi => ?_
  have hi' : i + 1 < n := by have := Finset.mem_range.mp hi; omega
  exact mul_nonneg (by linarith [sCoef_ge_one hlam hi']) (fi_nonneg z _)

theorem ph_scale {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) (z : PCoord ε → ℂ) {t : ℝ}
    (ht : 1 ≤ t) : t * Ph lam (pmat z) ≤ Ph lam ((t : ℂ) • pmat z) := by
  unfold Ph
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i + 1 < n := by have := Finset.mem_range.mp hi; omega
  have hs := sCoef_ge_one hlam hi'
  have hf := fi_scale z (i := i + 1) (by omega) ht
  calc t * (sCoef lam i * Fi (pmat z) (i + 1)) = sCoef lam i * (t * Fi (pmat z) (i + 1)) := by ring
    _ ≤ sCoef lam i * Fi ((t : ℂ) • pmat z) (i + 1) := mul_le_mul_of_nonneg_left hf (by linarith)

theorem sum_Ico_sCoef (lam : Fin n → ℝ) {b a : ℕ} (hba : b ≤ a) (ha : a < n) :
    ∑ i ∈ Ico b a, sCoef lam i = lam ⟨b, by omega⟩ - lam ⟨a, ha⟩ + ((a : ℝ) - (b : ℝ)) := by
  induction a, hba using Nat.le_induction with
  | base => simp
  | succ k hbk ih =>
    rw [Finset.sum_Ico_succ_top hbk, ih (by omega)]
    simp only [sCoef, dif_pos ha]
    push_cast
    ring

theorem sum_Ico_sCoef_fin (lam : Fin n → ℝ) (a b : Fin n) (h : b ≤ a) :
    ∑ i ∈ Ico (b : ℕ) a, sCoef lam i = wab lam a b := by
  rw [sum_Ico_sCoef lam (Fin.le_iff_val_le_val.mp h) a.isLt]
  simp only [Fin.eta, wab]
  ring

theorem sum_sCoef_ind (lam : Fin n → ℝ) (a b : Fin n) (c : ℝ) :
    ∑ i ∈ range (n - 1), sCoef lam i * (if (b : ℕ) < i + 1 ∧ i + 1 ≤ (a : ℕ) then c else 0) =
      if b < a then wab lam a b * c else 0 := by
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter, ← Finset.sum_mul]
  have ha := a.isLt
  have hf : (range (n - 1)).filter (fun i => (b : ℕ) < i + 1 ∧ i + 1 ≤ (a : ℕ)) = Ico (b : ℕ) a := by
    ext i
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [hf]
  split_ifs with h
  · rw [sum_Ico_sCoef_fin lam a b h.le]
  · have h' : (a : ℕ) ≤ b := Fin.le_iff_val_le_val.mp (not_lt.mp h)
    rw [Finset.Ico_eq_empty_of_le h', sum_empty, zero_mul]

theorem pmat_coord {ε : Fin n → Bool} (z : PCoord ε → ℂ) (ab : PCoord ε) :
    pmat z ab.1.1 ab.1.2 = z ab := by
  unfold pmat
  rw [dif_pos ab.2]

theorem sum_pairs_pmat {ε : Fin n → Bool} (w : Fin n → Fin n → ℝ) (z : PCoord ε → ℂ) :
    ∑ x : Fin n × Fin n, (if x.2 < x.1 then w x.1 x.2 * ‖pmat z x.1 x.2‖ ^ 2 else 0) =
      ∑ ab : PCoord ε, w ab.1.1 ab.1.2 * ‖z ab‖ ^ 2 := by
  rw [← Finset.sum_filter_of_ne (p := fun x : Fin n × Fin n => x.2 < x.1 ∧ ε x.1 ≠ ε x.2)]
  · rw [Finset.sum_subtype (p := fun x : Fin n × Fin n => x.2 < x.1 ∧ ε x.1 ≠ ε x.2) _ (by simp)]
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [if_pos ab.2.1, pmat_coord]
  · intro x _ hx
    by_contra hP
    apply hx
    by_cases h1 : x.2 < x.1
    · have h2 : ε x.1 = ε x.2 := by
        by_contra h
        exact hP ⟨h1, h⟩
      have h3 : pmat z x.1 x.2 = 0 := by
        unfold pmat
        rw [dite_eq_right (fun h => h.2 h2), dite_eq_right (fun h => lt_asymm h.1 h1)]
      rw [if_pos h1, h3, norm_zero]
      ring
    · rw [if_neg h1]

theorem sum_sCoef_Vi {ε : Fin n → Bool} (lam : Fin n → ℝ) (z : PCoord ε → ℂ) :
    ∑ i ∈ range (n - 1), sCoef lam i * Vi (pmat z) (i + 1) = Qf lam z := by
  have step1 : ∑ i ∈ range (n - 1), sCoef lam i * Vi (pmat z) (i + 1) =
      ∑ a : Fin n, ∑ b : Fin n, if b < a then wab lam a b * ‖pmat z a b‖ ^ 2 else 0 := by
    simp only [Vi, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    exact sum_sCoef_ind lam a b _
  rw [step1, ← Fintype.sum_prod_type', Qf]
  exact sum_pairs_pmat (wab lam) z

theorem ph_lower {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : Antitone lam) (z : PCoord ε → ℂ) {ep : ℝ}
    (h1 : rhoP z ≤ ep) (h2 : ep ≤ 1) : (1 - ep) * Qf lam z ≤ 2 * Ph lam (pmat z) := by
  rw [← sum_sCoef_Vi lam z, Ph, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i + 1 < n := by have := Finset.mem_range.mp hi; omega
  have hs := sCoef_ge_one hlam hi'
  have hf := fi_lower z (i := i + 1) (by omega) h1 h2
  have := mul_le_mul_of_nonneg_left hf (show (0 : ℝ) ≤ sCoef lam i by linarith)
  nlinarith

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.SumNormAdjointSqEqHsOp
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

open CompactHaarProbability in
theorem fF_conj_pmat_eq_op_inv_mul_fF_mul_op {ε : Fin n → Bool} {lam : Fin n → ℝ} (T : KType ε (lowK ε lam)) (k : KG ε) (z : PCoord ε → ℂ) :
    fF ε lam T (toMK k⁻¹ * pmat z * toMK k) = T.op k⁻¹ * fF ε lam T (pmat z) * T.op k := by
  rw [fF_eq_integral, fF_eq_integral]
  have h1 : ∀ (c : ℂ) (I : T.V →L[ℂ] T.V), T.op k⁻¹ * (c • I) * T.op k = c • conjE T k⁻¹ I := by
    intro c I
    rw [conjE_apply, inv_inv, mul_smul_comm, smul_mul_assoc]
  rw [h1, ← ContinuousLinearEquiv.integral_comp_comm]
  congr 1
  conv_rhs => rw [← integral_mul_left_eq_self _ k]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hm : ∀ a b : KG ε, toMK (a * b) = toMK a * toMK b := fun _ _ => rfl
  have he : toMK (k * x)⁻¹ * pmat z * toMK (k * x) = toMK x⁻¹ * (toMK k⁻¹ * pmat z * toMK k) * toMK x := by
    rw [_root_.mul_inv_rev, hm, hm]
    simp only [Matrix.mul_assoc]
  have hop : T.op k⁻¹ * (T.op (k * x) * projW T * T.op (k * x)⁻¹) * T.op k = T.op x * projW T * T.op x⁻¹ := by
    rw [_root_.mul_inv_rev, op_mul, op_mul]
    simp only [mul_assoc]
    rw [op_inv_mul, mul_one, ← mul_assoc (T.op k⁻¹), op_inv_mul, one_mul]
  beta_reduce
  rw [conjE_apply, inv_inv, mul_smul_comm, smul_mul_assoc, he, hop]

theorem sum_norm_adjoint_sq_eq_hsOp {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [CompleteSpace V] (A : V →L[ℂ] V) :
    ∑ i, ‖(ContinuousLinearMap.adjoint A) (stdOrthonormalBasis ℂ V i)‖ ^ 2 = hsOp A := by
  unfold hsOp
  set b := stdOrthonormalBasis ℂ V
  have h1 : ∀ i, ‖(ContinuousLinearMap.adjoint A) (b i)‖ ^ 2 = ∑ j, ‖⟪b i, A (b j)⟫_ℂ‖ ^ 2 := by
    intro i
    rw [← b.sum_sq_norm_inner_right]
    refine sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.adjoint_inner_right, norm_inner_symm]
  have h2 : ∀ j, ‖A (b j)‖ ^ 2 = ∑ i, ‖⟪b i, A (b j)⟫_ℂ‖ ^ 2 := fun j => (b.sum_sq_norm_inner_right _).symm
  simp_rw [h1, h2]
  exact sum_comm

theorem hsOp_ge_integral {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (A : T.V →L[ℂ] T.V) :
    (Module.finrank ℂ T.V : ℝ) * ∫ k, ‖⟪T.op k T.w, A (T.op k T.w)⟫_ℂ‖ ^ 2 ∂(dk ε) ≤ hsOp A := by
  set b := stdOrthonormalBasis ℂ T.V
  set B := ContinuousLinearMap.adjoint A
  have hc : Continuous fun k : KG ε => T.op k T.w := (KType_continuous_op T).clm_apply continuous_const
  have hpt : ∀ k : KG ε, ‖⟪T.op k T.w, A (T.op k T.w)⟫_ℂ‖ ^ 2 ≤ ∑ i, ‖⟪B (b i), T.op k T.w⟫_ℂ‖ ^ 2 := by
    intro k
    have hn : ‖T.op k T.w‖ = 1 := by rw [KType_norm_op_apply, T.w_norm]
    have e : ∑ i, ‖⟪B (b i), T.op k T.w⟫_ℂ‖ ^ 2 = ‖A (T.op k T.w)‖ ^ 2 := by
      rw [← b.sum_sq_norm_inner_right]
      refine sum_congr rfl fun i _ => ?_
      rw [ContinuousLinearMap.adjoint_inner_left]
    rw [e]
    have := norm_inner_le_norm (𝕜 := ℂ) (T.op k T.w) (A (T.op k T.w))
    rw [hn, one_mul] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have hI1 : Integrable (fun k : KG ε => ‖⟪T.op k T.w, A (T.op k T.w)⟫_ℂ‖ ^ 2) (dk ε) :=
    integrable_dk_of_continuous ((continuous_inner.comp (hc.prodMk (A.continuous.comp hc))).norm.pow 2)
  have hI2 : ∀ i, Integrable (fun k : KG ε => ‖⟪B (b i), T.op k T.w⟫_ℂ‖ ^ 2) (dk ε) := fun i =>
    integrable_dk_of_continuous ((continuous_const.inner hc).norm.pow 2)
  have hmono := integral_mono hI1 (integrable_finsetSum _ fun i _ => hI2 i) hpt
  rw [integral_finsetSum _ fun i _ => hI2 i] at hmono
  have hd : (0 : ℝ) ≤ Module.finrank ℂ T.V := Nat.cast_nonneg _
  calc (Module.finrank ℂ T.V : ℝ) * ∫ k, ‖⟪T.op k T.w, A (T.op k T.w)⟫_ℂ‖ ^ 2 ∂(dk ε)
      ≤ (Module.finrank ℂ T.V : ℝ) * ∑ i, ∫ k, ‖⟪B (b i), T.op k T.w⟫_ℂ‖ ^ 2 ∂(dk ε) :=
        mul_le_mul_of_nonneg_left hmono hd
    _ = ∑ i, ‖B (b i)‖ ^ 2 := by
        rw [mul_sum]
        refine sum_congr rfl fun i _ => ?_
        rw [kschur_coef, T.w_norm, one_pow, one_mul]
    _ = hsOp A := sum_norm_adjoint_sq_eq_hsOp A

open CompactHaarProbability in
theorem continuous_fF (ε : Fin n → Bool) (lam : Fin n → ℝ) {Λ : Fin n → ℝ} (T : KType ε Λ) :
    Continuous fun z : PCoord ε → ℂ => fF ε lam T (pmat z) := by
  letI : IsProbabilityMeasure (dk ε) := ⟨by
    change (muK ε Set.univ)⁻¹ * muK ε Set.univ = 1
    exact ENNReal.inv_mul_cancel
      (ENNReal.toReal_pos_iff.mp (muK_univ_pos ε)).1.ne'
      (ENNReal.toReal_pos_iff.mp (muK_univ_pos ε)).2.ne⟩
  letI : IsFiniteMeasureOnCompacts (dk ε) := ⟨fun K hK =>
    (measure_mono (Set.subset_univ K)).trans_lt (measure_lt_top (dk ε) Set.univ)⟩
  have hf : Continuous (fun p : (PCoord ε → ℂ) × KG ε =>
      ((Real.exp (-Ph lam (toMK p.2⁻¹ * pmat p.1 * toMK p.2)) : ℝ) : ℂ) • (T.op p.2 * projW T * T.op p.2⁻¹)) :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_potential_conj_prod lam).neg)).smul
      ((cont_conj T _).comp continuous_snd)
  have h2 := continuous_parametric_integral_of_continuous (μ := dk ε)
    (f := fun z k => ((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) • (T.op k * projW T * T.op k⁻¹))
    hf isCompact_univ
  simp only [Measure.restrict_univ] at h2
  have he : (fun z : PCoord ε → ℂ => fF ε lam T (pmat z)) = fun z => ((Module.finrank ℂ T.V : ℝ) : ℂ) •
      ∫ k, ((Real.exp (-Ph lam (toMK k⁻¹ * pmat z * toMK k)) : ℝ) : ℂ) • (T.op k * projW T * T.op k⁻¹) ∂(dk ε) :=
    funext fun z => fF_eq_integral lam T _
  rw [he]
  exact (continuous_const : Continuous fun _ : PCoord ε → ℂ => ((Module.finrank ℂ T.V : ℝ) : ℂ)).smul h2

theorem inner_fF_conj {ε : Fin n → Bool} {lam : Fin n → ℝ} (T : KType ε (lowK ε lam)) (k : KG ε)
    (z : PCoord ε → ℂ) :
    ⟪T.w, fF ε lam T (pmat (adK k⁻¹ z)) T.w⟫_ℂ = ⟪T.op k T.w, fF ε lam T (pmat z) (T.op k T.w)⟫_ℂ := by
  rw [← conj_pmat_eq_adK, fF_conj_pmat_eq_op_inv_mul_fF_mul_op, KType_op_inv_eq_adjoint, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.adjoint_inner_right]

theorem formal_degree_inequality {ε : Fin n → Bool} {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {T : KType ε (lowK ε lam)}
    {j : T.V →L[ℂ] H} (hF : FData ε lam σ T j) {d : ℝ} (hd : Formalism.MainNotions.S.IsFdeg (muCD ε) σ d) :
    ENNReal.ofReal (cPQ ε) *
        ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (‖⟪T.w, fF ε lam T (pmat z) T.w⟫_ℂ‖ ^ 2 * Jac z) ≤
      ENNReal.ofReal ((Module.finrank ℂ T.V : ℝ) / d) := by
  letI : IsProbabilityMeasure (dk ε) := ⟨by
    change (muK ε Set.univ)⁻¹ * muK ε Set.univ = 1
    exact ENNReal.inv_mul_cancel
      (ENNReal.toReal_pos_iff.mp (muK_univ_pos ε)).1.ne'
      (ENNReal.toReal_pos_iff.mp (muK_univ_pos ε)).2.ne⟩
  letI : IsFiniteMeasureOnCompacts (dk ε) := ⟨fun K hK =>
    (measure_mono (Set.subset_univ K)).trans_lt (measure_lt_top (dk ε) Set.univ)⟩
  letI : SFinite (dk ε) := by infer_instance
  have hpos : 0 < (Module.finrank ℂ T.V : ℝ) := by
    have : Nontrivial T.V := ⟨⟨T.w, 0, fun h => by
      have := T.w_norm; rw [h, norm_zero] at this; exact zero_ne_one this⟩⟩
    exact_mod_cast Module.finrank_pos
  have l6 := lemma6a hF hd
  set D : ℝ := (Module.finrank ℂ T.V : ℝ) with hD
  set G : (PCoord ε → ℂ) → ℝ := fun z => ‖⟪T.w, fF ε lam T (pmat z) T.w⟫_ℂ‖ ^ 2 with hG
  set h : KG ε → (PCoord ε → ℂ) → ℝ :=
    fun k z => ‖⟪T.op k T.w, fF ε lam T (pmat z) (T.op k T.w)⟫_ℂ‖ ^ 2 * Jac z with hh
  have hFc := continuous_fF ε lam T
  have hJc := pb_jac_continuous ε
  have hGc : Continuous G := (continuous_const.inner (hFc.clm_apply continuous_const)).norm.pow 2
  have hc : Continuous fun k : KG ε => T.op k T.w := (KType_continuous_op T).clm_apply continuous_const
  have hhc : Continuous (Function.uncurry h) := by
    have a : Continuous fun p : KG ε × (PCoord ε → ℂ) => T.op p.1 T.w := hc.comp continuous_fst
    exact ((a.inner ((hFc.comp continuous_snd).clm_apply a)).norm.pow 2).mul (hJc.comp continuous_snd)
  have s1 : ∀ k : KG ε, ∫⁻ z, ENNReal.ofReal (h k z) = ∫⁻ z, ENNReal.ofReal (G z * Jac z) := by
    intro k
    have hm : Measurable fun z => ENNReal.ofReal (G z * Jac z) :=
      ENNReal.measurable_ofReal.comp (hGc.mul hJc).measurable
    rw [← (adK_measurePreserving k⁻¹).lintegral_comp hm]
    refine lintegral_congr fun z => ?_
    simp only [h, G, inner_fF_conj, jac_adK]
  have s2 : ∫⁻ z, ENNReal.ofReal (G z * Jac z) = ∫⁻ z, ∫⁻ k, ENNReal.ofReal (h k z) ∂(dk ε) := by
    have e : ∫⁻ z, ENNReal.ofReal (G z * Jac z) = ∫⁻ k, (∫⁻ z, ENNReal.ofReal (h k z)) ∂(dk ε) := by
      simp only [s1, lintegral_const]
      rw [measure_univ, mul_one]
    rw [e, lintegral_lintegral_swap (f := fun k z => ENNReal.ofReal (h k z)) (μ := dk ε) (ν := volume)
      (ENNReal.measurable_ofReal.comp hhc.measurable).aemeasurable]
  have s3 : ∀ z, ENNReal.ofReal D * ∫⁻ k, ENNReal.ofReal (h k z) ∂(dk ε) ≤
      ENNReal.ofReal (hsOp (fF ε lam T (pmat z)) * Jac z) := by
    intro z
    have hi : Integrable (fun k => ‖⟪T.op k T.w, fF ε lam T (pmat z) (T.op k T.w)⟫_ℂ‖ ^ 2) (dk ε) :=
      integrable_dk_of_continuous ((continuous_inner.comp (hc.prodMk ((fF ε lam T (pmat z)).continuous.comp hc))).norm.pow 2)
    rw [← ofReal_integral_eq_lintegral_ofReal (hi.mul_const _)
      (Filter.Eventually.of_forall fun k => mul_nonneg (by positivity) (jacobian_nonneg z)),
      integral_mul_const, ← ENNReal.ofReal_mul hpos.le, ← mul_assoc]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hsOp_ge_integral T _) (jacobian_nonneg z))
  have s4 : ENNReal.ofReal D * ∫⁻ z, ENNReal.ofReal (G z * Jac z) ≤
      ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (hsOp (fF ε lam T (pmat z)) * Jac z) := by
    rw [s2, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono s3
  have s5 : ENNReal.ofReal D * (ENNReal.ofReal (cPQ ε) * ∫⁻ z, ENNReal.ofReal (G z * Jac z)) ≤
      ENNReal.ofReal D * ENNReal.ofReal (D / d) := by
    rw [← ENNReal.ofReal_mul hpos.le, show D * (D / d) = D ^ 2 / d by ring, l6, mul_left_comm]
    exact mul_le_mul_right s4 _
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr hpos).ne' ENNReal.ofReal_ne_top).1 s5

theorem lintegral_fF_coeff_sq_le_finrank_div_fdeg {ε : Fin n → Bool} {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {T : KType ε (lowK ε lam)}
    {j : T.V →L[ℂ] H} (hF : FData ε lam σ T j) {d : ℝ} (hd : Formalism.MainNotions.S.IsFdeg (muCD ε) σ d) :
    ENNReal.ofReal (cPQ ε) *
        ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (‖⟪T.w, fF ε lam T (pmat z) T.w⟫_ℂ‖ ^ 2 * Jac z) ≤
      ENNReal.ofReal ((Module.finrank ℂ T.V : ℝ) / d) :=
  formal_degree_inequality hF hd

end ReciprocityTheory.ChartRestriction.DS
end
end

