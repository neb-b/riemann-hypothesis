module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0009
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.ProdSubLtEqFactorial
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarBasic
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0010
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0006
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KSchur

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdLower
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem formal_degree_liminf_lower_bound {ε : Fin n → Bool} {lam : Fin n → ℝ} (T : ∀ t : ℕ, KType ε (lowK ε (lamT lam t)))
    (hlim : ∀ y : PCoord ε → ℂ, Filter.Tendsto (fun t : ℕ => ⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ) Filter.atTop
      (nhds ((Real.exp (-(Qf (0 : Fin n → ℝ) y / 2)) : ℝ) : ℂ))) :
    ENNReal.ofReal (PiW ε 0) ≤ Filter.liminf (fun t : ℕ => ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
      ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat z) (T t).w⟫_ℂ‖ ^ 2 * Jac z))
      Filter.atTop := by

  have hsq : ∀ y : PCoord ε → ℂ,
      ‖(((Real.exp (-(Qf (0 : Fin n → ℝ) y / 2))) : ℝ) : ℂ)‖ ^ 2 = Real.exp (-Qf (0 : Fin n → ℝ) y) := by
    intro y
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, sq, ← Real.exp_add]
    congr 1
    ring
  have htend : ∀ y : PCoord ε → ℂ, Filter.Tendsto (fun t : ℕ => ENNReal.ofReal
      (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2))
      Filter.atTop (nhds (ENNReal.ofReal (Real.exp (-Qf (0 : Fin n → ℝ) y)))) := by
    intro y
    rw [← hsq y]
    exact ENNReal.tendsto_ofReal (((hlim y).norm).pow 2)
  have hmeas : ∀ t : ℕ, Measurable (fun y : PCoord ε → ℂ => ENNReal.ofReal
      (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2)) := by
    intro t
    exact ENNReal.measurable_ofReal.comp
      ((((fdl_inner_continuous (lamT lam t) (T t) (T t).w (T t).w).comp
        (continuous_const_smul _)).norm.pow 2).measurable)
  have key : ∀ t : ℕ, 1 ≤ t →
      ∫⁻ y : PCoord ε → ℂ, ENNReal.ofReal
        (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2) ≤
      ENNReal.ofReal ((t : ℝ) ^ (pOf ε * qOf ε)) *
        ∫⁻ z : PCoord ε → ℂ, ENNReal.ofReal (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat z) (T t).w⟫_ℂ‖ ^ 2 * Jac z) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := Nat.cast_pos.mpr ht
    have hs : (0 : ℝ) < (Real.sqrt t)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 ht0)
    have hpow : ((Real.sqrt t)⁻¹) ^ (2 * (pOf ε * qOf ε)) = ((t : ℝ) ^ (pOf ε * qOf ε))⁻¹ := by
      rw [pow_mul, inv_pow, Real.sq_sqrt ht0.le, inv_pow]
    conv_rhs => rw [lintegral_pcoord_smul _ hs]
    try rw [show 2 * pOf ε * qOf ε = 2 * (pOf ε * qOf ε) from mul_assoc _ _ _]
    rw [hpow, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity),
      ENNReal.ofReal_one, one_mul]
    refine lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_
    exact le_mul_of_one_le_right (sq_nonneg _) (jac_ge_one _)
  calc ENNReal.ofReal (PiW ε 0)
      = ∫⁻ y : PCoord ε → ℂ, ENNReal.ofReal (Real.exp (-Qf (0 : Fin n → ℝ) y)) := (fdl_gauss ε).symm
    _ = ∫⁻ y : PCoord ε → ℂ, Filter.liminf (fun t : ℕ => ENNReal.ofReal
          (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2))
          Filter.atTop := by
        congr 1
        funext y
        rw [(htend y).liminf_eq]
    _ ≤ Filter.liminf (fun t : ℕ => ∫⁻ y : PCoord ε → ℂ, ENNReal.ofReal
          (‖⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ‖ ^ 2))
          Filter.atTop := lintegral_liminf_le hmeas
    _ ≤ _ := by
        refine Filter.liminf_le_liminf ?_
        filter_upwards [Filter.eventually_ge_atTop 1] with t ht using key t ht

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdPointwise
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem trace_dMat_pmat {ε : Fin n → Bool} (y : PCoord ε → ℂ) : trace (Lap.Base.dMat (Dvec n) * pmat y) = 0 := by
  simp only [Lap.Base.dMat, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
  refine Finset.sum_eq_zero fun a _ => ?_
  simp [pmat]

theorem pmat_herm_apply {ε : Fin n → Bool} (y : PCoord ε → ℂ) (a b : Fin n) :
    pmat y b a = star (pmat y a b) := by
  simp only [pmat]
  by_cases h1 : a < b ∧ ε b ≠ ε a
  · have h2 : ¬ (b < a ∧ ε a ≠ ε b) := fun h => lt_asymm h.1 h1.1
    simp only [dif_pos h1, dif_neg h2, star_star]
  · by_cases h2 : b < a ∧ ε a ≠ ε b
    · simp only [dif_neg h1, dif_pos h2]
    · simp only [dif_neg h1, dif_neg h2, star_zero]

theorem sum_pairs_pmat_fp {ε : Fin n → Bool} (w : Fin n → Fin n → ℝ) (z : PCoord ε → ℂ) :
    ∑ x : Fin n × Fin n, (if x.2 < x.1 then w x.1 x.2 * ‖pmat z x.1 x.2‖ ^ 2 else 0) =
      ∑ ab : PCoord ε, w ab.1.1 ab.1.2 * ‖z ab‖ ^ 2 := by
  classical
  have key : ∀ x : Fin n × Fin n, (if x.2 < x.1 then w x.1 x.2 * ‖pmat z x.1 x.2‖ ^ 2 else 0) =
      (if h : x.2 < x.1 ∧ ε x.1 ≠ ε x.2 then w x.1 x.2 * ‖z ⟨x, h⟩‖ ^ 2 else 0) := by
    rintro ⟨a, b⟩
    dsimp only
    by_cases h : b < a ∧ ε a ≠ ε b
    · rw [dif_pos h, if_pos h.1]
      have hp : pmat z a b = z ⟨(a, b), h⟩ := by
        simp only [pmat, dif_pos h]
      rw [hp]
    · rw [dif_neg h]
      split_ifs with hab
      · have h2 : ¬ (a < b ∧ ε b ≠ ε a) := fun h' => lt_asymm hab h'.1
        have hp : pmat z a b = 0 := by
          simp only [pmat, dif_neg h, dif_neg h2]
        rw [hp]; simp
      · rfl
  rw [Finset.sum_congr rfl (fun x _ => key x)]
  rw [← Finset.sum_filter_of_ne (p := fun x : Fin n × Fin n => x.2 < x.1 ∧ ε x.1 ≠ ε x.2)
    (fun x _ hx => by
      by_contra h
      exact hx (dif_neg h))]
  rw [Finset.sum_subtype (p := fun x : Fin n × Fin n => x.2 < x.1 ∧ ε x.1 ≠ ε x.2) _
    (fun x => by simp)]
  refine Finset.sum_congr rfl fun ab _ => ?_
  exact dif_pos ab.2

private theorem pmat_apply_eq_zero_of_sign_eq {ε : Fin n → Bool} (y : PCoord ε → ℂ) {a b : Fin n} (he : ε a = ε b) :
    pmat y a b = 0 := by
  simp only [pmat]
  rw [dif_neg (fun h => h.2 he), dif_neg (fun h => h.2 he.symm)]

theorem qForm_term {ε : Fin n → Bool} (y : PCoord ε → ℂ) (a b : Fin n) :
    -((((Dvec n a : ℝ) : ℂ) - ((Dvec n b : ℝ) : ℂ)) * (pmat y a b * Lap.Base.partNM ε (Dvec n) (pmat y) b a)) =
      (((if b < a then (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) * ‖pmat y a b‖ ^ 2 else 0 : ℝ)) : ℂ) := by
  have hD : ((Dvec n a : ℝ) : ℂ) - ((Dvec n b : ℝ) : ℂ) = ((((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) : ℝ) : ℂ) := by
    simp only [Dvec]; push_cast; ring
  by_cases h : b < a ∧ ε a ≠ ε b
  · have hin : Lap.Base.InNM ε (Dvec n) b a := Or.inr h
    have hN : Lap.Base.partNM ε (Dvec n) (pmat y) b a = pmat y b a := by
      rw [Lap.Base.partNM, Matrix.of_apply, if_pos hin]
    rw [hN, if_pos h.1, hD, pmat_herm_apply y a b, Complex.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    push_cast; ring
  · have h0 : pmat y a b * Lap.Base.partNM ε (Dvec n) (pmat y) b a = 0 := by
      rw [Lap.Base.partNM, Matrix.of_apply]
      split_ifs with hin
      · rcases hin with ⟨_, he, _⟩ | h'
        · rw [pmat_apply_eq_zero_of_sign_eq y he, zero_mul]
        · exact absurd h' h
      · exact mul_zero _
    rw [h0, mul_zero, neg_zero]
    split_ifs with hba
    · have he : ε a = ε b := by
        by_contra he
        exact h ⟨hba, he⟩
      rw [pmat_apply_eq_zero_of_sign_eq y he]; simp
    · simp

theorem qForm_pmat {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    Lap.Base.qForm ε (Dvec n) (pmat y) = ((Qf (0 : Fin n → ℝ) y : ℝ) : ℂ) := by
  have h1 : Lap.Base.qForm ε (Dvec n) (pmat y) = ∑ a : Fin n, ∑ b : Fin n,
      -((((Dvec n a : ℝ) : ℂ) - ((Dvec n b : ℝ) : ℂ)) *
        (pmat y a b * Lap.Base.partNM ε (Dvec n) (pmat y) b a)) := by
    have e : ∀ a b : Fin n, -((((Dvec n a : ℝ) : ℂ) - ((Dvec n b : ℝ) : ℂ)) *
        (pmat y a b * Lap.Base.partNM ε (Dvec n) (pmat y) b a)) =
        -(((Dvec n a : ℝ) : ℂ) * (pmat y a b * Lap.Base.partNM ε (Dvec n) (pmat y) b a)) +
          ((Dvec n b : ℝ) : ℂ) * (Lap.Base.partNM ε (Dvec n) (pmat y) b a * pmat y a b) :=
      fun a b => by ring
    simp_rw [e, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    rw [Finset.sum_comm (f := fun a b : Fin n =>
      ((Dvec n b : ℝ) : ℂ) * (Lap.Base.partNM ε (Dvec n) (pmat y) b a * pmat y a b))]
    simp only [Lap.Base.qForm, Lap.Base.dMat, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
    simp only [Matrix.sub_apply, Matrix.mul_apply, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
    ring
  rw [h1]
  simp only [qForm_term]
  have e2 := sum_pairs_pmat_fp (fun a b : Fin n => ((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) y
  rw [Fintype.sum_prod_type' (f := fun a b : Fin n =>
    (if b < a then (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) * ‖pmat y a b‖ ^ 2 else 0 : ℝ))] at e2
  rw [← Complex.ofReal_inj] at e2
  simp only [Complex.ofReal_sum] at e2
  rw [e2, ← Complex.ofReal_sum]
  congr 1
  simp only [Qf, wab, Pi.zero_apply, sub_self, zero_add]

theorem matrix_coefficient_pointwise_limit (hB3 : Lap.Base.TangentPairingStatement) {ε : Fin n → Bool} {lam : Fin n → ℝ} (H : ℕ → Type)
    [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℂ (H t)] [∀ t, CompleteSpace (H t)]
    (σ : ∀ t : ℕ, Matrix (Fin n) (Fin n) ℂ → (H t →L[ℂ] H t)) (T : ∀ t : ℕ, KType ε (lowK ε (lamT lam t)))
    (j : ∀ t : ℕ, (T t).V →L[ℂ] H t)
    (hF : ∀ᶠ t in Filter.atTop, FData ε (lamT lam t) (σ t) (T t) (j t))
    (hsm : ∀ᶠ t in Filter.atTop, ∃ (H' : Type) (_ : NormedAddCommGroup H') (_ : InnerProductSpace ℂ H')
      (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')) (w' : H'), Lap.Base.IsHWSmooth ε σ' (lamT lam t) w' ∧
        ∀ z : PCoord ε → ℂ, ⟪w', σ' (NormedSpace.exp (pmat z)) w'⟫_ℂ =
          ⟪(T t).w, fF ε (lamT lam t) (T t) (pmat z) (T t).w⟫_ℂ)
    (y : PCoord ε → ℂ) :
    Filter.Tendsto (fun t : ℕ => ⟪(T t).w, fF ε (lamT lam t) (T t) (pmat ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y)) (T t).w⟫_ℂ) Filter.atTop
      (nhds ((Real.exp (-(Qf (0 : Fin n → ℝ) y / 2)) : ℝ) : ℂ)) := by
  obtain ⟨C, hC⟩ := hB3 n ε (Dvec n) (lowK ε lam) (S7.hs (pmat y) + 1)
  have hinG : inG ε (pmat y) := by
    unfold inG Jm
    ext a b
    simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
      Matrix.zero_apply]
    rw [pmat_herm_apply y a b, star_star]
    by_cases he : ε a = ε b
    · rw [pmat_apply_eq_zero_of_sign_eq y he]; simp
    · cases ha : ε a <;> cases hb : ε b <;> simp_all
  have hR : S7.hs (pmat y) ≤ (S7.hs (pmat y) + 1) ^ 2 := by
    nlinarith [sq_nonneg (S7.hs (pmat y) + 1 / 2)]
  have hsq : Filter.Tendsto (fun t : ℕ => Real.sqrt (t : ℝ)) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_atTop.mpr fun b => ⟨⌈b ^ 2⌉₊, fun a ha => ?_⟩
    refine (le_abs_self b).trans (Real.abs_le_sqrt ?_)
    exact (Nat.le_ceil _).trans (by exact_mod_cast ha)
  have hC0 : Filter.Tendsto (fun t : ℕ => C / Real.sqrt (t : ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hsq
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hC0
  filter_upwards [hsm, Filter.eventually_ge_atTop 1] with t ht ht1
  obtain ⟨H', i1, i2, σ', w', hw', heq⟩ := ht
  letI := i1
  letI := i2
  have hlow : lowK ε (lamT lam t) = (t : ℝ) • Dvec n + lowK ε lam := by
    ext a
    simp only [lowK, lamT, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hb := hC (t : ℝ) (by exact_mod_cast ht1) H' σ' (lamT lam t) w' hw' hlow (pmat y) hinG hR
  rw [trace_dMat_pmat y, qForm_pmat y, mul_zero, neg_zero, Complex.exp_zero, mul_one] at hb
  have hy : ((((Real.sqrt t)⁻¹ : ℝ) : ℂ) • y) = ((Real.sqrt t)⁻¹ : ℝ) • y := by
    ext ab
    simp only [Pi.smul_apply, smul_eq_mul, Complex.real_smul]
  have hL : (((Real.exp (-(Qf (0 : Fin n → ℝ) y / 2)) : ℝ) : ℂ)) =
      Complex.exp (-((Qf (0 : Fin n → ℝ) y : ℝ) : ℂ) / 2) := by
    rw [Complex.ofReal_exp]; push_cast; ring_nf
  rw [← heq, hy, adKAux_pmat_smul, hL]
  exact hb

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HsEighthLeOfSmall
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem pmat_smul {ε : Fin n → Bool} (c : ℝ) (z : PCoord ε → ℂ) :
    pmat (c • z) = (c : ℂ) • pmat z := by
  ext a b
  simp only [pmat, Pi.smul_apply, Matrix.smul_apply]
  split_ifs <;> simp [Complex.real_smul]

theorem hs_pmat_smul {ε : Fin n → Bool} (c : ℝ) (z : PCoord ε → ℂ) :
    hs (pmat (c • z)) = c ^ 2 * hs (pmat z) := by
  rw [hs_pmat, hs_pmat, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem hs_half_le_quadratic {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    hs (pmat z) / 2 ≤ Qf (0 : Fin n → ℝ) z := by
  have e : hs (pmat z) / 2 = ∑ ab, ‖z ab‖ ^ 2 := by rw [hs_pmat]; ring
  rw [e, Qf]
  refine Finset.sum_le_sum fun ab _ => ?_
  have hv : ((ab.1.2 : ℕ) : ℝ) + 1 ≤ ((ab.1.1 : ℕ) : ℝ) := by exact_mod_cast Fin.lt_def.mp ab.2.1
  have hw : 1 ≤ wab (0 : Fin n → ℝ) ab.1.1 ab.1.2 := by simp only [wab, Pi.zero_apply]; linarith
  exact le_mul_of_one_le_left (by positivity) hw

theorem hs_eighth_le_of_small {ε : Fin n → Bool} (z : PCoord ε → ℂ) (h : rhoP z ≤ 1 / 2) :
    hs (pmat z) / 8 ≤ Ph (0 : Fin n → ℝ) (pmat z) := by
  have hA : Antitone (0 : Fin n → ℝ) := fun _ _ _ => le_rfl
  have h1 := ph_lower hA z h (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have h2 := hs_half_le_quadratic z
  linarith

theorem potential_lower_min {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    1 / 16 * min (hs (pmat z)) (Real.sqrt (hs (pmat z)) / Real.sqrt (2 * (q0 ε : ℝ))) ≤
      Ph (0 : Fin n → ℝ) (pmat z) := by
  have hA : Antitone (0 : Fin n → ℝ) := fun _ _ _ => le_rfl
  have hH0 : 0 ≤ hs (pmat z) := by rw [hs_pmat]; positivity
  have hP0 := ph_nonneg hA z
  rcases Nat.eq_zero_or_pos (q0 ε) with hq | hq
  · have e : min (hs (pmat z)) (Real.sqrt (hs (pmat z)) / Real.sqrt (2 * (q0 ε : ℝ))) = 0 := by
      rw [hq]; simp [hH0]
    rw [e]; linarith
  · set c := Real.sqrt (2 * (q0 ε : ℝ)) with hc
    have hq1 : (1 : ℝ) ≤ (q0 ε : ℝ) := by exact_mod_cast hq
    have hc0 : 0 < c := Real.sqrt_pos.mpr (by linarith)
    set r := Real.sqrt (hs (pmat z)) with hr
    have hrr : r ^ 2 = hs (pmat z) := Real.sq_sqrt hH0
    have hr0 : 0 ≤ r := Real.sqrt_nonneg _
    have hrho : rhoP z = c * r := rfl
    by_cases hsm : c * r ≤ 1 / 2
    · have := hs_eighth_le_of_small z (by rw [hrho]; exact hsm)
      have hm := min_le_left (hs (pmat z)) (r / c)
      nlinarith
    · replace hsm := lt_of_not_ge hsm
      have hrp : 0 < r := by
        by_contra h0
        have : r = 0 := le_antisymm (not_lt.mp h0) hr0
        rw [this, mul_zero] at hsm; linarith
      set t := 2 * c * r with ht
      have ht1 : 1 ≤ t := by rw [ht]; linarith
      have ht0 : 0 < t := by linarith
      set z' := (1 / t) • z with hz'
      have hpz : pmat z = (t : ℂ) • pmat z' := by
        rw [hz', pmat_smul, smul_smul, ← Complex.ofReal_mul, mul_one_div_cancel ht0.ne',
          Complex.ofReal_one, one_smul]
      have hhs : hs (pmat z') = (1 / t) ^ 2 * r ^ 2 := by rw [hz', hs_pmat_smul, hrr]
      have hsq : Real.sqrt (hs (pmat z')) = 1 / t * r := by
        rw [hhs, ← mul_pow, Real.sqrt_sq (by positivity)]
      have hrho' : rhoP z' ≤ 1 / 2 := by
        have e2 : rhoP z' = c * Real.sqrt (hs (pmat z')) := rfl
        rw [e2, hsq, ht]
        field_simp
        linarith
      have hsm' := hs_eighth_le_of_small z' hrho'
      have hsc := ph_scale hA z' ht1
      rw [← hpz] at hsc
      have hm := min_le_right (hs (pmat z)) (r / c)
      have key : 1 / 16 * (r / c) ≤ t * (hs (pmat z') / 8) := by
        rw [hhs, ht]
        field_simp
        nlinarith
      have := mul_le_mul_of_nonneg_left hsm' ht0.le
      nlinarith

end ReciprocityTheory.ChartRestriction.DS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.PolarRight
section
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def rmulPR (G : Matrix (Fin n) (Fin n) ℂ) (A : Fin n → Fin n → ℂ) : Fin n → Fin n → ℂ :=
  (Matrix.of A : Matrix (Fin n) (Fin n) ℂ) * G

def polarPR {ε : Fin n → Bool} (kz : KG ε × (PCoord ε → ℂ)) : Fin n → Fin n → ℂ := polarM kz

theorem continuous_rmulPR (G : Matrix (Fin n) (Fin n) ℂ) : Continuous (rmulPR G) := by
  unfold rmulPR
  exact (continuous_id.matrix_mul continuous_const :
    Continuous fun A : Matrix (Fin n) (Fin n) ℂ => A * G)

theorem measurable_polarPR (ε : Fin n → Bool) : Measurable (polarPR (ε := ε)) := by
  have h : Continuous (polarPR (ε := ε)) := polarM_continuous ε
  exact h.measurable

theorem rmulPR_polarPR {ε : Fin n → Bool} {G : Matrix (Fin n) (Fin n) ℂ} (hG : inUJ ε G)
    (z : PCoord ε → ℂ) : ∃ k' : KG ε, ∀ k : KG ε,
      rmulPR G (polarPR (k, z)) = polarPR (k * k', actR G z) := by
  have hE : inUJ ε (NormedSpace.exp (pmat z)) := exp_pmat_inUJ z
  have hEG : inUJ ε (NormedSpace.exp (pmat z) * G) := by
    unfold inUJ at hE hG ⊢
    rw [Matrix.conjTranspose_mul]
    calc Gᴴ * (NormedSpace.exp (pmat z))ᴴ * Jm ε * (NormedSpace.exp (pmat z) * G)
        = Gᴴ * ((NormedSpace.exp (pmat z))ᴴ * Jm ε * NormedSpace.exp (pmat z)) * G := by
          simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [hE, hG]
  obtain ⟨⟨k', w⟩, hkw⟩ := polarM_surj _ hEG
  have hw : actR G z = w := by
    funext ab
    have h1 : plog (NormedSpace.exp (pmat z) * G) = pmat w := by
      rw [← hkw, plog_polarM]
    simp only [actR, h1, pmat, dif_pos ab.2]
  refine ⟨k', fun k => ?_⟩
  rw [hw]
  simp only [rmulPR, polarPR, polarM] at hkw ⊢
  have hm : toMK (k * k') = toMK k * toMK k' := rfl
  show toMK k * NormedSpace.exp (pmat z) * G = _
  rw [Matrix.mul_assoc, ← hkw, hm, Matrix.mul_assoc]

theorem muPolarMat_mul_right (ε : Fin n → Bool) {G : Matrix (Fin n) (Fin n) ℂ} (hG : inUJ ε G) :
    Measure.map (rmulPR G) (muPolarMat ε) = muPolarMat ε := by
  have hP : Measurable (polarPR (ε := ε)) := measurable_polarPR ε
  have hR : Measurable (rmulPR G) := (continuous_rmulPR G).measurable
  have hA : Measurable (actR (ε := ε) G) := (JacB.actR_continuous hG).measurable
  have hc := coreP hG
  have : IsFiniteMeasure (dk ε) := by
    rw [isFiniteMeasure_iff, (dk_props ε).1.measure_univ]
    exact ENNReal.one_lt_top

  have key : ∀ S : Set (Fin n → Fin n → ℂ), MeasurableSet S →
      muPolarMat ε S = ∫⁻ z, dk ε {k | polarPR (k, z) ∈ S}
        ∂(volume.withDensity fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z)) := by
    intro S hS
    show (Measure.map (polarPR (ε := ε)) ((dk ε).prod
      (volume.withDensity fun z : PCoord ε → ℂ => ENNReal.ofReal (Jac z)))) S = _
    rw [Measure.map_apply hP hS, Measure.prod_apply_symm (hP hS)]
    rfl
  ext S hS
  rw [Measure.map_apply hR hS, key _ (hR hS), key _ hS]
  have step : ∀ z : PCoord ε → ℂ, dk ε {k | polarPR (k, z) ∈ rmulPR G ⁻¹' S} =
      dk ε {k | polarPR (k, actR G z) ∈ S} := by
    intro z
    obtain ⟨k', hk'⟩ := rmulPR_polarPR hG z
    have hset : {k | polarPR (k, z) ∈ rmulPR G ⁻¹' S} =
        (fun k => k * k') ⁻¹' {k | polarPR (k, actR G z) ∈ S} := by
      ext k
      simp only [Set.mem_setOf_eq, Set.mem_preimage, hk']
    rw [hset, measure_preimage_mul_right]
  simp_rw [step]
  have hφ : Measurable fun w : PCoord ε → ℂ => dk ε {k | polarPR (k, w) ∈ S} :=
    measurable_measure_prodMk_right (hP hS)
  rw [← lintegral_map hφ hA, hc]

theorem muPolar_mul_right (ε : Fin n → Bool) (g : UJ ε) :
    Measure.map (fun x => x * g) (muPolar ε) = muPolar ε := by
  show Measure.map (fun x => x * g) (Measure.comap (intMuCD_eM ε) (muPolarMat ε)) =
    Measure.comap (intMuCD_eM ε) (muPolarMat ε)
  by_cases h : Function.Injective (intMuCD_eM ε) ∧
      ∀ s, MeasurableSet s → NullMeasurableSet (intMuCD_eM ε '' s) (muPolarMat ε)
  swap
  · simp only [Measure.comap, dif_neg h, Measure.map_zero]
  haveI : BorelSpace (UJ ε) := ⟨rfl⟩
  have hRm : Measurable (fun x : UJ ε => x * g) := (continuous_mul_const g).measurable
  have hG : inUJ ε (toM g) := g.2
  have h4 := muPolarMat_mul_right ε hG
  have hRM : Measurable (rmulPR (toM g)) := (continuous_rmulPR (toM g)).measurable
  ext S hS
  rw [Measure.map_apply hRm hS, Measure.comap_apply₀ _ _ h.1 h.2 (hRm hS).nullMeasurableSet,
    Measure.comap_apply₀ _ _ h.1 h.2 hS.nullMeasurableSet]
  have h1 : toM g * toM g⁻¹ = 1 := by
    rw [show toM g * toM g⁻¹ = toM (g * g⁻¹) from rfl, mul_inv_cancel]
    rfl
  have himg : intMuCD_eM ε '' ((fun x => x * g) ⁻¹' S) =
      rmulPR (toM g) ⁻¹' (intMuCD_eM ε '' S) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y * g, hy, rfl⟩
    · rintro ⟨y, hy, hxy⟩
      refine ⟨y * g⁻¹, ?_, ?_⟩
      · show y * g⁻¹ * g ∈ S
        rw [inv_mul_cancel_right]
        exact hy
      · have hx : toM y = Matrix.of x * toM g := hxy
        show toM y * toM g⁻¹ = x
        rw [hx, Matrix.mul_assoc, h1, Matrix.mul_one]
        rfl
  rw [himg, ← Measure.map_apply₀ hRM.aemeasurable (by rw [h4]; exact h.2 S hS), h4]

end ReciprocityTheory.ChartRestriction.DS
end
end

