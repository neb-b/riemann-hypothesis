module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0011
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0003
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalSer
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0010

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.CoeffOneSubstOfConstantCoeffEqZero
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

section Field
variable {K : Type} [Field K] (g2 g3 : K)

theorem coeff_one_subst_of_constantCoeff_eq_zero (f g : PowerSeries K) (hg : constantCoeff g = 0) :
    coeff 1 (f.subst g) = coeff 1 f * coeff 1 g := by
  have hs : HasSubst g := HasSubst.of_constantCoeff_zero hg
  have hX : X ∣ g := X_dvd_iff.mpr hg
  rw [PowerSeries.coeff_subst' hs, finsum_eq_single _ 1]
  · simp [smul_eq_mul]
  · intro d hd
    rcases Nat.lt_or_gt_of_ne hd with h | h
    · have : d = 0 := by omega
      subst this
      simp
    · have h2 : X ^ d ∣ g ^ d := pow_dvd_pow_of_dvd hX d
      have h3 := X_pow_dvd_iff.mp h2 1 h
      simp [h3]

theorem uSer_const : constantCoeff (uSer g2 g3) = 0 := by
  unfold uSer
  rw [map_mul, map_mul, constantCoeff_X, zero_mul, zero_mul]
theorem uSer_coeff_one : coeff 1 (uSer g2 g3) = 1 := by
  unfold uSer
  rw [mul_assoc, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply,
    map_mul, constantCoeff_inv]
  unfold wpNum wpDen
  simp [← coeff_zero_eq_constantCoeff_apply]

theorem isUnit_coeff_one_weierstrassExp : IsUnit (coeff 1 (uSer g2 g3)) := by
  rw [uSer_coeff_one]
  exact isUnit_one

theorem exists_rightInverse_weierstrassExp : ∃ t : PowerSeries K, constantCoeff t = 0 ∧ (uSer g2 g3).subst t = X := ⟨(uSer g2 g3).substInvOfIsUnit (isUnit_coeff_one_weierstrassExp g2 g3), PowerSeries.constantCoeff_substInvOfIsUnit _ _,
  PowerSeries.subst_substInvOfIsUnit_right _ (uSer_const g2 g3) _⟩

theorem lgS_const : constantCoeff (lgS g2 g3) = 0 := by
  unfold lgS
  rw [dite_eq_left (exists_rightInverse_weierstrassExp g2 g3)]
  exact (exists_rightInverse_weierstrassExp g2 g3).choose_spec.1
theorem uSer_subst_lgS : (uSer g2 g3).subst (lgS g2 g3) = X := by
  unfold lgS
  rw [dite_eq_left (exists_rightInverse_weierstrassExp g2 g3)]
  exact (exists_rightInverse_weierstrassExp g2 g3).choose_spec.2
theorem lgS_coeff_one : coeff 1 (lgS g2 g3) = 1 := by
  have h := congrArg (coeff 1) (uSer_subst_lgS g2 g3)
  rw [coeff_one_subst_of_constantCoeff_eq_zero _ _ (lgS_const g2 g3), uSer_coeff_one, one_mul] at h
  simpa using h

theorem eq_substInv_of_rightInverse (t : PowerSeries K) (ht : constantCoeff t = 0)
    (h : (uSer g2 g3).subst t = X) :
    t = (uSer g2 g3).substInvOfIsUnit (isUnit_coeff_one_weierstrassExp g2 g3) := by
  have h1 := PowerSeries.subst_comp_subst_apply (HasSubst.of_constantCoeff_zero (uSer_const g2 g3))
    (HasSubst.of_constantCoeff_zero ht) ((uSer g2 g3).substInvOfIsUnit (isUnit_coeff_one_weierstrassExp g2 g3))
  rw [PowerSeries.subst_substInvOfIsUnit_left _ (uSer_const g2 g3), PowerSeries.subst_X (HasSubst.of_constantCoeff_zero ht),
    h, PowerSeries.X_subst] at h1
  exact h1

theorem weierstrassLog_eq_substInv : lgS g2 g3 = (uSer g2 g3).substInvOfIsUnit (isUnit_coeff_one_weierstrassExp g2 g3) := eq_substInv_of_rightInverse g2 g3 (lgS g2 g3) (lgS_const g2 g3) (uSer_subst_lgS g2 g3)

theorem lgS_subst_uSer : (lgS g2 g3).subst (uSer g2 g3) = X := by
  rw [weierstrassLog_eq_substInv]
  exact PowerSeries.subst_substInvOfIsUnit_left _ (uSer_const g2 g3) _

theorem lgS_unique (t : PowerSeries K) (ht : constantCoeff t = 0) (h : (uSer g2 g3).subst t = X) :
    t = lgS g2 g3 := by
  exact (eq_substInv_of_rightInverse g2 g3 t ht h).trans (weierstrassLog_eq_substInv g2 g3).symm

theorem constantCoeff_C_mul_weierstrassLog (b : K) : constantCoeff (C b * lgS g2 g3) = 0 := by
  rw [map_mul, constantCoeff_C, lgS_const, mul_zero]

theorem mult_const (b : K) : constantCoeff ((uSer g2 g3).subst (C b * lgS g2 g3)) = 0 := by
  have hs := constantCoeff_C_mul_weierstrassLog g2 g3 b
  have ha : HasSubst (C b * lgS g2 g3) := HasSubst.of_constantCoeff_zero hs
  rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_subst' ha, finsum_eq_single _ 0]
  · simp [uSer_const]
  · intro d hd
    simp [map_pow, hs, zero_pow hd]
theorem mult_log (b : K) :
    (lgS g2 g3).subst ((uSer g2 g3).subst (C b * lgS g2 g3)) = C b * lgS g2 g3 := by
  have hu := HasSubst.of_constantCoeff_zero (uSer_const g2 g3)
  have ha := HasSubst.of_constantCoeff_zero (constantCoeff_C_mul_weierstrassLog g2 g3 b)
  have h1 := PowerSeries.subst_comp_subst_apply hu ha (lgS g2 g3)
  rw [lgS_subst_uSer, PowerSeries.subst_X ha] at h1
  exact h1.symm
theorem mult_unique (b : K) (e : PowerSeries K) (he : constantCoeff e = 0)
    (h : (lgS g2 g3).subst e = C b * lgS g2 g3) : e = (uSer g2 g3).subst (C b * lgS g2 g3) := by
  have hl := HasSubst.of_constantCoeff_zero (lgS_const g2 g3)
  have hE := HasSubst.of_constantCoeff_zero he
  have h1 := PowerSeries.subst_comp_subst_apply hl hE (uSer g2 g3)
  rw [uSer_subst_lgS, PowerSeries.subst_X hE, h] at h1
  exact h1

theorem ltLog_const (l : ℕ) (hl : 2 ≤ l) : constantCoeff (ltLog K l) = 0 := by
  first | unfold Formalism.G.ltLog | unfold Formalism.L2.Th1.CM.ltLog
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, dite_eq_right]
  rintro ⟨j, hj⟩
  have h0 : 0 < (l ^ 2) ^ j := pow_pos (pow_pos (by omega) 2) j
  rw [← hj] at h0
  exact lt_irrefl 0 h0

end Field

section Map
variable {K L : Type} [Field K] [Field L] (φ : K →+* L) (g2 g3 : K)

theorem cW_unfold {K : Type} [Field K] (g2 g3 : K) (k : ℕ) : cW g2 g3 k =
    if k = 2 then g2 / 20 else if k = 3 then g3 / 28 else
    if 4 ≤ k then
      3 / ((2 * (k : K) + 1) * ((k : K) - 3)) *
        ∑ m : Fin (k - 3), cW g2 g3 (m.val + 2) * cW g2 g3 (k - (m.val + 2))
    else 0 := by
  rw [cW]
  first
    | (rw [Nat.strongRecOn_beta]; rfl)
    | (rw [Nat.strongRecOn'_beta]; rfl)
    | (rw [Nat.strongRecOn_eq]; rfl)
    | (unfold Nat.strongRecOn; rw [Nat.strongRec_eq]; rfl)
    | (exact (Nat.strongRecOn_beta' ..).trans rfl)

theorem cW_map (k : ℕ) : φ (cW g2 g3 k) = cW (φ g2) (φ g3) k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [cW_unfold, cW_unfold (φ g2) (φ g3)]
    split_ifs with h1 h2 h3
    · rw [map_div₀]
      congr 1
      exact_mod_cast map_natCast φ 20
    · rw [map_div₀]
      congr 1
      exact_mod_cast map_natCast φ 28
    · set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_mul, map_div₀, map_sum, map_ofNat, map_natCast, map_sub, map_add (f := _), map_one]
      congr 1
      refine Finset.sum_congr rfl fun m _ => ?_
      have hm := m.2
      rw [ih _ (by omega), ih _ (by omega)]
    · simp

theorem wpNum_map : PowerSeries.map φ (wpNum g2 g3) = wpNum (φ g2) (φ g3) := by
  ext n
  unfold wpNum
  rw [coeff_map, coeff_mk, coeff_mk]
  split_ifs <;> simp [cW_map]

theorem wpDen_map : PowerSeries.map φ (wpDen g2 g3) = wpDen (φ g2) (φ g3) := by
  ext n
  unfold wpDen
  rw [coeff_map, coeff_mk, coeff_mk]
  split_ifs <;> simp [cW_map]

theorem wpDen_const' {K : Type} [Field K] (g2 g3 : K) : constantCoeff (wpDen g2 g3) = 1 := by
  unfold wpDen
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]
  simp

theorem uSer_map : PowerSeries.map φ (uSer g2 g3) = uSer (φ g2) (φ g3) := by
  have hD : constantCoeff (wpDen (φ g2) (φ g3)) ≠ 0 := by rw [wpDen_const']; exact one_ne_zero
  have hD0 : constantCoeff (wpDen g2 g3) ≠ 0 := by rw [wpDen_const']; exact one_ne_zero
  have h : map φ (wpDen g2 g3)⁻¹ = (wpDen (φ g2) (φ g3))⁻¹ := by
    rw [PowerSeries.eq_inv_iff_mul_eq_one hD, ← wpDen_map, ← map_mul,
      PowerSeries.inv_mul_cancel _ hD0, map_one]
  unfold uSer
  rw [map_mul, map_mul, map_X, wpNum_map, h]

theorem map_subst_ps {a : PowerSeries K} (ha : constantCoeff a = 0) (f : PowerSeries K) :
    PowerSeries.map φ (f.subst a) = (PowerSeries.map φ f).subst (PowerSeries.map φ a) := by
  erw [PowerSeries.map_subst (HasSubst.of_constantCoeff_zero ha)]
  try rfl

theorem lgS_map : PowerSeries.map φ (lgS g2 g3) = lgS (φ g2) (φ g3) := by
  refine lgS_unique (φ g2) (φ g3) _ ?_ ?_
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      lgS_const, map_zero]
  · rw [← uSer_map, ← map_subst_ps φ (lgS_const g2 g3), uSer_subst_lgS, map_X]

theorem ltLog_map (l : ℕ) : PowerSeries.map φ (ltLog K l) = ltLog L l := by
  ext n
  first | unfold Formalism.G.ltLog | unfold Formalism.L2.Th1.CM.ltLog
  rw [coeff_map, coeff_mk, coeff_mk]
  split_ifs <;> simp

theorem mult_map (b : K) :
    PowerSeries.map φ ((uSer g2 g3).subst (C b * lgS g2 g3))
      = (uSer (φ g2) (φ g3)).subst (C (φ b) * lgS (φ g2) (φ g3)) := by
  rw [map_subst_ps φ (constantCoeff_C_mul_weierstrassLog g2 g3 b), uSer_map, map_mul, map_C, lgS_map]

theorem lt_map (l : ℕ) (hl : 2 ≤ l) (ε : K) :
    PowerSeries.map φ ((uSer g2 g3).subst (C ε * ltLog K l))
      = (uSer (φ g2) (φ g3)).subst (C (φ ε) * ltLog L l) := by
  have h0 : constantCoeff (C ε * ltLog K l) = 0 := by
    rw [map_mul, constantCoeff_C, ltLog_const l hl, mul_zero]
  rw [map_subst_ps φ h0, uSer_map, map_mul, map_C, ltLog_map]

end Map

theorem omegaK_quad (d : ℕ) (hd : d % 4 = 3) :
    omegaK d ^ 2 - omegaK d + (((d + 1) / 4 : ℕ) : ℂ) = 0 := by
  unfold omegaK
  have h4 : (((d + 1) / 4 : ℕ) : ℂ) = ((d : ℂ) + 1) / 4 := by
    have h : 4 ∣ d + 1 := by omega
    rw [Nat.cast_div h (by norm_num)]
    push_cast
    ring
  have hs : ((Real.sqrt (d : ℝ) : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    norm_cast
  rw [h4]
  linear_combination (((Real.sqrt (d : ℝ) : ℝ) : ℂ) ^ 2 / 4) * Complex.I_sq - (1 / 4 : ℂ) * hs

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgHonG
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

def triSol {K : Type} [Field K] (a : ℕ → ℕ → K) (b : ℕ → K) : ℕ → K
  | m => (b m - ∑ i : Fin m, triSol a b i.1 * a i.1 m) / a m m

theorem triSol_eq {K : Type} [Field K] (a : ℕ → ℕ → K) (b : ℕ → K) (ha : ∀ m, a m m ≠ 0)
    (m : ℕ) : ∑ i ∈ Finset.range (m + 1), triSol a b i * a i m = b m := by
  have h : triSol a b m = (b m - ∑ i : Fin m, triSol a b i.1 * a i.1 m) / a m m := by
    rw [triSol]
  rw [Finset.sum_range_succ, Finset.sum_range, h, div_mul_cancel₀ _ (ha m)]
  ring

theorem triSol_norm (a : ℕ → ℕ → K) (b : ℕ → K) (ha1 : ∀ i m, ‖a i m‖ ≤ 1)
    (ha : ∀ m, ‖a m m‖ = 1) (r : ℝ) (hb : ∀ m, ‖b m‖ ≤ r) (m : ℕ) : ‖triSol a b m‖ ≤ r := by
  have hr : 0 ≤ r := (norm_nonneg _).trans (hb 0)
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [triSol, norm_div, ha, div_one, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hb m) ?_)
    rw [norm_neg]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr fun i _ => ?_
    rw [norm_mul]
    calc ‖triSol a b i.1‖ * ‖a i.1 m‖ ≤ r * 1 :=
          mul_le_mul (ih i.1 i.2) (ha1 _ _) (norm_nonneg _) hr
      _ = r := mul_one r

theorem norm_pow_apply_of_isometric (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (i : ℕ) (x : K) :
    ‖(τ ^ i) x‖ = ‖x‖ := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, hτ, ih]

def triIter {K : Type} [Field K] (a : ℕ → ℕ → K) (π : K) : ℕ → ℕ → K
  | 0 => triSol a (fun m => if m = 0 then a 0 0 else 0)
  | k + 1 => triSol a (fun m => if m = 0 then 0 else π * triIter a π k (m + 1))

theorem triIter_norm (a : ℕ → ℕ → K) (π : K) (ha1 : ∀ i m, ‖a i m‖ ≤ 1)
    (ha : ∀ m, ‖a m m‖ = 1) (k m : ℕ) : ‖triIter a π k m‖ ≤ ‖π‖ ^ k := by
  induction k generalizing m with
  | zero =>
    rw [triIter, pow_zero]
    refine triSol_norm a _ ha1 ha 1 (fun j => ?_) m
    split_ifs
    · exact ha1 0 0
    · simp
  | succ k ih =>
    rw [triIter]
    refine triSol_norm a _ ha1 ha _ (fun j => ?_) m
    split_ifs
    · simp
    · rw [norm_mul, pow_succ']
      exact mul_le_mul_of_nonneg_left (ih _) (norm_nonneg _)

theorem twisted_division (τ : K →+* K) (hτ : ∀ x, ‖τ x‖ = ‖x‖) (π : K) (hπ : ‖π‖ < 1)
    (c : ℕ → K) (hc0 : ‖c 0‖ = 1) (hc : ∀ i, ‖c i‖ ≤ 1) :
    ∃ t : ℕ → K, t 0 = 1 ∧ (∀ n, ‖t n‖ ≤ 1) ∧
      ∀ n, 2 ≤ n → π * t n = ∑ i ∈ Finset.range n, t i * (τ ^ i) (c (n - 1 - i)) := by
  set a : ℕ → ℕ → K := fun i m => (τ ^ i) (c (m - i)) with ha_def
  have ha1 : ∀ i m, ‖a i m‖ ≤ 1 := fun i m => by
    rw [ha_def]; simp only; rw [norm_pow_apply_of_isometric τ hτ]; exact hc _
  have ha : ∀ m, ‖a m m‖ = 1 := fun m => by
    rw [ha_def]; simp only; rw [norm_pow_apply_of_isometric τ hτ, Nat.sub_self]; exact hc0
  have ha0 : ∀ m, a m m ≠ 0 := fun m h => by
    have := ha m; rw [h, norm_zero] at this; exact zero_ne_one this
  have hsum : ∀ m, Summable fun k => triIter a π k m := fun m =>
    Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg π) hπ)
      (fun k => triIter_norm a π ha1 ha k m)
  have hz0 : triIter a π 0 0 = 1 := by
    have h := triSol_eq a (fun m => if m = 0 then a 0 0 else 0) ha0 0
    simp only [zero_add, Finset.sum_range_one, if_true] at h
    rw [triIter]
    exact mul_right_cancel₀ (ha0 0) (h.trans (one_mul _).symm)
  have hzs : ∀ k, triIter a π (k + 1) 0 = 0 := fun k => by
    have h := triSol_eq a (fun m => if m = 0 then 0 else π * triIter a π k (m + 1)) ha0 0
    simp only [zero_add, Finset.sum_range_one, if_true] at h
    rw [triIter]
    exact (mul_eq_zero.mp h).resolve_right (ha0 0)
  refine ⟨fun m => ∑' k, triIter a π k m, ?_, fun n => ?_, fun n hn => ?_⟩
  · simp only
    rw [(hsum 0).tsum_eq_zero_add, hz0]
    simp [hzs]
  · refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg zero_le_one fun k => ?_
    exact (triIter_norm a π ha1 ha k n).trans (pow_le_one₀ (norm_nonneg _) hπ.le)
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hterm : ∀ i, (∑' k, triIter a π k i) * (τ ^ i) (c (m + 2 - 1 - i))
        = ∑' k, triIter a π k i * a i (m + 1) := fun i => by
      rw [tsum_mul_right]
      rfl
    simp only [hterm]
    rw [← Summable.tsum_finsetSum (fun i _ => (hsum i).mul_right _)]
    have hS : Summable fun k => ∑ i ∈ Finset.range (m + 2), triIter a π k i * a i (m + 1) :=
      summable_sum fun i _ => (hsum i).mul_right _
    rw [hS.tsum_eq_zero_add, ← tsum_mul_left]
    have h0 : ∑ i ∈ Finset.range (m + 2), triIter a π 0 i * a i (m + 1) = 0 := by
      have h := triSol_eq a (fun m => if m = 0 then a 0 0 else 0) ha0 (m + 1)
      simpa [triIter] using h
    rw [h0, zero_add]
    refine tsum_congr fun k => ?_
    have h := triSol_eq a (fun m => if m = 0 then 0 else π * triIter a π k (m + 1)) ha0 (m + 1)
    simpa [triIter] using h.symm

end ReciprocityTheory.ChartRestriction.L1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGmQ
section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem prodSer_coeffIn {m : ℕ} (hm : 0 < m) : CoeffIn (Rm m) (prodSer m) := by
  unfold prodSer
  refine Finset.prod_induction _ (CoeffIn (Rm m)) (fun a b ha hb => ha.mul hb) ?_
    (fun t ht => facSer_coeffIn hm ht)
  intro n
  rw [PowerSeries.coeff_one]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem prodSer_conv {m : ℕ} (hm : 0 < m) : Conv (prodSer m) := by
  unfold prodSer
  refine Finset.prod_induction _ Conv (fun a b ha hb => ha.mul hb) ?_
    (fun t ht => facSer_conv hm ht)
  intro x _
  refine (hasSum_single 0 fun n hn => ?_).summable
  simp [PowerSeries.coeff_one, hn]

theorem prodSer_ev {m : ℕ} (hm : 0 < m) (τ : ℍ) : ev (prodSer m) (qm m τ) = Gm m τ := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hx : ‖qm m τ‖ < 1 := by
    unfold qm
    rw [Complex.norm_exp]
    have e : (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) / (m : ℂ)).re = -(2 * Real.pi * τ.im) / m := by
      rw [Complex.div_natCast_re]
      simp
    rw [e, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (div_neg_of_neg_of_pos (by nlinarith [Real.pi_pos, τ.im_pos]) hm')
  have h1 : Conv (1 : PowerSeries ℂ) := by
    intro x _
    refine (hasSum_single 0 fun n hn => ?_).summable
    simp [PowerSeries.coeff_one, hn]
  have key : ∀ s ⊆ Tm m, Conv (∏ t ∈ s, facSer m t) ∧
      ev (∏ t ∈ s, facSer m t) (qm m τ) = ∏ t ∈ s, fac t τ := by
    intro s
    classical
    refine Finset.induction_on s ?_ ?_
    · intro _
      refine ⟨by simpa using h1, ?_⟩
      simp only [Finset.prod_empty]
      unfold ev
      rw [tsum_eq_single 0 fun n hn => by simp [PowerSeries.coeff_one, hn]]
      simp
    · intro a s ha ih hs
      have has : a ∈ Tm m := hs (Finset.mem_insert_self a s)
      obtain ⟨c1, c2⟩ := ih fun y hy => hs (Finset.mem_insert_of_mem hy)
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      exact ⟨(facSer_conv hm has).mul c1, by
        rw [ev_mul (facSer_conv hm has) c1 hx, facSer_ev hm has, c2]⟩
  unfold prodSer Gm
  exact (key _ subset_rfl).2

theorem prodSer_low {m : ℕ} (hm : 0 < m) (hsq : ¬ IsSquare m) : ∃ n0 u, LowUnit (Rm m) (prodSer m) n0 u := by
  unfold prodSer
  refine LowUnit.prod _ _ fun t ht => facSer_low hm ht ?_
  intro heq
  apply hsq
  unfold Tm at ht
  rw [Finset.mem_image] at ht
  obtain ⟨x, hx, rfl⟩ := ht
  rw [Finset.mem_sigma, Nat.mem_divisors] at hx
  dsimp only at heq
  refine ⟨x.1, ?_⟩
  have h2 := Nat.div_mul_cancel hx.1.1
  rw [← heq] at h2
  exact h2.symm

theorem gmQ_xp {m : ℕ} (hm : 0 < m) : xp m (qExpansion 1 (Gm m)) = prodSer m := by
  have hm0 : m ≠ 0 := hm.ne'
  have hF := gmForm hm
  refine eq_of_ev_eq (hF.conv.xp hm0) (prodSer_conv hm) ?_
  intro x hx0 hx1
  rw [ev_xp _ hm0]
  have hxne : x ≠ 0 := norm_pos_iff.mp hx0
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm0
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog : Real.log ‖x‖ < 0 := Real.log_neg hx0 hx1

  let w : ℂ := ⟨(m : ℝ) * Complex.arg x / (2 * Real.pi), -((m : ℝ) * Real.log ‖x‖) / (2 * Real.pi)⟩
  have him : 0 < w.im := by
    show 0 < -((m : ℝ) * Real.log ‖x‖) / (2 * Real.pi)
    apply div_pos _ (by positivity)
    nlinarith
  let τ : ℍ := ⟨w, him⟩
  have hτ : (τ : ℂ) = w := rfl
  have hlogx : 2 * (Real.pi : ℂ) * Complex.I * w / (m : ℂ) = Complex.log x := by
    apply Complex.ext
    · rw [Complex.div_natCast_re, Complex.log_re]
      simp [w]
      field_simp
    · rw [Complex.div_natCast_im, Complex.log_im]
      simp [w]
      field_simp
  have hq : qm m τ = x := by
    unfold qm
    rw [hτ, hlogx, Complex.exp_log hxne]
  have hq1 : qm 1 τ = x ^ m := by
    rw [← hq]
    unfold qm
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  rw [← hq1, hF.ev_eq τ, ← prodSer_ev hm τ, hq]

theorem gmQ_coeffIn {m : ℕ} (hm : 0 < m) : CoeffIn (Rm m) (qExpansion 1 (Gm m)) := by
  intro n
  have h := congrArg (PowerSeries.coeff (m * n)) (gmQ_xp hm)
  simp only [xp, PowerSeries.coeff_mk, dvd_mul_right, if_true, Nat.mul_div_cancel_left n hm] at h
  rw [h]
  exact prodSer_coeffIn hm (m * n)

theorem gmQ_low {m : ℕ} (hm : 0 < m) (hsq : ¬ IsSquare m) :
    ∃ n0 u, LowUnit (Rm m) (qExpansion 1 (Gm m)) n0 u := by
  obtain ⟨n0, u, hu1, hu2, hu3, hlow, hn0⟩ := prodSer_low hm hsq
  have hc : ∀ n, PowerSeries.coeff n (prodSer m) =
      if m ∣ n then PowerSeries.coeff (n / m) (qExpansion 1 (Gm m)) else 0 := by
    intro n
    rw [← gmQ_xp hm]
    simp [xp]
  have hdvd : m ∣ n0 := by
    by_contra h
    rw [hc, if_neg h] at hn0
    exact hu3 hn0.symm
  obtain ⟨k, rfl⟩ := hdvd
  refine ⟨k, u, hu1, hu2, hu3, fun j hj => ?_, ?_⟩
  · have h2 := hlow (m * j) (by nlinarith)
    rw [hc, if_pos (dvd_mul_right m j), Nat.mul_div_cancel_left j hm] at h2
    exact h2
  · rw [hc, if_pos (dvd_mul_right m k), Nat.mul_div_cancel_left k hm] at hn0
    exact hn0

end ReciprocityTheory.ChartRestriction.L1
end
end

