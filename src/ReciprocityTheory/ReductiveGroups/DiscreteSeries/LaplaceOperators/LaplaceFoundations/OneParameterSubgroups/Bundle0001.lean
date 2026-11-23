module

public import Mathlib

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.OneParameterSubgroups.ExistsCyclic
section
open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.N

def formV {m : ℕ} (u v : Fin m → ℝ) : ℝ := ∑ s : Fin m, (-1) ^ (s.val + 1) * u s * v s

theorem formV_symm {m : ℕ} (u v : Fin m → ℝ) : formV u v = formV v u := by
  unfold formV
  exact Finset.sum_congr rfl fun s _ => by ring

theorem sign_prod {m : ℕ} (x : Fin m → ℝ) (hx : StrictAnti x) (s : Fin m) :
    0 < (-1) ^ s.val * ∏ j ∈ univ.erase s, (x s - x j) := by
  classical
  have habs : ∀ j ∈ univ.erase s, |x s - x j| = (if j < s then -1 else 1) * (x s - x j) := by
    intro j hj
    have hjs : j ≠ s := Finset.ne_of_mem_erase hj
    split_ifs with h
    · have h1 : x s < x j := hx h
      rw [abs_of_neg (by linarith)]
      ring
    · have h2 : s < j := lt_of_le_of_ne (not_lt.1 h) (Ne.symm hjs)
      have h1 : x j < x s := hx h2
      rw [abs_of_pos (by linarith)]
      ring
  have hc : ((univ.erase s).filter (fun j => j < s)).card = s.val := by
    have he : (univ.erase s).filter (fun j => j < s) = Finset.Iio s := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_Iio]
      exact ⟨fun h => h.2, fun h => ⟨ne_of_lt h, h⟩⟩
    rw [he, Fin.card_Iio]
  have hprod : ∏ j ∈ univ.erase s, |x s - x j| = (-1) ^ s.val * ∏ j ∈ univ.erase s, (x s - x j) := by
    rw [Finset.prod_congr rfl habs, Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const,
      Finset.prod_const, one_pow, mul_one, hc]
  rw [← hprod]
  exact Finset.prod_pos fun j hj =>
    abs_pos.2 (sub_ne_zero.2 (hx.injective.ne (Finset.ne_of_mem_erase hj).symm))

private theorem sum_pow_mul_inv_prod_sub_eq_ite {m : ℕ} (x : Fin m → ℝ) (hx : Function.Injective x) (k : ℕ)
    (hk : k < m) :
    ∑ s : Fin m, x s ^ k * (∏ j ∈ univ.erase s, (x s - x j))⁻¹ = if k + 1 = m then 1 else 0 := by
  classical
  have hinj : Set.InjOn x ((univ : Finset (Fin m)) : Set (Fin m)) := fun a _ b _ h => hx h
  have hdeg : (Polynomial.X ^ k : Polynomial ℝ).degree < ((univ : Finset (Fin m)).card : WithBot ℕ) := by
    rw [card_univ, Fintype.card_fin, Polynomial.degree_X_pow]
    exact_mod_cast hk
  have hI := Lagrange.eq_interpolate hinj hdeg
  have hc := congrArg (fun p : Polynomial ℝ => p.coeff (m - 1)) hI
  try simp only at hc
  rw [Lagrange.interpolate_apply, Polynomial.finsetSum_coeff] at hc
  have hb : ∀ s : Fin m, (Lagrange.basis univ x s).coeff (m - 1) =
      (∏ j ∈ univ.erase s, (x s - x j))⁻¹ := by
    intro s
    simp only [Lagrange.basis, Lagrange.basisDivisor]
    rw [Finset.prod_mul_distrib, ← map_prod, Polynomial.coeff_C_mul]
    have hmon : (∏ j ∈ univ.erase s, (Polynomial.X - Polynomial.C (x j))).Monic :=
      Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C _
    have hnd : (∏ j ∈ univ.erase s, (Polynomial.X - Polynomial.C (x j))).natDegree = m - 1 := by
      rw [Polynomial.natDegree_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C _]
      simp [Polynomial.natDegree_X_sub_C, card_erase_of_mem]
    rw [← hnd, hmon.coeff_natDegree, mul_one, prod_inv_distrib]
  simp only [Polynomial.coeff_C_mul, hb, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.coeff_X_pow] at hc
  have e : (m - 1 = k) ↔ (k + 1 = m) := by omega
  simp only [e] at hc
  exact hc.symm

theorem exists_cyclic (r : ℕ) (x : Fin (2 * r + 1) → ℝ) (hx : StrictAnti x) :
    ∃ c : Fin (2 * r + 1) → ℝ, (∀ s, c s ≠ 0) ∧ ∀ i j : ℕ, i + j ≤ 2 * r →
      formV (fun s => x s ^ i * c s) (fun s => x s ^ j * c s) = if i + j = 2 * r then -1 else 0 := by
  classical
  have hP : ∀ s, 0 < (-1) ^ s.val * ∏ j ∈ univ.erase s, (x s - x j) := fun s => sign_prod x hx s
  have hPne : ∀ s, ∏ j ∈ univ.erase s, (x s - x j) ≠ 0 := fun s h => by
    have h1 := hP s
    rw [h, mul_zero] at h1
    exact lt_irrefl _ h1
  have hq : ∀ s, 0 < (-1) ^ s.val / ∏ j ∈ univ.erase s, (x s - x j) := fun s => by
    have h1 : (-1 : ℝ) ^ s.val / ∏ j ∈ univ.erase s, (x s - x j) =
        ((-1) ^ s.val * ∏ j ∈ univ.erase s, (x s - x j)) / (∏ j ∈ univ.erase s, (x s - x j)) ^ 2 := by
      have := hPne s
      first
      | (field_simp; done)
      | (field_simp; ring)
    rw [h1]
    exact div_pos (hP s) (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (hPne s))))
  refine ⟨fun s => Real.sqrt ((-1) ^ s.val / ∏ j ∈ univ.erase s, (x s - x j)),
    fun s => (Real.sqrt_pos.2 (hq s)).ne', fun i j hij => ?_⟩
  have hterm : ∀ s : Fin (2 * r + 1),
      (-1 : ℝ) ^ (s.val + 1) * (x s ^ i * Real.sqrt ((-1) ^ s.val / ∏ j ∈ univ.erase s, (x s - x j))) *
        (x s ^ j * Real.sqrt ((-1) ^ s.val / ∏ j ∈ univ.erase s, (x s - x j))) =
      -(x s ^ (i + j) * (∏ j ∈ univ.erase s, (x s - x j))⁻¹) := by
    intro s
    have hs := Real.mul_self_sqrt (hq s).le
    have hne := hPne s
    rcases Nat.even_or_odd s.val with he | ho
    · rw [he.neg_one_pow] at hs
      rw [he.neg_one_pow, (he.add_one).neg_one_pow, pow_add]
      linear_combination (-(x s ^ i * x s ^ j)) * hs
    · rw [ho.neg_one_pow] at hs
      rw [ho.neg_one_pow, (ho.add_one).neg_one_pow, pow_add]
      linear_combination (x s ^ i * x s ^ j) * hs
  simp only [formV]
  rw [Finset.sum_congr rfl fun s _ => hterm s, Finset.sum_neg_distrib,
    sum_pow_mul_inv_prod_sub_eq_ite x hx.injective (i + j) (by omega)]
  by_cases h : i + j = 2 * r
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega), neg_zero]

theorem exists_dual {m : ℕ} (x c : Fin m → ℝ) (hx : Function.Injective x) (hc : ∀ s, c s ≠ 0)
    (y : Fin m → ℝ) : ∃ v : Fin m → ℝ, ∀ i : Fin m, formV v (fun s => x s ^ i.val * c s) = y i := by
  classical
  have hW : IsUnit (Matrix.vandermonde x)ᵀ.det := by
    rw [Matrix.det_transpose]
    exact (Matrix.det_vandermonde_ne_zero_iff.2 hx).isUnit
  refine ⟨fun s => ((Matrix.vandermonde x)ᵀ⁻¹ *ᵥ y) s / ((-1) ^ (s.val + 1) * c s), fun i => ?_⟩
  have hw : (Matrix.vandermonde x)ᵀ *ᵥ ((Matrix.vandermonde x)ᵀ⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hW, Matrix.one_mulVec]
  conv_rhs => rw [← hw]
  simp only [formV, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.vandermonde_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  have h1 : ((-1 : ℝ) ^ (s.val + 1) * c s) ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) (hc s)
  have h2 := hc s
  first
  | (field_simp; done)
  | (field_simp; ring)

theorem formV_sub_sum {m r : ℕ} (u w : Fin m → ℝ) (k : Fin r → ℝ) (g : Fin r → Fin m → ℝ) :
    formV (fun s => u s - ∑ b, k b * g b s) w = formV u w - ∑ b, k b * formV (g b) w := by
  simp only [formV, mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun s _ => by ring

theorem frame (r : ℕ) (x : Fin (2 * r + 1) → ℝ) (hx : StrictAnti x) :
    ∃ (e f : Fin r → Fin (2 * r + 1) → ℝ) (z : Fin (2 * r + 1) → ℝ),
      (∀ a b, formV (e a) (e b) = 0) ∧ (∀ a b, formV (f a) (f b) = 0) ∧
      (∀ a b, formV (f a) (e b) = if a = b then 1 else 0) ∧
      (∀ a, formV (e a) z = 0) ∧ (∀ a, formV (f a) z = 0) ∧ formV z z = -1 ∧
      (∀ a s, x s * e a s = if h : a.val + 1 < r then e ⟨a.val + 1, h⟩ s else z s) := by
  classical
  obtain ⟨c, hc0, hc⟩ := exists_cyclic r x hx
  let g : ℕ → Fin (2 * r + 1) → ℝ := fun i s => x s ^ i * c s
  have hG : ∀ i j : ℕ, i + j ≤ 2 * r →
      formV (g i) (g j) = if i + j = 2 * r then -1 else 0 := hc
  have hdual : ∀ a : Fin r, ∃ v : Fin (2 * r + 1) → ℝ, ∀ i : Fin (2 * r + 1),
      formV v (g i.val) = if i.val = a.val then 1 else 0 := fun a =>
    exists_dual x c hx.injective hc0 _
  choose f' hf' using hdual
  let e : Fin r → Fin (2 * r + 1) → ℝ := fun a => g a.val
  let z : Fin (2 * r + 1) → ℝ := g r
  let Q : Fin r → Fin r → ℝ := fun a b => formV (f' a) (f' b)
  let f : Fin r → Fin (2 * r + 1) → ℝ := fun a s => f' a s - ∑ b, (1 / 2 * Q a b) * e b s
  have hee : ∀ a b : Fin r, formV (e a) (e b) = 0 := by
    intro a b
    have := a.isLt
    have := b.isLt
    change formV (g a.val) (g b.val) = 0
    rw [hG _ _ (by omega), if_neg (by omega)]
  have hez : ∀ a : Fin r, formV (e a) z = 0 := by
    intro a
    have := a.isLt
    change formV (g a.val) (g r) = 0
    rw [hG _ _ (by omega), if_neg (by omega)]
  have hzz : formV z z = -1 := by
    change formV (g r) (g r) = -1
    rw [hG _ _ (by omega), if_pos (by omega)]
  have hf'e : ∀ a b : Fin r, formV (f' a) (e b) = if a = b then 1 else 0 := by
    intro a b
    have h := hf' a ⟨b.val, by omega⟩
    change formV (f' a) (g b.val) = _
    rw [show formV (f' a) (g b.val) = if b.val = a.val then 1 else 0 from h]
    by_cases hab : a = b
    · subst hab
      simp
    · rw [if_neg (fun h' => hab (Fin.ext h'.symm)), if_neg hab]
  have hf'z : ∀ a : Fin r, formV (f' a) z = 0 := by
    intro a
    have := a.isLt
    have h := hf' a ⟨r, by omega⟩
    change formV (f' a) (g r) = 0
    rw [show formV (f' a) (g r) = if r = a.val then 1 else 0 from h, if_neg (by omega)]
  have hfe : ∀ a b : Fin r, formV (f a) (e b) = if a = b then 1 else 0 := by
    intro a b
    have h1 : formV (f a) (e b) = formV (f' a) (e b) - ∑ c, (1 / 2 * Q a c) * formV (e c) (e b) :=
      formV_sub_sum _ _ _ _
    rw [h1, hf'e]
    simp [hee]
  have hfz : ∀ a : Fin r, formV (f a) z = 0 := by
    intro a
    have h1 : formV (f a) z = formV (f' a) z - ∑ c, (1 / 2 * Q a c) * formV (e c) z :=
      formV_sub_sum _ _ _ _
    rw [h1, hf'z]
    simp [hez]
  have hff : ∀ a b : Fin r, formV (f a) (f b) = 0 := by
    intro a b
    have h1 : formV (f a) (f b) = formV (f' a) (f b) - ∑ c, (1 / 2 * Q a c) * formV (e c) (f b) :=
      formV_sub_sum _ _ _ _
    have h2 : formV (f' a) (f b) = Q b a - ∑ d, (1 / 2 * Q b d) * formV (e d) (f' a) := by
      rw [formV_symm]
      exact formV_sub_sum _ _ _ _
    have h3 : ∀ c, formV (e c) (f b) = if b = c then 1 else 0 := fun c => by
      rw [formV_symm, hfe]
    have h4 : ∀ d, formV (e d) (f' a) = if a = d then 1 else 0 := fun d => by
      rw [formV_symm, hf'e]
    rw [h1, h2]
    simp only [h3, h4, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hQ : Q b a = Q a b := formV_symm _ _
    rw [hQ]
    ring
  refine ⟨e, f, z, hee, hff, hfe, hez, hfz, hzz, fun a s => ?_⟩
  change x s * (x s ^ a.val * c s) = if h : a.val + 1 < r then g (a.val + 1) s else g r s
  split_ifs with h
  · ring
  · have hr : a.val + 1 = r := by omega
    have hp : x s ^ r = x s ^ (a.val + 1) := by rw [hr]
    change x s * (x s ^ a.val * c s) = x s ^ r * c s
    rw [hp]
    ring

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.OneParameterSubgroups.OneParam
section
open MeasureTheory Complex Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.N

theorem ode_bound (U U' : ℝ → ℂ) (a b : ℂ) (ha : a.re = 0) {δ : ℝ} (hU0 : U 0 = 1)
    (hder : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt U (U' s) s)
    (hb : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖U' s - (a + s * b) * U s‖ ≤ δ) :
    ‖U 1 * cexp (-a) - cexp (b / 2)‖ ≤ δ * Real.exp ‖b‖ := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (hb 0 ⟨le_rfl, zero_le_one⟩)
  have hofs : ∀ t : ℝ, HasDerivAt (fun y : ℝ => (y : ℂ)) 1 t := fun t => (hasDerivAt_id t).ofReal_comp
  set g : ℝ → ℂ := fun t => -(a * (t : ℂ)) - (t : ℂ) ^ 2 * b / 2 with hg_def
  have hg : ∀ t : ℝ, HasDerivAt g (-(a + (t : ℂ) * b)) t := by
    intro t
    have h3 := ((hofs t).const_mul a).neg.sub (((hofs t).pow 2).mul_const b |>.div_const 2)
    exact h3.congr_deriv (by first | ring | (norm_num; ring) | norm_num | (simp; ring) | simp)
  set W : ℝ → ℂ := fun t => U t * cexp (g t) with hW
  have hWd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt W ((U' t - (a + (t : ℂ) * b) * U t) * cexp (g t)) t := by
    intro t ht
    have := (hder t ht).mul (hg t).cexp
    exact this.congr_deriv (by ring)
  have hgre : ∀ t ∈ Set.Icc (0 : ℝ) 1, (g t).re ≤ ‖b‖ / 2 := by
    intro t ht
    have hre : (g t).re = -(t ^ 2 * b.re / 2) := by
      simp only [hg_def]
      simp [Complex.mul_re, ha]
      rw [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hre]
    have hb1 : -b.re ≤ ‖b‖ := (neg_le_abs b.re).trans (Complex.abs_re_le_norm b)
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    nlinarith [mul_le_mul_of_nonneg_left hb1 (sq_nonneg t), norm_nonneg b]
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := W)
    (C := δ * Real.exp (‖b‖ / 2)) (fun t ht => (hWd t ht).hasDerivWithinAt)
    (fun t ht => by
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self ht
      rw [norm_mul, Complex.norm_exp]
      exact mul_le_mul (hb t ht') (Real.exp_le_exp.mpr (hgre t ht')) (Real.exp_pos _).le hδ)
    1 ⟨zero_le_one, le_rfl⟩
  have hW0 : W 0 = 1 := by simp [hW, hg_def, hU0]
  have hg1 : g 1 + b / 2 = -a := by simp only [hg_def]; push_cast; ring
  have hid : U 1 * cexp (-a) - cexp (b / 2) = (W 1 - W 0) * cexp (b / 2) := by
    rw [hW0, ← hg1]
    simp only [hW, Complex.exp_add]
    ring
  have hre2 : (b / 2).re ≤ ‖b‖ / 2 := by
    have : (b / 2).re = b.re / 2 := by simp
    rw [this]
    linarith [Complex.re_le_norm b]
  rw [hid, norm_mul, Complex.norm_exp]
  calc ‖W 1 - W 0‖ * Real.exp (b / 2).re
      ≤ (δ * Real.exp (‖b‖ / 2) * (1 - 0)) * Real.exp (‖b‖ / 2) :=
        mul_le_mul hmvt (Real.exp_le_exp.mpr hre2) (Real.exp_pos _).le
          (mul_nonneg (mul_nonneg hδ (Real.exp_pos _).le) (by norm_num))
    _ = δ * Real.exp ‖b‖ := by rw [sub_zero, mul_one, mul_assoc, ← Real.exp_add, add_halves]

theorem one_param {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (w : H) (hw : ‖w‖ = 1) (φ : V →ₗ[ℂ] H) (d : V →ₗ[ℂ] ℂ) (st : V → V)
    {C Cd Cs K T : ℝ} (hC : 0 ≤ C) (hCd : 0 ≤ Cd) (hCs : 0 ≤ Cs) (hK : 0 ≤ K) (hT : 1 ≤ T)
    (hd : ∀ X, ‖d X‖ ≤ Cd * ‖X‖) (hst : ∀ X, ‖st X‖ ≤ Cs * ‖X‖)
    (hstadd : ∀ X X', st (X + X') = st X + st X') (hdst : ∀ X, d (st X) = starRingEnd ℂ (d X))
    (Yl Yp Ym ρ1 : V) (ρ : ℝ → V) (him : (d Yl).re = 0)
    (hρ : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖ρ τ - Ym - (τ : ℂ) • ρ1‖ ≤ K * τ ^ 2)
    (ha : ‖φ Yp‖ ≤ C) (ha' : ‖φ (st Ym)‖ ≤ C) (hc : ‖φ Yl - ((T : ℂ) * d Yl) • w‖ ≤ C)
    (hall : ∀ X, ‖φ X - ((T : ℂ) * d X) • w‖ ≤ C * Real.sqrt T * ‖X‖)
    (u : ℝ → H →L[ℂ] H) (hu : ∀ s v, ‖u s v‖ = ‖v‖) (hu0 : u 0 w = w)
    (hder : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun s => ⟪w, u s w⟫_ℂ)
      ⟪w, u s (φ ((((Real.sqrt T)⁻¹ : ℝ) : ℂ) • (Yl + Yp + Ym)))⟫_ℂ s)
    (hmove : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ⟪w, u s (φ Ym)⟫_ℂ = ⟪φ (st (ρ (s / Real.sqrt T))), u s w⟫_ℂ) :
    ‖⟪w, u 1 w⟫_ℂ * cexp (-((Real.sqrt T : ℂ) * d Yl)) - cexp (d ρ1 / 2)‖ ≤
      (3 * C + C * Cs * ‖ρ1‖ + Cd * K + C * Cs * K) / Real.sqrt T * Real.exp ‖d ρ1‖ := by
  have hsT : 1 ≤ Real.sqrt T := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hT
  have hsT0 : 0 < Real.sqrt T := by linarith
  have hTs : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt (by linarith)
  have hw2 : ⟪w, w⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw]; simp
  have hin : ∀ s (v : H), ‖⟪w, u s v⟫_ℂ‖ ≤ ‖v‖ := fun s v =>
    (norm_inner_le_norm _ _).trans (by rw [hu, hw, one_mul])
  have hin' : ∀ s (v : H), ‖⟪v, u s w⟫_ℂ‖ ≤ ‖v‖ := fun s v =>
    (norm_inner_le_norm _ _).trans (by rw [hu, hw, mul_one])
  have hU1 : ∀ s, ‖⟪w, u s w⟫_ℂ‖ ≤ 1 := fun s => (hin s w).trans hw.le
  refine ode_bound (δ := (3 * C + C * Cs * ‖ρ1‖ + Cd * K + C * Cs * K) / Real.sqrt T)
    (fun s => ⟪w, u s w⟫_ℂ)
    (fun s => ⟪w, u s (φ ((((Real.sqrt T)⁻¹ : ℝ) : ℂ) • (Yl + Yp + Ym)))⟫_ℂ)
    ((Real.sqrt T : ℂ) * d Yl) (d ρ1) ?_ ?_ hder ?_
  · simp [him]
  · show ⟪w, u 0 w⟫_ℂ = 1
    rw [hu0, hw2]
  intro s hs
  have hm := hmove s hs
  obtain ⟨hs0, hs1⟩ := hs
  set c : ℝ := (Real.sqrt T)⁻¹ with hc_def
  have hc0 : 0 < c := inv_pos.mpr hsT0
  have hcs : c * Real.sqrt T = 1 := inv_mul_cancel₀ hsT0.ne'
  have hτ0 : 0 ≤ s / Real.sqrt T := div_nonneg hs0 hsT0.le
  have hτ1 : s / Real.sqrt T ≤ 1 := (div_le_one hsT0).mpr (hs1.trans hsT)
  have hτc : s / Real.sqrt T = s * c := by rw [hc_def, div_eq_mul_inv]
  set τ := s / Real.sqrt T with hτ
  have he₂ := hρ τ ⟨hτ0, hτ1⟩
  set e₂ := ρ τ - Ym - (τ : ℂ) • ρ1 with he₂_def
  set X := ρ τ - Ym with hX
  have hXe : X = (τ : ℂ) • ρ1 + e₂ := by rw [he₂_def]; abel
  have hstρ : st (ρ τ) = st Ym + st X := by rw [← hstadd, hX]; congr 1; abel
  have hdX : d X = (τ : ℂ) * d ρ1 + d e₂ := by rw [hXe, map_add (f := _), map_smul, smul_eq_mul]
  have e1 : φ Yl = ((T : ℂ) * d Yl) • w + (φ Yl - ((T : ℂ) * d Yl) • w) := by abel
  have e3 : φ (st X) = ((T : ℂ) * d (st X)) • w + (φ (st X) - ((T : ℂ) * d (st X)) • w) := by abel
  have he3 := hall (st X)
  set E1 := φ Yl - ((T : ℂ) * d Yl) • w with hE1
  set E3 := φ (st X) - ((T : ℂ) * d (st X)) • w with hE3
  have h1r : c * T = Real.sqrt T := by
    calc c * T = c * (Real.sqrt T * Real.sqrt T) := by rw [hTs]
      _ = (c * Real.sqrt T) * Real.sqrt T := by ring
      _ = Real.sqrt T := by rw [hcs, one_mul]
  have h2r : c * T * τ = s := by
    rw [h1r, hτc]
    calc Real.sqrt T * (s * c) = s * (c * Real.sqrt T) := by ring
      _ = s := by rw [hcs, mul_one]
  have h1 : (c : ℂ) * (T : ℂ) = (Real.sqrt T : ℂ) := by exact_mod_cast h1r
  have h2 : (c : ℂ) * (T : ℂ) * (τ : ℂ) = (s : ℂ) := by exact_mod_cast h2r
  have hmain : ⟪w, u s (φ ((c : ℂ) • (Yl + Yp + Ym)))⟫_ℂ
      - ((Real.sqrt T : ℂ) * d Yl + (s : ℂ) * d ρ1) * ⟪w, u s w⟫_ℂ
      = (c : ℂ) * ⟪w, u s E1⟫_ℂ + (c : ℂ) * ⟪w, u s (φ Yp)⟫_ℂ + (c : ℂ) * ⟪φ (st Ym), u s w⟫_ℂ
        + (c : ℂ) * T * d e₂ * ⟪w, u s w⟫_ℂ + (c : ℂ) * ⟪E3, u s w⟫_ℂ := by
    simp only [map_smul, map_add (f := _), inner_smul_right, inner_add_right]
    rw [hm, hstρ, map_add (f := _), inner_add_left, e1, e3]
    simp only [map_add (f := _), map_smul, inner_add_right, inner_smul_right, inner_add_left, inner_smul_left,
      hdst, map_mul, Complex.conj_ofReal, Complex.conj_conj, RCLike.conj_conj, hdX]
    linear_combination (d Yl * ⟪w, u s w⟫_ℂ) * h1 + (d ρ1 * ⟪w, u s w⟫_ℂ) * h2
  rw [hmain]
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hcn : ‖(c : ℂ)‖ = c := Complex.norm_of_nonneg hc0.le
  have b1 : ‖(c : ℂ) * ⟪w, u s E1⟫_ℂ‖ ≤ c * C := by
    rw [norm_mul, hcn]; exact mul_le_mul_of_nonneg_left ((hin s E1).trans hc) hc0.le
  have b2 : ‖(c : ℂ) * ⟪w, u s (φ Yp)⟫_ℂ‖ ≤ c * C := by
    rw [norm_mul, hcn]; exact mul_le_mul_of_nonneg_left ((hin s _).trans ha) hc0.le
  have b3 : ‖(c : ℂ) * ⟪φ (st Ym), u s w⟫_ℂ‖ ≤ c * C := by
    rw [norm_mul, hcn]; exact mul_le_mul_of_nonneg_left ((hin' s _).trans ha') hc0.le
  have hτs : τ = s * c := hτc
  have hTτ : T * τ ^ 2 ≤ 1 := by
    have e : T * τ ^ 2 = s ^ 2 := by
      rw [hτs, ← hTs]
      calc Real.sqrt T * Real.sqrt T * (s * c) ^ 2 = s ^ 2 * (c * Real.sqrt T) ^ 2 := by ring
        _ = s ^ 2 := by rw [hcs, one_pow, mul_one]
    rw [e]; nlinarith
  have hde2 : ‖d e₂‖ ≤ Cd * (K * τ ^ 2) := (hd e₂).trans (mul_le_mul_of_nonneg_left he₂ hCd)
  have b4 : ‖(c : ℂ) * T * d e₂ * ⟪w, u s w⟫_ℂ‖ ≤ c * (Cd * K) := by
    rw [norm_mul, norm_mul, norm_mul, hcn, Complex.norm_of_nonneg hT0]
    calc c * T * ‖d e₂‖ * ‖⟪w, u s w⟫_ℂ‖ ≤ c * T * (Cd * (K * τ ^ 2)) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hde2 (mul_nonneg hc0.le hT0)) (hU1 s)
            (norm_nonneg _) (mul_nonneg (mul_nonneg hc0.le hT0) (mul_nonneg hCd (mul_nonneg hK (sq_nonneg τ))))
      _ = c * (Cd * K) * (T * τ ^ 2) := by ring
      _ ≤ c * (Cd * K) * 1 := mul_le_mul_of_nonneg_left hTτ (mul_nonneg hc0.le (mul_nonneg hCd hK))
      _ = c * (Cd * K) := mul_one _
  have hXb : ‖X‖ ≤ τ * ‖ρ1‖ + K * τ ^ 2 := by
    rw [hXe]
    calc ‖(τ : ℂ) • ρ1 + e₂‖ ≤ ‖(τ : ℂ) • ρ1‖ + ‖e₂‖ := norm_add_le _ _
      _ ≤ τ * ‖ρ1‖ + K * τ ^ 2 := by
        rw [norm_smul, Complex.norm_of_nonneg hτ0]; linarith
  have hc1 : c ≤ 1 := by rw [hc_def]; exact inv_le_one_of_one_le₀ hsT
  have hτc' : τ ≤ c := by rw [hτs]; nlinarith
  have hτ2 : τ ^ 2 ≤ c := by nlinarith
  have b5 : ‖(c : ℂ) * ⟪E3, u s w⟫_ℂ‖ ≤ C * Cs * (c * ‖ρ1‖ + K * c) := by
    rw [norm_mul, hcn]
    calc c * ‖⟪E3, u s w⟫_ℂ‖ ≤ c * (C * Real.sqrt T * (Cs * (τ * ‖ρ1‖ + K * τ ^ 2))) := by
          apply mul_le_mul_of_nonneg_left _ hc0.le
          refine (hin' s E3).trans (he3.trans ?_)
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC hsT0.le)
          exact (hst X).trans (mul_le_mul_of_nonneg_left hXb hCs)
      _ = C * Cs * (τ * ‖ρ1‖ + K * τ ^ 2) * (c * Real.sqrt T) := by ring
      _ = C * Cs * (τ * ‖ρ1‖ + K * τ ^ 2) := by rw [hcs, mul_one]
      _ ≤ C * Cs * (c * ‖ρ1‖ + K * c) := by
          have q1 := mul_le_mul_of_nonneg_right hτc' (norm_nonneg ρ1)
          have q2 := mul_le_mul_of_nonneg_left hτ2 hK
          have q3 : τ * ‖ρ1‖ + K * τ ^ 2 ≤ c * ‖ρ1‖ + K * c := add_le_add q1 q2
          exact mul_le_mul_of_nonneg_left q3 (mul_nonneg hC hCs)
  have n4 := norm_add_le ((c : ℂ) * ⟪w, u s E1⟫_ℂ + (c : ℂ) * ⟪w, u s (φ Yp)⟫_ℂ
    + (c : ℂ) * ⟪φ (st Ym), u s w⟫_ℂ + (c : ℂ) * T * d e₂ * ⟪w, u s w⟫_ℂ) ((c : ℂ) * ⟪E3, u s w⟫_ℂ)
  have n3 := norm_add_le ((c : ℂ) * ⟪w, u s E1⟫_ℂ + (c : ℂ) * ⟪w, u s (φ Yp)⟫_ℂ
    + (c : ℂ) * ⟪φ (st Ym), u s w⟫_ℂ) ((c : ℂ) * T * d e₂ * ⟪w, u s w⟫_ℂ)
  have n2 := norm_add_le ((c : ℂ) * ⟪w, u s E1⟫_ℂ + (c : ℂ) * ⟪w, u s (φ Yp)⟫_ℂ)
    ((c : ℂ) * ⟪φ (st Ym), u s w⟫_ℂ)
  have n1 := norm_add_le ((c : ℂ) * ⟪w, u s E1⟫_ℂ) ((c : ℂ) * ⟪w, u s (φ Yp)⟫_ℂ)
  have hR : c * C + c * C + c * C + c * (Cd * K) + C * Cs * (c * ‖ρ1‖ + K * c)
      = (3 * C + C * Cs * ‖ρ1‖ + Cd * K + C * Cs * K) * c := by ring
  rw [div_eq_mul_inv, ← hc_def]
  linarith [n1, n2, n3, n4, b1, b2, b3, b4, b5, hR]

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
end

