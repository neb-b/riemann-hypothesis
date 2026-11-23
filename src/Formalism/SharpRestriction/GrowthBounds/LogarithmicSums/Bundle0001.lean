module

public import Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.Conclusion1OfGainBoundAll
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Harmonic.Bounds

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.NumData
section
noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G Filter

namespace Formalism.MainNotions.AuxBlock8.Pf.G5.Nu

theorem ev_log (c α : ℝ) (hα : 0 < α) : ∀ᶠ x : ℝ in atTop, c * Real.log x ≤ x ^ α := by
  have h := (isLittleO_log_rpow_atTop hα).bound (show (0 : ℝ) < 1 / (|c| + 1) by positivity)
  filter_upwards [h, eventually_gt_atTop 0] with x hx hx0
  have hp := Real.rpow_pos_of_pos hx0 α
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hp] at hx
  have hc : c * Real.log x ≤ |c| * |Real.log x| := by
    rw [← abs_mul]; exact le_abs_self _
  have h1 : |c| * |Real.log x| ≤ |c| * (1 / (|c| + 1) * x ^ α) :=
    mul_le_mul_of_nonneg_left hx (abs_nonneg c)
  have h3 : |c| / (|c| + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have h2 : |c| * (1 / (|c| + 1) * x ^ α) = |c| / (|c| + 1) * x ^ α := by ring
  nlinarith [mul_le_mul_of_nonneg_right h3 hp.le]

theorem ev_pow (c α β : ℝ) (h : α < β) : ∀ᶠ x : ℝ in atTop, c * x ^ α ≤ x ^ β := by
  have ht := (tendsto_rpow_atTop (sub_pos.2 h)).eventually_ge_atTop |c|
  filter_upwards [ht, eventually_gt_atTop 0] with x hx hx0
  have hp := Real.rpow_pos_of_pos hx0 α
  have e : x ^ β = x ^ α * x ^ (β - α) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_right (le_abs_self c) hp.le, mul_le_mul_of_nonneg_left hx hp.le]

theorem k_le_x_pow_six {D : D7} (L : SizeData₂ D) (hS : Formalism.MainNotions.SizesAt L) : (D.R.k : ℝ) ≤ L.sc.x ^ (6 : ℝ) := by
  have hK := hS.2.2.1.2
  simp only [Formalism.MainNotions.szTh] at hK
  refine hK.trans (Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le ?_)
  have h1 := L.sc.eps_lt
  have h2 := L.sc.eps_pos
  linarith

theorem one_le_k (D : D7) : (1 : ℝ) ≤ (D.R.k : ℝ) := by
  have h := D.R.m_add_three_le_k
  exact_mod_cast (show 1 ≤ D.R.k by omega)

theorem xpow_le_exp (x N y : ℝ) (hx : 0 < x) (h : N * Real.log x ≤ y) : x ^ N ≤ Real.exp y := by
  rw [Real.rpow_def_of_pos hx]
  exact Real.exp_le_exp.mpr (by rw [mul_comm]; exact h)

theorem ev_const (c α : ℝ) (hα : 0 < α) : ∀ᶠ x : ℝ in atTop, c ≤ Real.exp (x ^ α) := by
  filter_upwards [(tendsto_rpow_atTop hα).eventually_ge_atTop c] with x hx
  linarith [Real.add_one_le_exp (x ^ α)]

def rE (eps : ℝ) : ℕ := ⌈8 * (2 + 8 * eps + 2) / eps⌉₊ + 1

theorem rG_rE (s : Scale) : rG s = rE s.eps := rfl

theorem first_bound_arith (C c η l X' xn Y b : ℝ) (hC0 : 0 ≤ C) (hc0 : 0 ≤ c) (hη0 : 0 ≤ η) (hl0 : 0 ≤ l) (hxn0 : 0 ≤ xn)
    (hC : C ≤ Y) (hc : c ≤ Y) (hη : η ≤ Y) (hl : l ≤ Y) (hxn : xn ≤ Y) (hX : 1 ≤ X') (hY : 10 ≤ Y)
    (hb : Y ^ 7 * X' ≤ b) : C * (c + η) * l * (X' * xn + 2) ≤ b := by
  have hY0 : 0 ≤ Y := by linarith
  have hX0 : 0 ≤ X' := by linarith
  have h1 : c + η ≤ 2 * Y := by linarith
  have h2 : X' * xn + 2 ≤ X' * (2 * Y) := by nlinarith
  have a1 : C * (c + η) ≤ Y * (2 * Y) := mul_le_mul hC h1 (by linarith) hY0
  have a2 : C * (c + η) * l ≤ Y * (2 * Y) * Y :=
    mul_le_mul a1 hl hl0 (mul_nonneg hY0 (by linarith))
  have a3 : C * (c + η) * l * (X' * xn + 2) ≤ Y * (2 * Y) * Y * (X' * (2 * Y)) :=
    mul_le_mul a2 h2 (by nlinarith [mul_nonneg hX0 hxn0]) (mul_nonneg (mul_nonneg hY0 (by linarith)) hY0)
  have h10 : (10 : ℝ) ^ 3 ≤ Y ^ 3 := pow_le_pow_left₀ (by norm_num) hY 3
  have h4 : 4 * Y ^ 4 ≤ Y ^ 7 := by
    have := mul_le_mul_of_nonneg_left (show (4 : ℝ) ≤ Y ^ 3 by norm_num at h10; linarith) (pow_nonneg hY0 4)
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h4 hX0]

theorem n1'_arith (C f Nm la X' xn Y b : ℝ) (hC0 : 0 ≤ C) (hf0 : 0 ≤ f) (hN0 : 0 ≤ Nm) (hl0 : 0 ≤ la) (hxn0 : 0 ≤ xn)
    (hC : C ≤ Y) (hf : f ≤ Y) (hN : Nm ≤ Y) (hl : la ≤ Y) (hxn : xn ≤ Y) (hX : 1 ≤ X') (hY : 10 ≤ Y)
    (hb : Y ^ 7 * X' ≤ b) : C * f * (Nm ^ 2 * la + la ^ 2 / Real.log 2) * (X' * xn + 2) ≤ b := by
  have hY0 : 0 ≤ Y := by linarith
  have hX0 : 0 ≤ X' := by linarith
  have hl2 := Real.log_two_gt_d9
  have hlpos : 0 < Real.log 2 := by linarith
  have m1 : Nm ^ 2 * la ≤ Y ^ 2 * Y := mul_le_mul (pow_le_pow_left₀ hN0 hN 2) hl hl0 (sq_nonneg _)
  have m2 : la ^ 2 / Real.log 2 ≤ 2 * Y ^ 2 := by
    rw [div_le_iff₀ hlpos]
    nlinarith [pow_le_pow_left₀ hl0 hl 2, sq_nonneg Y]
  have mid0 : 0 ≤ Nm ^ 2 * la + la ^ 2 / Real.log 2 :=
    add_nonneg (mul_nonneg (sq_nonneg _) hl0) (div_nonneg (sq_nonneg _) hlpos.le)
  have mid : Nm ^ 2 * la + la ^ 2 / Real.log 2 ≤ 2 * Y ^ 3 := by nlinarith [sq_nonneg Y]
  have h2 : X' * xn + 2 ≤ X' * (2 * Y) := by nlinarith
  have a1 : C * f ≤ Y * Y := mul_le_mul hC hf hf0 hY0
  have a2 : C * f * (Nm ^ 2 * la + la ^ 2 / Real.log 2) ≤ Y * Y * (2 * Y ^ 3) :=
    mul_le_mul a1 mid mid0 (mul_nonneg hY0 hY0)
  have a3 := mul_le_mul a2 h2 (by nlinarith [mul_nonneg hX0 hxn0])
    (mul_nonneg (mul_nonneg hY0 hY0) (mul_nonneg (by norm_num) (pow_nonneg hY0 3)))
  have h10 : (10 : ℝ) ≤ Y := hY
  have h4 : 4 * Y ^ 6 ≤ Y ^ 7 := by nlinarith [pow_nonneg hY0 6]
  nlinarith [mul_le_mul_of_nonneg_right h4 hX0]

theorem second_bound_arith_a (g k W x b' X' b : ℝ) (hg : g ≤ x / 2) (hx : 0 < x) (hkW : 0 ≤ k ^ 2 * W) (hb' : 0 ≤ b')
    (h : k ^ 2 * W * x * x ≤ X') (hX : b' * X' = x * b) : g * (k ^ 2 * W) * b' ≤ b / 2 := by
  have hAb : 0 ≤ k ^ 2 * W * b' := mul_nonneg hkW hb'
  have h1 : k ^ 2 * W * x * x * b' ≤ X' * b' := mul_le_mul_of_nonneg_right h hb'
  have h2 : k ^ 2 * W * x * b' ≤ b := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_lt_mul_of_pos_left hc hx]
  nlinarith [mul_le_mul_of_nonneg_right hg hAb]

theorem second_bound_arith_b (g k W x b : ℝ) (hg : g ≤ x / 2) (hx : 0 < x) (hk : 1 ≤ k) (hW : x ^ 2 ≤ W) (hW1 : 1 ≤ W)
    (hb : 0 ≤ b) : g * (k ^ 2 * W) * (x * b * ((k * W) ^ 4)⁻¹) ≤ b / 2 := by
  have hk0 : 0 < k := by linarith
  have hW0 : 0 < W := by linarith
  have hP : 0 < (k * W) ^ 4 := by positivity
  have hq : 0 ≤ k ^ 2 * W * (x * b * ((k * W) ^ 4)⁻¹) :=
    mul_nonneg (by positivity) (mul_nonneg (mul_nonneg hx.le hb) (inv_nonneg.2 hP.le))
  have hk2 : 1 ≤ k ^ 2 := one_le_pow₀ hk
  have hW2 : 1 ≤ W ^ 2 := one_le_pow₀ hW1
  have hkW1 : 1 ≤ k ^ 2 * W ^ 2 := one_le_mul_of_one_le_of_one_le hk2 hW2
  have a1 : x ^ 2 * (k ^ 2 * W) ≤ W * (k ^ 2 * W) := mul_le_mul_of_nonneg_right hW (by positivity)
  have a2 : k ^ 2 * W ^ 2 ≤ (k * W) ^ 4 := by
    have := mul_le_mul_of_nonneg_left hkW1 (by positivity : (0 : ℝ) ≤ k ^ 2 * W ^ 2)
    nlinarith
  have key : x * (k ^ 2 * W * (x * b * ((k * W) ^ 4)⁻¹)) ≤ b := by
    rw [show x * (k ^ 2 * W * (x * b * ((k * W) ^ 4)⁻¹)) = x ^ 2 * k ^ 2 * W * b / (k * W) ^ 4 by
      rw [div_eq_mul_inv]; ring]
    rw [div_le_iff₀ hP]
    nlinarith [mul_le_mul_of_nonneg_right (le_trans a1 (by nlinarith : W * (k ^ 2 * W) ≤ (k * W) ^ 4)) hb]
  nlinarith [mul_le_mul_of_nonneg_right hg hq, key]

theorem fourth_bound_arith (z C lx La a k p0 x : ℝ) (hC : 0 ≤ C) (hlx : 0 ≤ lx) (hLa : 0 ≤ La) (ha : 0 ≤ a)
    (hx : 0 < x) (hk : 0 < k) (hl : z * (1 + z) ≤ 2 * x) (hg : 4 * C * lx ≤ x) (h1 : La * x ^ 3 ≤ k) (h2 : x ^ 3 ≤ p0) :
    z * (1 + z) * (C * lx * (La * a / k + a / p0)) ≤ a / x := by
  have hx3 : 0 < x ^ 3 := pow_pos hx 3
  have hp0 : 0 < p0 := lt_of_lt_of_le hx3 h2
  have hbr0 : 0 ≤ La * a / k + a / p0 :=
    add_nonneg (div_nonneg (mul_nonneg hLa ha) hk.le) (div_nonneg ha hp0.le)
  have hQ0 : 0 ≤ C * lx * (La * a / k + a / p0) := mul_nonneg (mul_nonneg hC hlx) hbr0
  have b1 : La * a / k ≤ a / x ^ 3 := by
    rw [div_le_div_iff₀ hk hx3]
    nlinarith [mul_le_mul_of_nonneg_left h1 ha]
  have b2 : a / p0 ≤ a / x ^ 3 := div_le_div_of_nonneg_left ha hx3 h2
  have hax : 0 ≤ a / x ^ 3 := div_nonneg ha hx3.le
  have b3 : C * lx * (La * a / k + a / p0) ≤ x / 4 * (2 * (a / x ^ 3)) :=
    mul_le_mul (by linarith) (by linarith) hbr0 (by positivity)
  calc z * (1 + z) * (C * lx * (La * a / k + a / p0))
      ≤ 2 * x * (C * lx * (La * a / k + a / p0)) := mul_le_mul_of_nonneg_right hl hQ0
    _ ≤ 2 * x * (x / 4 * (2 * (a / x ^ 3))) := mul_le_mul_of_nonneg_left b3 (by positivity)
    _ = a / x := by
      have hx0 : x ≠ 0 := hx.ne'
      first
        | (field_simp; ring)
        | field_simp

end Formalism.MainNotions.AuxBlock8.Pf.G5.Nu

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.PrimeSums
section
noncomputable section

open scoped BigOperators

namespace Formalism.MainNotions.AuxBlock8.Pf.G5

theorem sum_ite_mem_le {S R : Finset ℕ} (f : ℕ → ℝ) (hf : ∀ p ∈ R, 0 ≤ f p) :
    ∑ p ∈ S, (if p ∈ R then f p else 0) ≤ ∑ p ∈ R, f p := by
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp; exact (Finset.mem_filter.1 hp).2
  · intro p hp _; exact hf p hp

def prB (y : ℝ) : Finset ℕ := (Finset.range ⌈y⌉₊).filter Nat.Prime

theorem mem_prB {y : ℝ} {p : ℕ} : p ∈ prB y ↔ p.Prime ∧ (p : ℝ) < y := by
  simp [prB, Nat.lt_ceil, and_comm]

theorem card_prB_le (y : ℝ) (hy : 0 ≤ y) : ((prB y).card : ℝ) ≤ y + 1 := by
  have h1 : (prB y).card ≤ ⌈y⌉₊ := by
    have := Finset.card_filter_le (Finset.range ⌈y⌉₊) Nat.Prime
    simpa [prB] using this
  have h2 : ((prB y).card : ℝ) ≤ (⌈y⌉₊ : ℝ) := by exact_mod_cast h1
  have h3 := Nat.ceil_lt_add_one hy
  linarith

theorem sum_log_prB (y : ℝ) (hy : 0 ≤ y) : ∑ p ∈ prB y, Real.log p ≤ Real.log 4 * y := by
  refine le_trans ?_ (Chebyshev.theta_le_log4_mul_x hy)
  unfold Chebyshev.theta
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨h1, h2⟩ := mem_prB.1 hp
    exact Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨h1.pos, Nat.le_floor h2.le⟩, h1⟩
  · intro p hp _
    exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.1 hp).2.one_lt.le)

theorem sum_logdiv_prB (y : ℝ) (hy : 1 ≤ y) :
    ∑ p ∈ prB y, Real.log p / p ≤ Real.log y * (1 + Real.log y) := by
  have hly : 0 ≤ Real.log y := Real.log_nonneg hy
  have h1 : ∑ p ∈ prB y, Real.log p / p ≤ ∑ p ∈ prB y, Real.log y * ((p : ℝ))⁻¹ := by
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨hp1, hp2⟩ := mem_prB.1 hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1.pos
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (Real.log_le_log hp0 hp2.le) (inv_nonneg.2 hp0.le)
  refine le_trans h1 ?_
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ hly
  have h2 : ∑ p ∈ prB y, ((p : ℝ))⁻¹ ≤ ∑ p ∈ Finset.Icc 1 ⌊y⌋₊, ((p : ℝ))⁻¹ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hp1, hp2⟩ := mem_prB.1 hp
      exact Finset.mem_Icc.2 ⟨hp1.pos, Nat.le_floor hp2.le⟩
    · intro p _ _
      positivity
  refine le_trans h2 ?_
  have h3 := harmonic_le_one_add_log ⌊y⌋₊
  rw [harmonic_eq_sum_Icc] at h3
  push_cast at h3
  refine le_trans h3 ?_
  have h4 : (1 : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast Nat.le_floor (by simpa using hy)
  have h5 : Real.log (⌊y⌋₊ : ℝ) ≤ Real.log y := Real.log_le_log (by linarith) (Nat.floor_le (by linarith))
  linarith

end Formalism.MainNotions.AuxBlock8.Pf.G5

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.RemainingCountingStatement
section
noncomputable section

open scoped BigOperators
open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.G

namespace Formalism.MainNotions.AuxBlock8.Pf

def FamilyAskBounds {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → 0 ≤ Ce → 0 ≤ Cm →
    ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
      AdmFam Fm K X Y C31 Ce Cm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, RequiresAll (X x i)

def RemainingCountingStatement {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → 0 ≤ Ce → 0 ≤ Cm →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
      AdmFam Fm K X Y C31 Ce Cm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
        GainBoundAll (X x i) K C ((Fm.L x i).sc.b ^ (x ^ (-(eps / 2))))

def FamilyFourthBound {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → 0 ≤ Ce → 0 ≤ Cm →
    ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
      AdmFam Fm K X Y C31 Ce Cm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Conclusion2 (Fm.D x i) (Fm.L x i) (X x i) K

def RestW {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → 0 ≤ Ce → 0 ≤ Cm →
    ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
      AdmFam Fm K X Y C31 Ce Cm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, WeightVectorExists (Fm.D x i) (Fm.L x i) (X x i) K

def FamilyFifthBound {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → 0 ≤ Ce → 0 ≤ Cm → ∀ C : ℝ, 0 ≤ C →
    ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
      AdmFam Fm K X Y C31 Ce Cm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
        GainBoundAll (X x i) K C ((Fm.L x i).sc.b ^ (x ^ (-(eps / 2)))) → PointsLemma (Fm.D x i) (Fm.L x i) (X x i) K

def RestT {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∀ K : Consts, K.Nonneg → ∀ C31 Ce Cm : ℝ, 0 < C31 → 0 ≤ Ce → 0 ≤ Cm → ∀ C : ℝ, 0 ≤ C →
    ∀ (X : ∀ x (i : Fm.Ix x), Inst (Fm.D x i) (Fm.L x i)) (Y : ∀ x (i : Fm.Ix x), LatInst (Fm.D x i)),
      AdmFam Fm K X Y C31 Ce Cm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, WeightedPrimeSumBound (Fm.D x i) (Fm.L x i) (X x i) K C

theorem eps_pos {eps : ℝ} (Fm : FamP eps) : 0 < eps := by
  obtain ⟨i⟩ := Fm.Ix_zero
  rw [← Fm.L_eps 0 i]
  exact (Fm.L 0 i).sc.eps_pos

theorem stmtEF_of {eps : ℝ} (Fm : FamP eps) (h0 : FamilyAskBounds Fm) (h1 : RemainingCountingStatement Fm) (h2 : FamilyFourthBound Fm) (hW : RestW Fm)
    (h3 : FamilyFifthBound Fm) (hT : RestT Fm) : FamilyClosedForm Fm := by
  intro K hK C31 Ce Cm hC31 hCe hCm
  obtain ⟨C, hC, hG⟩ := h1 K hK C31 Ce Cm hC31 hCe hCm
  refine ⟨C, hC, fun X Y hA => ?_⟩
  obtain ⟨a0, ha0⟩ := h0 K hK C31 Ce Cm hC31 hCe hCm X Y hA
  obtain ⟨a1, ha1⟩ := hG X Y hA
  obtain ⟨a2, ha2⟩ := h2 K hK C31 Ce Cm hC31 hCe hCm X Y hA
  obtain ⟨aW, haW⟩ := hW K hK C31 Ce Cm hC31 hCe hCm X Y hA
  obtain ⟨a3, ha3⟩ := h3 K hK C31 Ce Cm hC31 hCe hCm C hC X Y hA
  obtain ⟨aT, haT⟩ := hT K hK C31 Ce Cm hC31 hCe hCm C hC X Y hA
  refine ⟨fun x => x ^ (-(eps / 2)), ?_, max a0 (max a1 (max a2 (max aW (max a3 aT)))), fun x hx i => ?_⟩
  · exact tendsto_rpow_neg_atTop (half_pos (eps_pos Fm))
  · simp only [ge_iff_le, max_le_iff] at hx
    obtain ⟨e0, e1, e2, eW, e3, eT⟩ := hx
    have g0 := ha0 x e0 i
    have g1 := ha1 x e1 i
    have g2 := ha2 x e2 i
    have gW := haW x eW i
    have g3 := ha3 x e3 i g1
    have gT := haT x eT i
    have g1' := g1 (aL (Fm.L x i)) (bL (Fm.L x i))
    refine ⟨g1' ?_, g2, g3, gW, fun a b ha hb p hp _ => g0 a b ha hb p hp, gT⟩

    intro t ht
    unfold aL bL
    simp only [dif_pos ht]
    exact ⟨((Fm.L x i).aT_win ⟨t, ht⟩).1, ((Fm.L x i).aT_win ⟨t, ht⟩).2, (Fm.L x i).bT_ge ⟨t, ht⟩⟩

theorem stmtF_of_stmtEF {eps : ℝ} (Fm : FamP eps) (h : FamilyClosedForm Fm) : KudlaFamilyStatement Fm := by
  intro K hK X Y hA
  obtain ⟨C31, Ce, Cm, hC31, hCe, hCm, hA'⟩ := hA
  obtain ⟨C, hC, hP⟩ := h K hK C31 Ce Cm hC31 hCe hCm
  exact ⟨C, hP X Y hA'⟩

end Formalism.MainNotions.AuxBlock8.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.LogarithmicSums.TsumTruncatedShiftLe
section
noncomputable section

open scoped BigOperators

namespace Formalism.MainNotions.AuxBlock8.Pf

theorem summable_geo (p y : ℝ) (hp : 2 ≤ p) : Summable (fun e : ℕ => y / p ^ e) := by
  have h : Summable (fun e : ℕ => y * (1 / p) ^ e) :=
    (summable_geometric_of_lt_one (by positivity) (by rw [div_lt_one (by linarith)]; linarith)).mul_left y
  refine h.congr (fun e => ?_)
  rw [one_div, inv_pow, div_eq_mul_inv]

theorem summable_if_of_le (p y : ℝ) (hp : 2 ≤ p) (f : ℕ → ℝ) (Q : ℕ → Prop) [DecidablePred Q]
    (h0 : ∀ e, 0 ≤ f e) (h1 : ∀ e, f e ≤ y / p ^ e) : Summable (fun e => if Q e then f e else 0) := by
  refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) (summable_geo p y hp)
  · split_ifs
    · exact h0 e
    · exact le_rfl
  · split_ifs
    · exact h1 e
    · exact le_trans (h0 e) (h1 e)

theorem summable_odd (p y : ℝ) (hp : 2 ≤ p) (Q : ℕ → Prop) [DecidablePred Q] :
    Summable (fun e : ℕ => if Q e then y / p ^ e else 0) := by
  have h := (summable_geo p |y| hp)
  refine Summable.of_norm_bounded h (fun e => ?_)
  have hpe : 0 < p ^ e := by positivity
  split_ifs
  · rw [Real.norm_eq_abs, abs_div, abs_of_pos hpe]
  · rw [norm_zero]; positivity

theorem tsum_odd (p y : ℝ) (hp : 2 ≤ p) (Q : ℕ → Prop) [DecidablePred Q] (hQ : ∀ e, Q e ↔ Odd e) :
    ∑' e : ℕ, (if Q e then y / p ^ e else 0) = p / (p ^ 2 - 1) * y := by
  set f : ℕ → ℝ := fun e => if Q e then y / p ^ e else 0 with hf
  have he : ∀ k : ℕ, f (2 * k) = 0 := by
    intro k
    rw [hf]
    exact if_neg (fun h => by have := (hQ _).1 h; exact (Nat.not_odd_iff_even.2 (even_two_mul k)) this)
  have ho : ∀ k : ℕ, f (2 * k + 1) = y / p * (1 / p ^ 2) ^ k := by
    intro k
    rw [hf]
    have : Q (2 * k + 1) := (hQ _).2 (odd_two_mul_add_one k)
    simp only [if_pos this]
    rw [pow_succ, pow_mul, one_div, inv_pow]
    field_simp
  have hp2 : (1 : ℝ) / p ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith
  have hs0 : Summable (fun k : ℕ => f (2 * k)) := by
    simp only [he]; exact summable_zero
  have hs1 : Summable (fun k : ℕ => f (2 * k + 1)) := by
    simp only [ho]
    exact (summable_geometric_of_lt_one (by positivity) hp2).mul_left _
  rw [← tsum_even_add_odd hs0 hs1]
  simp only [he, ho, tsum_zero, zero_add]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hp2]
  have h1 : p ^ 2 - 1 ≠ 0 := by nlinarith
  have h2 : p ≠ 0 := by linarith
  have h3 : (1 : ℝ) - 1 / p ^ 2 ≠ 0 := by linarith
  field_simp

theorem max_add_min_eq (u w : ℝ) : max 0 (u - w) + min u w = u := by
  rcases le_total u w with h | h
  · rw [max_eq_left (by linarith), min_eq_left h]; ring
  · rw [max_eq_right (by linarith), min_eq_right h]; ring

theorem tsum_pos_add_min (p y : ℝ) (hp : 2 ≤ p) (hy : 0 ≤ y) (w : ℕ → ℝ) (hw : ∀ e, 0 ≤ w e)
    (Q : ℕ → Prop) [DecidablePred Q] (hQ : ∀ e, Q e ↔ Odd e) :
    ∑' e : ℕ, (if Q e then max 0 (y / p ^ e - w e) else 0) +
      ∑' e : ℕ, (if Q e then min (y / p ^ e) (w e) else 0) = p / (p ^ 2 - 1) * y := by
  have hpe : ∀ e : ℕ, 0 ≤ y / p ^ e := fun e => div_nonneg hy (by positivity)
  have s1 : Summable (fun e : ℕ => if Q e then max 0 (y / p ^ e - w e) else 0) :=
    summable_if_of_le p y hp _ Q (fun e => le_max_left _ _)
      (fun e => max_le (hpe e) (by have := hw e; linarith))
  have s2 : Summable (fun e : ℕ => if Q e then min (y / p ^ e) (w e) else 0) :=
    summable_if_of_le p y hp _ Q (fun e => le_min (hpe e) (hw e)) (fun e => min_le_left _ _)
  rw [← s1.tsum_add s2, ← tsum_odd p y hp Q hQ]
  congr 1
  funext e
  split_ifs
  · exact max_add_min_eq _ _
  · simp

theorem tsum_pos_le (p y : ℝ) (hp : 2 ≤ p) (hy : 0 ≤ y) (w : ℕ → ℝ) (hw : ∀ e, 0 ≤ w e)
    (Q : ℕ → Prop) [DecidablePred Q] (hQ : ∀ e, Q e → Odd e) :
    ∑' e : ℕ, (if Q e then max 0 (y / p ^ e - w e) else 0) ≤ p / (p ^ 2 - 1) * y := by
  classical
  have hpe : ∀ e : ℕ, 0 ≤ y / p ^ e := fun e => div_nonneg hy (by positivity)
  rw [← tsum_odd p y hp (fun e => Odd e) (fun e => Iff.rfl)]
  refine Summable.tsum_le_tsum (fun e => ?_)
    (summable_if_of_le p y hp _ Q (fun e => le_max_left _ _)
      (fun e => max_le (hpe e) (by have := hw e; linarith))) (summable_odd p y hp _)
  by_cases h : Q e
  · rw [if_pos h, if_pos (hQ e h)]
    exact max_le (hpe e) (by have := hw e; linarith)
  · rw [if_neg h]
    split_ifs
    · exact hpe e
    · exact le_rfl

theorem tsum_truncated_shift_le (p y c A : ℝ) (hp : 2 ≤ p) (hc : 0 ≤ c) (hy : 2 * c ≤ y) (hyA : y ≤ A) (hA : 1 ≤ A)
    (w w' : ℕ → ℝ) (hw : ∀ e, 1 ≤ w e) (hw0 : ∀ e, 0 ≤ w' e) (hw' : ∀ e, w' e ≤ w e + c)
    (Q : ℕ → Prop) [DecidablePred Q] (hQ : ∀ e, Q e → Odd e) :
    ∑' e : ℕ, (if Q e then max 0 (y / p ^ e - w e) else 0) - 3 * c * Real.logb p A ≤
      ∑' e : ℕ, (if Q e then max 0 ((y - 2 * c) / p ^ e - w' e) else 0) := by
  classical
  have hy0 : 0 ≤ y := by linarith
  set M : ℕ := ⌊Real.logb p A⌋₊ with hM
  have hlog : 0 ≤ Real.logb p A := Real.logb_nonneg (by linarith) hA
  have hpe : ∀ e : ℕ, 0 ≤ y / p ^ e := fun e => div_nonneg hy0 (by positivity)
  have hpe' : ∀ e : ℕ, 0 ≤ (y - 2 * c) / p ^ e := fun e => div_nonneg (by linarith) (by positivity)
  have sF : Summable (fun e : ℕ => if Q e then max 0 (y / p ^ e - w e) else 0) :=
    summable_if_of_le p y hp _ Q (fun e => le_max_left _ _)
      (fun e => max_le (hpe e) (by have := hw e; linarith))
  have sG : Summable (fun e : ℕ => if Q e then max 0 ((y - 2 * c) / p ^ e - w' e) else 0) :=
    summable_if_of_le p (y - 2 * c) hp _ Q (fun e => le_max_left _ _)
      (fun e => max_le (hpe' e) (by have := hw0 e; linarith))
  have sH : Summable (fun e : ℕ => if e ∈ Finset.Icc 1 M then 3 * c else 0) :=
    summable_of_ne_finset_zero (s := Finset.Icc 1 M) (fun e he => if_neg he)
  have hH : ∑' e : ℕ, (if e ∈ Finset.Icc 1 M then 3 * c else 0) ≤ 3 * c * Real.logb p A := by
    rw [tsum_eq_sum (s := Finset.Icc 1 M) (fun e he => if_neg he)]
    rw [Finset.sum_congr rfl (fun e he => if_pos he), Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    have h1 : ((M + 1 - 1 : ℕ) : ℝ) ≤ Real.logb p A := by
      rw [Nat.add_sub_cancel]
      exact Nat.floor_le hlog
    nlinarith
  have hterm : ∀ e : ℕ, (if Q e then max 0 (y / p ^ e - w e) else 0) ≤
      (if Q e then max 0 ((y - 2 * c) / p ^ e - w' e) else 0) +
        (if e ∈ Finset.Icc 1 M then 3 * c else 0) := by
    intro e
    have h3c : (0 : ℝ) ≤ (if e ∈ Finset.Icc 1 M then 3 * c else 0) := by
      split_ifs
      · linarith
      · exact le_rfl
    by_cases h : Q e
    · rw [if_pos h, if_pos h]
      by_cases hpos : y / p ^ e ≤ w e
      · rw [max_eq_left (by linarith)]
        exact add_nonneg (le_max_left _ _) h3c
      · push_neg at hpos
        have hpp : (0 : ℝ) < p ^ e := by positivity
        have h1 : 1 < y / p ^ e := lt_of_le_of_lt (hw e) hpos
        have h2 : p ^ e < y := by rwa [lt_div_iff₀ hpp, one_mul] at h1
        have h3 : (e : ℝ) ≤ Real.logb p A := by
          rw [Real.le_logb_iff_rpow_le (by linarith) (by linarith), Real.rpow_natCast]
          linarith
        have h4 : e ∈ Finset.Icc 1 M := by
          rw [Finset.mem_Icc]
          refine ⟨?_, Nat.le_floor h3⟩
          obtain ⟨k, hk⟩ := hQ e h
          omega
        rw [if_pos h4, max_eq_right (by linarith)]
        have h5 : 2 * c / p ^ e ≤ 2 * c := div_le_self (by linarith) (one_le_pow₀ (by linarith))
        have h6 : (y - 2 * c) / p ^ e = y / p ^ e - 2 * c / p ^ e := sub_div _ _ _
        have h7 := hw' e
        have h8 : (y - 2 * c) / p ^ e - w' e ≤ max 0 ((y - 2 * c) / p ^ e - w' e) := le_max_right _ _
        linarith
    · rw [if_neg h, if_neg h]
      linarith
  have := Summable.tsum_le_tsum hterm sF (sG.add sH)
  rw [sG.tsum_add sH] at this
  linarith

end Formalism.MainNotions.AuxBlock8.Pf

end
end

