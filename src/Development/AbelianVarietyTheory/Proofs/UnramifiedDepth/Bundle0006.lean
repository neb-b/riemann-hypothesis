module

public import Mathlib
public import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
public import ReciprocityTheory.DualLattices.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FactorizationLeFourFifteenths
section
open ReciprocityTheory.PGsh

namespace GlobalTheory

theorem factorization_le_four_fifteenths {l B : ℕ} (hl : 5 ≤ l) (hB : B ≠ 0) :
    (B.factorization l : ℝ) ≤ 4 / 15 * (B : ℝ) := by
  have h1 : l ^ B.factorization l ≤ B := Nat.ordProj_le l hB
  have h2 : 5 ^ B.factorization l ≤ l ^ B.factorization l := Nat.pow_le_pow_left hl _
  have h3 : ∀ k : ℕ, 4 * k + 1 ≤ 5 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ]; omega
  have h4 : 4 * B.factorization l + 1 ≤ B := le_trans (h3 _) (le_trans h2 h1)
  have h5 : (4 : ℝ) * (B.factorization l : ℝ) + 1 ≤ B := by exact_mod_cast h4
  have h6 : (0 : ℝ) ≤ (B.factorization l : ℝ) := Nat.cast_nonneg _
  linarith

theorem four_fifteenths_le_slope_gap {x : ℝ} (hx : 5 ≤ x) {i : ℕ} (hi : 1 ≤ i) :
    4 / 15 ≤ (1 / (x ^ 2 - 1) + 1 / 2 - 1 / (8 * x ^ i)) - 1 / (x - 1) := by
  have h1 : x ≤ x ^ i := by
    simpa using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ x) hi
  have h2 : 1 / (8 * x ^ i) ≤ 1 / 40 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hp : 0 < x ^ 2 - 1 := by nlinarith
  have hq : 0 < x - 1 := by linarith
  have h3 : 1 / (x - 1) - 1 / (x ^ 2 - 1) = x / (x ^ 2 - 1) := by
    have : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
    rw [this]
    have hr : 0 < x + 1 := by linarith
    field_simp
    ring
  have h4 : x / (x ^ 2 - 1) ≤ 5 / 24 := by
    rw [div_le_div_iff₀ hp (by norm_num)]
    nlinarith
  linarith

theorem weight_of_weight_pderiv :
  (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → 5 ≤ l → ∀ (i : ℕ) (κ κ' : Type) [Fintype κ] [Fintype κ'] [DecidableEq κ] [DecidableEq κ'] (h₁ : MvPowerSeries (κ ⊕ κ') C), 1 ≤ i →
    (∀ α, MvPowerSeries.coeff α h₁ ≠ 0 → ∃ q, α (Sum.inr q) ≠ 0) → (∀ b, (∀ α, (((0) - α.sum (fun j e => Sum.elim (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (l : ℝ) ^ i)) (fun _ => 1 / ((l : ℝ) - 1)) j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (MvPowerSeries.pderiv (R := C) (Sum.inr b) h₁)))) →
    (∀ α, (((1 / (l - 1)) - α.sum (fun j e => Sum.elim (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (l : ℝ) ^ i)) (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 1 / 2 - 1 / (8 * (l : ℝ) ^ i)) j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (h₁)))) := by
  intro C _ _ v l hl hv h5 i κ κ' _ _ _ _ h₁ hi hsupp hder α
  by_cases h0 : MvPowerSeries.coeff α h₁ = 0
  · rw [h0, v.map_zero]; exact le_top
  obtain ⟨b, hb⟩ := hsupp α h0
  obtain ⟨β, rfl⟩ : ∃ β : κ ⊕ κ' →₀ ℕ, α = β + Finsupp.single (Sum.inr b) 1 := by
    refine ⟨α - Finsupp.single (Sum.inr b) 1, ?_⟩
    rw [tsub_add_cancel_of_le]
    exact Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hb)
  have h := hder b β
  have hc : ((β (Sum.inr b) : C) + 1) = ((β (Sum.inr b) + 1 : ℕ) : C) := by push_cast; rfl
  rw [MvPowerSeries.coeff_pderiv, hc, v.map_mul,
    ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.natCast_eq_factorization v hl hv (Nat.succ_ne_zero _)] at h
  have hf := factorization_le_four_fifteenths h5 (Nat.succ_ne_zero (β (Sum.inr b)))
  have hg := four_fifteenths_le_slope_gap (x := (l : ℝ)) (by exact_mod_cast h5) hi
  generalize v (MvPowerSeries.coeff (β + Finsupp.single (Sum.inr b) 1) h₁) = w at h ⊢
  induction w using WithTop.recTopCoe with
  | top => exact le_top
  | coe w =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe] at h
    rw [WithTop.coe_le_coe]
    rw [Finsupp.sum_add_index' (by intro j; simp) (by intro j e e'; push_cast; ring),
      Finsupp.sum_single_index (by simp)]
    rw [Finsupp.sum_fintype _ _ (by intro j; simp), Fintype.sum_sum_type] at h ⊢
    simp only [Sum.elim_inl, Sum.elim_inr, ← Finset.mul_sum] at h ⊢
    have hJ : (β (Sum.inr b) : ℝ) ≤ ∑ q, (β (Sum.inr q) : ℝ) :=
      Finset.single_le_sum (f := fun q => (β (Sum.inr q) : ℝ))
        (fun q _ => Nat.cast_nonneg _) (Finset.mem_univ b)
    have hJ0 : (0 : ℝ) ≤ β (Sum.inr b) := Nat.cast_nonneg _
    push_cast at hf ⊢
    generalize (∑ q, (β (Sum.inr q) : ℝ)) = J at h hJ ⊢
    generalize (1 / ((l : ℝ) ^ 2 - 1) + 1 / 2 - 1 / (8 * (l : ℝ) ^ i)) = c' at hg ⊢
    generalize 1 / ((l : ℝ) - 1) = c at h hg ⊢
    have hm : 4 / 15 * (J + 1) ≤ (c' - c) * (J + 1) :=
      mul_le_mul_of_nonneg_right hg (by linarith)
    nlinarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LegendreBoundsFactorialMultiIndexCapelli
section
open ReciprocityTheory.PGsh

namespace GlobalTheory.LegendreBounds

theorem digitSum_le (l N : ℕ) (hl : 1 < l) :
    (Nat.digits l N).sum ≤ (Nat.log l N + 1) * (l - 1) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have hlen : (Nat.digits l N).length = Nat.log l N + 1 := Nat.length_digits l N hl hN.ne'
    have hd : ∀ d ∈ Nat.digits l N, d ≤ l - 1 := fun d hd => by
      have := Nat.digits_lt_base hl hd
      omega
    calc (Nat.digits l N).sum ≤ (Nat.digits l N).length * (l - 1) := by
          simpa [smul_eq_mul] using List.sum_le_card_nsmul _ _ hd
      _ = (Nat.log l N + 1) * (l - 1) := by rw [hlen]

theorem legendre_real (l : ℕ) (hl : l.Prime) (N : ℕ) :
    (padicValNat l N.factorial : ℝ) = ((N : ℝ) - ((Nat.digits l N).sum : ℕ)) / (l - 1) := by
  have := Fact.mk hl
  have h1 : (l - 1) * padicValNat l N.factorial = N - (Nat.digits l N).sum :=
    by simpa [Nat.padicValNat_def] using (hl.sub_one_mul_multiplicity_factorial (n := N))
  have h2 : (Nat.digits l N).sum ≤ N := Nat.digit_sum_le l N
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have h3 := congrArg (Nat.cast : ℕ → ℝ) h1
  rw [Nat.cast_mul, Nat.cast_sub hl.one_le, Nat.cast_sub h2, Nat.cast_one] at h3
  rw [eq_div_iff (by linarith)]
  linear_combination h3

private theorem digits_sum_div_pred_le_log_add_one (l N : ℕ) (hl : 1 < l) :
    ((Nat.digits l N).sum : ℝ) / (l - 1) ≤ Nat.log l N + 1 := by
  have hl1 : (0 : ℝ) < l - 1 := by
    have : (1 : ℝ) < l := by exact_mod_cast hl
    linarith
  rw [div_le_iff₀ hl1]
  have h := digitSum_le l N hl
  have h' : ((Nat.digits l N).sum : ℝ) ≤ ((Nat.log l N + 1) * (l - 1) : ℕ) := by exact_mod_cast h
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_sub hl.le, Nat.cast_one] at h'
  exact h'

private theorem natLog_le_logb_of_le (l N M : ℕ) (hl : 1 < l) (hM : 1 ≤ M) (hNM : N ≤ M) :
    (Nat.log l N : ℝ) ≤ Real.logb l M := by
  have hl' : (1 : ℝ) < l := by exact_mod_cast hl
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  rw [Real.le_logb_iff_rpow_le hl' hM', Real.rpow_natCast]
  have : l ^ Nat.log l N ≤ M := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simpa using hM
    · exact (Nat.pow_log_le_self l hN.ne').trans hNM
  exact_mod_cast this

theorem lower (l : ℕ) (hl : l.Prime) (N M : ℕ) (hM : 1 ≤ M) (hNM : N ≤ M) :
    (N : ℝ) / (l - 1) - (Real.logb l M + 1) ≤ padicValNat l N.factorial := by
  have h1 := digits_sum_div_pred_le_log_add_one l N hl.one_lt
  have h2 := natLog_le_logb_of_le l N M hl.one_lt hM hNM
  rw [legendre_real l hl N, sub_div]
  linarith

theorem upper (l : ℕ) (hl : l.Prime) (N : ℕ) :
    (padicValNat l N.factorial : ℝ) ≤ (N : ℝ) / (l - 1) := by
  have hl1 : (0 : ℝ) < l - 1 := by
    have : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
    linarith
  rw [legendre_real l hl N, div_le_div_iff_of_pos_right hl1]
  have : (0 : ℝ) ≤ ((Nat.digits l N).sum : ℕ) := Nat.cast_nonneg _
  linarith

theorem upper_of_pos (l : ℕ) (hl : l.Prime) (N : ℕ) (hN : 1 ≤ N) :
    (padicValNat l N.factorial : ℝ) ≤ ((N : ℝ) - 1) / (l - 1) := by
  have hl1 : (0 : ℝ) < l - 1 := by
    have : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
    linarith
  have hN0 : N ≠ 0 := by omega
  have hs : 1 ≤ (Nat.digits l N).sum := by
    have hmem := List.getLast_mem ((Nat.digits_ne_nil_iff_ne_zero (b := l) (n := N)).mpr hN0)
    have hlast := Nat.getLast_digit_ne_zero l hN0
    have := List.le_sum_of_mem hmem
    omega
  have hs' : (1 : ℝ) ≤ ((Nat.digits l N).sum : ℕ) := by exact_mod_cast hs
  rw [legendre_real l hl N, div_le_div_iff_of_pos_right hl1]
  linarith

theorem padicValNat_prod_factorial (l : ℕ) (hl : l.Prime) {κ : Type} (s : Finset κ)
    (A : κ → ℕ) :
    (padicValNat l (∏ j ∈ s, (A j).factorial) : ℝ)
      = ∑ j ∈ s, (padicValNat l (A j).factorial : ℝ) := by
  have := Fact.mk hl
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [Nat.padicValNat_def]
  · intro a t ha ih
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.factorial_ne_zero _)
        (Finset.prod_ne_zero_iff.mpr fun j _ => Nat.factorial_ne_zero _), Nat.cast_add, ih]

theorem legendre_bounds :
  (∀ (l : ℕ), l.Prime → (∀ N : ℕ, 1 ≤ N → (N : ℝ) / (l - 1) - (Real.logb l N + 1) ≤ padicValNat l N.factorial ∧ (padicValNat l N.factorial : ℝ) ≤ (N - 1) / (l - 1)) ∧
    (∀ (κ : Type) [Fintype κ] (A : κ → ℕ), 1 ≤ ∑ j, A j → ((∑ j, A j : ℕ) : ℝ) / (l - 1) - Fintype.card κ * (Real.logb l ((∑ j, A j : ℕ) : ℝ) + 1) ≤ padicValNat l (∏ j, (A j).factorial)) ∧
    ∀ n₀ x : ℕ, (padicValNat l (∏ c ∈ Finset.range n₀, (x + c).factorial) : ℝ) - padicValNat l (∏ c ∈ Finset.range n₀, c.factorial) ≤
      n₀ * x / (l - 1) + n₀ * (Real.logb l n₀ + 1)) := by
  intro l hl
  refine ⟨fun N hN => ⟨lower l hl N N hN le_rfl, upper_of_pos l hl N hN⟩, ?_, ?_⟩
  · intro κ _ A hA
    rw [padicValNat_prod_factorial l hl Finset.univ A]
    have key : ∀ j ∈ (Finset.univ : Finset κ), (A j : ℝ) / (l - 1) - (Real.logb l ((∑ i, A i : ℕ) : ℝ) + 1)
        ≤ padicValNat l (A j).factorial := fun j _ =>
      lower l hl (A j) (∑ i, A i) hA
        (Finset.single_le_sum (fun i _ => Nat.zero_le (A i)) (Finset.mem_univ j))
    have h := Finset.sum_le_sum key
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_div,
      ← Nat.cast_sum] at h
    linarith
  · intro n₀ x
    rcases Nat.eq_zero_or_pos n₀ with rfl | hn
    · simp
    · have e1 := padicValNat_prod_factorial l hl (Finset.range n₀) (fun c => x + c)
      have e2 := padicValNat_prod_factorial l hl (Finset.range n₀) (fun c => c)
      rw [e1, e2, ← Finset.sum_sub_distrib]
      calc _ ≤ ∑ c ∈ Finset.range n₀, ((x : ℝ) / (l - 1) + (Real.logb l n₀ + 1)) :=
            Finset.sum_le_sum fun c hc => by
              have h1 := upper l hl (x + c)
              have h2 := lower l hl c n₀ hn (Finset.mem_range.mp hc).le
              push_cast at h1
              have h3 : ((x : ℝ) + c) / (l - 1) = x / (l - 1) + c / (l - 1) := add_div _ _ _
              linarith
        _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end GlobalTheory.LegendreBounds
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.OrdGeOfLgSumEqLinear
section
open ReciprocityTheory.PGsh

namespace GlobalTheory.ExpWeight

open MvPowerSeries

variable {C : Type} [Field C] {M : ℕ}

def OrdBelow (v : AddValuation C (WithTop ℝ)) (ρ : ℝ) (D : ℕ) (g : MvPowerSeries (Fin M) C)
    (r : ℝ) : Prop :=
  ∀ α : Fin M →₀ ℕ, Finsupp.degree α < D →
    (((r - ρ * (Finsupp.degree α : ℕ) : ℝ)) : WithTop ℝ) ≤ v (coeff α g)

theorem OrdBelow.mul {v : AddValuation C (WithTop ℝ)} {ρ : ℝ} {D : ℕ}
    {g h : MvPowerSeries (Fin M) C} {r s : ℝ} (hg0 : constantCoeff g = 0)
    (hh0 : constantCoeff h = 0) (hg : OrdBelow v ρ D g r) (hh : OrdBelow v ρ D h s) :
    OrdBelow v ρ (D + 1) (g * h) (r + s) := by
  classical
  intro α hα
  rw [coeff_mul]
  refine v.map_le_sum fun p hp => ?_
  have hp' : p.1 + p.2 = α := by simpa using hp
  by_cases h1 : p.1 = 0
  · rw [h1, coeff_zero_eq_constantCoeff_apply, hg0, zero_mul, v.map_zero]; exact le_top
  by_cases h2 : p.2 = 0
  · rw [h2, coeff_zero_eq_constantCoeff_apply, hh0, mul_zero, v.map_zero]; exact le_top
  have hd : Finsupp.degree p.1 + Finsupp.degree p.2 = Finsupp.degree α := by
    rw [← hp', map_add (f := _)]
  have d1 : Finsupp.degree p.1 ≠ 0 := fun e => h1 ((Finsupp.degree_eq_zero_iff _).1 e)
  have d2 : Finsupp.degree p.2 ≠ 0 := fun e => h2 ((Finsupp.degree_eq_zero_iff _).1 e)
  rw [v.map_mul]
  refine le_trans (le_of_eq ?_) (add_le_add (hg p.1 (by omega)) (hh p.2 (by omega)))
  rw [← WithTop.coe_add, ← hd]
  congr 1
  push_cast
  ring

theorem OrdBelow.pow_succ {v : AddValuation C (WithTop ℝ)} {ρ : ℝ} {D : ℕ}
    {g : MvPowerSeries (Fin M) C} {r : ℝ} (hg0 : constantCoeff g = 0)
    (hg : OrdBelow v ρ D g r) (k : ℕ) :
    OrdBelow v ρ D (g ^ (k + 1)) (((k + 1 : ℕ) : ℝ) * r) := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
    have h := OrdBelow.mul (by simp [hg0]) hg0 ih hg
    intro α hα
    have h' := h α (by omega)
    rw [_root_.pow_succ g (k + 1)]
    refine le_trans (le_of_eq ?_) h'
    congr 1
    push_cast
    ring

theorem OrdBelow.pow {v : AddValuation C (WithTop ℝ)} {ρ : ℝ} {D : ℕ}
    {g : MvPowerSeries (Fin M) C} {r : ℝ} (hg0 : constantCoeff g = 0)
    (hg : OrdBelow v ρ D g r) {N : ℕ} (hN : 2 ≤ N) :
    OrdBelow v ρ (D + 1) (g ^ N) ((N : ℝ) * r) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 + 1 := ⟨N - 2, by omega⟩
  have h := OrdBelow.mul (by simp [hg0]) hg0 (hg.pow_succ hg0 k) hg
  rw [_root_.pow_succ g (k + 1)]
  convert h using 1
  push_cast
  ring

theorem ordGe_of_lgSum_eq_linear :
  (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → ∀ (d M : ℕ) (al : Fin d → ℕ → Fin d → C) (z : Fin d → Fin M → C) (t : Fin d → MvPowerSeries (Fin M) C),
    (∀ c e, al c 0 e = if c = e then 1 else 0) → (∀ c (n : ℕ) e, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (al c n e)) → (∀ c j, 0 ≤ v (z c j)) →
    (∀ c, MvPowerSeries.constantCoeff (t c) = 0) → (∀ e, lgSum l al t e = ∑ j, MvPowerSeries.C (z e j) * MvPowerSeries.X j) →
    ∀ c, OrdGe v (fun _ => 1 / ((l : ℝ) - 1)) (t c) (1 / ((l : ℝ) - 1))) := by
  intro C _ _ v l hl _ d M al z t h0 hal hz ht hlg
  classical
  set ρ : ℝ := 1 / ((l : ℝ) - 1) with hρ
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have hρ1 : ρ * ((l : ℝ) - 1) = 1 := by
    rw [hρ]; field_simp [show (l : ℝ) - 1 ≠ 0 by linarith]
  have hρ0 : 0 < ρ := by rw [hρ]; apply one_div_pos.2; linarith
  have key : ∀ D : ℕ, ∀ c, OrdBelow v ρ D (t c) ρ := by
    intro D
    induction D with
    | zero => intro c α hα; omega
    | succ D ih =>
      intro e α hα
      have h1 : coeff α (lgSum l al t e) = coeff α (∑ j, MvPowerSeries.C (z e j) * MvPowerSeries.X j) := by
        rw [hlg e]
      have h2 : coeff α (lgSum l al t e) =
          ∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, al a n e * coeff α (t a ^ (l ^ n)) := rfl
      rw [h2, Finset.sum_range_succ'] at h1
      have h3 : ∑ a, al a 0 e * coeff α (t a ^ (l ^ 0)) = coeff α (t e) := by
        simp [h0]
      rw [h3] at h1
      rw [eq_sub_of_add_eq' h1]
      refine v.map_le_sub ?_ ?_
      · rw [map_sum]
        refine v.map_le_sum fun j _ => ?_
        rw [coeff_C_mul, coeff_X]
        split_ifs with hj
        · rw [hj, mul_one]
          simpa using hz e j
        · rw [mul_zero, v.map_zero]; exact le_top
      · refine v.map_le_sum fun n _ => v.map_le_sum fun a _ => ?_
        have hN : 2 ≤ l ^ (n + 1) := le_trans hl.two_le (Nat.le_self_pow (by omega) l)
        have h4 := (ih a).pow (ht a) hN α hα
        rw [v.map_mul]
        refine le_trans ?_ (add_le_add (hal a (n + 1) e) h4)
        rw [← WithTop.coe_add, WithTop.coe_le_coe]
        have hb := one_add_mul_sub_le_pow (a := (l : ℝ)) (by linarith) (n + 1)
        have hb' := mul_le_mul_of_nonneg_left hb hρ0.le
        push_cast at hb' ⊢
        have : ρ * (1 + ((n : ℝ) + 1) * (l - 1)) = ρ + (n + 1) := by
          linear_combination ((n : ℝ) + 1) * hρ1
        linarith
  intro c α
  have h := key (Finsupp.degree α + 1) c α (by omega)
  refine le_trans (le_of_eq ?_) h
  congr 2
  rw [Finsupp.degree_eq_sum, ← Finset.mul_sum]
  push_cast
  rfl

end GlobalTheory.ExpWeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PsWeightCalculus
section
open ReciprocityTheory.PGsh

namespace GlobalTheory

theorem psWeight_mul {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {σ : Type}
    [DecidableEq σ] (ρ : σ → ℝ) (g g' : MvPowerSeries σ C) (r r' : ℝ)
    (h : ∀ α, (((r) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α g))
    (h' : ∀ α, (((r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α g')) :
    ∀ α, (((r + r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α (g * g')) := by
  intro α
  rw [MvPowerSeries.coeff_mul]
  refine AddValuation.map_le_sum v ?_
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [AddValuation.map_mul]
  have hs : α.sum (fun j e => ρ j * (e : ℝ)) =
      p.1.sum (fun j e => ρ j * (e : ℝ)) + p.2.sum (fun j e => ρ j * (e : ℝ)) := by
    rw [← hp]
    exact Finsupp.sum_add_index' (fun j => by simp) (fun j a b => by push_cast; ring)
  calc (((r + r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      = (((r - p.1.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
        + ((r' - p.2.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)) := by
        rw [← WithTop.coe_add, hs]
        congr 1
        ring
    _ ≤ v (MvPowerSeries.coeff p.1 g) + v (MvPowerSeries.coeff p.2 g') :=
        add_le_add (h p.1) (h' p.2)

theorem psWeight_add {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {σ : Type}
    (ρ : σ → ℝ) (g g' : MvPowerSeries σ C) (r r' : ℝ)
    (h : ∀ α, (((r) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α g))
    (h' : ∀ α, (((r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α g')) :
    ∀ α, (((min r r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α (g + g')) := by
  intro α
  have hc : MvPowerSeries.coeff α (g + g') =
      MvPowerSeries.coeff α g + MvPowerSeries.coeff α g' := map_add _ _ _
  rw [hc]
  refine AddValuation.map_le_add v ?_ ?_
  · exact le_trans (WithTop.coe_le_coe.mpr (sub_le_sub_right (min_le_left r r') _)) (h α)
  · exact le_trans (WithTop.coe_le_coe.mpr (sub_le_sub_right (min_le_right r r') _)) (h' α)

theorem psWeight_pow {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {σ : Type}
    [DecidableEq σ] (ρ : σ → ℝ) (g : MvPowerSeries σ C) (r : ℝ)
    (h : ∀ α, (((r) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α g)) (N : ℕ) :
    ∀ α, (((N * r) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ)
      ≤ v (MvPowerSeries.coeff α (g ^ N)) := by
  induction N with
  | zero =>
    intro α
    rw [pow_zero, MvPowerSeries.coeff_one]
    split_ifs with hα
    · subst hα
      simp
    · rw [AddValuation.map_zero]
      exact le_top
  | succ n ih =>
    intro α
    rw [pow_succ]
    have e : ((n + 1 : ℕ) : ℝ) * r = n * r + r := by push_cast; ring
    rw [e]
    exact psWeight_mul v ρ (g ^ n) g (n * r) r ih h α

theorem psWeight_calculus :
  (∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (σ : Type) [Fintype σ] [DecidableEq σ] (ρ : σ → ℝ) (g g' : MvPowerSeries σ C) (r r' : ℝ),
    (∀ α, (((r) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (g))) → ((∀ α, (((r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (g'))) → (∀ α, (((r + r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (g * g'))) ∧ (∀ α, (((min r r') - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (g + g')))) ∧ ∀ N : ℕ, (∀ α, (((N * r) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (g ^ N)))) := by
  intro C _ v σ _ _ ρ g g' r r' h
  exact ⟨fun h' => ⟨psWeight_mul v ρ g g' r r' h h', psWeight_add v ρ g g' r r' h h'⟩,
    fun N => psWeight_pow v ρ g r h N⟩

end GlobalTheory
end

