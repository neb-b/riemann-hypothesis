module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumIntervalIntegralLeOfSpaced
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory

theorem gallagher_interval (f f' h : ℝ → ℝ) (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : Continuous f') (hh : Continuous h) (hb : ∀ t, |f' t| ≤ h t) (x δ : ℝ) (hδ : 0 < δ) :
    f x ≤ ∫ t in x..(x + δ), (f t / δ + h t) := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun t => (hf t).continuousAt
  have hF : ∀ t, HasDerivAt (fun t => (t - x - δ) / δ * f t) (f t / δ + (t - x - δ) / δ * f' t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (t - x - δ) / δ) (1 / δ) t :=
      (((hasDerivAt_id t).sub_const x).sub_const δ).div_const δ
    exact (h1.fun_mul (hf t)).congr_deriv (by ring)
  have hc : Continuous fun t => f t / δ + (t - x - δ) / δ * f' t := by fun_prop
  have h2 := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := x) (b := x + δ)
    (fun t _ => hF t) (hc.intervalIntegrable _ _)
  have h3 : (x + δ - x - δ) / δ * f (x + δ) - (x - x - δ) / δ * f x = f x := by
    field_simp
    ring
  rw [h3] at h2
  rw [← h2]
  apply intervalIntegral.integral_mono_on (by linarith) (hc.intervalIntegrable _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  intro t ht
  have h4 : |(t - x - δ) / δ| ≤ 1 := by
    rw [abs_div, abs_of_pos hδ, div_le_one hδ, abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have h5 : (t - x - δ) / δ * f' t ≤ h t := by
    calc _ ≤ |(t - x - δ) / δ * f' t| := le_abs_self _
      _ = |(t - x - δ) / δ| * |f' t| := abs_mul _ _
      _ ≤ 1 * h t := mul_le_mul h4 (hb t) (abs_nonneg _) zero_le_one
      _ = h t := one_mul _
  linarith

theorem integral_exp_two_pi_sub (n m : ℕ) (y : ℝ) :
    ∫ t in y..(y + 1), Complex.exp (2 * Real.pi * I * ((n : ℂ) - m) * t) = if n = m then 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · have hc : (2 * Real.pi * I * ((n : ℂ) - m)) ≠ 0 := by
      have : (n : ℂ) - m ≠ 0 := sub_ne_zero.2 (by exact_mod_cast h)
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [this, hpi, I_ne_zero]
    rw [integral_exp_mul_complex hc]
    have : Complex.exp (2 * Real.pi * I * ((n : ℂ) - m) * ((y + 1 : ℝ) : ℂ))
        = Complex.exp (2 * Real.pi * I * ((n : ℂ) - m) * (y : ℂ)) := by
      have h1 := Complex.exp_int_mul_two_pi_mul_I ((n : ℤ) - m)
      rw [show 2 * Real.pi * I * ((n : ℂ) - m) * ((y + 1 : ℝ) : ℂ)
        = 2 * Real.pi * I * ((n : ℂ) - m) * (y : ℂ) + (((n : ℤ) - m : ℤ) : ℂ) * (2 * Real.pi * I) by
          push_cast; ring, Complex.exp_add, h1, mul_one]
    rw [this]; simp

theorem norm_expSum_shift (s : Finset ℕ) (b : ℕ → ℂ) (c t : ℝ) :
    ‖∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * ((n : ℂ) - c) * t)‖
      = ‖∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * t)‖ := by
  have : ∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * ((n : ℂ) - c) * t)
      = Complex.exp (((-(2 * Real.pi * c * t) : ℝ) : ℂ) * I) *
        ∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * t) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast; ring
  rw [this, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem integral_norm_sq_expSum (s : Finset ℕ) (b : ℕ → ℂ) (y : ℝ) :
    ∫ t in y..(y + 1), ‖∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * t)‖ ^ 2
      = ∑ n ∈ s, ‖b n‖ ^ 2 := by
  have key : ∀ t : ℝ, ((‖∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * t)‖ ^ 2 : ℝ) : ℂ)
      = ∑ n ∈ s, ∑ m ∈ s, b n * (starRingEnd ℂ) (b m) *
        Complex.exp (2 * Real.pi * I * ((n : ℂ) - m) * t) := by
    intro t
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, ← Complex.exp_conj]
    simp only [map_mul, conj_ofReal, conj_I, map_natCast, map_ofNat]
    rw [mul_mul_mul_comm, ← Complex.exp_add]
    congr 2
    ring
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [key]
  rw [intervalIntegral.integral_finsetSum (fun n _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  push_cast
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [intervalIntegral.integral_finsetSum (fun n _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp_rw [intervalIntegral.integral_const_mul, integral_exp_two_pi_sub]
  simp [hn, Complex.mul_conj']

theorem sum_intervalIntegral_le_of_spaced (g : ℝ → ℝ) (hg : Continuous g) (h0 : ∀ t, 0 ≤ g t)
    (S : Finset ℝ) (p : ℝ → ℝ) (δ y : ℝ) (hδ : 0 < δ)
    (h1 : ∀ x ∈ S, y ≤ p x) (h2 : ∀ x ∈ S, p x + δ ≤ y + 1)
    (h3 : ∀ x ∈ S, ∀ z ∈ S, x ≠ z → δ ≤ |p x - p z|) :
    ∑ x ∈ S, ∫ t in (p x)..(p x + δ), g t ≤ ∫ t in y..(y + 1), g t := by
  have hi : ∀ u v : ℝ, IntegrableOn g (Set.Ioc u v) := fun u v =>
    (hg.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  rw [intervalIntegral.integral_of_le (by linarith : y ≤ y + 1)]
  rw [Finset.sum_congr rfl fun x _ =>
    intervalIntegral.integral_of_le (by linarith : p x ≤ p x + δ)]
  rw [← integral_biUnion_finset S (s := fun x => Set.Ioc (p x) (p x + δ))
    (fun _ _ => measurableSet_Ioc) ?_ (fun x _ => hi _ _)]
  · apply setIntegral_mono_set (hi _ _) (Filter.Eventually.of_forall h0)
    apply Filter.Eventually.of_forall
    intro t ht
    simp only [Set.mem_iUnion] at ht
    obtain ⟨x, hx, ht⟩ := ht
    exact ⟨lt_of_le_of_lt (h1 x hx) ht.1, ht.2.trans (h2 x hx)⟩
  · intro x hx z hz hxz
    have := h3 x hx z hz hxz
    rw [Function.onFun, Set.disjoint_left]
    intro t ht ht'
    have : |p x - p z| < δ := by
      rw [abs_lt]; constructor <;> linarith [ht.1, ht.2, ht'.1, ht'.2]
    linarith

theorem expSum_sub_int (s : Finset ℕ) (b : ℕ → ℂ) (x : ℝ) (k : ℤ) :
    ∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * ((x - k : ℝ) : ℂ))
      = ∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * x) := by
  refine Finset.sum_congr rfl fun n _ => ?_
  have h1 := Complex.exp_int_mul_two_pi_mul_I (-(n * k))
  rw [show 2 * Real.pi * I * (n : ℂ) * ((x - k : ℝ) : ℂ)
    = 2 * Real.pi * I * n * x + ((-(n * k) : ℤ) : ℂ) * (2 * Real.pi * I) by
      push_cast; ring, Complex.exp_add, h1, mul_one]

theorem additive_large_sieve : ∀ (M N : ℕ) (a : ℕ → ℂ) (S : Finset ℝ) (δ : ℝ), 0 < δ → δ ≤ 1 → (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∀ k : ℤ, δ ≤ |x - y - k|) → ∑ x ∈ S, ‖∑ n ∈ Finset.Ioc M (M + N), a n * Complex.exp (2 * Real.pi * I * n * x)‖ ^ 2 ≤ (1 / δ + 2 * Real.pi * N) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  intro M N a S δ hδ hδ1 hS
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rcases S.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
  · simp only [Finset.sum_empty]; positivity
  set s := Finset.Ioc M (M + N) with hs
  set c : ℝ := M + N / 2 with hc
  set L : ℝ := Real.pi * N with hL
  have hL0 : 0 < L := by positivity
  set b : ℕ → ℂ := fun n => a n * (2 * Real.pi * I * ((n : ℂ) - c)) with hb
  set T : ℝ → ℂ := fun t => ∑ n ∈ s, a n * Complex.exp (2 * Real.pi * I * ((n : ℂ) - c) * t) with hT
  set T' : ℝ → ℂ := fun t => ∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * ((n : ℂ) - c) * t) with hT'
  have hd : ∀ t, HasDerivAt T (T' t) t := by
    intro t
    apply HasDerivAt.fun_sum
    intro n _
    have h1 : HasDerivAt (fun t : ℝ => 2 * Real.pi * I * ((n : ℂ) - c) * (t : ℂ))
        (2 * Real.pi * I * ((n : ℂ) - c)) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (2 * Real.pi * I * ((n : ℂ) - c))
    exact ((h1.cexp).const_mul (a n)).congr_deriv (by simp only [hb]; ring)
  have hTc : Continuous T := by simp only [hT]; fun_prop
  have hTc' : Continuous T' := by simp only [hT']; fun_prop
  have hG : ∀ x, ‖T x‖ ^ 2 ≤ ∫ t in x..(x + δ), (‖T t‖ ^ 2 / δ + (L * ‖T t‖ ^ 2 + ‖T' t‖ ^ 2 / L)) := by
    intro x
    refine gallagher_interval (fun t => ‖T t‖ ^ 2) (fun t => 2 * inner ℝ (T t) (T' t))
      (fun t => L * ‖T t‖ ^ 2 + ‖T' t‖ ^ 2 / L) (fun t => (hd t).norm_sq) (by fun_prop) (by fun_prop) ?_ x δ hδ
    intro t
    have h1 := abs_real_inner_le_norm (T t) (T' t)
    rw [abs_mul, abs_two]
    have h2 : L * ‖T t‖ ^ 2 + ‖T' t‖ ^ 2 / L - 2 * (‖T t‖ * ‖T' t‖)
        = (L * ‖T t‖ - ‖T' t‖) ^ 2 / L := by field_simp; ring
    have h3 : 0 ≤ (L * ‖T t‖ - ‖T' t‖) ^ 2 / L := by positivity
    linarith
  set p : ℝ → ℝ := fun x => x - (⌊x - y⌋ : ℤ) with hp
  have hsum := sum_intervalIntegral_le_of_spaced
    (fun t => ‖T t‖ ^ 2 / δ + (L * ‖T t‖ ^ 2 + ‖T' t‖ ^ 2 / L)) (by fun_prop) (fun t => by positivity)
    S p δ y hδ (fun x _ => by simp only [hp]; linarith [Int.floor_le (x - y)]) ?_ ?_
  · have e1 : ∫ t in y..(y + 1), ‖T t‖ ^ 2 = ∑ n ∈ s, ‖a n‖ ^ 2 := by
      simp only [hT, norm_expSum_shift]; exact integral_norm_sq_expSum s a y
    have e2 : ∫ t in y..(y + 1), ‖T' t‖ ^ 2 = ∑ n ∈ s, ‖b n‖ ^ 2 := by
      simp only [hT', norm_expSum_shift]; exact integral_norm_sq_expSum s b y
    have e3 : ∑ n ∈ s, ‖b n‖ ^ 2 ≤ L ^ 2 * ∑ n ∈ s, ‖a n‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun n hn => ?_
      rw [hs, Finset.mem_Ioc] at hn
      have hn1 : (M : ℝ) < n := by exact_mod_cast hn.1
      have hn2 : (n : ℝ) ≤ M + N := by exact_mod_cast hn.2
      have h4 : ‖(n : ℂ) - c‖ ≤ N / 2 := by
        rw [show (n : ℂ) - c = ((n - c : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_le]
        constructor <;> linarith
      have h5 : ‖b n‖ ≤ L * ‖a n‖ := by
        simp only [hb, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos, Complex.norm_ofNat]
        calc ‖a n‖ * (2 * Real.pi * 1 * ‖(n : ℂ) - c‖) ≤ ‖a n‖ * (2 * Real.pi * 1 * (N / 2)) := by
              gcongr
          _ = L * ‖a n‖ := by rw [hL]; ring
      rw [← mul_pow]
      gcongr
    have e4 : ∫ t in y..(y + 1), (‖T t‖ ^ 2 / δ + (L * ‖T t‖ ^ 2 + ‖T' t‖ ^ 2 / L))
        = (∑ n ∈ s, ‖a n‖ ^ 2) / δ + (L * ∑ n ∈ s, ‖a n‖ ^ 2 + (∑ n ∈ s, ‖b n‖ ^ 2) / L) := by
      rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _),
        intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_div,
        intervalIntegral.integral_div, intervalIntegral.integral_const_mul, e1, e2]
    have e5 : (∑ n ∈ s, ‖b n‖ ^ 2) / L ≤ L * ∑ n ∈ s, ‖a n‖ ^ 2 := by
      rw [div_le_iff₀ hL0]; nlinarith
    calc _ = ∑ x ∈ S, ‖T (p x)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [hT, hp]
          rw [norm_expSum_shift, expSum_sub_int]
      _ ≤ _ := Finset.sum_le_sum fun x _ => hG (p x)
      _ ≤ _ := hsum
      _ = _ := e4
      _ ≤ (∑ n ∈ s, ‖a n‖ ^ 2) / δ + (L * ∑ n ∈ s, ‖a n‖ ^ 2 + L * ∑ n ∈ s, ‖a n‖ ^ 2) := by
          linarith
      _ = _ := by rw [hL]; ring
  · intro x hx
    simp only [hp]
    by_cases hxy : x = y
    · subst hxy; simp [hδ1]
    · have h1 := hS x hx y hy hxy (⌊x - y⌋ + 1)
      have h2 := Int.lt_floor_add_one (x - y)
      push_cast at h1
      rw [abs_of_neg (by linarith)] at h1
      linarith
  · intro x hx z hz hxz
    have h1 := hS x hx z hz hxz (⌊x - y⌋ - ⌊z - y⌋)
    simp only [hp]
    convert h1 using 2
    push_cast; ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumPiFinsetFinSuccCons
section
namespace GlobalTheory

open Finset

theorem sum_piFinset_fin_succ_cons {α K : Type} [AddCommMonoid K] (n : ℕ) (S : Finset α)
    (F : (Fin (n + 1) → α) → K) :
    ∑ t ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S), F t =
      ∑ a ∈ S, ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S), F (Fin.cons a t) := by
  rw [← Finset.sum_product' S (Fintype.piFinset (fun _ : Fin n => S))
    (fun a t => F (Fin.cons a t))]
  symm
  refine Finset.sum_equiv (Fin.consEquiv (fun _ => α)) ?_ ?_
  · rintro ⟨a, t⟩
    simp [Fin.forall_fin_succ, Fin.consEquiv]
  · rintro ⟨a, t⟩ _
    rfl

theorem weighted_sum_piFinset_fin {α K : Type} [CommRing K] (G : (α → K) → Prop)
    (S S' : Finset α) (w w' : K)
    (h : ∀ f, G f → w * ∑ a ∈ S, f a = w' * ∑ a ∈ S', f a) (n : ℕ) :
    ∀ F : (Fin n → α) → K, (∀ (t : Fin n → α) (i : Fin n), G (fun a => F (Function.update t i a))) →
      w ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S), F t =
        w' ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S'), F t := by
  induction n with
  | zero => intro F _; simp
  | succ n ih =>
    intro F hF
    have h1 : ∀ a : α, w ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S), F (Fin.cons a t) =
        w' ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S'), F (Fin.cons a t) := by
      intro a
      refine ih (fun t => F (Fin.cons a t)) ?_
      intro t i
      have := hF (Fin.cons a t) i.succ
      simpa only [← Fin.cons_update] using this
    have h2 : ∀ t : Fin n → α, w * ∑ a ∈ S, F (Fin.cons a t) =
        w' * ∑ a ∈ S', F (Fin.cons a t) := by
      intro t
      rcases isEmpty_or_nonempty α with hα | ⟨⟨a0⟩⟩
      · simp [Finset.eq_empty_of_isEmpty S, Finset.eq_empty_of_isEmpty S']
      · refine h _ ?_
        have := hF (Fin.cons a0 t) 0
        simpa only [Fin.update_cons_zero] using this
    rw [sum_piFinset_fin_succ_cons, sum_piFinset_fin_succ_cons]
    calc w ^ (n + 1) * ∑ a ∈ S, ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S), F (Fin.cons a t)
        = w * ∑ a ∈ S, w ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S), F (Fin.cons a t) := by
          rw [← Finset.mul_sum]; ring
      _ = w * ∑ a ∈ S, w' ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S'), F (Fin.cons a t) := by
          simp only [h1]
      _ = w' ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S'), w * ∑ a ∈ S, F (Fin.cons a t) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]; ring
      _ = w' ^ n * ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S'), w' * ∑ a ∈ S', F (Fin.cons a t) := by
          simp only [h2]
      _ = _ := by
          rw [← Finset.mul_sum, Finset.sum_comm]; ring

theorem weighted_sum_piFinset : ∀ (ι α K : Type) [Fintype ι] [DecidableEq ι] [CommRing K] (G : (α → K) → Prop) (S S' : Finset α) (w w' : K), (∀ f, G f → w * ∑ a ∈ S, f a = w' * ∑ a ∈ S', f a) → ∀ F : (ι → α) → K, (∀ (t : ι → α) (i : ι), G (fun a => F (Function.update t i a))) → w ^ Fintype.card ι * ∑ t ∈ Fintype.piFinset (fun _ : ι => S), F t = w' ^ Fintype.card ι * ∑ t ∈ Fintype.piFinset (fun _ : ι => S'), F t := by
  intro ι α K _ _ _ G S S' w w' h F hF
  let e := Fintype.equivFin ι
  have key : ∀ T : Finset α, ∑ t ∈ Fintype.piFinset (fun _ : ι => T), F t =
      ∑ t ∈ Fintype.piFinset (fun _ : Fin (Fintype.card ι) => T), F (t ∘ e) := by
    intro T
    symm
    refine Finset.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl α)) ?_ ?_
    · intro t
      simp only [Fintype.mem_piFinset, Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.coe_refl,
        Function.comp, id]
      exact ⟨fun H i => H _, fun H i => by simpa using H (e.symm i)⟩
    · intro t _
      rfl
  rw [key, key]
  refine weighted_sum_piFinset_fin G S S' w w' h _ (fun t => F (t ∘ e)) ?_
  intro t i
  simp only [Function.update_comp_equiv]
  exact hF _ _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SummableExpNegMulSq
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.ShiftedTheta

theorem hasSum_int_inv_sq :
    HasSum (fun n : ℤ => (1 : ℝ) / (n : ℝ) ^ 2) (Real.pi ^ 2 / 3) := by
  have h := HasSum.of_nat_of_neg (f := fun n : ℤ => (1 : ℝ) / (n : ℝ) ^ 2)
    (show HasSum _ (Real.pi ^ 2 / 6) by simpa using hasSum_zeta_two)
    (show HasSum _ (Real.pi ^ 2 / 6) by simpa using hasSum_zeta_two)
  have e : Real.pi ^ 2 / 6 + Real.pi ^ 2 / 6 - 1 / ((0 : ℤ) : ℝ) ^ 2 = Real.pi ^ 2 / 3 := by
    simp
    ring
  exact e ▸ h

theorem exp_neg_le {y : ℝ} (hy : 0 < y) : Real.exp (-y) ≤ 2 / y ^ 2 := by
  have h := Real.pow_div_factorial_le_exp y hy.le 2
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  norm_num [Nat.factorial] at h
  linarith

theorem exp_neg_mul_sq_le {c : ℝ} (hc : 0 < c) {n : ℤ} (hn : n ≠ 0) :
    Real.exp (-(c * (n : ℝ) ^ 2)) ≤ 2 / c ^ 2 * (1 / (n : ℝ) ^ 2) := by
  have h0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ n ^ 2 := by
      have := sq_pos_of_ne_zero hn
      omega
    exact_mod_cast this
  refine (exp_neg_le (by positivity)).trans ?_
  rw [div_mul_div_comm, mul_one, mul_pow]
  refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  nlinarith

theorem summable_exp_neg_mul_sq {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℤ => Real.exp (-(c * (n : ℝ) ^ 2)) := by
  refine Summable.of_norm_bounded_eventually (hasSum_int_inv_sq.summable.mul_left (2 / c ^ 2)) ?_
  filter_upwards [eventually_cofinite_ne (0 : ℤ)] with n hn
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact exp_neg_mul_sq_le hc hn

theorem summable_shifted {s : ℝ} (θ : ℝ) (hs : 0 < s) :
    Summable fun m : ℤ => Real.exp (-(s * (m + θ) ^ 2)) := by
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun m => ?_)
    ((summable_exp_neg_mul_sq (half_pos hs)).mul_left (Real.exp (s * θ ^ 2)))
  rw [← Real.exp_add, Real.exp_le_exp]
  nlinarith [mul_nonneg hs.le (sq_nonneg ((m : ℝ) + 2 * θ))]

theorem poisson {s : ℝ} (θ : ℝ) (hs : 0 < s) :
    ((∑' m : ℤ, Real.exp (-(s * (m + θ) ^ 2)) : ℝ) : ℂ) =
      (Real.sqrt (Real.pi / s) : ℂ) * ∑' n : ℤ,
        cexp (-(Real.pi : ℂ) * ((Real.pi / s : ℝ) : ℂ) * n ^ 2 + 2 * Real.pi * (-I * θ) * n) := by
  have ha : 0 < Real.pi / s := div_pos Real.pi_pos hs
  rw [Complex.tsum_exp_neg_quadratic (by rwa [ofReal_re])]
  have h1 : ((Real.pi / s : ℝ) : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt (Real.pi / s) : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow ha.le]
    norm_num
  have h2 : (Real.sqrt (Real.pi / s) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 ha).ne'
  rw [h1, ← mul_assoc, mul_one_div_cancel h2, one_mul, ofReal_tsum]
  refine tsum_congr fun n => ?_
  have h3 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h4 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have h5 : I * (-I * θ) = θ := by
    rw [← mul_assoc, mul_neg, I_mul_I]; ring
  rw [h5]
  push_cast
  congr 1
  field_simp

theorem shifted_theta_bound : ∀ s θ : ℝ, 0 < s → Summable (fun m : ℤ => Real.exp (-(s * (m + θ) ^ 2))) ∧ |∑' m : ℤ, Real.exp (-(s * (m + θ) ^ 2)) - Real.sqrt (Real.pi / s)| ≤ Real.sqrt (Real.pi / s) * s ^ 2 := by
  intro s θ hs
  refine ⟨summable_shifted θ hs, ?_⟩
  set g : ℤ → ℂ := fun n =>
    cexp (-(Real.pi : ℂ) * ((Real.pi / s : ℝ) : ℂ) * n ^ 2 + 2 * Real.pi * (-I * θ) * n) with hg
  have hpi := Real.pi_pos
  have hc : 0 < Real.pi ^ 2 / s := by positivity
  have hn : ∀ n : ℤ, ‖g n‖ = Real.exp (-(Real.pi ^ 2 / s * (n : ℝ) ^ 2)) := by
    intro n
    have e : -(Real.pi : ℂ) * ((Real.pi / s : ℝ) : ℂ) * n ^ 2 + 2 * Real.pi * (-I * θ) * n
        = ((-(Real.pi ^ 2 / s * (n : ℝ) ^ 2) : ℝ) : ℂ) + ((-(2 * Real.pi * θ * n) : ℝ) : ℂ) * I := by
      push_cast
      ring
    simp only [hg]
    rw [e, Complex.exp_add, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_exp_ofReal]
  have hsum : Summable g :=
    Summable.of_norm_bounded (summable_exp_neg_mul_sq hc) fun n => (hn n).le
  have hb : ‖∑' n : ℤ, if n = 0 then 0 else g n‖ ≤ 2 / (Real.pi ^ 2 / s) ^ 2 * (Real.pi ^ 2 / 3) := by
    refine tsum_of_norm_bounded (hasSum_int_inv_sq.mul_left _) fun n => ?_
    split_ifs with h
    · rw [norm_zero]; positivity
    · rw [hn]; exact exp_neg_mul_sq_le hc h
  have hb2 : 2 / (Real.pi ^ 2 / s) ^ 2 * (Real.pi ^ 2 / 3) ≤ s ^ 2 := by
    have e : 2 / (Real.pi ^ 2 / s) ^ 2 * (Real.pi ^ 2 / 3) = s ^ 2 * (2 / (3 * Real.pi ^ 2)) := by
      field_simp
    rw [e]
    refine mul_le_of_le_one_right (sq_nonneg _) ?_
    rw [div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hg0 : g 0 = 1 := by simp [hg]
  have hp := poisson θ hs
  change _ = _ * ∑' n, g n at hp
  rw [hsum.tsum_eq_add_tsum_ite 0, hg0] at hp
  rw [← Real.norm_eq_abs, ← Complex.norm_real, ofReal_sub, hp, mul_add, mul_one,
    add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (hb.trans hb2) (Real.sqrt_nonneg _)

end GlobalTheory.ShiftedTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ZetaEqSubIntegralFract
section
namespace GlobalTheory.ZetaFractionalIntegral

open MeasureTheory Set Filter Asymptotics

lemma zeta_eq_mul_integral_floor {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s * ∫ t in Set.Ioi (1 : ℝ), ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  have hO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (fun _ : ℕ ↦ (1 : ℝ)) k) =O[atTop] fun n ↦ (n : ℝ) ^ (1 : ℝ) := by
    refine Asymptotics.isBigO_of_le _ fun n ↦ ?_
    simp
  have key := LSeries_eq_mul_integral_of_nonneg (fun _ ↦ (1 : ℝ)) zero_le_one hs hO (fun _ ↦ zero_le_one)
  have e1 : LSeries (fun n : ℕ ↦ (((fun _ : ℕ ↦ (1 : ℝ)) n : ℝ) : ℂ)) s = riemannZeta s := by
    rw [← LSeries_one_eq_riemannZeta hs]
    congr 1
  rw [← e1, key]
  congr 2
  funext t
  simp

lemma integrableOn_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Set.Ioi 1) := integrableOn_Ioi_cpow_of_lt (by simp only [Complex.neg_re]; linarith) one_pos

lemma integrableOn_fract_mul {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) := by
  have hg : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Set.Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp only [Complex.neg_re, Complex.add_re, Complex.one_re]; linarith) one_pos
  refine MeasureTheory.Integrable.mono hg (((Complex.measurable_ofReal.comp measurable_fract).aestronglyMeasurable).mul
    hg.aestronglyMeasurable) (Filter.Eventually.of_forall fun t => ?_)
  rw [norm_mul]
  have h0 := Int.fract_nonneg t
  have h1 := Int.fract_lt_one t
  have : ‖((Int.fract t : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
    exact h1.le
  calc ‖((Int.fract t : ℝ) : ℂ)‖ * ‖(t : ℂ) ^ (-(s + 1))‖ ≤ 1 * ‖(t : ℂ) ^ (-(s + 1))‖ :=
        mul_le_mul_of_nonneg_right this (norm_nonneg _)
    _ = ‖(t : ℂ) ^ (-(s + 1))‖ := one_mul _

theorem zeta_eq_sub_integral_fract :
    (let d1 : ℂ → ℂ := @(fun (s : ℂ) ↦ ∫ (t : ℝ) in Set.Ioi (1 : ℝ), (↑(Int.fract t) : ℂ) * (↑t : ℂ) ^ (-(s + (1 : ℂ)))); ∀ {s : ℂ}, (1 : ℝ) < Complex.re s → riemannZeta s = s / (s - (1 : ℂ)) - s * d1 s) := by
  intro d1 s hs
  simp only [d1]
  have hA := integrableOn_cpow_neg hs
  have hB := integrableOn_fract_mul hs
  have hsplit : ∫ t in Set.Ioi (1 : ℝ), ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      (∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s)) -
        ∫ t in Set.Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
    rw [← integral_sub hA hB]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
    have hfl : ((⌊t⌋₊ : ℕ) : ℝ) = t - Int.fract t := by
      rw [Int.self_sub_fract, natCast_floor_eq_intCast_floor ht0.le]
    have hpow : (t : ℂ) ^ (-s) = (t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
      rw [show -s = -(s + 1) + 1 by ring, Complex.cpow_add _ _ (by exact_mod_cast ht0.ne'), Complex.cpow_one,
        mul_comm]
    have hfl' : ((⌊t⌋₊ : ℕ) : ℂ) = (t : ℂ) - ((Int.fract t : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, hfl, Complex.ofReal_sub]
    rw [hpow, hfl']
    ring
  have hI : ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s) = 1 / (s - 1) := by
    rw [integral_Ioi_cpow_of_lt (by simp only [Complex.neg_re]; linarith) one_pos, Complex.ofReal_one,
      Complex.one_cpow, show -s + 1 = -(s - 1) by ring, div_neg, neg_div, neg_neg]
  rw [zeta_eq_mul_integral_floor hs, hsplit, hI]
  ring

end GlobalTheory.ZetaFractionalIntegral
end

