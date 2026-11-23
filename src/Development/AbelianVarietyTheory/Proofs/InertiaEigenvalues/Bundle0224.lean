module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0193

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormUnitPowSubOne
section
noncomputable section

open Filter Topology

namespace GlobalTheory.PadicLogUnits

variable {l : ℕ} [hl : Fact l.Prime]

def term (y : ℚ_[l]) (k : ℕ) : ℚ_[l] := (-1 : ℚ_[l]) ^ k * y ^ (k + 1) / ((k : ℚ_[l]) + 1)

def lg (x : ℚ_[l]) : ℚ_[l] := ∑' k : ℕ, term (x - 1) k

lemma inv_norm_succ_le (k : ℕ) : ‖((k : ℚ_[l]) + 1)‖⁻¹ ≤ 2 ^ k := by
  have h0 : ((k + 1 : ℕ) : ℚ_[l]) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have h1 : ((k : ℚ_[l]) + 1) = ((k + 1 : ℕ) : ℚ_[l]) := by push_cast; rfl
  rw [h1, Padic.norm_eq_zpow_neg_valuation h0, Padic.valuation_natCast, zpow_neg, inv_inv,
    zpow_natCast]
  have h2 : l ^ padicValNat l (k + 1) ≤ k + 1 := Nat.le_of_dvd (Nat.succ_pos k) (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
  rw [Nat.padicValNat_def] at h2
  have h3 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  exact_mod_cast h2.trans h3

lemma norm_pow_div_le {y : ℚ_[l]} (hy : ‖y‖ ≤ 1 / 3) (k : ℕ) :
    ‖y ^ (k + 1) / ((k : ℚ_[l]) + 1)‖ ≤ ‖y‖ * (2 / 3) ^ k := by
  rw [norm_div, norm_pow, div_eq_mul_inv, pow_succ']
  have h1 : ‖y‖ ^ k ≤ (1 / 3) ^ k := pow_le_pow_left₀ (norm_nonneg _) hy k
  calc ‖y‖ * ‖y‖ ^ k * ‖((k : ℚ_[l]) + 1)‖⁻¹ ≤ ‖y‖ * (1 / 3) ^ k * 2 ^ k := by
        gcongr
        exact inv_norm_succ_le k
    _ = ‖y‖ * (2 / 3) ^ k := by rw [mul_assoc, ← mul_pow]; norm_num

lemma norm_term_le {y : ℚ_[l]} (hy : ‖y‖ ≤ 1 / 3) (k : ℕ) :
    ‖term y k‖ ≤ ‖y‖ * (2 / 3) ^ k := by
  rw [term, mul_div_assoc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  exact norm_pow_div_le hy k

lemma summable_geo (c : ℝ) : Summable fun k : ℕ => c * (2 / 3 : ℝ) ^ k :=
  (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left c

lemma summable_term {y : ℚ_[l]} (hy : ‖y‖ ≤ 1 / 3) : Summable (term y) :=
  Summable.of_norm_bounded (summable_geo ‖y‖) (norm_term_le hy)

lemma norm_lg {x : ℚ_[l]} (hx : ‖x - 1‖ ≤ 1 / 3) : ‖lg x‖ = ‖x - 1‖ := by
  rcases eq_or_ne (x - 1) 0 with h | h
  · simp [lg, h, term]
  have hpos : 0 < ‖x - 1‖ := norm_pos_iff.mpr h
  rw [lg, (summable_term hx).tsum_eq_zero_add]
  have h0 : term (x - 1) 0 = x - 1 := by simp [term]
  have h1 : ‖∑' k : ℕ, term (x - 1) (k + 1)‖ ≤ ‖x - 1‖ * (2 / 3) := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun k => ?_
    refine (norm_term_le hx (k + 1)).trans ?_
    gcongr
    exact pow_le_of_le_one (by norm_num) (by norm_num) (Nat.succ_ne_zero k)
  have h2 : ‖∑' k : ℕ, term (x - 1) (k + 1)‖ < ‖x - 1‖ := by linarith
  rw [h0, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h2.ne', max_eq_left h2.le]

lemma desc_eval_neg_one (k : ℕ) :
    (descPochhammer ℚ_[l] k).eval (-1) = (-1) ^ k * (k.factorial : ℚ_[l]) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [descPochhammer_succ_eval, ih, Nat.factorial_succ]
    push_cast
    ring

lemma tendsto_pow_zero : Tendsto (fun n : ℕ => (l : ℚ_[l]) ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_norm_lt_one Padic.norm_p_lt_one

lemma tendsto_choose (k : ℕ) :
    Tendsto (fun n : ℕ => (((l ^ n - 1).choose k : ℕ) : ℚ_[l])) atTop (𝓝 ((-1) ^ k)) := by
  have hk : (k.factorial : ℚ_[l]) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have h1 : Tendsto (fun n : ℕ => (l : ℚ_[l]) ^ n - 1) atTop (𝓝 (-1)) := by
    simpa using (tendsto_pow_zero (l := l)).sub_const 1
  have h2 := (((descPochhammer ℚ_[l] k).continuous.tendsto (-1)).comp h1).div_const
    (k.factorial : ℚ_[l])
  rw [desc_eval_neg_one, mul_div_cancel_right₀ _ hk] at h2
  refine h2.congr fun n => ?_
  rw [Nat.cast_choose_eq_descPochhammer_div, Nat.cast_sub (Nat.one_le_pow _ _ hl.out.pos)]
  simp

lemma pow_sub_one_div (y : ℚ_[l]) (M : ℕ) :
    ((1 + y) ^ (M + 1) - 1) / ((M + 1 : ℕ) : ℚ_[l]) =
      ∑' k : ℕ, ((M.choose k : ℕ) : ℚ_[l]) * (y ^ (k + 1) / ((k : ℚ_[l]) + 1)) := by
  have h0 : ((M + 1 : ℕ) : ℚ_[l]) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero M
  rw [tsum_eq_sum (s := Finset.range (M + 1))
    (fun k hk => by rw [Nat.choose_eq_zero_of_lt (by simpa using hk)]; simp)]
  rw [add_comm 1 y, add_pow, Finset.sum_range_succ', div_eq_iff h0, Finset.sum_mul]
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one, add_sub_cancel_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : ((k : ℚ_[l]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have h := congrArg (Nat.cast : ℕ → ℚ_[l]) (Nat.add_one_mul_choose_eq M k)
  push_cast at h ⊢
  field_simp
  linear_combination (-(y ^ (k + 1))) * h

lemma tendsto_lg {x : ℚ_[l]} (hx : ‖x - 1‖ ≤ 1 / 3) :
    Tendsto (fun n : ℕ => (x ^ (l ^ n) - 1) / (l : ℚ_[l]) ^ n) atTop (𝓝 (lg x)) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (n k : ℕ) => (((l ^ n - 1).choose k : ℕ) : ℚ_[l]) *
      ((x - 1) ^ (k + 1) / ((k : ℚ_[l]) + 1))) (g := term (x - 1))
    (summable_geo ‖x - 1‖) (fun k => by
      rw [term, mul_div_assoc]; exact (tendsto_choose k).mul_const _)
    (Eventually.of_forall fun n k => by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)).trans
        (norm_pow_div_le hx k))
  refine h.congr fun n => ?_
  rw [← pow_sub_one_div, Nat.sub_add_cancel (Nat.one_le_pow _ _ hl.out.pos)]
  simp

lemma norm_mul_sub_one {x w : ℚ_[l]} (hx : ‖x - 1‖ ≤ 1 / 3) (hw : ‖w - 1‖ ≤ 1 / 3) :
    ‖x * w - 1‖ ≤ 1 / 3 := by
  have : x * w - 1 = (x - 1) * (w - 1) + (x - 1) + (w - 1) := by ring
  rw [this]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hw)
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hx)
  rw [norm_mul]
  nlinarith [norm_nonneg (x - 1), norm_nonneg (w - 1)]

lemma lg_mul {x w : ℚ_[l]} (hx : ‖x - 1‖ ≤ 1 / 3) (hw : ‖w - 1‖ ≤ 1 / 3) :
    lg (x * w) = lg x + lg w := by
  have h := ((tendsto_lg hx).add (tendsto_lg hw)).add
    (tendsto_pow_zero.mul ((tendsto_lg hx).mul (tendsto_lg hw)))
  rw [zero_mul, add_zero] at h
  refine tendsto_nhds_unique (tendsto_lg (norm_mul_sub_one hx hw)) (h.congr fun n => ?_)
  have h0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  rw [mul_pow]
  field_simp
  ring

lemma lg_pow {x : ℚ_[l]} (hx : ‖x - 1‖ ≤ 1 / 3) (m : ℕ) :
    ‖x ^ m - 1‖ ≤ 1 / 3 ∧ lg (x ^ m) = m * lg x := by
  induction m with
  | zero => simp [lg, term]
  | succ m ih =>
    rw [pow_succ]
    refine ⟨norm_mul_sub_one ih.1 hx, ?_⟩
    rw [lg_mul ih.1 hx, ih.2]
    push_cast
    ring

lemma continuousOn_lg : ContinuousOn (lg (l := l)) {x | ‖x - 1‖ ≤ 1 / 3} := by
  refine continuousOn_tsum (fun k => ?_) (summable_geo (1 / 3)) (fun k x hx => ?_)
  · unfold term
    fun_prop
  · refine (norm_term_le hx k).trans ?_
    gcongr
    exact hx

lemma norm_unit_pow_sub_one {u : ℚ_[l]} (hu : ‖u‖ = 1) :
    ‖u ^ (l * (l - 1)) - 1‖ ≤ (l : ℝ) ^ (-(2 : ℕ) : ℤ) := by
  let z : ℤ_[l] := ⟨u, hu.le⟩
  have hz : IsUnit z := PadicInt.isUnit_iff.mpr hu
  obtain ⟨v, hv⟩ := hz.map (PadicInt.toZModPow (p := l) 2)
  have h1 := ZMod.pow_totient v
  rw [Nat.totient_prime_pow hl.out (by norm_num)] at h1
  have h2 : z ^ (l * (l - 1)) - 1 ∈ RingHom.ker (PadicInt.toZModPow (p := l) 2) := by
    rw [RingHom.mem_ker, RingHom.map_sub, map_pow, map_one, ← hv, ← Units.val_pow_eq_pow_val]
    simp only [Nat.add_one_sub_one, pow_one] at h1
    rw [h1]
    simp
  rw [PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow] at h2
  exact h2

lemma zpow_le_third {j : ℕ} (h1 : 1 ≤ j) (h2 : l = 2 → 2 ≤ j) :
    (l : ℝ) ^ (-(j : ℤ)) ≤ 1 / 3 := by
  have h3 : 3 ≤ l ^ j := by
    by_cases h : l = 2
    · subst h
      exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (h2 rfl))
    · have := hl.out.two_le
      calc 3 ≤ l ^ 1 := by rw [pow_one]; omega
        _ ≤ l ^ j := Nat.pow_le_pow_right hl.out.pos h1
  rw [zpow_neg, zpow_natCast, one_div]
  exact inv_anti₀ (by norm_num) (by exact_mod_cast h3)

lemma norm_unit_pow_sub_one' {u : ℚ_[l]} (hu : ‖u‖ = 1) : ‖u ^ (l * (l - 1)) - 1‖ ≤ 1 / 3 :=
  (norm_unit_pow_sub_one hu).trans (zpow_le_third (by norm_num) fun _ => le_rfl)

lemma logZl_eq (u : ℚ_[l]) :
    Formalism.MainNotions.LocalSituation.logZl l u = lg (u ^ (l * (l - 1))) / ((l : ℚ_[l]) * ((l : ℚ_[l]) - 1)) := rfl

lemma norm_sub_one : ‖(l : ℚ_[l]) - 1‖ = 1 := by
  have h : ‖(l : ℚ_[l])‖ < ‖(-1 : ℚ_[l])‖ := by
    simpa using Padic.norm_p_lt_one (p := l)
  rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne, max_eq_right h.le]
  simp

theorem logZl_hom : ∀ (l : ℕ) [Fact l.Prime],
    (∀ u w : ℚ_[l], ‖u‖ = 1 → ‖w‖ = 1 →
      Formalism.MainNotions.LocalSituation.logZl l (u * w) = Formalism.MainNotions.LocalSituation.logZl l u + Formalism.MainNotions.LocalSituation.logZl l w) ∧
    ContinuousOn (Formalism.MainNotions.LocalSituation.logZl l) {u | ‖u‖ = 1} ∧
    (∀ u : ℚ_[l], ‖u‖ = 1 → ‖Formalism.MainNotions.LocalSituation.logZl l u‖ ≤ 1) ∧
    ∀ j : ℕ, 1 ≤ j → (l = 2 → 2 ≤ j) → ∀ u : ℚ_[l], ‖u - 1‖ ≤ (l : ℝ) ^ (-(j : ℤ)) →
      ‖Formalism.MainNotions.LocalSituation.logZl l u‖ = ‖u - 1‖ := by
  intro l hl
  refine ⟨fun u w hu hw => ?_, ?_, fun u hu => ?_, fun j h1 h2 u hu => ?_⟩
  · rw [logZl_eq, logZl_eq, logZl_eq, mul_pow,
      lg_mul (norm_unit_pow_sub_one' hu) (norm_unit_pow_sub_one' hw), add_div]
  · exact (continuousOn_lg.comp (continuous_pow (l * (l - 1))).continuousOn
      fun u hu => norm_unit_pow_sub_one' hu).div_const _
  · have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl.out.one_le
    rw [logZl_eq, norm_div, norm_lg (norm_unit_pow_sub_one' hu), norm_mul, norm_sub_one,
      mul_one, Padic.norm_p, div_le_one (by positivity)]
    refine (norm_unit_pow_sub_one hu).trans ?_
    rw [← zpow_neg_one]
    exact zpow_le_zpow_right₀ hl1 (by norm_num)
  · have hu' := hu.trans (zpow_le_third h1 h2)
    have h0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast hl.out.ne_zero
    have h3 : (l : ℚ_[l]) - 1 ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_sub_one]; exact one_ne_zero
    rw [logZl_eq, (lg_pow hu' _).2, Nat.cast_mul, Nat.cast_sub hl.out.one_le, Nat.cast_one,
      mul_div_cancel_left₀ _ (mul_ne_zero h0 h3), norm_lg hu']

end GlobalTheory.PadicLogUnits
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiFree
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc

namespace GlobalTheory.Cyc.PhiFree

open PowerSeries

theorem bijective_of_congr {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (a : R) [IsPrecomplete (Ideal.span {a}) M] [IsHausdorff (Ideal.span {a}) M]
    [IsHausdorff (Ideal.span {a}) N] (ha : ∀ y : N, a • y = 0 → y = 0) (S T : M →ₗ[R] N)
    (hS : Function.Bijective S) (h : ∀ z, T z - S z ∈ (Ideal.span {a} • ⊤ : Submodule R N)) :
    Function.Bijective T := by
  constructor
  · rw [injective_iff_map_eq_zero]
    have step : ∀ z, T z = 0 → ∃ z', T z' = 0 ∧ z = a • z' := fun z hz => by
      have h1 := h z
      rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
      obtain ⟨u, -, hu⟩ := h1
      obtain ⟨v, rfl⟩ := hS.2 u
      have h2 : z = a • (-v) := hS.1 (by rw [map_smul, map_neg, smul_neg, hu, hz]; simp)
      exact ⟨-v, ha _ (by rw [← map_smul, ← h2, hz]), h2⟩
    have all : ∀ (n : ℕ) z, T z = 0 → ∃ z', z = a ^ n • z' := fun n => by
      induction n with
      | zero => exact fun z _ => ⟨z, by simp⟩
      | succ n ih =>
        intro z hz
        obtain ⟨z', h1, rfl⟩ := step z hz
        obtain ⟨w, rfl⟩ := ih z' h1
        exact ⟨w, by rw [smul_smul, pow_succ']⟩
    intro z hz
    refine IsHausdorff.haus' (I := Ideal.span {a}) z fun n => ?_
    obtain ⟨w, rfl⟩ := all n z hz
    rw [SModEq.zero]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self a) n) trivial
  · refine surjective_of_mkQ_comp_surjective (I := Ideal.span {a}) fun G => ?_
    obtain ⟨G, rfl⟩ := Submodule.Quotient.mk_surjective _ G
    obtain ⟨z, rfl⟩ := hS.2 G
    exact ⟨z, (Submodule.Quotient.eq _).2 (h z)⟩

theorem bijective_one_add {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (x : B) (n : ℕ)
    (h : Function.Bijective fun z : Fin n → A => ∑ j : Fin n, x ^ (j : ℕ) * f (z j)) :
    Function.Bijective fun z : Fin n → A => ∑ j : Fin n, (1 + x) ^ (j : ℕ) * f (z j) := by
  have key : ∀ (t : B) (p : Polynomial.degreeLT A n),
      ∑ j : Fin n, t ^ (j : ℕ) * f (Polynomial.degreeLTEquiv A n p j) = p.1.eval₂ f t := fun t p => by
    rw [Polynomial.eval₂_eq_sum, ← Polynomial.sum_fin _ (by simp) (Polynomial.mem_degreeLT.1 p.2)]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  let e : (Fin n → A) ≃ₗ[A] (Fin n → A) := (Polynomial.degreeLTEquiv A n).symm.trans
    ((Polynomial.taylorLinearEquiv 1 n).trans (Polynomial.degreeLTEquiv A n))
  convert h.comp e.bijective using 1
  funext z
  obtain ⟨p, rfl⟩ := (Polynomial.degreeLTEquiv A n).surjective z
  simp only [e, Function.comp, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, key]
  change _ = (Polynomial.taylor 1 p.1).eval₂ f x
  rw [Polynomial.taylor_apply, Polynomial.eval₂_comp]
  simp [add_comm]

theorem coeff_sum_expand {R : Type} [CommRing R] (n : ℕ) (hn : n ≠ 0) (z : Fin n → R⟦X⟧) (i : Fin n)
    (m : ℕ) : coeff (n * m + i) (∑ j : Fin n, X ^ (j : ℕ) * expand n hn (z j)) = coeff m (z i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single i]
  · rw [coeff_X_pow_mul, coeff_expand_mul]
  · intro j _ hj
    rw [coeff_X_pow_mul']
    split_ifs with h
    · refine coeff_expand_of_not_dvd _ _ _ fun hd => hj (Fin.ext ?_)
      have h1 : (j : ℕ) ≡ n * m + i [MOD n] := (Nat.modEq_iff_dvd' h).2 hd
      have h2 : n * m + i ≡ i [MOD n] := by simp [Nat.ModEq]
      exact (h1.trans h2).eq_of_lt_of_lt j.2 i.2
    · rfl
  · simp

theorem bijective_expand {R : Type} [CommRing R] (n : ℕ) (hn : n ≠ 0) :
    Function.Bijective fun z : Fin n → R⟦X⟧ => ∑ j : Fin n, X ^ (j : ℕ) * expand n hn (z j) := by
  constructor
  · intro z z' h
    funext i
    ext m
    rw [← coeff_sum_expand n hn z, ← coeff_sum_expand n hn z']
    exact congrArg _ h
  · intro y
    refine ⟨fun i => PowerSeries.mk fun m => coeff (n * m + i) y, ?_⟩
    ext k
    have h := coeff_sum_expand n hn (fun i => PowerSeries.mk fun m => coeff (n * m + i) y)
      ⟨k % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩ (k / n)
    simpa [Nat.div_add_mod] using h

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]

theorem coeff_phi_sub_expand_mem (J : Ideal O) (hl : (l : O) ∈ J) (z : O⟦X⟧) (k : ℕ) :
    coeff k (phi l O z - expand l (Fact.out : l.Prime).ne_zero z) ∈ J := by
  have h : (PowerSeries.map (Ideal.Quotient.mk J)).comp (phi l O : O⟦X⟧ →+* O⟦X⟧) =
      (PowerSeries.map (Ideal.Quotient.mk J)).comp
        (expand l (Fact.out : l.Prime).ne_zero : O⟦X⟧ →ₐ[O] O⟦X⟧) := by
    have hX : PowerSeries.map (Ideal.Quotient.mk J) (phi l O X) = X ^ l := by
      obtain ⟨r, hr⟩ := Series.phi_X_mod l O
      have h0 : ((l : ℕ) : (O ⧸ J)⟦X⟧) = 0 := by
        rw [← map_natCast (C (R := O ⧸ J)), ← map_natCast (Ideal.Quotient.mk J),
          Ideal.Quotient.eq_zero_iff_mem.2 hl, map_zero]
      rw [hr]
      simp [h0]
    refine Fon.ps_hom_ext (fun r => ?_) ?_ ?_
    · exact congrArg (PowerSeries.map (Ideal.Quotient.mk J))
        (((phi l O).commutes r).trans ((expand l (Fact.out : l.Prime).ne_zero).commutes r).symm)
    · exact hX.trans (by simp)
    · refine Fon.eq_zero_of_pow_dvd ?_
      change constantCoeff (PowerSeries.map (Ideal.Quotient.mk J) (phi l O X)) = 0
      rw [hX]
      simp [(Fact.out : l.Prime).ne_zero]
  have h1 := congrArg (coeff k) (RingHom.congr_fun h z)
  rw [map_sub, ← Ideal.Quotient.eq]
  simpa only [RingHom.comp_apply, coeff_map, RingHom.coe_coe] using h1

end GlobalTheory.Cyc.PhiFree

namespace GlobalTheory.Cyc

open PhiFree CompleteBaseChange

theorem phi_free : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Algebra ℤ_[l] O], (l : O) ≠ 0 → ¬ IsUnit (l : O) → ∀ y : PowerSeries O, ∃! z : Fin l → PowerSeries O, y = ∑ j : Fin l, (1 + PowerSeries.X) ^ (j : ℕ) * phi l O (z j) := by
  intro l _ O _ _ _ _ _ _ hl y
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hm := ha.maximalIdeal_eq
  have hla : (l : O) ∈ Ideal.span {a} := hm ▸ (IsLocalRing.mem_maximalIdeal _).2 hl
  have : IsAdicComplete (Ideal.span {a}) O := hm ▸ ‹_›
  have hJ : (Ideal.span {a}).FG := Submodule.fg_span_singleton a
  have : IsPrecomplete (Ideal.span {a}) (PowerSeries O) := isPrecomplete_pi (Unit →₀ ℕ) hJ
  have : IsHausdorff (Ideal.span {a}) (PowerSeries O) := isHausdorff_pi (Unit →₀ ℕ) hJ
  have : IsPrecomplete (Ideal.span {a}) (Fin l → PowerSeries O) := isPrecomplete_pi _ hJ
  have : IsHausdorff (Ideal.span {a}) (Fin l → PowerSeries O) := isHausdorff_pi _ hJ
  let F : (PowerSeries O →ₐ[O] PowerSeries O) → (Fin l → PowerSeries O) →ₗ[O] PowerSeries O := fun f =>
    { toFun := fun z => ∑ j : Fin l, PowerSeries.X ^ (j : ℕ) * f (z j)
      map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by simp [Finset.smul_sum] }
  have hT : Function.Bijective (F (phi l O)) := by
    refine bijective_of_congr a (fun y hy => ?_) (F (PowerSeries.expand l (Fact.out : l.Prime).ne_zero)) _
      (bijective_expand l _) fun z => ?_
    · ext k
      have h1 := congrArg (PowerSeries.coeff k) hy
      rw [map_smul, map_zero, smul_eq_mul] at h1
      exact (mul_eq_zero.1 h1).resolve_left ha.ne_zero
    · change (∑ j : Fin l, _) - (∑ j : Fin l, _) ∈ _
      rw [← Finset.sum_sub_distrib]
      refine Submodule.sum_mem _ fun j _ => ?_
      have h1 : phi l O (z j) - PowerSeries.expand l (Fact.out : l.Prime).ne_zero (z j) ∈
          (Ideal.span {a} • ⊤ : Submodule O (PowerSeries O)) :=
        (mem_smul_top_pi (ι := Unit →₀ ℕ) hJ _).2 fun d => by
          have h2 := coeff_phi_sub_expand_mem l O _ hla (z j) (d ())
          rw [PowerSeries.coeff, Finsupp.unique_single d |>.symm] at h2
          rw [smul_eq_mul, Ideal.mul_top]
          exact h2
      rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1 ⊢
      obtain ⟨u, -, hu⟩ := h1
      exact ⟨PowerSeries.X ^ (j : ℕ) * u, trivial, by rw [← mul_sub, ← hu, mul_smul_comm]⟩
  have h := (bijective_one_add (phi l O : PowerSeries O →+* PowerSeries O) PowerSeries.X l hT).existsUnique y
  simpa only [eq_comm (a := y), RingHom.coe_coe] using h

end GlobalTheory.Cyc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenWeightSubquotientModelMemResidues
section
namespace GlobalTheory.Models
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

theorem exists_of_resCount_ne_zero_sq {k : Type} [Field k] {U : Multiset ℤ} {w : ℤ} {x : k}
    (h : resCount U w x ≠ 0) : ∃ u ∈ U, ((u - w : ℤ) : k) = x := by
  classical
  unfold resCount at h
  rw [Ne, Multiset.card_eq_zero] at h
  obtain ⟨u, hu⟩ := Multiset.exists_mem_of_ne_zero h
  rw [Multiset.mem_filter] at hu
  exact ⟨u, hu.1, hu.2⟩

theorem ModTh.sen_model_subquot_mem_U : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ (A₁ A : Ob k G) (j : (Fin A₁.m → k) →ₗ[k] (Fin M.T.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin A.m → k)) (N : Lats k n A.m), IsHom A₁ M.T j → Function.Injective j → IsHom A₁ A p → Function.Surjective p → M.Model A N → ∀ i x, sen ((F.D A).γ i) (N i) x ≠ 0 → ∃ u ∈ Dt.U i, ((u - Dt.w i : ℤ) : k) = x := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 h2 h3 A₁ A j p N hj hji hp hps hN i x hx
  have hT := _root_.GlobalTheory.Models.model_obj_and_abc F M M.T M.Nstd M.std_model
  have hm1 := _root_.GlobalTheory.Models.SubModel.model_pre F M A₁ M.T j M.Nstd hj hji M.std_model
  have hm := ModTh.model_push_of_surjective F M A₁ A p _ hp hps hm1
  have habc0 := (_root_.GlobalTheory.Models.model_obj_and_abc F M A _ hm).2
  have habc := (_root_.GlobalTheory.Models.model_obj_and_abc F M A N hN).2
  obtain ⟨c, hc, hs⟩ := _root_.GlobalTheory.Models.sen_near_of_abc (F.D A) Dt _ N habc0 habc i x hx
  have hle := _root_.GlobalTheory.Models.sen_push_pre_le F M.T A₁ A j p Dt.w Dt.wst M.Nstd hT.1 hj hji hp hps hT.2 i (x + c)
  have hs' : sen ((F.D M.T).γ i) (M.Nstd i) (x + c) ≠ 0 := fun h0 => hs (by
    rw [h0] at hle; exact Nat.le_zero.mp hle)
  rw [M.std_sen] at hs'
  obtain ⟨u, hu, hux⟩ := exists_of_resCount_ne_zero_sq hs'
  obtain ⟨u', hu', hux'⟩ := _root_.GlobalTheory.Models.model_sen_mem F M A N hN i x hx
  rcases Multiset.mem_add.mp hu' with hU | hB
  · exact ⟨u', hU, hux'⟩
  · exfalso
    obtain ⟨hb1, hb2⟩ := mem_block.mp hB
    obtain ⟨hc1, hc2⟩ := abs_le.mp hc
    refine (_root_.GlobalTheory.WindowArith.windows (k := k) Dt h1 h2 h3 i).2.1 u hu (u' + c) (by omega) (by omega) ?_
    rw [← hux'] at hux
    push_cast at hux ⊢
    linear_combination hux

end GlobalTheory.Models
end

