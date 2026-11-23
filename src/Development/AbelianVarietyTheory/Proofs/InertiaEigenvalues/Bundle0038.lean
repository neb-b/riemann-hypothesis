module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntContinuousHomNormalizeOne
section
namespace GlobalTheory

theorem padicInt_hom_normalize : ∀ {G : Type} [Group G] [TopologicalSpace G] (p : ℕ) [Fact p.Prime] (χ : G → ℤ_[p]), Continuous χ → (∀ g h, χ (g * h) = χ g + χ h) → ∀ (g₀ : G), χ g₀ ≠ 0 → ∃ ψ : G → ℤ_[p], Continuous ψ ∧ (∀ g h, ψ (g * h) = ψ g + ψ h) ∧ (∀ g, χ g = 0 → ψ g = 0) ∧ ∃ g, ψ g = 1 := by
  intro G _ _ p _ χ hχ hadd g₀ hg₀
  classical
  have hex : ∃ n : ℕ, ∃ g, χ g ≠ 0 ∧ (χ g).valuation = n := ⟨_, g₀, hg₀, rfl⟩
  obtain ⟨g₁, hg₁, hv₁⟩ := Nat.find_spec hex
  have hmin : ∀ g, χ g ≠ 0 → (χ g₁).valuation ≤ (χ g).valuation := by
    intro g hg
    rw [hv₁]
    exact Nat.find_min' hex ⟨g, hg, rfl⟩
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hle : ∀ g, ‖χ g‖ ≤ ‖χ g₁‖ := by
    intro g
    by_cases hg : χ g = 0
    · rw [hg, norm_zero]; exact norm_nonneg _
    rw [PadicInt.norm_eq_zpow_neg_valuation hg, PadicInt.norm_eq_zpow_neg_valuation hg₁]
    apply zpow_le_zpow_right₀ hp1
    have := hmin g hg
    omega
  have hn₁ : (χ g₁ : ℚ_[p]) ≠ 0 := fun h => hg₁ (PadicInt.coe_eq_zero.1 h)
  have hbd : ∀ g, ‖(χ g : ℚ_[p]) / (χ g₁ : ℚ_[p])‖ ≤ 1 := by
    intro g
    rw [norm_div, div_le_one (norm_pos_iff.2 hn₁)]
    exact hle g
  refine ⟨fun g => ⟨(χ g : ℚ_[p]) / (χ g₁ : ℚ_[p]), hbd g⟩, ?_, ?_, ?_, g₁, ?_⟩
  · apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp hχ).div_const _
  · intro g h
    apply Subtype.ext
    show ((χ (g * h) : ℚ_[p])) / (χ g₁ : ℚ_[p]) = (χ g : ℚ_[p]) / (χ g₁ : ℚ_[p]) + (χ h : ℚ_[p]) / (χ g₁ : ℚ_[p])
    rw [hadd, PadicInt.coe_add, add_div]
  · intro g hg
    apply Subtype.ext
    simp [hg]
  · apply Subtype.ext
    simp [div_self hn₁]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowSmulMemOfLe
section
namespace GlobalTheory.PowerScalarMembership

theorem pow_smul_mem_of_le {O V : Type} [CommRing O] [AddCommGroup V] [Module O V]
    (L : Submodule O V) (c : O) {x : V} {m n : ℕ} (hmn : m ≤ n) (h : c ^ m • x ∈ L) :
    c ^ n • x ∈ L := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [pow_add, mul_comm, mul_smul]
  exact L.smul_mem _ h

theorem exists_pow_smul_mem {LL O : Type} [Field LL] [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] (c : O)
    (hc : ∀ a : LL, ∃ (k : ℕ) (b : O), algebraMap O LL b = algebraMap O LL c ^ k * a)
    (L : Submodule O V) (hL : Submodule.span LL (L : Set V) = ⊤) (x : V) :
    ∃ m : ℕ, c ^ m • x ∈ L := by
  have hx : x ∈ Submodule.span LL (L : Set V) := hL ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨0, by simpa using hy⟩
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨max m n, ?_⟩
    rw [smul_add]
    exact L.add_mem (pow_smul_mem_of_le L c (le_max_left _ _) hm)
      (pow_smul_mem_of_le L c (le_max_right _ _) hn)
  | smul a y _ hy =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨k, b, hb⟩ := hc a
    refine ⟨k + m, ?_⟩
    have key : c ^ (k + m) • (a • y) = b • (c ^ m • y) := by
      rw [← algebraMap_smul LL (c ^ (k + m)), smul_smul, ← algebraMap_smul LL b,
        ← algebraMap_smul LL (c ^ m), smul_smul, hb, map_pow, map_pow, pow_add]
      congr 1
      ring
    rw [key]
    exact L.smul_mem b hm

theorem main : ∀ {LL O : Type} [inst : Field LL] [inst_1 : CommRing O] [inst_2 : Algebra O LL] [TopologicalSpace LL] {V : Type} [inst_4 : AddCommGroup V] [inst_5 : Module LL V] [inst_6 : Module O V] [IsScalarTower O LL V] (c : O), (∀ (a : LL), ∃ (k : ℕ) (b : O), (Algebra.algebraMap O LL : O → LL) b = (Algebra.algebraMap O LL : O → LL) c ^ k * a) → ∀ (L S : Submodule O V), Submodule.span LL (↑L : Set V) = ⊤ → Submodule.FG S → ∃ (m : ℕ), ∀ x ∈ S, c ^ m • x ∈ L := by
  intro LL O _ _ _ _ V _ _ _ _ c hc L S hL hS
  obtain ⟨s, rfl⟩ := hS
  choose f hf using fun x => exists_pow_smul_mem (LL := LL) c hc L hL x
  refine ⟨s.sup f, fun x hx => ?_⟩
  have hle : Submodule.span O (s : Set V) ≤ L.comap ((c ^ s.sup f) • LinearMap.id) := by
    rw [Submodule.span_le]
    intro y hy
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]
    exact pow_smul_mem_of_le L c (Finset.le_sup hy) (hf y)
  simpa using hle hx

end GlobalTheory.PowerScalarMembership
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowSubDvdChoosePrimePowOfLt
section
open scoped BigOperators

namespace GlobalTheory

theorem pow_sub_dvd_choose_prime_pow_of_lt :
    ∀ (l a c i : ℕ), l.Prime → 1 ≤ i → i < l ^ (c + 1) → l ^ (a - c) ∣ (l ^ a).choose i := by
  intro l a c i hl hi hlt
  obtain ⟨v, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : i ≠ 0) l hl.one_lt.ne'
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hi)
  have hv : v ≤ c := by
    have h1 : l ^ v ≤ l ^ v * m := Nat.le_mul_of_pos_right _ hm0
    have h2 : l ^ v < l ^ (c + 1) := lt_of_le_of_lt h1 hlt
    have := (Nat.pow_lt_pow_iff_right hl.one_lt).1 h2
    omega
  have hpos : 0 < l ^ a := pow_pos hl.pos a
  have key : l ^ a ∣ l ^ v * m * (l ^ a).choose (l ^ v * m) := by
    obtain ⟨n, hn⟩ : ∃ n, l ^ a = n + 1 := ⟨l ^ a - 1, by omega⟩
    obtain ⟨k, hk⟩ : ∃ k, l ^ v * m = k + 1 := ⟨l ^ v * m - 1, by omega⟩
    rw [hn, hk]
    refine ⟨n.choose k, ?_⟩
    rw [mul_comm]
    exact (Nat.add_one_mul_choose_eq n k).symm
  have h2 : l ^ (a - v) ∣ m * (l ^ a).choose (l ^ v * m) := by
    rcases le_or_gt v a with h | h
    · have key' : l ^ v * l ^ (a - v) ∣ l ^ v * (m * (l ^ a).choose (l ^ v * m)) := by
        rw [← pow_add, Nat.add_sub_of_le h, ← mul_assoc]
        exact key
      exact (Nat.mul_dvd_mul_iff_left (pow_pos hl.pos v)).1 key'
    · rw [show a - v = 0 by omega, pow_zero]
      exact one_dvd _
  have hcop : (l ^ (a - v)).Coprime m := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hl).2 hm)
  have h3 : l ^ (a - v) ∣ (l ^ a).choose (l ^ v * m) := hcop.dvd_of_dvd_mul_left h2
  exact (pow_dvd_pow l (by omega : a - c ≤ a - v)).trans h3

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowSubOneLe
section
namespace GlobalTheory.UltrametricPowerBound

variable {l : ℕ} [Fact (Nat.Prime l)]

lemma ultra (q r : ℚ_[l]) : ‖q + r‖ ≤ max ‖q‖ ‖r‖ := Padic.nonarchimedean q r

lemma pow_sub_one_le (w : ℚ_[l]) (hw : ‖w‖ ≤ 1) (k : ℕ) : ‖w ^ k - 1‖ ≤ ‖w - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : w ^ (k + 1) - 1 = w * (w ^ k - 1) + (w - 1) := by ring
    rw [e]
    refine (ultra _ _).trans (max_le ?_ le_rfl)
    rw [norm_mul]
    calc ‖w‖ * ‖w ^ k - 1‖ ≤ 1 * ‖w ^ k - 1‖ := by gcongr
      _ ≤ ‖w - 1‖ := by rw [one_mul]; exact ih

theorem main : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (w : ℚ_[l]), ‖w‖ ≤ (1 : ℝ) → ∀ (k : ℕ),
    ‖w ^ k - (1 : ℚ_[l]) - (↑k : ℚ_[l]) * (w - (1 : ℚ_[l]))‖ ≤ ‖w - (1 : ℚ_[l])‖ ^ (2 : ℕ) := by
  intro l _ w hw k
  induction k with
  | zero => simp
  | succ k ih =>
    have e : w ^ (k + 1) - 1 - ((k + 1 : ℕ) : ℚ_[l]) * (w - 1)
        = (w ^ k - 1 - (k : ℚ_[l]) * (w - 1)) + (w - 1) * (w ^ k - 1) := by push_cast; ring
    rw [e]
    refine (ultra _ _).trans (max_le ih ?_)
    rw [norm_mul, sq]
    exact mul_le_mul_of_nonneg_left (pow_sub_one_le w hw k) (norm_nonneg _)

end GlobalTheory.UltrametricPowerBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesEqCOfSubstFixedNotRootOfUnity
section
namespace GlobalTheory


open PowerSeries in
theorem powerSeries_eq_C_of_subst_eq_self (L : Type) [Field L] (y : PowerSeries L)
    (hy : PowerSeries.constantCoeff y = 0)
    (hu : ∀ k : ℕ, 0 < k → (PowerSeries.coeff 1 y) ^ k ≠ 1) (a : PowerSeries L)
    (ha : (PowerSeries.subst y a : PowerSeries L) = a) :
    a = PowerSeries.C (PowerSeries.constantCoeff a) := by
  classical
  obtain ⟨z, rfl⟩ : X ∣ y := by rwa [PowerSeries.X_dvd_iff]
  have hs : HasSubst (X * z) := HasSubst.of_constantCoeff_zero' hy
  have hu1 : coeff 1 (X * z) = constantCoeff z := by
    rw [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  rw [hu1] at hu

  have hc : ∀ n, coeff n (a.subst (X * z)) =
      ∑ d ∈ Finset.range (n + 1), coeff d a * coeff (n - d) (z ^ d) := by
    intro n
    rw [coeff_subst' hs, finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
    · refine Finset.sum_congr rfl fun d hd => ?_
      rw [mul_pow, coeff_X_pow_mul', if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)),
        smul_eq_mul]
    · intro d hd
      rw [Function.mem_support] at hd
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra h
      apply hd
      rw [mul_pow, coeff_X_pow_mul', if_neg (by omega), smul_zero]

  have main : ∀ k, 0 < k → coeff k a = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      have h1 := hc k
      rw [ha, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, Nat.sub_self,
        coeff_zero_eq_constantCoeff_apply, map_pow] at h1
      · have h2 : coeff k a * (1 - constantCoeff z ^ k) = 0 := by
          rw [mul_sub, mul_one, ← h1, sub_self]
        rcases mul_eq_zero.mp h2 with h | h
        · exact h
        · exact absurd (sub_eq_zero.mp h).symm (hu k hk)
      · intro d hd
        rcases Nat.eq_zero_or_pos d with rfl | hd0
        · simp [coeff_one, hk.ne']
        · rw [ih d (Finset.mem_range.mp hd) hd0, zero_mul]
  ext n
  rcases n with _ | n
  · simp
  · rw [coeff_C, if_neg (Nat.succ_ne_zero n)]
    exact main (n + 1) (Nat.succ_pos n)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowerSeriesExistsUniqueDecompOverFrobeniusLikeEn
section
open scoped PowerSeries Pointwise

namespace GlobalTheory.InertiaEigenvalues.PowerSeriesFree

theorem coeff_term {O : Type} [CommRing O] (l : ℕ) (φ : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (hφ : ∀ (f : O⟦X⟧) (m : ℕ), PowerSeries.coeff m (φ f) = if l ∣ m then PowerSeries.coeff (m / l) f else 0)
    (j m : ℕ) (g : O⟦X⟧) :
    PowerSeries.coeff m (PowerSeries.X ^ j * φ g) =
      if j ≤ m ∧ l ∣ (m - j) then PowerSeries.coeff ((m - j) / l) g else 0 := by
  rw [PowerSeries.coeff_X_pow_mul']
  by_cases h : j ≤ m
  · simp only [h, true_and, if_true]
    exact hφ g (m - j)
  · simp [h]

theorem coeff_sum {O : Type} [CommRing O] (l : ℕ) (hl : 2 ≤ l) (φ : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (hφ : ∀ (f : O⟦X⟧) (m : ℕ), PowerSeries.coeff m (φ f) = if l ∣ m then PowerSeries.coeff (m / l) f else 0)
    (g : Fin l → O⟦X⟧) (m : ℕ) :
    PowerSeries.coeff m (∑ j : Fin l, PowerSeries.X ^ j.val * φ (g j)) =
      PowerSeries.coeff (m / l) (g ⟨m % l, Nat.mod_lt _ (by omega)⟩) := by
  have hl0 : 0 < l := by omega
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  rw [Finset.sum_eq_single (⟨m % l, Nat.mod_lt _ hl0⟩ : Fin l)]
  · rw [coeff_term l φ hφ]
    have h1 : m % l ≤ m := Nat.mod_le _ _
    have h2 : l ∣ m - m % l := by
      have := Nat.div_add_mod m l
      exact ⟨m / l, by omega⟩
    have h3 : (m - m % l) / l = m / l := by
      have := Nat.div_add_mod m l
      rw [show m - m % l = l * (m / l) by omega]
      exact Nat.mul_div_cancel_left _ hl0
    simp only [h1, h2, and_self, if_true, h3]
  · intro j _ hj
    rw [coeff_term l φ hφ]
    rw [if_neg]
    rintro ⟨hjm, k, hk⟩
    apply hj
    ext
    simp only
    have hjl := j.isLt
    have : m = l * k + j.val := by omega
    rw [this, Nat.mul_add_mod]
    exact (Nat.mod_eq_of_lt hjl).symm
  · intro h; exact absurd (Finset.mem_univ _) h

theorem main : ∀ {O : Type} [CommRing O] (l : ℕ), 2 ≤ l → ∀ (φ : O⟦X⟧ →ₐ[O] O⟦X⟧), (∀ (f : O⟦X⟧) (m : ℕ), PowerSeries.coeff m (φ f) = if l ∣ m then PowerSeries.coeff (m / l) f else 0) → ∀ f : O⟦X⟧, ∃! g : Fin l → O⟦X⟧, f = ∑ j : Fin l, PowerSeries.X ^ j.val * φ (g j) := by
  intro O _ l hl φ hφ f
  have hl0 : 0 < l := by omega
  refine ⟨fun j => PowerSeries.mk (fun n => PowerSeries.coeff (n * l + j.val) f), ?_, ?_⟩
  · ext m
    rw [coeff_sum l hl φ hφ, PowerSeries.coeff_mk]
    simp only
    rw [Nat.div_add_mod']
  · intro g hg
    funext j
    ext n
    rw [PowerSeries.coeff_mk, hg, coeff_sum l hl φ hφ]
    have hj := j.isLt
    have e1 : (n * l + j.val) / l = n := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hl0, Nat.div_eq_of_lt hj, Nat.zero_add]
    have e2 : (n * l + j.val) % l = j.val := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    simp only [e1, e2]

end GlobalTheory.InertiaEigenvalues.PowerSeriesFree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdOneSubBoundedBelowOfSummable
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem exp_neg_two_mul_le_one_sub {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1 / 2) :
    Real.exp (-(2 * s)) ≤ 1 - s := by
  have hpos : 0 < 1 + 2 * s := by linarith
  have h2 : 1 + 2 * s ≤ Real.exp (2 * s) := by linarith [Real.add_one_le_exp (2 * s)]
  rw [Real.exp_neg]
  have h3 : (Real.exp (2 * s))⁻¹ ≤ (1 + 2 * s)⁻¹ := inv_anti₀ hpos h2
  have h4 : (1 + 2 * s)⁻¹ ≤ 1 - s := by
    rw [inv_le_iff_one_le_mul₀ hpos]
    nlinarith
  linarith

theorem prod_one_sub_bounded_below :
    ∀ (ι : Type) (s : ι → ℝ), (∀ v, 0 ≤ s v) → (∀ v, s v < 1) → Summable s →
      ∃ δ : ℝ, 0 < δ ∧ ∀ S : Finset ι, δ ≤ ∏ v ∈ S, (1 - s v) := by
  intro ι s h0 h1 hs
  classical
  have hev : ∀ᶠ v in cofinite, s v < 1 / 2 :=
    hs.tendsto_cofinite_zero.eventually (eventually_lt_nhds (by norm_num))
  have hfin : {v | ¬ s v < 1 / 2}.Finite := Filter.eventually_cofinite.mp hev
  set F : Finset ι := hfin.toFinset with hFdef
  have hout : ∀ v, v ∉ F → s v ≤ 1 / 2 := by
    intro v hv
    by_contra hcon
    exact hv (by
      rw [hFdef, Set.Finite.mem_toFinset]
      intro hlt
      exact hcon hlt.le)
  have hfac : ∀ v, 0 < 1 - s v := fun v => by linarith [h1 v]
  have hle1 : ∀ v, 1 - s v ≤ 1 := fun v => by linarith [h0 v]
  have hc : 0 < ∏ v ∈ F, (1 - s v) := Finset.prod_pos fun v _ => hfac v
  refine ⟨(∏ v ∈ F, (1 - s v)) * Real.exp (-(2 * ∑' v, s v)), mul_pos hc (Real.exp_pos _),
    fun S => ?_⟩
  have hsplit : ∏ v ∈ S, (1 - s v) =
      (∏ v ∈ S.filter (· ∈ F), (1 - s v)) * ∏ v ∈ S.filter (· ∉ F), (1 - s v) :=
    (Finset.prod_filter_mul_prod_filter_not S (· ∈ F) _).symm
  have hsub : S.filter (· ∈ F) ⊆ F := fun v hv => (Finset.mem_filter.mp hv).2
  have hA : ∏ v ∈ F, (1 - s v) ≤ ∏ v ∈ S.filter (· ∈ F), (1 - s v) := by
    rw [← Finset.prod_sdiff hsub]
    have hp : 0 ≤ ∏ v ∈ S.filter (· ∈ F), (1 - s v) :=
      Finset.prod_nonneg fun v _ => (hfac v).le
    have hq : ∏ v ∈ F \ S.filter (· ∈ F), (1 - s v) ≤ 1 :=
      Finset.prod_le_one₀ (fun v _ => (hfac v).le) (fun v _ => hle1 v)
    exact mul_le_of_le_one_left hp hq
  have hB : Real.exp (-(2 * ∑' v, s v)) ≤ ∏ v ∈ S.filter (· ∉ F), (1 - s v) := by
    have hsum : ∑ v ∈ S.filter (· ∉ F), s v ≤ ∑' v, s v :=
      hs.sum_le_tsum _ (fun v _ => h0 v)
    calc Real.exp (-(2 * ∑' v, s v))
        ≤ Real.exp (∑ v ∈ S.filter (· ∉ F), -(2 * s v)) := by
          apply Real.exp_le_exp.mpr
          rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
          linarith
      _ = ∏ v ∈ S.filter (· ∉ F), Real.exp (-(2 * s v)) := Real.exp_sum _ _
      _ ≤ ∏ v ∈ S.filter (· ∉ F), (1 - s v) :=
          Finset.prod_le_prod₀ (fun v _ => (Real.exp_pos _).le)
            (fun v hv => exp_neg_two_mul_le_one_sub (h0 v)
              (hout v (Finset.mem_filter.mp hv).2))
  rw [hsplit]
  exact mul_le_mul hA hB (Real.exp_pos _).le
    (Finset.prod_nonneg fun v _ => (hfac v).le)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProjectiveOfFreeLatticeOverFiniteFreeRing
section
namespace GlobalTheory

theorem projective_compHom_of_free_of_finite_free :
    ∀ (Z S A D : Type) [CommRing Z] [CommRing S] [CommRing A] [AddCommGroup D] [Module A D] (z : Z →+* S) (a : S →+* A) (N : Submodule A D) (q : ℕ) (x : Fin q → D), (∀ y, y ∈ N ↔ ∃ s : Fin q → S, y = ∑ i, a (s i) • x i) → (∀ s : Fin q → S, ∑ i, a (s i) • x i = 0 → s = 0) → (∃ (d : ℕ) (w : Fin d → S), ∀ y : S, ∃! c : Fin d → Z, y = ∑ i, z (c i) * w i) → @Module.Projective Z _ ↥N _ (Module.compHom _ (a.comp z)) := by
  intro Z S A D _ _ _ _ _ z a N q x hN hli ⟨d, w, hw⟩
  letI : Module Z N := Module.compHom _ (a.comp z)
  have hsm : ∀ (r : Z) (n : N), ((r • n : N) : D) = a (z r) • (n : D) := fun _ _ => rfl
  let f : (Fin q → Fin d → Z) →ₗ[Z] N :=
    { toFun := fun c => ⟨∑ i, a (∑ m, z (c i m) * w m) • x i, (hN _).2 ⟨_, rfl⟩⟩
      map_add' := fun c c' => by
        apply Subtype.ext
        simp [add_mul, Finset.sum_add_distrib, add_smul]
      map_smul' := fun r c => by
        apply Subtype.ext
        rw [hsm]
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Finset.smul_sum,
          smul_smul, mul_assoc, ← Finset.mul_sum] }
  have hinj : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    have h1 := hli (fun i => ∑ m, z (c i m) * w m) (congrArg Subtype.val hc)
    funext i
    have h2 : (0 : S) = ∑ m, z (c i m) * w m := (congrFun h1 i).symm
    exact (hw 0).unique h2 (by simp)
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨s, rfl⟩ := (hN y).1 hy
    choose c hc _ using fun i => hw (s i)
    refine ⟨c, Subtype.ext ?_⟩
    change ∑ i, a (∑ m, z (c i m) * w m) • x i = ∑ i, a (s i) • x i
    exact Finset.sum_congr rfl fun i _ => by rw [← hc i]
  exact Module.Projective.of_equiv (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RTensorPairingEqZeroOfFlipInjective
section
open TensorProduct Module

namespace GlobalTheory

theorem rTensor_pairing_eq_zero_of_flip_injective : ∀ (F : Type) [Field F] (B : Type) [AddCommGroup B] [Module F B] (V V' : Type) [AddCommGroup V] [Module F V] [AddCommGroup V'] [Module F V'] [FiniteDimensional F V'] (m : V →ₗ[F] V' →ₗ[F] F), (∀ y, (∀ x, m x y = 0) → y = 0) → ∀ y : V' ⊗[F] B, (∀ v : V, TensorProduct.lid F B (LinearMap.rTensor B (m v) y) = 0) → y = 0 := by
  intro F _ B _ _ V V' _ _ _ _ _ m hm y hy
  have hinj : Function.Injective m.flip :=
    (injective_iff_map_eq_zero m.flip).2 fun z h =>
      hm z fun x => by simpa using LinearMap.congr_fun h x
  have hsurj : Function.Surjective m := LinearMap.flip_injective_iff₂.1 hinj
  let b := Module.finBasis F V'
  have key : ∀ z : V' ⊗[F] B,
      z = ∑ j, b j ⊗ₜ (TensorProduct.lid F B (LinearMap.rTensor B (b.coord j) z)) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v w =>
      simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Basis.coord_apply]
      simp_rw [← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul, b.sum_repr]
    | add z₁ z₂ h₁ h₂ =>
      conv_lhs => rw [h₁, h₂]
      simp only [map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib]
  rw [key y]
  refine Finset.sum_eq_zero fun j _ => ?_
  obtain ⟨v, hv⟩ := hsurj (b.coord j)
  rw [← hv, hy v, TensorProduct.tmul_zero]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanImageSemilinearLatticeEq
section
open NumberField

namespace GlobalTheory

theorem span_image_span_eq_of_integral (K : Type) [Field K] [NumberField K] (O : Type) [CommRing O] [IsDomain O]
    (e : K →+* FractionRing O) (V V' : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module (FractionRing O) V'] [Module O V']
    [IsScalarTower O (FractionRing O) V'] (iV : V →ₛₗ[e] V')
    (he : ∀ a : 𝓞 K, e (a : K) ∈ (algebraMap O (FractionRing O)).range) (S : Set V) :
    Submodule.span O (iV '' (Submodule.span (𝓞 K) S : Set V)) = Submodule.span O (iV '' S) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    induction hv using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      obtain ⟨z, hz⟩ := he a
      have h1 : a • x = ((a : K)) • x := (algebraMap_smul K a x).symm
      rw [h1, LinearMap.map_smulₛₗ, ← hz, algebraMap_smul]
      exact Submodule.smul_mem _ z hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

end GlobalTheory
end

