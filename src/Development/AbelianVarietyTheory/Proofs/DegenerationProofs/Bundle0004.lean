module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsReducedCombination
section
open Module

namespace GlobalTheory

namespace LatticeIneq

variable {X : Type} [AddCommGroup X]

theorem weighted_add_le (q : QuadraticMap ℤ X ℝ) (hq : ∀ x, 0 ≤ q x) (j : ℕ) (a b : X) :
    (j : ℝ) * q (a + b) ≤ (j + 1) * q a + j * (j + 1) * q b := by
  have h1 : q (a + b) = q a + q b + QuadraticMap.polar q a b := by
    simp [QuadraticMap.polar]
  have h2 : q (a + (-(j : ℤ)) • b) = q a + q ((-(j : ℤ)) • b)
      + QuadraticMap.polar q a ((-(j : ℤ)) • b) := by
    simp only [QuadraticMap.polar]; ring
  rw [QuadraticMap.polar_smul_right, QuadraticMap.map_smul] at h2
  have h3 := hq (a + (-(j : ℤ)) • b)
  rw [h2] at h3
  simp only [zsmul_eq_mul] at h3
  push_cast at h3
  rw [h1]
  nlinarith

theorem map_sum_le (q : QuadraticMap ℤ X ℝ) (hq : ∀ x, 0 ≤ q x) {I : Type} (s : Finset I)
    (v : I → X) : q (∑ x ∈ s, v x) ≤ s.card * ∑ x ∈ s, q (v x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.card_insert_of_notMem hi]
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    · have hpos : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
      have h := weighted_add_le q hq s.card (∑ x ∈ s, v x) (v i)
      rw [add_comm (v i)]
      push_cast
      refine le_of_mul_le_mul_left ?_ hpos
      have h2 := mul_le_mul_of_nonneg_left ih (by positivity : (0 : ℝ) ≤ (s.card : ℝ) + 1)
      nlinarith

theorem exists_int_combination {I : Type} [Fintype I] (N : ℕ) (yy w : I → X)
    (hw : ∀ x, ∃ μ, w x = yy x + N • μ) (z : X)
    (hz : z ∈ AddSubgroup.closure (Set.range yy ∪ Set.range fun μ : X => N • μ)) :
    ∃ (k : I → ℤ) (μ : X), z + N • μ = ∑ x, k x • w x := by
  classical
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    rcases hy with ⟨i, rfl⟩ | ⟨μ, rfl⟩
    · obtain ⟨μ, hμ⟩ := hw i
      refine ⟨Pi.single i 1, μ, ?_⟩
      rw [Finset.sum_eq_single i]
      · simp [hμ]
      · intro b _ hb; simp [Pi.single_eq_of_ne hb]
      · simp
    · exact ⟨0, -μ, by simp⟩
  | zero => exact ⟨0, 0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨k, μ, h⟩ := ha
    obtain ⟨k', μ', h'⟩ := hb
    refine ⟨k + k', μ + μ', ?_⟩
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, ← h, ← h', smul_add]
    abel
  | neg a _ ha =>
    obtain ⟨k, μ, h⟩ := ha
    refine ⟨-k, -μ, ?_⟩
    simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, ← h, smul_neg]
    abel

theorem exists_reduced_combination {I : Type} [Fintype I] (N : ℕ) (hN : 1 ≤ N) (yy w : I → X)
    (hw : ∀ x, ∃ μ, w x = yy x + N • μ) (z : X)
    (hz : z ∈ AddSubgroup.closure (Set.range yy ∪ Set.range fun μ : X => N • μ)) :
    ∃ (k : I → ℤ) (μ : X), (∀ x, 0 ≤ k x ∧ k x ≤ N) ∧ z + N • μ = ∑ x, k x • w x := by
  obtain ⟨k, μ, h⟩ := exists_int_combination N yy w hw z hz
  have hN' : (0 : ℤ) < N := by exact_mod_cast hN
  refine ⟨fun x => k x % N, μ - ∑ x, (k x / N) • w x,
    fun x => ⟨Int.emod_nonneg _ hN'.ne', (Int.emod_lt_of_pos _ hN').le⟩, ?_⟩
  rw [smul_sub, ← add_sub_assoc, h, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← natCast_zsmul, smul_smul, ← sub_smul]
  simp only [Int.emod_def]

end LatticeIneq


open LatticeIneq in
theorem lattice_inequality :
    ∀ (X : Type) [AddCommGroup X] (q : QuadraticMap ℤ X ℝ), (∀ x, 0 ≤ q x) → ∀ (I : Type) [Fintype I] (N N' j : ℕ), 1 ≤ N → N ∣ N' → 1 ≤ j → ∀ (yy w : I → X) (vth : I → ℝ) (αs c : X) (vf' : ℝ), (∀ x, ∃ μ, w x = yy x + N' • μ) → (∀ x, q (w x) ≤ (N' : ℝ) ^ 2 * vth x) → q αs ≤ N * vf' → c - αs ∈ AddSubgroup.closure (Set.range yy ∪ Set.range fun μ : X => N • μ) → ∃ μ : X, j * (q (c + N • μ) / N) ≤ (j + 1) * vf' + (j * (j + 1) * Fintype.card I * N * N' ^ 2 : ℕ) * ∑ x, vth x := by
  intro X _ q hq I _ N N' j hN hNN' _ yy w vth αs c vf' hw hwq hα hc
  obtain ⟨m, rfl⟩ := hNN'
  have hw' : ∀ x, ∃ μ, w x = yy x + N • μ := fun x => by
    obtain ⟨μ, hμ⟩ := hw x
    exact ⟨m • μ, by rw [hμ, mul_smul]⟩
  obtain ⟨k, μ, hk, h⟩ := LatticeIneq.exists_reduced_combination N hN yy w hw' _ hc
  refine ⟨μ, ?_⟩
  have hc' : c + N • μ = αs + ∑ x, k x • w x := by rw [← h]; abel
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := LatticeIneq.weighted_add_le q hq j αs (∑ x, k x • w x)
  have h2 := LatticeIneq.map_sum_le q hq Finset.univ (fun x => k x • w x)
  have h3 : ∑ x, q (k x • w x) ≤ (N : ℝ) ^ 2 * ((N * m : ℕ) : ℝ) ^ 2 * ∑ x, vth x := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [QuadraticMap.map_smul, zsmul_eq_mul]
    have a0 : (0 : ℝ) ≤ k x := by exact_mod_cast (hk x).1
    have a1 : (k x : ℝ) ≤ N := by exact_mod_cast (hk x).2
    have a2 : ((k x * k x : ℤ) : ℝ) ≤ (N : ℝ) ^ 2 := by push_cast; nlinarith
    calc _ ≤ (N : ℝ) ^ 2 * q (w x) := mul_le_mul_of_nonneg_right a2 (hq _)
      _ ≤ (N : ℝ) ^ 2 * (((N * m : ℕ) : ℝ) ^ 2 * vth x) :=
        mul_le_mul_of_nonneg_left (hwq x) (by positivity)
      _ = _ := by ring
  rw [Finset.card_univ] at h2
  have h4 := h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
  have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ (j : ℝ) * (j + 1))
  have h6 := mul_le_mul_of_nonneg_left hα (by positivity : (0 : ℝ) ≤ (j : ℝ) + 1)
  rw [hc', ← mul_div_assoc, div_le_iff₀ hNpos]
  push_cast at h5 ⊢
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRingHomPowerSeriesRoot
section
open PowerSeries

namespace GlobalTheory

namespace SeriesRoot

variable {O : Type*} [CommRing O]

noncomputable def residuePart (k l : ℕ) : PowerSeries O →+ PowerSeries O where
  toFun f := PowerSeries.mk fun n => coeff (k * n + l) f
  map_zero' := by ext n; simp
  map_add' f g := by ext n; simp

theorem coeff_residuePart (k l n : ℕ) (f : PowerSeries O) :
    coeff n (residuePart k l f) = coeff (k * n + l) f := by
  simp [residuePart]

theorem coeff_X_pow_mul_expand {k : ℕ} (hk : k ≠ 0) {j : ℕ} (hj : j < k) (g : PowerSeries O)
    (m : ℕ) :
    coeff m (X ^ j * expand k hk g) = if m % k = j then coeff (m / k) g else 0 := by
  rw [coeff_X_pow_mul', coeff_expand]
  by_cases h : m % k = j
  · have hm : m = k * (m / k) + j := by rw [← h]; exact (Nat.div_add_mod m k).symm
    have h1 : j ≤ m := by omega
    have h2 : m - j = k * (m / k) := by omega
    rw [if_pos h1, if_pos h, h2, if_pos (dvd_mul_right _ _),
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hk)]
  · rw [if_neg h]
    split_ifs with h1 h2
    · exfalso
      obtain ⟨c, hc⟩ := h2
      apply h
      have : m = j + k * c := by omega
      rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
    · rfl
    · rfl

theorem sum_residuePart {k : ℕ} (hk : k ≠ 0) (f : PowerSeries O) :
    ∑ l ∈ Finset.range k, X ^ l * expand k hk (residuePart k l f) = f := by
  ext m
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_congr rfl
    (fun l hl => coeff_X_pow_mul_expand hk (Finset.mem_range.1 hl) _ m), Finset.sum_ite_eq,
    if_pos (Finset.mem_range.2 (Nat.mod_lt _ (Nat.pos_of_ne_zero hk))), coeff_residuePart,
    Nat.div_add_mod]

theorem residuePart_X_pow_mul_expand {k : ℕ} (hk : k ≠ 0) {j l : ℕ} (hj : j < k) (hl : l < k)
    (g : PowerSeries O) :
    residuePart k l (X ^ j * expand k hk g) = if l = j then g else 0 := by
  ext n
  rw [coeff_residuePart, coeff_X_pow_mul_expand hk hj, Nat.mul_add_mod, Nat.mod_eq_of_lt hl,
    Nat.mul_add_div (Nat.pos_of_ne_zero hk), Nat.div_eq_of_lt hl, add_zero]
  split_ifs <;> simp

variable {K : Type*} [CommRing K]

noncomputable def extendAdd (φ : PowerSeries O →+* K) (k : ℕ) (t : K) : PowerSeries O →+ K where
  toFun f := ∑ l ∈ Finset.range k, t ^ l * φ (residuePart k l f)
  map_zero' := by simp
  map_add' f g := by simp [mul_add, Finset.sum_add_distrib]

theorem extendAdd_apply (φ : PowerSeries O →+* K) (k : ℕ) (t : K) (f : PowerSeries O) :
    extendAdd φ k t f = ∑ l ∈ Finset.range k, t ^ l * φ (residuePart k l f) := rfl

theorem extendAdd_X_pow_mul_expand_of_lt (φ : PowerSeries O →+* K) {k : ℕ} (hk : k ≠ 0) (t : K)
    {j : ℕ} (hj : j < k) (g : PowerSeries O) :
    extendAdd φ k t (X ^ j * expand k hk g) = t ^ j * φ g := by
  rw [extendAdd_apply, Finset.sum_eq_single j]
  · rw [residuePart_X_pow_mul_expand hk hj hj, if_pos rfl]
  · intro l hl hlj
    rw [residuePart_X_pow_mul_expand hk hj (Finset.mem_range.1 hl), if_neg hlj, map_zero,
      mul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 hj) h

theorem extendAdd_X_pow_mul_expand (φ : PowerSeries O →+* K) {k : ℕ} (hk : k ≠ 0) {t : K}
    (ht : t ^ k = φ X) (j : ℕ) (g : PowerSeries O) :
    extendAdd φ k t (X ^ j * expand k hk g) = t ^ j * φ g := by
  have h : (X : PowerSeries O) ^ j * expand k hk g =
      X ^ (j % k) * expand k hk (X ^ (j / k) * g) := by
    rw [map_mul, map_pow, expand_X, ← pow_mul, ← mul_assoc, ← pow_add, Nat.mod_add_div]
  rw [h, extendAdd_X_pow_mul_expand_of_lt φ hk t (Nat.mod_lt _ (Nat.pos_of_ne_zero hk)),
    map_mul, map_pow, ← ht, ← pow_mul, ← mul_assoc, ← pow_add, Nat.mod_add_div]

theorem extendAdd_mul (φ : PowerSeries O →+* K) {k : ℕ} (hk : k ≠ 0) {t : K}
    (ht : t ^ k = φ X) (f g : PowerSeries O) :
    extendAdd φ k t (f * g) = extendAdd φ k t f * extendAdd φ k t g := by
  conv_lhs => rw [← sum_residuePart hk f, ← sum_residuePart hk g]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [extendAdd_apply φ k t f, extendAdd_apply φ k t g, Finset.sum_mul_sum, Finset.sum_mul_sum,
    map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_mul_mul_comm, ← pow_add, ← map_mul, extendAdd_X_pow_mul_expand φ hk ht, map_mul,
    pow_add]
  ring

noncomputable def extendHom (φ : PowerSeries O →+* K) {k : ℕ} (hk : k ≠ 0) {t : K}
    (ht : t ^ k = φ X) : PowerSeries O →+* K where
  toFun := extendAdd φ k t
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := by simpa using extendAdd_X_pow_mul_expand φ hk ht 0 1
  map_mul' := extendAdd_mul φ hk ht

theorem extendHom_expand (φ : PowerSeries O →+* K) {k : ℕ} (hk : k ≠ 0) {t : K}
    (ht : t ^ k = φ X) (g : PowerSeries O) : extendHom φ hk ht (expand k hk g) = φ g := by
  have := extendAdd_X_pow_mul_expand φ hk ht 0 g
  rw [pow_zero, pow_zero, one_mul, one_mul] at this
  exact this

theorem extendHom_X (φ : PowerSeries O →+* K) {k : ℕ} (hk : k ≠ 0) {t : K}
    (ht : t ^ k = φ X) : extendHom φ hk ht X = t := by
  have := extendAdd_X_pow_mul_expand φ hk ht 1 1
  rw [pow_one, pow_one, map_one, map_one, mul_one, mul_one] at this
  exact this

end SeriesRoot

theorem exists_ringHom_powerSeries_root :
    ∀ (O K : Type) [CommRing O] [CommRing K] (φ : PowerSeries O →+* K) (k : ℕ) (t : K), 0 < k →
      t ^ k = φ PowerSeries.X → ∃ Φ : PowerSeries O →+* K,
        (∀ a, Φ (PowerSeries.C a) = φ (PowerSeries.C a)) ∧ Φ PowerSeries.X = t ∧
          ∀ f, Φ f ∈ Subring.closure (Set.range φ ∪ {t}) := by
  intro O K _ _ φ k t hk ht
  refine ⟨SeriesRoot.extendHom φ hk.ne' ht, fun a => ?_, SeriesRoot.extendHom_X φ hk.ne' ht,
    fun f => ?_⟩
  · rw [← SeriesRoot.extendHom_expand φ hk.ne' ht (PowerSeries.C a), expand_C]
  · change ∑ l ∈ Finset.range k, t ^ l * φ (SeriesRoot.residuePart k l f) ∈ _
    refine Subring.sum_mem _ fun l _ => Subring.mul_mem _ (Subring.pow_mem _ ?_ l) ?_
    · exact Subring.subset_closure (Or.inr rfl)
    · exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueAddEquivOfCompatibleCongr
section
open Module

namespace GlobalTheory

private theorem int_eq_zero_of_forall_pow_dvd (n : ℕ) (hn : 2 ≤ n) (c : ℤ)
    (h : ∀ j : ℕ, (n : ℤ) ^ j ∣ c) : c = 0 := by
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (h c.natAbs) ?_
  rw [Int.natAbs_pow, Int.natAbs_natCast]
  exact Nat.lt_pow_self (by omega)

private theorem eq_zero_of_forall_pow_nsmul_dvd (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (n : ℕ) (hn : 2 ≤ n) (z : X) (h : ∀ j : ℕ, ∃ μ : X, z = n ^ j • μ) :
    z = 0 := by
  set b := Module.Free.chooseBasis ℤ X
  apply b.repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply]
  refine int_eq_zero_of_forall_pow_dvd n hn _ fun j => ?_
  obtain ⟨μ, hμ⟩ := h j
  refine ⟨b.repr μ i, ?_⟩
  rw [hμ, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
  push_cast
  ring


open Module in
theorem _root_.GlobalTheory.existsUnique_addEquiv_of_compatible_congr :
    ∀ (X X' : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup X'] [Module.Free ℤ X'] [Module.Finite ℤ X'] (n : ℕ), 2 ≤ n → ∀ r : ℕ → X → X' → Prop, (∀ j x, ∃ x', r j x x') → (∀ j x', ∃ x, r j x x') → (∀ j x y x' y', r j x x' → r j y y' → r j (x + y) (x' + y')) → (∀ j x y x' y', r j x x' → r j y y' → ((∃ μ, y = x + n ^ j • μ) ↔ ∃ μ', y' = x' + n ^ j • μ')) → (∀ j x x' μ μ', r j x x' → r j (x + n ^ j • μ) (x' + n ^ j • μ')) → (∀ x, ∃ x', ∀ j, r j x x') → (∀ x', ∃ x, ∀ j, r j x x') → ∃! e : X ≃+ X', ∀ j x, r j x (e x) := by
  intro X X' _ _ _ _ _ _ n hn r _ _ hadd hcong _ hfwd hbwd
  have sepR : ∀ x x' y', (∀ j, r j x x') → (∀ j, r j x y') → x' = y' := by
    intro x x' y' hx hy
    refine (sub_eq_zero.1 (eq_zero_of_forall_pow_nsmul_dvd X' n hn (y' - x') fun j => ?_)).symm
    obtain ⟨μ', hμ'⟩ := (hcong j x x x' y' (hx j) (hy j)).1 ⟨0, by simp⟩
    exact ⟨μ', by rw [hμ', add_sub_cancel_left]⟩
  have sepL : ∀ x y x', (∀ j, r j x x') → (∀ j, r j y x') → x = y := by
    intro x y x' hx hy
    refine (sub_eq_zero.1 (eq_zero_of_forall_pow_nsmul_dvd X n hn (y - x) fun j => ?_)).symm
    obtain ⟨μ, hμ⟩ := (hcong j x y x' x' (hx j) (hy j)).2 ⟨0, by simp⟩
    exact ⟨μ, by rw [hμ, add_sub_cancel_left]⟩
  choose f hf using hfwd
  have fadd : ∀ x y, f (x + y) = f x + f y := fun x y =>
    sepR _ _ _ (hf (x + y)) fun j => hadd j x y _ _ (hf x j) (hf y j)
  have bij : Function.Bijective f := by
    refine ⟨fun x y hxy => sepL x y (f x) (hf x) fun j => ?_, fun x' => ?_⟩
    · rw [hxy]
      exact hf y j
    · obtain ⟨x, hx⟩ := hbwd x'
      exact ⟨x, sepR _ _ _ (hf x) hx⟩
  refine ⟨AddEquiv.ofBijective (AddMonoidHom.mk' f fadd) bij, fun j x => hf x j, fun e he => ?_⟩
  ext x
  exact sepR x (e x) (f x) (fun j => he j x) (hf x)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FinrankSpanResidueLe
section
namespace GlobalTheory.ResidueSpanScale

theorem exists_scale {O K J : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [Finite J] (c : J → K) (j : J) (hj : c j ≠ 0) :
    ∃ (j₀ : J) (d : J → O), c j₀ ≠ 0 ∧ d j₀ = 1 ∧ ∀ i, c i = c j₀ * algebraMap O K (d i) := by
  classical
  haveI : Nonempty J := ⟨j⟩
  obtain ⟨j₀, h₀⟩ := Finite.exists_max (fun i => ValuationRing.valuation O K (c i))
  have hv : ValuationRing.valuation O K (c j₀) ≠ 0 := by
    intro h
    have h1 := h₀ j
    rw [h, le_zero_iff] at h1
    exact hj ((Valuation.zero_iff _).1 h1)
  have hc : c j₀ ≠ 0 := fun h => hv (by rw [h, map_zero])
  have hex : ∀ i, ∃ a : O, algebraMap O K a = c i / c j₀ := by
    intro i
    rw [← ValuationRing.mem_integer_iff, Valuation.mem_integer_iff, map_div₀]
    exact div_le_one_of_le₀ (h₀ i) zero_le
  choose d hd using hex
  refine ⟨j₀, d, hc, ?_, fun i => ?_⟩
  · apply IsFractionRing.injective O K
    rw [hd, div_self hc, map_one]
  · rw [hd]; field_simp

theorem finrank_span_residue_le {O K I A B : Type} [CommRing O] [IsDomain O] [ValuationRing O]
    [Field K] [Algebra O K] [IsFractionRing O K] [Finite I] (f : I → A → K)
    (g : I → B → IsLocalRing.ResidueField O)
    (h : ∀ b : B, ∃ (a : A) (w : I → O), ∀ i : I,
      f i a = algebraMap O K (w i) ∧ g i b = IsLocalRing.residue O (w i)) :
    Module.finrank (IsLocalRing.ResidueField O)
        (Submodule.span (IsLocalRing.ResidueField O) (Set.range g)) ≤
      Module.finrank K (Submodule.span K (Set.range f)) := by
  classical
  obtain ⟨κ, e, he, hsp, hli⟩ := exists_linearIndependent' (IsLocalRing.ResidueField O) g
  haveI : Finite κ := Finite.of_injective e he
  haveI : Fintype κ := Fintype.ofFinite κ
  have hf : LinearIndependent K (f ∘ e) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra hne
    push Not at hne
    obtain ⟨j, hj⟩ := hne
    obtain ⟨j₀, d, hc₀, hd₀, hd⟩ := exists_scale (O := O) c j hj
    have hz : ∑ i, IsLocalRing.residue O (d i) • (g ∘ e) i = 0 := by
      funext b
      obtain ⟨a, w, hw⟩ := h b
      have h1 := congrFun hc a
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
        Pi.zero_apply] at h1 ⊢
      have h2 : c j₀ * algebraMap O K (∑ i, d i * w (e i)) = 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← h1, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, (hw (e i)).1, ← mul_assoc, ← hd i]
      have h3 : ∑ i, d i * w (e i) = 0 := by
        apply IsFractionRing.injective O K
        rw [map_zero]
        exact (mul_eq_zero.1 h2).resolve_left hc₀
      have h4 := congrArg (IsLocalRing.residue O) h3
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero] at h4
      rw [← h4]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, (hw (e i)).2]
    have := Fintype.linearIndependent_iff.1 hli _ hz j₀
    rw [hd₀, map_one] at this
    exact one_ne_zero this
  haveI : Module.Finite K (Submodule.span K (Set.range f)) :=
    Module.Finite.span_of_finite K (Set.finite_range f)
  rw [← hsp, finrank_span_eq_card hli, ← finrank_span_eq_card hf]
  exact Submodule.finrank_mono (Submodule.span_mono (Set.range_comp_subset_range e f))

end GlobalTheory.ResidueSpanScale
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FinsuppEqZeroOfSumTorsionCharactersEqZero
section
open Module

namespace GlobalTheory

theorem exists_eq_add_nsmul_of_torsion_characters_eq (k X : Type) [Field k] [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (N : ℕ) (ζ : k) (hN : 0 < N)
    (hζ : IsPrimitiveRoot ζ N) (α β : X)
    (h : ∀ t : Multiplicative X →* kˣ, t ^ N = 1 →
      t (Multiplicative.ofAdd α) = t (Multiplicative.ofAdd β)) :
    ∃ w, α = β + N • w := by
  classical
  have hu : IsUnit ζ := hζ.isUnit hN.ne'
  obtain ⟨u, rfl⟩ := hu
  have hu' : IsPrimitiveRoot u N := IsPrimitiveRoot.coe_units_iff.mp hζ
  let b := Module.Free.chooseBasis ℤ X
  have key : ∀ i, (N : ℤ) ∣ b.repr (α - β) i := by
    intro i
    let t : Multiplicative X →* kˣ :=
      { toFun := fun x => u ^ (b.repr (Multiplicative.toAdd x) i)
        map_one' := by simp
        map_mul' := by
          intro x y
          simp [zpow_add] }
    have ht : t ^ N = 1 := by
      refine MonoidHom.ext fun x => ?_
      have : (u ^ (b.repr (Multiplicative.toAdd x) i)) ^ N = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu'.pow_eq_one,
          one_zpow]
      rw [MonoidHom.pow_apply, MonoidHom.one_apply]
      exact this
    have h1 : u ^ (b.repr α i) = u ^ (b.repr β i) := h t ht
    rw [← hu'.zpow_eq_one_iff_dvd, map_sub, Finsupp.sub_apply, zpow_sub, h1, mul_inv_cancel]
  choose d hd using key
  refine ⟨∑ i, d i • b i, ?_⟩
  rw [← sub_eq_iff_eq_add', ← b.sum_repr (α - β), Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hd i, mul_smul, natCast_zsmul]

theorem finsupp_eq_zero_of_sum_torsion_characters_eq_zero :
    ∀ (k X : Type) [Field k] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (N : ℕ) (ζ : k), 0 < N → IsPrimitiveRoot ζ N → ∀ (M : Type) [AddCommGroup M] [Module k M] (c : X →₀ M), (∀ α ∈ c.support, ∀ β ∈ c.support, (∃ w, α = β + N • w) → α = β) → (∀ t : Multiplicative X →* kˣ, t ^ N = 1 → c.sum (fun α m => (t (Multiplicative.ofAdd α) : k) • m) = 0) → c = 0 := by
  intro k X _ _ _ _ N ζ hN hζ M _ _ c hc hsum
  classical
  let G : Subgroup (Multiplicative X →* kˣ) := (powMonoidHom N).ker
  let ev : c.support → (G →* k) := fun α =>
    { toFun := fun t => ((t : Multiplicative X →* kˣ) (Multiplicative.ofAdd (α : X)) : k)
      map_one' := by simp
      map_mul' := by
        intro s t
        simp }
  have hinj : Function.Injective ev := by
    intro α β hαβ
    apply Subtype.ext
    refine hc _ α.2 _ β.2
      (exists_eq_add_nsmul_of_torsion_characters_eq k X N ζ hN hζ _ _ fun t ht => ?_)
    exact Units.ext (DFunLike.congr_fun hαβ (⟨t, ht⟩ : G))
  have hli : LinearIndependent k (fun α : c.support => (ev α : G → k)) :=
    (linearIndependent_monoidHom G k).comp ev hinj
  ext α
  by_contra hα
  have hmem : α ∈ c.support := Finsupp.mem_support_iff.mpr hα
  apply hα
  rw [Finsupp.zero_apply, ← Module.forall_dual_apply_eq_zero_iff k]
  intro φ
  refine Fintype.linearIndependent_iff.mp hli (fun β => φ (c β)) ?_ ⟨α, hmem⟩
  funext t
  have h0 := congrArg φ (hsum t t.2)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finsupp.sum, map_sum, map_zero, ← Finset.sum_coe_sort] at h0
  rw [Finset.sum_apply, Pi.zero_apply, ← h0]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
  rfl

end GlobalTheory
end

