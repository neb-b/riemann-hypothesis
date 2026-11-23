module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PolyDegreeSlashActionRightActionProperties
section
noncomputable section

open Polynomial Matrix
open scoped MatrixGroups

namespace GlobalTheory.HeckeFamilyMatrices.SlPAct

abbrev rowA (g : Matrix (Fin 2) (Fin 2) ℤ) : ℂ[X] := C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)

abbrev rowB (g : Matrix (Fin 2) (Fin 2) ℤ) : ℂ[X] := C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)

theorem polySlash_apply (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p = ∑ i ∈ Finset.range (w + 1), p.coeff i • (rowA g ^ i * rowB g ^ (w - i)) := by
  simp [slP, LinearMap.sum_apply, rowA, rowB]

theorem slP_X_pow (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) {i : ℕ} (hi : i ≤ w) :
    slP w g (X ^ i) = rowA g ^ i * rowB g ^ (w - i) := by
  rw [polySlash_apply]
  simp only [coeff_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hi)) h

theorem eq_sum_of_mem {w : ℕ} {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1)) :
    p = ∑ i ∈ Finset.range (w + 1), C (p.coeff i) * X ^ i := by
  by_cases h0 : p = 0
  · subst h0; simp
  · apply as_sum_range_C_mul_X_pow'
    rw [natDegree_lt_iff_degree_lt h0]
    exact mem_degreeLT.1 hp

theorem mem_of_natDegree_le {w : ℕ} {q : ℂ[X]} (h : q.natDegree ≤ w) : q ∈ degreeLT ℂ (w + 1) := by
  rw [mem_degreeLT]
  exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_of_le h)

theorem natDegree_rows_le (g : Matrix (Fin 2) (Fin 2) ℤ) {i w : ℕ} (hi : i ≤ w) :
    (rowA g ^ i * rowB g ^ (w - i)).natDegree ≤ w := by
  have hA : (rowA g).natDegree ≤ 1 := natDegree_linear_le
  have hB : (rowB g).natDegree ≤ 1 := natDegree_linear_le
  calc (rowA g ^ i * rowB g ^ (w - i)).natDegree
      ≤ (rowA g ^ i).natDegree + (rowB g ^ (w - i)).natDegree := natDegree_mul_le
    _ ≤ i * 1 + (w - i) * 1 := add_le_add (natDegree_pow_le_of_le i hA) (natDegree_pow_le_of_le _ hB)
    _ = w := by omega

theorem polySlash_mem (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) : slP w g p ∈ degreeLT ℂ (w + 1) := by
  rw [polySlash_apply]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (mem_of_natDegree_le ?_)
  exact natDegree_rows_le g (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))

theorem polySlash_one (w : ℕ) {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1)) : slP w 1 p = p := by
  rw [polySlash_apply]
  conv_rhs => rw [eq_sum_of_mem hp]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [smul_eq_C_mul, rowA, rowB]

theorem polySlash_conj (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    (slP w g p).map (starRingEnd ℂ) = slP w g (p.map (starRingEnd ℂ)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [polySlash_apply, polySlash_apply, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [smul_eq_C_mul, Polynomial.map_mul, Polynomial.map_pow, coeff_map, rowA, rowB]

theorem slP_C_mul_X_pow (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (c : ℂ) {i : ℕ} (hi : i ≤ w) :
    slP w g (C c * X ^ i) = c • (rowA g ^ i * rowB g ^ (w - i)) := by
  rw [← smul_eq_C_mul, map_smul, slP_X_pow w g hi]

theorem polySlash_mul {m n : ℕ} (g : Matrix (Fin 2) (Fin 2) ℤ) {u v : ℂ[X]}
    (hu : u ∈ degreeLT ℂ (m + 1)) (hv : v ∈ degreeLT ℂ (n + 1)) :
    slP (m + n) g (u * v) = slP m g u * slP n g v := by
  have e : u * v = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
      C (u.coeff i * v.coeff j) * X ^ (i + j) := by
    conv_lhs => rw [eq_sum_of_mem hu, eq_sum_of_mem hv]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [C_mul, pow_add]; ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum, polySlash_apply m g u, polySlash_apply n g v, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hi' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  have hj' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  rw [slP_C_mul_X_pow _ _ _ (by omega)]
  have : m + n - (i + j) = (m - i) + (n - j) := by omega
  rw [this, smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul, C_mul, pow_add, pow_add]
  ring

theorem pow_mem {a : ℕ} {u : ℂ[X]} (hu : u ∈ degreeLT ℂ 2) : u ^ a ∈ degreeLT ℂ (a + 1) := by
  apply mem_of_natDegree_le
  have h1 : u.natDegree ≤ 1 := by
    by_cases h0 : u = 0
    · simp [h0]
    · have := (natDegree_lt_iff_degree_lt h0).2 (mem_degreeLT.1 hu); omega
  calc (u ^ a).natDegree ≤ a * 1 := natDegree_pow_le_of_le a h1
    _ = a := by omega

theorem polySlash_pow (g : Matrix (Fin 2) (Fin 2) ℤ) {u : ℂ[X]} (hu : u ∈ degreeLT ℂ 2) (a : ℕ) :
    slP a g (u ^ a) = slP 1 g u ^ a := by
  induction a with
  | zero =>
    have := slP_X_pow 0 g (i := 0) le_rfl
    simpa using this
  | succ a ih =>
    rw [pow_succ, polySlash_mul g (pow_mem hu) hu, ih, pow_succ]

theorem rowA_mem (g : Matrix (Fin 2) (Fin 2) ℤ) : rowA g ∈ degreeLT ℂ 2 := mem_of_natDegree_le natDegree_linear_le
theorem rowB_mem (g : Matrix (Fin 2) (Fin 2) ℤ) : rowB g ∈ degreeLT ℂ 2 := mem_of_natDegree_le natDegree_linear_le

theorem polySlash_one_linear (h : Matrix (Fin 2) (Fin 2) ℤ) (x y : ℂ) :
    slP 1 h (C x * X + C y) = C x * rowA h + C y * rowB h := by
  have e1 := slP_X_pow 1 h (i := 1) le_rfl
  have e0 := slP_X_pow 1 h (i := 0) (by omega)
  simp only [pow_one, pow_zero, one_mul, mul_one, Nat.sub_self, Nat.sub_zero] at e1 e0
  have e0' : slP 1 h (C y) = C y * rowB h := by
    calc slP 1 h (C y) = slP 1 h (y • (1 : ℂ[X])) := by rw [smul_eq_C_mul, mul_one]
      _ = y • rowB h := by rw [map_smul, e0]
      _ = C y * rowB h := smul_eq_C_mul _
  rw [map_add (f := _), e0', ← smul_eq_C_mul, map_smul, e1, smul_eq_C_mul]

theorem polySlash_one_rowA (g h : Matrix (Fin 2) (Fin 2) ℤ) : slP 1 h (rowA g) = rowA (g * h) := by
  rw [rowA, polySlash_one_linear]
  simp only [rowA, rowB, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  simp only [C_add, C_mul]
  ring

theorem polySlash_one_rowB (g h : Matrix (Fin 2) (Fin 2) ℤ) : slP 1 h (rowB g) = rowB (g * h) := by
  rw [rowB, polySlash_one_linear]
  simp only [rowA, rowB, Matrix.mul_apply, Fin.sum_univ_two]
  push_cast
  simp only [C_add, C_mul]
  ring

theorem polySlash_rowA_pow_mul_rowB_pow (g h : Matrix (Fin 2) (Fin 2) ℤ) (a b : ℕ) :
    slP (a + b) h (rowA g ^ a * rowB g ^ b) = rowA (g * h) ^ a * rowB (g * h) ^ b := by
  rw [polySlash_mul h (pow_mem (rowA_mem g)) (pow_mem (rowB_mem g)), polySlash_pow h (rowA_mem g),
    polySlash_pow h (rowB_mem g), polySlash_one_rowA, polySlash_one_rowB]

theorem polySlash_polySlash (w : ℕ) (g h : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w (g * h) p = slP w h (slP w g p) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [polySlash_apply w g p, map_sum, polySlash_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [map_smul]
  congr 1
  have := polySlash_rowA_pow_mul_rowB_pow g h i (w - i)
  rw [Nat.add_sub_cancel' hi'] at this
  exact this.symm

theorem polySlash_act : ∀ (w : ℕ) (g h : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]), p ∈ degreeLT ℂ (w + 1) →
    slP w g p ∈ degreeLT ℂ (w + 1) ∧ slP w (g * h) p = slP w h (slP w g p) ∧ slP w 1 p = p ∧
      (slP w g p).map (starRingEnd ℂ) = slP w g (p.map (starRingEnd ℂ)) :=
  fun w g h p hp => ⟨polySlash_mem w g p, polySlash_polySlash w g h p, polySlash_one w hp, polySlash_conj w g p⟩

end GlobalTheory.HeckeFamilyMatrices.SlPAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeMulBernoulliMem
section
open Finset GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.EisCong

variable {K : Type} [Field K] [CharZero K]

def pInt (p : ℕ) [Fact p.Prime] (K : Type) [Field K] : Subring K where
  carrier := {x | ∃ D : ℕ, ¬ p ∣ D ∧ IsIntegral ℤ ((D : K) * x)}
  mul_mem' := by
    rintro x y ⟨D, hD, hx⟩ ⟨E, hE, hy⟩
    refine ⟨D * E, fun h => ((Fact.out : p.Prime).dvd_mul.1 h).elim hD hE, ?_⟩
    have : ((D * E : ℕ) : K) * (x * y) = ((D : K) * x) * ((E : K) * y) := by push_cast; ring
    rw [this]; exact hx.mul hy
  one_mem' := ⟨1, (Fact.out : p.Prime).not_dvd_one, by simpa using isIntegral_one⟩
  add_mem' := by
    rintro x y ⟨D, hD, hx⟩ ⟨E, hE, hy⟩
    refine ⟨D * E, fun h => ((Fact.out : p.Prime).dvd_mul.1 h).elim hD hE, ?_⟩
    have : ((D * E : ℕ) : K) * (x + y) = (E : K) * ((D : K) * x) + (D : K) * ((E : K) * y) := by
      push_cast; ring
    rw [this]
    exact ((isIntegral_natCast E).mul hx).add ((isIntegral_natCast D).mul hy)
  zero_mem' := ⟨1, (Fact.out : p.Prime).not_dvd_one, by simpa using isIntegral_zero⟩
  neg_mem' := by
    rintro x ⟨D, hD, hx⟩
    exact ⟨D, hD, by rw [mul_neg]; exact hx.neg⟩

variable {p : ℕ} [Fact p.Prime]

omit [CharZero K] in
lemma mem_of_isIntegral {x : K} (h : IsIntegral ℤ x) : x ∈ pInt p K :=
  ⟨1, (Fact.out : p.Prime).not_dvd_one, by simpa using h⟩

lemma inv_nat_mem {m : ℕ} (h : ¬ p ∣ m) : (m : K)⁻¹ ∈ pInt p K := by
  have hm : (m : K) ≠ 0 := by
    have : m ≠ 0 := by rintro rfl; exact h (dvd_zero _)
    exact_mod_cast this
  exact ⟨m, h, by rw [mul_inv_cancel₀ hm]; exact isIntegral_one⟩

lemma inv_int_mem {c : ℤ} (h : ¬ (p : ℤ) ∣ c) : (c : K)⁻¹ ∈ pInt p K := by
  have h1 : ((c.natAbs : ℕ) : K)⁻¹ ∈ pInt p K := inv_nat_mem (fun h' => h (Int.natCast_dvd.2 h'))
  rcases Int.natAbs_eq c with h2 | h2
  · rw [h2]; simpa using h1
  · rw [h2]; simpa using neg_mem h1

omit [CharZero K] in
lemma root_zpow_mem {ζ : K} {M : ℕ} (hM : 0 < M) (h : IsPrimitiveRoot ζ M) (e : ℤ) : ζ ^ e ∈ pInt p K := by
  rcases e with e | e
  · simpa using pow_mem (mem_of_isIntegral (h.isIntegral hM)) e
  · rw [zpow_negSucc, ← inv_pow]; exact pow_mem (mem_of_isIntegral (h.inv.isIntegral hM)) _

lemma pow_div_mem {k e : ℕ} (hk : k ≠ 0) (h : k < p ^ (e + 1)) : (p : K) ^ e / k ∈ pInt p K := by
  have hp : p.Prime := Fact.out
  obtain ⟨v, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk p hp.ne_one
  have hu0 : u ≠ 0 := by rintro rfl; exact hu (dvd_zero _)
  have hv : v ≤ e := by
    have : p ^ v < p ^ (e + 1) := lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hu0)) h
    have := (Nat.pow_lt_pow_iff_right hp.one_lt).1 this
    omega
  obtain ⟨w, rfl⟩ := Nat.exists_eq_add_of_le hv
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have : (p : K) ^ (v + w) / ((p ^ v * u : ℕ) : K) = (p : K) ^ w * (u : K)⁻¹ := by
    push_cast; field_simp; ring
  rw [this]
  exact mul_mem (pow_mem (natCast_mem _ p) w) (inv_nat_mem hu)

lemma pow_div_add_two_mem (hp2 : p ≠ 2) (n i : ℕ) : ((p : K) ^ (n + 1)) ^ i / ((i : K) + 2) ∈ pInt p K := by
  have hp : p.Prime := Fact.out
  have h3 : 3 ≤ p := by have := hp.two_le; omega
  have h1 : ∀ i : ℕ, i + 2 < 3 ^ (i + 1) := by
    intro i
    induction i with
    | zero => norm_num
    | succ i ih => rw [pow_succ]; omega
  have h2 : i + 2 < p ^ ((n + 1) * i + 1) :=
    (h1 i).trans_le ((Nat.pow_le_pow_left h3 _).trans (Nat.pow_le_pow_right hp.pos (by nlinarith)))
  have := pow_div_mem (K := K) (k := i + 2) (by omega) h2
  rw [← pow_mul]
  simpa using this

lemma prime_mul_bernoulli_mem (k : ℕ) : (p : K) * ((bernoulli (k + 2) : ℚ) : K) ∈ pInt p K := by
  have hp : p.Prime := Fact.out
  rcases Nat.even_or_odd (k + 2) with ⟨m, hm⟩ | hodd
  · have hk2 : k + 2 = 2 * m := by omega
    obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen m
    have hB : bernoulli (k + 2) = (z : ℚ) -
        ∑ q ∈ Finset.range (2 * m + 2) with q.Prime ∧ (q - 1) ∣ 2 * m, (1 : ℚ) / q := by
      rw [hk2, hz]; ring
    rw [hB]
    push_cast
    rw [mul_sub, Finset.mul_sum]
    refine sub_mem (mul_mem (natCast_mem _ _) (intCast_mem _ _)) (sum_mem fun q hq => ?_)
    have hq' := (Finset.mem_filter.mp hq).2.1
    by_cases hql : q = p
    · subst hql
      have : (q : K) ≠ 0 := by exact_mod_cast hp.ne_zero
      rw [mul_one_div_cancel this]; exact one_mem _
    · rw [one_div]
      exact mul_mem (natCast_mem _ _)
        (inv_nat_mem fun h => hql ((Nat.prime_dvd_prime_iff_eq hp hq').mp h).symm)
  · rw [bernoulli_eq_zero_of_odd hodd (by omega)]
    simp

lemma choose_cast (m i : ℕ) :
    (((m + 2).choose (i + 2) : ℕ) : K) = ((m : K) + 2) * ((m + 1).choose (i + 1) : ℕ) / ((i : K) + 2) := by
  have h := Nat.add_one_mul_choose_eq (m + 1) (i + 1)
  have hi : (i : K) + 2 ≠ 0 := by exact_mod_cast (show i + 2 ≠ 0 by omega)
  rw [eq_div_iff hi]
  have h' := congrArg (Nat.cast : ℕ → K) h
  push_cast at h'
  simp only [add_assoc, one_add_one_eq_two] at h'
  rw [← h']

lemma binom_second (hp2 : p ≠ 2) (n m : ℕ) (x t : ℤ) :
    ∃ y ∈ pInt p K, ((x : K) + t * (p : K) ^ (n + 1)) ^ (m + 2) =
      (x : K) ^ (m + 2) + ((m : K) + 2) * t * (p : K) ^ (n + 1) * (x : K) ^ (m + 1) +
        ((m : K) + 2) * ((p : K) ^ (n + 1)) ^ 2 * y := by
  set Q : K := (p : K) ^ (n + 1) with hQ
  refine ⟨∑ i ∈ range (m + 1), (t : K) ^ (i + 2) * (x : K) ^ (m - i) * ((m + 1).choose (i + 1) : ℕ) *
    (Q ^ i / ((i : K) + 2)), sum_mem fun i _ => mul_mem (mul_mem (mul_mem (pow_mem (intCast_mem _ _) _)
      (pow_mem (intCast_mem _ _) _)) (natCast_mem _ _)) (pow_div_add_two_mem hp2 n i), ?_⟩
  rw [add_comm (x : K), add_pow, sum_range_succ', sum_range_succ', mul_sum]
  have : ∀ i ∈ range (m + 1), ((t : K) * Q) ^ (i + 1 + 1) * (x : K) ^ (m + 2 - (i + 1 + 1)) *
      ((m + 2).choose (i + 1 + 1) : ℕ) = ((m : K) + 2) * Q ^ 2 * ((t : K) ^ (i + 2) * (x : K) ^ (m - i) *
        ((m + 1).choose (i + 1) : ℕ) * (Q ^ i / ((i : K) + 2))) := by
    intro i _
    rw [show m + 2 - (i + 1 + 1) = m - i by omega, show i + 1 + 1 = i + 2 by omega, choose_cast]
    ring
  rw [sum_congr rfl this]
  simp
  ring

lemma binom_first (Q : ℤ) (k : ℕ) (x t : ℤ) :
    ∃ y : ℤ, ((x : K) + t * (Q : K)) ^ k = (x : K) ^ k + Q * y := by
  obtain ⟨y, hy⟩ := sub_dvd_pow_sub_pow (x + t * Q) x k
  refine ⟨t * y, ?_⟩
  have := congrArg (Int.cast : ℤ → K) hy
  push_cast at this ⊢
  linear_combination this



end GlobalTheory.EisCong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveCharDoubleSumPrimePowEval
section
open GlobalTheory.KummerEisensteinGalois Finset

namespace GlobalTheory.KummerEisensteinGalois.ChSum

theorem core {M : ℕ} [NeZero M] {K : Type} [Field K] (ψ : DirichletCharacter K M) (hψ : ψ.IsPrimitive)
    (e : AddChar (ZMod M) K) (he : e.IsPrimitive) (n₁ n₂ w D D' : ZMod M) (hw : n₁ * w = 1) :
    ∑ a : ZMod M, ∑ b : ZMod M, ψ (n₁ * b - n₂ * a) * e (a * D + b * D') =
      (if D + w * n₂ * D' = 0 then (M : K) else 0) * (ψ⁻¹ (w * D') * gaussSum ψ e) := by
  have step : ∀ a : ZMod M, ∑ b : ZMod M, ψ (n₁ * b - n₂ * a) * e (a * D + b * D') =
      ∑ s : ZMod M, ψ s * e (s * (w * D')) * e (a * (D + w * n₂ * D')) := by
    intro a
    let f : ZMod M ≃ ZMod M :=
      { toFun := fun s => w * (s + n₂ * a)
        invFun := fun b => n₁ * b - n₂ * a
        left_inv := fun s => by simp only; linear_combination (s + n₂ * a) * hw
        right_inv := fun b => by simp only; linear_combination b * hw }
    rw [← Equiv.sum_comp f]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [f, Equiv.coe_fn_mk]
    have h1 : n₁ * (w * (s + n₂ * a)) - n₂ * a = s := by linear_combination (s + n₂ * a) * hw
    have h2 : a * D + w * (s + n₂ * a) * D' = s * (w * D') + a * (D + w * n₂ * D') := by ring
    rw [h1, h2, AddChar.map_add_eq_mul]; ring
  have hG : ∑ s : ZMod M, ψ s * e (s * (w * D')) = ψ⁻¹ (w * D') * gaussSum ψ e := by
    rw [← gaussSum_mulShift_of_isPrimitive e hψ]
    unfold gaussSum
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [AddChar.mulShift_apply, mul_comm s]
  rw [Finset.sum_congr rfl fun a _ => step a, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [AddChar.sum_mulShift _ he, ← Finset.sum_mul, hG, ZMod.card]
  split_ifs <;> ring

theorem eval {M : ℕ} [NeZero M] {K : Type} [Field K] (ψ : DirichletCharacter K M) (hψ : ψ.IsPrimitive)
    (e : AddChar (ZMod M) K) (he : e.IsPrimitive) (n₁ n₂ w D D' : ZMod M) (hw : n₁ * w = 1) :
    (∀ u : (ZMod M)ˣ, D = u * (-n₂) → D' = u * n₁ →
      ∑ a : ZMod M, ∑ b : ZMod M, ψ (n₁ * b - n₂ * a) * e (a * D + b * D') =
        (M : K) * ψ⁻¹ (u : ZMod M) * gaussSum ψ e) ∧
    ((¬ ∃ u : (ZMod M)ˣ, D = u * (-n₂) ∧ D' = u * n₁) →
      ∑ a : ZMod M, ∑ b : ZMod M, ψ (n₁ * b - n₂ * a) * e (a * D + b * D') = 0) := by
  rw [core ψ hψ e he n₁ n₂ w D D' hw]
  refine ⟨fun u hD hD' => ?_, fun hno => ?_⟩
  · have h0 : D + w * n₂ * D' = 0 := by rw [hD, hD']; linear_combination (u : ZMod M) * n₂ * hw
    have hl : w * D' = u := by rw [hD']; linear_combination (u : ZMod M) * hw
    rw [if_pos h0, hl]; ring
  · by_cases hc : D + w * n₂ * D' = 0
    · have hnu : ¬ IsUnit (w * D') := by
        rintro ⟨v, hv⟩
        refine hno ⟨v, ?_, ?_⟩
        · rw [hv]; linear_combination hc
        · rw [hv]; linear_combination (-D') * hw
      rw [if_pos hc, MulChar.map_nonunit _ hnu]; ring
    · rw [if_neg hc, zero_mul]

theorem zpow_eq {M : ℕ} [NeZero M] {K : Type} [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ M) (z : ℤ) :
    ζ ^ z = AddChar.zmodChar M hζ.pow_eq_one (z : ZMod M) := by
  have hne : ζ ≠ 0 := hζ.ne_zero (NeZero.ne M)
  rw [AddChar.zmodChar_apply, ← zpow_natCast, ZMod.val_intCast]
  conv_lhs => rw [← Int.emod_add_mul_ediv z M]
  rw [zpow_add₀ hne, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow, mul_one]

theorem unit_of_not_dvd (p m : ℕ) (hp : p.Prime) (n : ℤ) (h : ¬ (p : ℤ) ∣ n) :
    ∃ w : ZMod (p ^ m), (n : ZMod (p ^ m)) * w = 1 := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hc : IsCoprime n ((p : ℤ) ^ m) :=
    (((Irreducible.coprime_iff_not_dvd hpZ.irreducible).mpr h).pow_left).symm
  obtain ⟨u, v, huv⟩ := hc
  refine ⟨(u : ZMod (p ^ m)), ?_⟩
  have := congrArg (fun z : ℤ => (z : ZMod (p ^ m))) huv
  simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_natCast, Int.cast_one] at this
  rw [← Nat.cast_pow, ZMod.natCast_self, mul_zero, add_zero] at this
  rw [mul_comm]; exact this

theorem charSum : ∀ (p m : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharZero K] (ψ : DirichletCharacter K (p ^ m)) (ζm : K), 1 ≤ m → ψ.IsPrimitive → IsPrimitiveRoot ζm (p ^ m) → ∀ n₁ n₂ d d' : ℤ, ¬ ((p : ℤ) ∣ n₁ ∧ (p : ℤ) ∣ n₂) → (∀ u : (ZMod (p ^ m))ˣ, (d : ZMod (p ^ m)) = u * (-(n₂ : ZMod (p ^ m))) → (d' : ZMod (p ^ m)) = u * (n₁ : ZMod (p ^ m)) → ∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - (n₂ : ZMod (p ^ m)) * a) * ζm ^ ((a.val : ℤ) * d + (b.val : ℤ) * d') = (p : K) ^ m * ψ⁻¹ (u : ZMod (p ^ m)) * gaussS p m ψ ζm) ∧ ((¬ ∃ u : (ZMod (p ^ m))ˣ, (d : ZMod (p ^ m)) = u * (-(n₂ : ZMod (p ^ m))) ∧ (d' : ZMod (p ^ m)) = u * (n₁ : ZMod (p ^ m))) → ∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m), ψ ((n₁ : ZMod (p ^ m)) * b - (n₂ : ZMod (p ^ m)) * a) * ζm ^ ((a.val : ℤ) * d + (b.val : ℤ) * d') = 0) := by
  intro p m _ K _ _ ψ ζm _ hψ hζ n₁ n₂ d d' hn
  have hp : p.Prime := Fact.out
  have he := AddChar.zmodChar_primitive_of_primitive_root (p ^ m) hζ
  set e := AddChar.zmodChar (p ^ m) hζ.pow_eq_one with he_def
  have hG : gaussS p m ψ ζm = gaussSum ψ e := rfl
  have hz : ∀ a b : ZMod (p ^ m), ζm ^ ((a.val : ℤ) * d + (b.val : ℤ) * d') =
      e (a * (d : ZMod (p ^ m)) + b * (d' : ZMod (p ^ m))) := by
    intro a b
    rw [zpow_eq hζ]
    congr 1
    simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  simp only [hz, hG]
  rw [← Nat.cast_pow]
  by_cases h1 : (p : ℤ) ∣ n₁
  · have h2 : ¬ (p : ℤ) ∣ n₂ := fun h => hn ⟨h1, h⟩
    obtain ⟨w, hw⟩ := unit_of_not_dvd p m hp n₂ h2
    have hw' : (-(n₂ : ZMod (p ^ m))) * (-w) = 1 := by rw [neg_mul_neg, hw]
    have key := eval ψ hψ e he (-(n₂ : ZMod (p ^ m))) (-(n₁ : ZMod (p ^ m))) (-w)
      (d' : ZMod (p ^ m)) (d : ZMod (p ^ m)) hw'
    have hswap : ∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m),
        ψ ((n₁ : ZMod (p ^ m)) * b - (n₂ : ZMod (p ^ m)) * a) *
          e (a * (d : ZMod (p ^ m)) + b * (d' : ZMod (p ^ m))) =
        ∑ a : ZMod (p ^ m), ∑ b : ZMod (p ^ m),
        ψ (-(n₂ : ZMod (p ^ m)) * b - -(n₁ : ZMod (p ^ m)) * a) *
          e (a * (d' : ZMod (p ^ m)) + b * (d : ZMod (p ^ m))) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [show -(n₂ : ZMod (p ^ m)) * b - -(n₁ : ZMod (p ^ m)) * a =
        (n₁ : ZMod (p ^ m)) * a - (n₂ : ZMod (p ^ m)) * b by ring, add_comm (a * (d' : ZMod (p ^ m)))]
    rw [hswap]
    rw [neg_neg] at key
    exact ⟨fun u hd hd' => key.1 u hd' hd,
      fun hno => key.2 fun ⟨u, hd', hd⟩ => hno ⟨u, hd, hd'⟩⟩
  · obtain ⟨w, hw⟩ := unit_of_not_dvd p m hp n₁ h1
    exact eval ψ hψ e he _ _ w _ _ hw

end GlobalTheory.KummerEisensteinGalois.ChSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SeparatingFamilySumClosedUnderProd
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory

theorem sepFamily_prod : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L] (F : Subfield L) (ι : Type) (s : Finset ι) (x y : ι → L), (∀ j ∈ s, x j ∈ F ∧ y j ∈ F ∧ v (x j) ≤ 1 ∧ v (y j) ≤ 1) → ∃ (n : ℕ) (a b : Fin n → L), (∀ i, a i ∈ F ∧ b i ∈ F ∧ v (a i) ≤ 1 ∧ v (b i) ≤ 1) ∧ ∀ σ : G, ∑ i, a i * σ • b i = ∏ j ∈ s, (x j - σ • y j) := by
  intro L _ v G _ _ F ι s x y hs
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨1, fun _ => 1, fun _ => 1, fun _ => ⟨F.one_mem, F.one_mem, by simp, by simp⟩,
      fun σ => by simp⟩
  | insert j s hj ih =>
    obtain ⟨n, a, b, hab, hsum⟩ := ih (fun k hk => hs k (Finset.mem_insert_of_mem hk))
    obtain ⟨hxF, hyF, hxv, hyv⟩ := hs j (Finset.mem_insert_self j s)
    refine ⟨n + n, Fin.append (fun i => x j * a i) (fun i => - a i),
      Fin.append b (fun i => y j * b i), ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [Fin.append_left]
        obtain ⟨h1, h2, h3, h4⟩ := hab i
        exact ⟨F.mul_mem hxF h1, h2, by rw [map_mul]; exact mul_le_one' hxv h3, h4⟩
      · simp only [Fin.append_right]
        obtain ⟨h1, h2, h3, h4⟩ := hab i
        exact ⟨F.neg_mem h1, F.mul_mem hyF h2, by rw [Valuation.map_neg]; exact h3,
          by rw [map_mul]; exact mul_le_one' hyv h4⟩
    · intro σ
      rw [Finset.prod_insert hj, ← hsum σ, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, smul_mul']
      have e1 : ∑ i, x j * a i * σ • b i = x j * ∑ i, a i * σ • b i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
      have e2 : ∑ i, -a i * (σ • y j * σ • b i) = -(σ • y j * ∑ i, a i * σ • b i) := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [e1, e2]; ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ZpowCongrOfModEq
section
open GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.KummerEisensteinGalois

lemma zpow_congr_of_modEq {K : Type} [Field K] {ζ : K} {M : ℕ} (hζ : IsPrimitiveRoot ζ M) (hM : 0 < M)
    {u v : ℤ} (h : u ≡ v [ZMOD M]) : ζ ^ u = ζ ^ v := by
  have h0 : ζ ≠ 0 := hζ.ne_zero hM.ne'
  have h1 : ζ ^ (u - v) = 1 := (hζ.zpow_eq_one_iff_dvd (u - v)).2 (Int.ModEq.dvd h.symm)
  calc ζ ^ u = ζ ^ (v + (u - v)) := by rw [add_sub_cancel]
    _ = ζ ^ v * ζ ^ (u - v) := zpow_add₀ h0 _ _
    _ = ζ ^ v := by rw [h1, mul_one]

end GlobalTheory.KummerEisensteinGalois
end

