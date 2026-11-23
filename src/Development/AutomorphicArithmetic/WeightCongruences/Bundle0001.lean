module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.WeightCongruences.ProdNegOneZpow
section
namespace UpperTheory

variable {E K K' : Type} [Field E] [Field K] [Field K'] {ι ι' : Type} [Fintype ι] [Fintype ι']

def MU (φ : ι → E →+* K) (e : ι → ℤ) : Prop :=
  ∀ z : E, (∃ m : ℕ, 0 < m ∧ z ^ m = 1) → ∏ i, φ i z ^ e i = 1

def MUQ (φ : ι → E →+* K) (e : ι → ℚ) : Prop :=
  ∃ a : ι → ℤ, (∀ i, e i = a i) ∧ MU φ a

theorem root_ne_zero {z : E} (hz : ∃ m : ℕ, 0 < m ∧ z ^ m = 1) : z ≠ 0 := by
  obtain ⟨m, hm, h⟩ := hz
  rintro rfl
  rw [zero_pow hm.ne'] at h
  exact zero_ne_one h

theorem prod_neg_one_zpow (e : ι → ℤ) : ∏ i, (-1 : K) ^ e i = (-1) ^ (∑ i, e i) := by
  classical
  refine Finset.induction_on (motive := fun s => ∏ i ∈ s, (-1 : K) ^ e i = (-1) ^ (∑ i ∈ s, e i)) Finset.univ (by simp) ?_
  intro a s ha ih
  rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ (by norm_num)]

namespace MU

variable {φ : ι → E →+* K} {e e' : ι → ℤ}

theorem add (h : MU φ e) (h' : MU φ e') : MU φ (e + e') := by
  intro z hz
  have hne : ∀ i, φ i z ≠ 0 := fun i => (map_ne_zero (φ i)).2 (root_ne_zero hz)
  show ∏ i, φ i z ^ (e i + e' i) = 1
  rw [Finset.prod_congr rfl fun i _ => zpow_add₀ (hne i) (e i) (e' i), Finset.prod_mul_distrib, h z hz, h' z hz, one_mul]

theorem neg (h : MU φ e) : MU φ (-e) := by
  intro z hz
  show ∏ i, φ i z ^ (-e i) = 1
  simp_rw [zpow_neg]
  rw [Finset.prod_inv_distrib, h z hz, inv_one]

theorem smul (h : MU φ e) (c : ℤ) : MU φ (fun i => c * e i) := by
  intro z hz
  show ∏ i, φ i z ^ (c * e i) = 1
  simp_rw [mul_comm c, zpow_mul]
  rw [Finset.prod_zpow, h z hz, one_zpow]

theorem const (h : MU φ (fun _ => 1)) (c : ℤ) : MU φ (fun _ => c) := by
  have h2 := h.smul c
  simpa using h2

theorem add_const (h : MU φ e) (h1 : MU φ (fun _ => 1)) (c : ℤ) : MU φ (fun i => e i + c) :=
  h.add (h1.const c)

theorem even [CharZero K] (h : MU φ e) : Even (∑ i, e i) := by
  have h1 := h (-1) ⟨2, by norm_num, by norm_num⟩
  simp only [map_neg, map_one] at h1
  rw [prod_neg_one_zpow] at h1
  by_contra hodd
  rw [Int.not_even_iff_odd] at hodd
  rw [hodd.neg_one_zpow] at h1
  norm_num at h1

end MU

namespace MUQ

variable {φ : ι → E →+* K} {e : ι → ℚ}

theorem even [CharZero K] (h : MUQ φ e) : ∃ z : ℤ, ∑ i, e i = 2 * (z : ℚ) := by
  obtain ⟨a, ha, hm⟩ := h
  obtain ⟨z, hz⟩ := hm.even
  refine ⟨z, ?_⟩
  simp only [ha]
  rw [← Int.cast_sum, hz]
  push_cast
  ring

theorem mu (h : MUQ φ e) {a : ι → ℤ} (ha : ∀ i, e i = a i) : MU φ a := by
  obtain ⟨b, hb, hm⟩ := h
  have hab : a = b := funext fun i => by
    have h3 := (ha i).symm.trans (hb i)
    exact_mod_cast h3
  subst hab
  exact hm

theorem add_const (h : MUQ φ e) (h1 : MU φ (fun _ => 1)) (c : ℤ) : MUQ φ (fun i => e i + c) := by
  obtain ⟨a, ha, hm⟩ := h
  exact ⟨fun i => a i + c, fun i => by simp [ha], hm.add_const h1 c⟩

end MUQ

end UpperTheory
end

-- bundled from Development.AutomorphicArithmetic.WeightCongruences.TorsionOrderLeTwoMulFinrankSq
section
open NumberField

private theorem le_mul_totient_sq (n : ℕ) : n ≤ (if Even n then 2 else 1) * n.totient ^ 2 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    rw [Nat.totient_prime_pow hp hk]
    by_cases h2 : p = 2
    · subst h2
      have he : Even (2 ^ k) := (Nat.even_pow.2 ⟨even_two, hk.ne'⟩)
      rw [if_pos he]
      have : 2 ^ k ≤ 2 * (2 ^ (k - 1)) ^ 2 := by
        rw [← pow_mul, ← pow_succ']
        exact Nat.pow_le_pow_right (by norm_num) (by omega)
      simpa using this
    · have hodd : ¬ Even (p ^ k) := by
        rw [Nat.even_pow]; rintro ⟨he, -⟩
        exact h2 ((Nat.Prime.even_iff hp).1 he)
      rw [if_neg hodd, one_mul]
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        rcases Nat.lt_or_ge p 3 with h | h
        · interval_cases p <;> simp_all
        · exact h
      have hsq : p ≤ (p - 1) ^ 2 := by
        obtain ⟨q, rfl⟩ : ∃ q, p = q + 3 := ⟨p - 3, by omega⟩
        rw [show q + 3 - 1 = q + 2 by omega]
        nlinarith
      calc p ^ k ≤ p ^ (2 * (k - 1) + 1) := Nat.pow_le_pow_right hp.pos (by omega)
        _ = (p ^ (k - 1)) ^ 2 * p := by rw [pow_succ, pow_mul, ← pow_mul, mul_comm 2]; ring
        _ ≤ (p ^ (k - 1)) ^ 2 * (p - 1) ^ 2 := Nat.mul_le_mul_left _ hsq
        _ = (p ^ (k - 1) * (p - 1)) ^ 2 := by ring
  | zero => simp
  | one => simp
  | coprime a b _ _ hab iha ihb =>
    rw [Nat.totient_mul hab]
    have hc : (if Even (a * b) then 2 else 1) = (if Even a then 2 else 1) * (if Even b then 2 else 1) := by
      by_cases ha : Even a <;> by_cases hb : Even b
      · exfalso
        have h2a : 2 ∣ a := even_iff_two_dvd.1 ha
        have h2b : 2 ∣ b := even_iff_two_dvd.1 hb
        have h := Nat.dvd_gcd h2a h2b
        rw [Nat.Coprime.gcd_eq_one hab] at h
        omega
      · simp [ha, hb, Nat.even_mul]
      · simp [ha, hb, Nat.even_mul]
      · have : ¬ Even (a * b) := by rw [Nat.even_mul]; tauto
        simp [ha, hb, this]
    rw [hc]
    calc a * b ≤ ((if Even a then 2 else 1) * a.totient ^ 2) * ((if Even b then 2 else 1) * b.totient ^ 2) :=
          Nat.mul_le_mul iha ihb
      _ = _ := by ring

private theorem le_two_totient_sq (n : ℕ) : n ≤ 2 * n.totient ^ 2 := by
  have h := le_mul_totient_sq n
  have hc : (if Even n then 2 else 1) ≤ 2 := by split_ifs <;> norm_num
  exact h.trans (Nat.mul_le_mul_right _ hc)

private theorem torsion_order_le_two_mul_finrank_sq (E : Type) [Field E] [NumberField E] :
    Units.torsionOrder E ≤ 2 * (Module.finrank ℚ E) ^ 2 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Units.torsion E)
  have hord : orderOf g = Units.torsionOrder E := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg]
    rfl
  have hpos : 0 < Units.torsionOrder E := Units.torsionOrder_pos E

  let ζ : E := algebraMap (𝓞 E) E (((g : (𝓞 E)ˣ) : 𝓞 E))
  have hprim : IsPrimitiveRoot ζ (Units.torsionOrder E) := by
    have h1 : IsPrimitiveRoot g (orderOf g) := IsPrimitiveRoot.orderOf g
    rw [hord] at h1
    have h2 := h1.map_of_injective (f := (Units.torsion E).subtype) Subtype.val_injective
    have h3 := h2.map_of_injective (f := Units.coeHom (𝓞 E)) (fun a b h => Units.ext h)
    exact h3.map_of_injective (f := algebraMap (𝓞 E) E) (FaithfulSMul.algebraMap_injective _ _)
  have : NeZero (Units.torsionOrder E) := ⟨hpos.ne'⟩
  have hmin : minpoly ℚ ζ = Polynomial.cyclotomic (Units.torsionOrder E) ℚ :=
    (hprim.minpoly_eq_cyclotomic_of_irreducible (Polynomial.cyclotomic.irreducible_rat hpos)).symm
  have hdeg : (Units.torsionOrder E).totient ≤ Module.finrank ℚ E := by
    rw [← Polynomial.natDegree_cyclotomic (Units.torsionOrder E) ℚ, ← hmin]
    exact minpoly.natDegree_le ζ
  calc Units.torsionOrder E ≤ 2 * (Units.torsionOrder E).totient ^ 2 := le_two_totient_sq _
    _ ≤ 2 * (Module.finrank ℚ E) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hdeg 2)

theorem UpperTheory.torsionOrder_le_two_mul_finrank_sq :
    ∀ (E : Type) [Field E] [NumberField E], NumberField.Units.torsionOrder E ≤ 2 * Module.finrank ℚ E ^ 2 := by
  intro E _ _
  exact torsion_order_le_two_mul_finrank_sq E
end

