module

public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0001
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0004
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.FrobeniusLocalisation.MemRam
section
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

theorem UpperTheory.HF.mem_ram :
    ∀ {φ : Frame} (H : HostAx φ) {l : ℕ}, l.Prime → (l ∈ H.ram ↔ H.el l ≠ 1) ∧ (l ∈ H.ram ↔ l ∣ H.condE) ∧ (l ∈ H.ram ↔ H.vdH l ≠ 0) ∧ (l ∈ H.ram → 1 / 2 ≤ H.vdH l) ∧ (l ∈ H.ram → 1 - 1 / (H.el l : ℝ) ≤ H.vdH l) := by
  intro φ H l hl
  haveI : Fact l.Prime := ⟨hl⟩
  have hN : H.condN ≠ 0 := H.condN_ne_zero
  obtain ⟨hE, hEpos, _⟩ := condE_spec H.toHostRaw
  set v := H.condN.factorization l with hv
  set e := H.condE.factorization l with he
  have hlay := fun j (hj : j ≤ v) => layer_bot H.toHostRaw hl hj
  have hev : e ≤ v := ((hlay 0 (Nat.zero_le _)).2.2)
  have hcardbot : ∀ j, j ≤ v →
      (Nat.card (H.imgOne (H.condN / l ^ v * l ^ j)) = 1 ↔ e ≤ j) := by
    intro j hj
    rw [Subgroup.card_eq_one]
    exact (hlay j hj).1
  have hdvdE : l ∣ H.condE ↔ 0 < e := by
    rw [he]
    exact hl.dvd_iff_one_le_factorization hEpos.ne'
  have hel : H.el l = Nat.card (H.imgOne (H.condN / l ^ v * l ^ 0)) := by
    simp [HostRaw.el, HostRaw.inertG, hv]
  have hA : H.el l ≠ 1 ↔ l ∣ H.condE := by
    rw [hel, Ne, hcardbot 0 (Nat.zero_le _), hdvdE]
    omega
  have hT : ∀ n : ℕ, 0 ≤ 1 - 1 / (n : ℝ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast h
      have : 1 / (n : ℝ) ≤ 1 := by
        rw [div_le_one (by linarith)]
        exact h1
      linarith
  have hT0 : ∀ n : ℕ, (1 - 1 / (n : ℝ) = 0 ↔ n = 1) := by
    intro n
    constructor
    · intro h
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · simp [h0] at h
      · have hn : (n : ℝ) ≠ 0 := by positivity
        have : (n : ℝ) = 1 := by
          field_simp at h
          linarith
        exact_mod_cast this
    · intro h
      simp [h]
  have hB : H.vdH l ≠ 0 ↔ l ∣ H.condE := by
    rw [vd_formula H hl, Ne, Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hT _), hdvdE]
    constructor
    · intro h
      by_contra h0
      apply h
      intro j hj
      rw [hT0, hcardbot j (Finset.mem_range.1 hj).le]
      omega
    · intro h hall
      have h0 := hall 0 (Finset.mem_range.2 (lt_of_lt_of_le h hev))
      rw [hT0, hcardbot 0 (Nat.zero_le _)] at h0
      omega
  have hC : l ∈ H.ram ↔ H.vdH l ≠ 0 := by
    have hd : (NumberField.discr H.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero H.E)
    have hr : (Module.finrank ℚ H.E : ℝ) ≠ 0 := by
      have := Module.finrank_pos (R := ℚ) (M := H.E)
      positivity
    simp only [HostRaw.ram, Nat.mem_primeFactors, HostRaw.vdH, Ne, div_eq_zero_iff, hr, or_false,
      Nat.cast_eq_zero, Nat.padicValNat_def, hl, hd, not_false_eq_true, true_and, and_true]
    exact dvd_iff_multiplicity_ne_zero (p := l) hd
  have hlow : l ∈ H.ram → 1 - 1 / (H.el l : ℝ) ≤ H.vdH l := by
    intro hram
    have hpos : 0 < e := hdvdE.1 (hB.1 (hC.1 hram))
    rw [vd_formula H hl, hel]
    exact Finset.single_le_sum (f := fun j => 1 - 1 / (Nat.card (H.imgOne (H.condN / l ^ v * l ^ j)) : ℝ))
      (fun j _ => hT _) (Finset.mem_range.2 (lt_of_lt_of_le hpos hev))
  refine ⟨hC.trans (hB.trans hA.symm), hC.trans hB, hC, fun hram => ?_, hlow⟩
  have h2 : 2 ≤ H.el l := by
    have h1 := (hC.trans (hB.trans hA.symm)).1 hram
    have := HostRaw.el_pos H.toHostRaw l
    omega
  have h2r : (2 : ℝ) ≤ H.el l := by exact_mod_cast h2
  have hq : 1 / (H.el l : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2r
  linarith [hlow hram]
end

-- bundled from Development.AutomorphicArithmetic.FrobeniusLocalisation.VdLe
section
open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem arith {l : ℕ} (hl : l.Prime) (k : ℕ) :
    ∑ j ∈ Finset.range (k + 1), (1 - ((l ^ j).totient : ℝ) / ((l ^ (k + 1)).totient : ℝ)) =
      ((k + 1 : ℕ) : ℝ) - 1 / ((l : ℝ) - 1) := by
  rw [Finset.sum_sub_distrib, ← Finset.sum_div]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hs : (∑ j ∈ Finset.range (k + 1), ((l ^ j).totient : ℝ)) = (l : ℝ) ^ k := by
    exact_mod_cast Formalism.HC.Der.Rd.sum_totient_pow hl k
  rw [hs, Nat.totient_prime_pow_succ hl]
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hl0 : (l : ℝ) - 1 ≠ 0 := by linarith
  have hp : (l : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by linarith)
  push_cast [Nat.cast_sub hl.one_le]
  congr 1
  rw [div_mul_eq_div_div, div_self hp]

private theorem intCast_mul_mul_mul_eq_of_mul_eq {l : ℕ} (hl : l.Prime) {j e c : ℕ} (hje : j ≤ e)
    (hd : c ∣ (l ^ e).totient / (l ^ j).totient) :
    1 - 1 / (c : ℝ) ≤ 1 - ((l ^ j).totient : ℝ) / ((l ^ e).totient : ℝ) := by
  have hjd : (l ^ j).totient ∣ (l ^ e).totient := Nat.totient_dvd_of_dvd (pow_dvd_pow l hje)
  have hj0 : 0 < (l ^ j).totient := Nat.totient_pos.2 (pow_pos hl.pos j)
  have he0 : 0 < (l ^ e).totient := Nat.totient_pos.2 (pow_pos hl.pos e)
  have hq0 : 0 < (l ^ e).totient / (l ^ j).totient := Nat.div_pos (Nat.le_of_dvd he0 hjd) hj0
  have hc0 : 0 < c := Nat.pos_of_dvd_of_pos hd hq0
  have hcle : c ≤ (l ^ e).totient / (l ^ j).totient := Nat.le_of_dvd hq0 hd
  have hq : (((l ^ e).totient / (l ^ j).totient : ℕ) : ℝ) =
      ((l ^ e).totient : ℝ) / ((l ^ j).totient : ℝ) :=
    Nat.cast_div hjd (by exact_mod_cast hj0.ne')
  have h1 : (1 : ℝ) / (((l ^ e).totient / (l ^ j).totient : ℕ) : ℝ) ≤ 1 / (c : ℝ) :=
    one_div_le_one_div_of_le (by exact_mod_cast hc0) (by exact_mod_cast hcle)
  rw [hq, one_div_div] at h1
  linarith

theorem UpperTheory.HF.vd_le :
    ∀ {φ : Frame} (H : HostAx φ) {l : ℕ}, l.Prime → H.vdH l ≤ (H.sl l : ℝ) - 1 / ((l : ℝ) - 1) ∧ H.vdH l ≤ (H.condE.factorization l : ℝ) := by
  intro φ H l hl
  have heN := (layer_bot H.toHostRaw hl (Nat.zero_le (H.condN.factorization l))).2.2
  simp only [UpperTheory.HF.Formalism.HC.HostRaw.sl]
  generalize hE : (UpperTheory.HF.Formalism.HC.HostRaw.condE H.toHostRaw).factorization l = e at heN ⊢
  have hcard : ∀ j ∈ Finset.range (H.condN.factorization l),
      (1 - 1 / (Nat.card (UpperTheory.HF.Formalism.HC.HostRaw.imgOne H.toHostRaw
        (H.condN / l ^ H.condN.factorization l * l ^ j)) : ℝ)) ≤
      if j < e then 1 - ((l ^ j).totient : ℝ) / ((l ^ e).totient : ℝ) else 0 := by
    intro j hj
    have hjN : j ≤ H.condN.factorization l := (Finset.mem_range.1 hj).le
    obtain ⟨hbot, hdvd, -⟩ := layer_bot H.toHostRaw hl hjN
    rw [hE] at hbot hdvd
    split_ifs with hje
    · exact intCast_mul_mul_mul_eq_of_mul_eq hl hje.le (hdvd hje.le)
    · push_neg at hje
      rw [hbot.2 hje, Subgroup.card_bot]
      simp
  have hsum := Finset.sum_le_sum hcard
  rw [← vd_formula H hl] at hsum
  have hS : ∑ j ∈ Finset.range (H.condN.factorization l),
      (if j < e then 1 - ((l ^ j).totient : ℝ) / ((l ^ e).totient : ℝ) else 0) =
      ∑ j ∈ Finset.range e, (1 - ((l ^ j).totient : ℝ) / ((l ^ e).totient : ℝ)) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le heN
    rw [hm, Finset.sum_range_add]
    have h2 : ∑ x ∈ Finset.range m,
        (if e + x < e then 1 - ((l ^ (e + x)).totient : ℝ) / ((l ^ e).totient : ℝ) else 0) = 0 :=
      Finset.sum_eq_zero (fun x _ => if_neg (by omega))
    rw [h2, add_zero]
    exact Finset.sum_congr rfl (fun j hj => if_pos (Finset.mem_range.1 hj))
  rw [hS] at hsum
  have hle : ∑ j ∈ Finset.range e, (1 - ((l ^ j).totient : ℝ) / ((l ^ e).totient : ℝ)) ≤ (e : ℝ) := by
    calc _ ≤ ∑ j ∈ Finset.range e, (1 : ℝ) :=
          Finset.sum_le_sum (fun j _ => sub_le_self 1 (by positivity))
      _ = e := by simp
  refine ⟨?_, hsum.trans hle⟩
  rcases e with _ | k
  · have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
    have h1 : 1 / ((l : ℝ) - 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    simp only [Finset.range_zero, Finset.sum_empty] at hsum
    simp only [Nat.zero_eq, zero_le, max_eq_left, Nat.cast_one]
    linarith
  · rw [arith hl k] at hsum
    rw [max_eq_right (by omega)]
    exact hsum
end

