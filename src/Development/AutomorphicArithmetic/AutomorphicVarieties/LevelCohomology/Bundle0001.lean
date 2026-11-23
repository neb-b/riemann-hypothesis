module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.ExistsPowDvdSubOfTwoPowDvdSubOne
section
theorem UpperTheory.exists_pow_dvd_sub_of_two_pow_dvd_sub_one :
    ∀ (Q a c : ℤ) (e n : ℕ), 2 ≤ e → Odd a → Q = 1 + 2 ^ e * a → (2 : ℤ) ^ e ∣ c - 1 → ∃ i : ℕ, (2 : ℤ) ^ n ∣ Q ^ i - c := by
  intro Q a c e n he ha hQ hc
  have hL : ∀ m : ℕ, ∃ u : ℤ, Odd u ∧ Q ^ (2 ^ m) = 1 + 2 ^ (e + m) * u := by
    intro m
    induction m with
    | zero => exact ⟨a, ha, by simp [hQ]⟩
    | succ m ih =>
      obtain ⟨u, hu, hQu⟩ := ih
      obtain ⟨k, hk⟩ : ∃ k, e + m = k + 1 := ⟨e + m - 1, by omega⟩
      refine ⟨u + 2 ^ k * u ^ 2, ?_, ?_⟩
      · have hev : Even ((2 : ℤ) ^ k * u ^ 2) := by
          have hk1 : k ≠ 0 := by omega
          exact (Int.even_pow.2 ⟨even_two, hk1⟩).mul_right _
        exact hu.add_even hev
      · rw [pow_succ, pow_mul, hQu, show e + (m + 1) = k + 2 by omega, hk]
        ring
  have hQodd : Odd Q := by
    have hev : Even ((2 : ℤ) ^ e * a) :=
      (Int.even_pow.2 ⟨even_two, by omega⟩).mul_right _
    rw [hQ, add_comm]
    exact hev.add_one
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    by_cases hne : n + 1 ≤ e
    · refine ⟨0, ?_⟩
      have h1 : (2 : ℤ) ^ (n + 1) ∣ 2 ^ e := pow_dvd_pow 2 hne
      have h2 : (2 : ℤ) ^ (n + 1) ∣ c - 1 := h1.trans hc
      have h3 : Q ^ 0 - c = -(c - 1) := by ring
      rw [h3]
      exact (dvd_neg).2 h2
    · obtain ⟨i, t, ht⟩ := ih
      obtain ⟨u, hu, hQu⟩ := hL (n - e)
      rw [show e + (n - e) = n by omega] at hQu
      rcases Int.even_or_odd t with ⟨s, hs⟩ | hto
      · refine ⟨i, s, ?_⟩
        rw [ht, hs, pow_succ]
        ring
      · have hsum : Even (t + u * Q ^ i) := hto.add_odd (hu.mul (hQodd.pow))
        obtain ⟨s, hs⟩ := hsum
        refine ⟨i + 2 ^ (n - e), s, ?_⟩
        have : Q ^ (i + 2 ^ (n - e)) - c = 2 ^ n * (t + u * Q ^ i) := by
          rw [pow_add, hQu]
          linear_combination ht
        rw [this, hs, pow_succ]
        ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.ExistsResidueMapPadicAlgClIntegers
section
theorem UpperTheory.exists_residue_map_padicAlgCl_integers :
    ∀ (l : ℕ) [Fact l.Prime], ∃ (k : Type) (_ : Field k) (_ : CharP k l) (A : Subring (PadicAlgCl l)) (red : A →+* k), (∀ x : PadicAlgCl l, x ∈ A ↔ ‖x‖ ≤ 1) ∧ ∀ x : A, red x = 0 ↔ ‖(x : PadicAlgCl l)‖ < 1 := by
  intro l _
  have hna : ∀ x y : PadicAlgCl l, ‖x + y‖ ≤ max ‖x‖ ‖y‖ := fun x y =>
    IsUltrametricDist.norm_add_le_max x y
  let A : Subring (PadicAlgCl l) :=
    { carrier := {x | ‖x‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, norm_mul] at *
        exact mul_le_one₀ ha (norm_nonneg _) hb
      one_mem' := by simp
      add_mem' := fun {a b} ha hb => (hna a b).trans (max_le ha hb)
      zero_mem' := by simp
      neg_mem' := fun {a} ha => by simpa using ha }
  have hA : ∀ x : PadicAlgCl l, x ∈ A ↔ ‖x‖ ≤ 1 := fun x => Iff.rfl
  let I : Ideal A :=
    { carrier := {x | ‖(x : PadicAlgCl l)‖ < 1}
      add_mem' := fun {a b} ha hb => lt_of_le_of_lt (hna _ _) (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        show ‖((c * x : A) : PadicAlgCl l)‖ < 1
        rw [Subring.coe_mul, norm_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) c.2) hx }
  have hI : ∀ x : A, x ∈ I ↔ ‖(x : PadicAlgCl l)‖ < 1 := fun x => Iff.rfl
  have hmax : I.IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨by simp [hI], fun J x hIJ hx hxJ => ?_⟩
    rw [hI, not_lt] at hx
    have h1 : ‖(x : PadicAlgCl l)‖ = 1 := le_antisymm x.2 hx
    have hx0 : (x : PadicAlgCl l) ≠ 0 := by
      intro h
      rw [h, norm_zero] at h1
      exact zero_ne_one h1
    have hinv : (x : PadicAlgCl l)⁻¹ ∈ A := by
      rw [hA, norm_inv, h1, inv_one]
    have : (⟨_, hinv⟩ : A) * x = 1 := Subtype.ext (inv_mul_cancel₀ hx0)
    rw [← this]
    exact J.mul_mem_left _ hxJ
  haveI := hmax
  have hl : ‖((l : A) : PadicAlgCl l)‖ < 1 := by
    have h := congrArg NNReal.toReal (PadicAlgCl.valuation_p l)
    rw [PadicAlgCl.valuation_coe] at h
    push_cast
    rw [h]
    have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    simp only [one_div, NNReal.coe_inv, NNReal.coe_natCast]
    exact inv_lt_one_of_one_lt₀ hl1
  refine ⟨A ⧸ I, Ideal.Quotient.field I, ?_, A, Ideal.Quotient.mk I, hA, fun x => ?_⟩
  · rw [CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)]
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    exact hl
  · rw [Ideal.Quotient.eq_zero_iff_mem]
    exact hI x
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.LxPartial
section
open Finset

namespace UpperTheory.V.X

private theorem shift_sum {K : Type} [CommRing K] (F s : ℕ) (w : ℕ → K) :
    ∑ a ∈ range F, w (s + a) = ∑ a ∈ range F, w a + ∑ a ∈ range s, (w (F + a) - w a) := by
  have h1 := Finset.sum_range_add w s F
  have h2 := Finset.sum_range_add w F s
  rw [add_comm F s, h1] at h2
  rw [Finset.sum_sub_distrib]
  linear_combination h2

theorem lx_partial {K : Type} [Field K] [CharZero K] (f N : ℕ) [NeZero N] (hf : 0 < f) (hc : Nat.Coprime f N) (φ : ℕ → K)
    (hper : ∀ a, φ (a + f) = φ a) (B : Subring K) (hφ : ∀ a, φ a ∈ B) (hN : (N : K)⁻¹ ∈ B) :
    ∃ (g : ZMod N → K) (c : K), (∀ u, g u ∈ B) ∧ c ∈ B ∧
      (∀ t : ℕ, f * t ≤ N → ∀ u, g u - g (u - (f * t : ℕ)) = t * c - if u.val < f * t then φ u.val else 0) ∧
      ∀ ξ : ZMod N → K, ∑ u, ξ u = 0 → ∑ a ∈ range (f * N), φ a * ξ a * a = (f * N : ℕ) * ∑ u, ξ u * g u := by
  classical
  let ψ : ZMod N → ℕ → K := fun u a => if (a : ZMod N) = u then φ a else 0
  let A : ZMod N → K := fun u => ∑ a ∈ range (f * N), ψ u a * a
  let S : ZMod N → K := fun u => ∑ a ∈ range (f * N), ψ u a
  have hF : ((f * N : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.mul_ne_zero hf.ne' (NeZero.ne N))
  have hf' : (f : K) ≠ 0 := Nat.cast_ne_zero.2 hf.ne'
  have hN' : (N : K) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hψB : ∀ u a, ψ u a ∈ B := by
    intro u a; simp only [ψ]; split_ifs
    · exact hφ a
    · exact B.zero_mem
  have hper' : ∀ t a, φ (f * t + a) = φ a := by
    intro t a
    induction t with
    | zero => simp
    | succ t ih => rw [show f * (t + 1) + a = (f * t + a) + f by ring, hper, ih]
  have hψ : ∀ (t : ℕ) u a, ψ u (f * t + a) = ψ (u - (f * t : ℕ)) a := by
    intro t u a
    simp only [ψ, hper']
    congr 1
    rw [Nat.cast_add, eq_sub_iff_add_eq, add_comm]
  have hψF : ∀ u a, ψ u (f * N + a) = ψ u a := by
    intro u a; rw [hψ]; simp
  have hS : ∀ (t : ℕ) u, S (u - (f * t : ℕ)) = S u := by
    intro t u
    simp only [S, ← hψ]
    rw [shift_sum (f * N) (f * t) (ψ u)]
    simp [hψF]
  have hA : ∀ (t : ℕ) u, A u - A (u - (f * t : ℕ)) = (f * t : ℕ) * S u - (f * N : ℕ) * ∑ a ∈ range (f * t), ψ u a := by
    intro t u
    have h := shift_sum (f * N) (f * t) (fun a => ψ u a * a)
    simp only [hψF] at h
    have e1 : ∑ a ∈ range (f * N), ψ u (f * t + a) * ((f * t + a : ℕ) : K) = A (u - (f * t : ℕ)) + (f * t : ℕ) * S (u - (f * t : ℕ)) := by
      simp only [A, S, hψ, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Nat.cast_add]; ring
    have e2 : ∑ a ∈ range (f * t), (ψ u a * ((f * N + a : ℕ) : K) - ψ u a * a) = (f * N : ℕ) * ∑ a ∈ range (f * t), ψ u a := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Nat.cast_add]; ring
    rw [e1, e2, hS] at h
    simp only [A] at h ⊢
    linear_combination -h
  have hgen : ∀ u : ZMod N, ∃ t : ℕ, u - (f * t : ℕ) = 0 := by
    intro u
    obtain ⟨v, hv⟩ := (ZMod.isUnit_iff_coprime f N).2 hc
    refine ⟨((v⁻¹ : (ZMod N)ˣ) * u : ZMod N).val, ?_⟩
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, ← hv, Units.mul_inv_cancel_left, sub_self]
  have hS0 : ∀ u, S u = S 0 := by
    intro u
    obtain ⟨t, ht⟩ := hgen u
    rw [← hS t u, ht]
  have hcB : S 0 * (N : K)⁻¹ ∈ B := B.mul_mem (B.sum_mem fun a _ => hψB _ _) hN
  have hd : ∀ (t : ℕ) u, A u / (f * N : ℕ) - A (u - (f * t : ℕ)) / (f * N : ℕ) =
      t * (S 0 * (N : K)⁻¹) - ∑ a ∈ range (f * t), ψ u a := by
    intro t u
    rw [← sub_div, hA, hS0]
    push_cast
    field_simp
  refine ⟨fun u => A u / (f * N : ℕ) - A 0 / (f * N : ℕ), S 0 * (N : K)⁻¹, ?_, hcB, ?_, ?_⟩
  · intro u
    obtain ⟨t, ht⟩ := hgen u
    have := hd t u
    rw [ht] at this
    simp only [this]
    exact B.sub_mem (B.mul_mem (natCast_mem B t) hcB) (B.sum_mem fun a _ => hψB _ _)
  · intro t ht u
    rw [sub_sub_sub_cancel_right, hd]
    congr 1
    have : ∀ a ∈ range (f * t), ψ u a = if u.val = a then φ a else 0 := by
      intro a ha
      rw [mem_range] at ha
      simp only [ψ]
      congr 1
      apply propext
      constructor
      · rintro rfl
        exact ZMod.val_natCast_of_lt (by omega)
      · rintro rfl
        exact ZMod.natCast_zmod_val u
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
    simp
  · intro ξ hξ
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, hξ, zero_mul, mul_zero, sub_zero, Finset.mul_sum]
    have : ∀ u, ((f * N : ℕ) : K) * (ξ u * (A u / (f * N : ℕ))) = ∑ a ∈ range (f * N), ξ u * (ψ u a * a) := by
      intro u
      rw [← Finset.mul_sum]
      simp only [A]
      field_simp
    simp only [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [ψ, ite_mul, mul_ite, zero_mul, mul_zero, Finset.sum_ite_eq, mem_univ, if_true]
    ring

end UpperTheory.V.X
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.PrimitiveTwoPowCharacterOneAddHalfEqNegOne
section
theorem UpperTheory.primitive_two_pow_character_one_add_half_eq_neg_one :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ), 2 ≤ n → ∀ ξ : DirichletCharacter R (2 ^ n), ξ.IsPrimitive → ξ (1 + 2 ^ (n - 1)) = -1 := by
  intro R _ _ n hn ξ hξ
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hk : k + 2 - 1 = k + 1 := by omega
  rw [hk]
  have h2 : (2 : ZMod (2 ^ (k + 2))) ^ (k + 2) = 0 := by
    have := ZMod.natCast_self (2 ^ (k + 2))
    push_cast at this
    exact this
  have huu : ((1 : ZMod (2 ^ (k + 2))) + 2 ^ (k + 1)) * (1 + 2 ^ (k + 1)) = 1 := by
    have e : ((1 : ZMod (2 ^ (k + 2))) + 2 ^ (k + 1)) * (1 + 2 ^ (k + 1))
        = 1 + 2 ^ (k + 2) * (1 + 2 ^ k) := by ring
    rw [e, h2, zero_mul, add_zero]
  have hsq : ξ (1 + 2 ^ (k + 1)) * ξ (1 + 2 ^ (k + 1)) = 1 := by
    rw [← map_mul, huu, map_one]
  have hpm : ξ (1 + 2 ^ (k + 1)) = 1 ∨ ξ (1 + 2 ^ (k + 1)) = -1 := by
    have : (ξ (1 + 2 ^ (k + 1)) - 1) * (ξ (1 + 2 ^ (k + 1)) + 1) = 0 := by
      linear_combination hsq
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases hpm with h1 | h1
  · exfalso
    have hd : 2 ^ (k + 1) ∣ 2 ^ (k + 2) := pow_dvd_pow 2 (by omega)
    have hft : ξ.FactorsThrough (2 ^ (k + 1)) := by
      rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
      intro x hx
      have hx' := hx
      rw [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, ← ZMod.natCast_val,
        Units.val_one] at hx'
      have hx'' : (((x : ZMod (2 ^ (k + 2))).val : ℕ) : ZMod (2 ^ (k + 1))) = ((1 : ℕ) : ZMod _) := by
        rw [hx', Nat.cast_one]
      rw [ZMod.natCast_eq_natCast_iff] at hx''
      rw [MonoidHom.mem_ker, Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
      have hv : (x : ZMod (2 ^ (k + 2))).val < 2 ^ (k + 2) := ZMod.val_lt _
      have hM : 2 ≤ 2 ^ (k + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hmod : (x : ZMod (2 ^ (k + 2))).val % 2 ^ (k + 1) = 1 := by
        have h := hx''
        unfold Nat.ModEq at h
        rw [h]
        exact Nat.mod_eq_of_lt (by omega)
      have hq : (x : ZMod (2 ^ (k + 2))).val / 2 ^ (k + 1) < 2 := by
        rw [Nat.div_lt_iff_lt_mul (by positivity)]
        calc (x : ZMod (2 ^ (k + 2))).val < 2 ^ (k + 2) := hv
          _ = 2 * 2 ^ (k + 1) := by ring
      have hdm := Nat.div_add_mod (x : ZMod (2 ^ (k + 2))).val (2 ^ (k + 1))
      rw [← ZMod.natCast_zmod_val (x : ZMod (2 ^ (k + 2)))]
      generalize hqd : (x : ZMod (2 ^ (k + 2))).val / 2 ^ (k + 1) = q at hq hdm
      rcases (by omega : q = 0 ∨ q = 1) with hq0 | hq1
      · rw [hq0, mul_zero, zero_add, hmod] at hdm
        rw [← hdm, Nat.cast_one, map_one]
      · rw [hq1, mul_one, hmod] at hdm
        rw [← hdm]
        push_cast
        rw [add_comm ((2 : ZMod (2 ^ (k + 2))) ^ (k + 1)) 1]
        exact h1
    have hle : ξ.conductor ≤ 2 ^ (k + 1) :=
      Nat.sInf_le ((DirichletCharacter.mem_conductorSet_iff _).mpr hft)
    have hlt : 2 ^ (k + 1) < 2 ^ (k + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    rw [DirichletCharacter.isPrimitive_def] at hξ
    omega
  · exact h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.TwoPowDvdSubOneOrAddOneOfPowTwoPow
section
theorem UpperTheory.two_pow_dvd_sub_one_or_add_one_of_pow_two_pow :
    ∀ (k a : ℕ) (x : ℤ), (2 : ℤ) ^ (a + k) ∣ x ^ (2 ^ k) - 1 → (2 : ℤ) ^ a ∣ x - 1 ∨ (2 : ℤ) ^ a ∣ x + 1 := by
  have B : ∀ (a : ℕ) (x : ℤ), (2 : ℤ) ^ (a + 1) ∣ x ^ 2 - 1 → (2 : ℤ) ^ a ∣ x - 1 ∨ (2 : ℤ) ^ a ∣ x + 1 := by
    intro a x h
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · left
      simp
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rcases Int.even_or_odd' x with ⟨q, hq | hq⟩
    · exfalso
      have h2 : (2 : ℤ) ∣ x ^ 2 - 1 := (dvd_pow_self 2 (by omega : b + 1 + 1 ≠ 0)).trans h
      rw [hq, show (2 * q) ^ 2 - 1 = 2 * (2 * q ^ 2) - 1 by ring] at h2
      omega
    · subst hq
      have e1 : (2 * q + 1) ^ 2 - 1 = 2 ^ 2 * (q * (q + 1)) := by ring
      rw [e1, show b + 1 + 1 = 2 + b by omega, pow_add] at h
      have h' : (2 : ℤ) ^ b ∣ q * (q + 1) := (mul_dvd_mul_iff_left (by norm_num)).1 h
      rcases Int.even_or_odd q with hqe | hqo
      · have hc : IsCoprime ((2 : ℤ) ^ b) (q + 1) :=
          (Int.isCoprime_two_left.2 hqe.add_one).pow_left
        left
        have hd := hc.dvd_of_dvd_mul_right h'
        rw [show 2 * q + 1 - 1 = 2 * q by ring, pow_succ, mul_comm ((2 : ℤ) ^ b) 2]
        exact mul_dvd_mul_left 2 hd
      · have hc : IsCoprime ((2 : ℤ) ^ b) q :=
          (Int.isCoprime_two_left.2 hqo).pow_left
        right
        have hd := hc.dvd_of_dvd_mul_left h'
        rw [show 2 * q + 1 + 1 = 2 * (q + 1) by ring, pow_succ, mul_comm ((2 : ℤ) ^ b) 2]
        exact mul_dvd_mul_left 2 hd
  intro k
  induction k with
  | zero =>
    intro a x h
    left
    simpa using h
  | succ k ih =>
    intro a x h
    have h' : (2 : ℤ) ^ ((a + 1) + k) ∣ (x ^ 2) ^ (2 ^ k) - 1 := by
      rw [← pow_mul, ← pow_succ', show a + 1 + k = a + (k + 1) by omega]
      exact h
    rcases ih (a + 1) (x ^ 2) h' with h1 | h1
    · exact B a x h1
    · rcases Nat.eq_zero_or_pos a with rfl | ha
      · left
        simp
      exfalso
      have h4 : (2 : ℤ) ^ 2 ∣ x ^ 2 + 1 := (pow_dvd_pow 2 (by omega : 2 ≤ a + 1)).trans h1
      norm_num at h4
      rcases Int.even_or_odd' x with ⟨q, hq | hq⟩
      · rw [hq, show (2 * q) ^ 2 + 1 = 4 * q ^ 2 + 1 by ring] at h4
        omega
      · rw [hq, show (2 * q + 1) ^ 2 + 1 = 4 * (q ^ 2 + q) + 2 by ring] at h4
        omega
end

