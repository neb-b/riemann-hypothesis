module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.ExistsBinomialExpansionModSq
section
open Finset UpperTheory.V.Bern UpperTheory.V.Stk

theorem UpperTheory.V.Stk.exists_binomial_expansion_mod_sq :
    ∀ (b j M : ℤ) (e : ℕ),
      (∃ z : ℤ, (b + M * j) ^ (e + 1) = b ^ (e + 1) + ((e : ℤ) + 1) * b ^ e * (M * j) + M ^ 2 * z) ∧
      ∃ w : ℤ, (b + M * j) ^ e = b ^ e + M * w := by
  intro b j M e
  have h2 : ∀ n : ℕ, ∃ w : ℤ, (b + M * j) ^ n = b ^ n + M * w := by
    intro n
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (b + M * j) b n
    refine ⟨j * c, ?_⟩
    have hd : (b + M * j) - b = M * j := by ring
    rw [hd] at hc
    linear_combination hc
  refine ⟨?_, h2 e⟩
  induction e with
  | zero => exact ⟨0, by ring⟩
  | succ n ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨b * z + ((n : ℤ) + 1) * b ^ n * j ^ 2 + M * j * z, ?_⟩
    push_cast
    linear_combination (b + M * j) * hz
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.GroupRingIntAtDivSmulOfPadicValNatLe
section
open Finset UpperTheory.V.Bern UpperTheory.V

theorem UpperTheory.V.Stk.groupRing_intAt_div_smul_of_padicValNat_le :
    ∀ (l : ℕ) [Fact l.Prime] (M D t : ℕ), 0 < M → 0 < D → t + padicValNat l D ≤ padicValNat l M →
      ∀ (Γ : Type) [CommGroup Γ] (z : MonoidAlgebra ℤ Γ), B4.IntAt l t (((M : ℚ) / (D : ℚ)) • Stk.cf ℚ Γ z) := by
  intro l _ M D t hM hD ht Γ _ z g
  have hp : l.Prime := Fact.out
  have hcoef : (((M : ℚ) / (D : ℚ)) • Stk.cf ℚ Γ z).coeff g = ((M : ℚ) / (D : ℚ)) * (z.coeff g : ℚ) := by
    simp [Stk.cf]
  rw [hcoef]
  have hdvdM : l ^ (padicValNat l D + t) ∣ M :=
    (pow_dvd_pow l (by omega)).trans (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
  have hdvdD : l ^ padicValNat l D ∣ D := (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
  obtain ⟨k, hk⟩ := hdvdM
  obtain ⟨E, hE⟩ := hdvdD
  have hnd : ¬ l ∣ E := by
    intro hl
    apply pow_succ_padicValNat_not_dvd (p := l) hD.ne'
    conv_rhs => rw [hE]
    rw [pow_succ]
    simpa only [Nat.padicValNat_def] using Nat.mul_dvd_mul_left (l ^ padicValNat l D) hl
  have hE0 : E ≠ 0 := by
    rintro rfl
    simp at hE
    omega
  have hl0 : (l : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hEq : (E : ℚ) ≠ 0 := by exact_mod_cast hE0
  have hMq : (M : ℚ) = (l : ℚ) ^ (padicValNat l D + t) * k := by exact_mod_cast hk
  have hDq : (D : ℚ) = (l : ℚ) ^ padicValNat l D * E := by exact_mod_cast hE
  have heq : (M : ℚ) / (D : ℚ) * (z.coeff g : ℚ) / (l : ℚ) ^ t = ((k : ℚ) / (E : ℚ)) * (z.coeff g : ℚ) := by
    rw [hMq, hDq, pow_add]
    field_simp
  rw [heq]
  refine (B4.Zl l).mul_mem ?_ (intCast_mem _ _)
  rw [B4.mem_Zl]
  intro hden
  apply hnd
  have h1 : (((k : ℤ) : ℚ) / ((E : ℤ) : ℚ)).den ∣ E := by
    rw [← Rat.divInt_eq_div]
    exact_mod_cast Rat.den_dvd (k : ℤ) (E : ℤ)
  push_cast at h1
  exact hden.trans h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.SingleInvMulGroupRingSumOverUnitsInv
section
open Finset UpperTheory.V.Bern UpperTheory.V.Stk

theorem UpperTheory.V.Stk.single_inv_mul_groupRingSumOverUnitsInv :
    ∀ (M a : ℕ) [NeZero M] (ha : a.Coprime M) (R Γ : Type) [CommRing R] [Group Γ] (φ : (ZMod M)ˣ →* Γ) (c : R)
      (f : ZMod M → R),
      MonoidAlgebra.single (φ (ZMod.unitOfCoprime a ha))⁻¹ c * sumEl φ f = sumEl φ fun b => c * f (yCl a b) := by
  intro M a _ ha R Γ _ _ φ c f
  unfold sumEl yCl
  rw [Finset.mul_sum]
  symm
  rw [← Equiv.sum_comp (Equiv.mulRight (ZMod.unitOfCoprime a ha))]
  refine Finset.sum_congr rfl fun b _ => ?_
  have key : ((a : ZMod M))⁻¹ * ((b : ZMod M) * (a : ZMod M)) = (b : ZMod M) := by
    rw [mul_comm (b : ZMod M), ← mul_assoc, mul_comm _ (a : ZMod M), ZMod.coe_mul_inv_eq_one a ha, one_mul]
  rw [MonoidAlgebra.single_mul_single]
  simp only [Equiv.coe_mulRight, map_mul, mul_inv_rev, Units.val_mul, ZMod.coe_unitOfCoprime, key]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.StickelbergerBernoulliCoeffExpansionModDenominat
section
open Finset UpperTheory.V.Bern UpperTheory.V.Stk

theorem UpperTheory.V.Stk.stickelbergerBernoulliCoeff_expansion_mod_denominator :
    ∀ (M e b : ℕ), 0 < M → ∃ z : ℤ,
      bcoef M (e + 1) b / ((e + 1 : ℕ) : ℚ) =
        (b : ℚ) ^ (e + 1) / (((e + 1 : ℕ) : ℚ) * M) - (b : ℚ) ^ e / 2 + 2 * (M : ℚ) / (dk (e + 1) : ℚ) * z := by
  intro M e b hM
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hD : (primorial (e + 1 + 1) : ℚ) ≠ 0 := by exact_mod_cast (primorial_pos _).ne'
  have hk : ((e + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero e
  have h : ∀ j : ℕ, ∃ z : ℤ, j ≤ e + 1 → (primorial (e + 1 + 1) : ℚ) * bernoulli j = z := by
    intro j
    by_cases hj : j ≤ e + 1
    · obtain ⟨z, hz⟩ := b_primden (e + 1) j hj
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose z hz using h
  refine ⟨∑ j ∈ range e, ((e + 1).choose (j + 1 + 1) : ℤ) * z (j + 1 + 1) * (M : ℤ) ^ j *
    (b : ℤ) ^ (e + 1 - (j + 1 + 1)), ?_⟩
  have hs : ∑ j ∈ range e, (((e + 1).choose (j + 1 + 1) : ℕ) : ℚ) * bernoulli (j + 1 + 1) *
      (M : ℚ) ^ (((j + 1 + 1 : ℕ) : ℤ) - 1) * (b : ℚ) ^ (e + 1 - (j + 1 + 1)) =
      (M : ℚ) / (primorial (e + 1 + 1) : ℚ) *
        ((∑ j ∈ range e, ((e + 1).choose (j + 1 + 1) : ℤ) * z (j + 1 + 1) * (M : ℤ) ^ j *
          (b : ℤ) ^ (e + 1 - (j + 1 + 1)) : ℤ) : ℚ) := by
    rw [Int.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j + 1 + 1 ≤ e + 1 := by have := mem_range.mp hj; omega
    have hp : (((j + 1 + 1 : ℕ) : ℤ) - 1) = ((j + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hp, zpow_natCast, Int.cast_mul, Int.cast_mul, Int.cast_mul, ← hz _ hj', Int.cast_pow, Int.cast_pow,
      Int.cast_natCast, Int.cast_natCast, Int.cast_natCast]
    field_simp
    ring
  rw [b_expand M (e + 1) b hM, Finset.sum_range_succ', Finset.sum_range_succ', hs]
  have hdk : (dk (e + 1) : ℚ) = 2 * ((e + 1 : ℕ) : ℚ) * (primorial (e + 1 + 1) : ℚ) := by
    rw [dk]; push_cast; ring
  rw [hdk]
  generalize ((∑ j ∈ range e, ((e + 1).choose (j + 1 + 1) : ℤ) * z (j + 1 + 1) * (M : ℤ) ^ j *
          (b : ℤ) ^ (e + 1 - (j + 1 + 1)) : ℤ) : ℚ) = S
  simp only [zero_add, Nat.choose_one_right, Nat.choose_zero_right, bernoulli_one, bernoulli_zero,
    Nat.add_sub_cancel, Nat.sub_zero, Nat.cast_one, Nat.cast_zero, sub_self, zpow_zero, zero_sub, zpow_neg, zpow_one]
  field_simp
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.StickelbergerCarrySpecAndWeightOneCoeffOfOdd
section
open Finset UpperTheory.V.Bern UpperTheory.V.Stk

theorem UpperTheory.V.Stk.stickelbergerCarry_spec_and_weightOne_coeff_of_odd :
    ∀ (M a : ℕ) [NeZero M], a.Coprime M → ∀ b : ZMod M,
      (a : ℤ) * ((yCl a b).val : ℤ) = (b.val : ℤ) + (M : ℤ) * jv M a b ∧ (Odd a → Eva M 1 a b = (Eone M a b : ℚ)) := by
  intro M a _ hcop b
  have hM : (M : ℤ) ∣ (a : ℤ) * ((yCl a b).val : ℤ) - (b.val : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, yCl, ← mul_assoc,
      ZMod.coe_mul_inv_eq_one a hcop, one_mul, sub_self]
  have h1 : (a : ℤ) * ((yCl a b).val : ℤ) = (b.val : ℤ) + (M : ℤ) * jv M a b := by
    rw [jv, Int.mul_ediv_cancel' hM]
    ring
  refine ⟨h1, fun hodd => ?_⟩
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have h1q : (a : ℚ) * ((yCl a b).val : ℚ) = (b.val : ℚ) + (M : ℚ) * (jv M a b : ℚ) := by
    exact_mod_cast h1
  obtain ⟨t, ht⟩ := hodd
  have hE : (Eone M a b : ℚ) = (t : ℚ) - (jv M a b : ℚ) := by
    rw [Eone]
    have : (((a : ℤ) - 1) / 2) = t := by omega
    rw [this]
    push_cast
    rfl
  rw [hE, Eva, Ev, Ev, bcoef, bcoef, Polynomial.bernoulli_one]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Nat.cast_one, sub_self,
    zpow_zero, one_mul, div_one, pow_one]
  have ha : (a : ℚ) ≠ 0 := by
    rw [ht]
    push_cast
    positivity
  have hy : ((yCl a b).val : ℚ) = ((b.val : ℚ) + (M : ℚ) * (jv M a b : ℚ)) / (a : ℚ) := by
    field_simp
    linarith [h1q]
  rw [hy]
  have hta : (a : ℚ) = 2 * t + 1 := by exact_mod_cast ht
  field_simp
  rw [hta]
  ring
end

