module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0016
public import Formalism.PeriodIntegrals.Bundle0011
public import Formalism.RealPlaceAnalysis.StatementU
public import Formalism.RealPlaceAnalysis.QuotientSettingHolds
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0019
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.Bundle0001
public import Formalism.UnipotentAdelicQuotients.Bundle0003
public import Formalism.UnipotentAdelicQuotients.Bundle0002
public import Formalism.PeriodIntegrals.ExplicitFormulaCounts.BridgeStdAddChar

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.HermitianForms.CasOfCapelliVec
section
open Finset

namespace GlobalTheory.CompanionTheory.Inh.CapelliCasimir
open Polynomial

noncomputable def rev {ι : Type} (s : Finset ι) (f : ι → ℂ) : ℂ[X] := ∏ l ∈ s, (1 + C (f l) * X)

theorem rev_coeff {ι : Type} (s : Finset ι) (f : ι → ℂ) :
    (rev s f).coeff 0 = 1 ∧ (rev s f).coeff 1 = ∑ l ∈ s, f l ∧
      2 * (rev s f).coeff 2 = (∑ l ∈ s, f l) ^ 2 - ∑ l ∈ s, f l ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rev, coeff_one]
  | insert a s ha ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have c1 : ∀ p : ℂ[X], (X * p).coeff 1 = p.coeff 0 := fun p => coeff_X_mul p 0
    have c2 : ∀ p : ℂ[X], (X * p).coeff 2 = p.coeff 1 := fun p => coeff_X_mul p 1
    have : rev (insert a s) f = rev s f + C (f a) * (X * rev s f) := by
      simp only [rev, prod_insert ha]; ring
    rw [this, sum_insert ha, sum_insert ha]
    simp only [coeff_add, coeff_C_mul]
    refine ⟨?_, ?_, ?_⟩
    · simp [h0]
    · rw [c1, h0, h1]; ring
    · rw [c2, h1]
      linear_combination h2

theorem rev_eval {ι : Type} (s : Finset ι) (f : ι → ℂ) (t : ℂ) (ht : t ≠ 0) :
    (rev s f).eval t = t ^ s.card * ∏ l ∈ s, (t⁻¹ + f l) := by
  rw [rev, eval_prod, ← prod_const, ← prod_mul_distrib]
  refine prod_congr rfl fun l _ => ?_
  simp; field_simp

theorem scalar_core (n : ℕ) (hn : 2 ≤ n) (ρ μ a : Fin n → ℂ) (b : Fin n → Fin n → ℂ) (r : ℕ → ℂ)
    (e c : ℂ)
    (h : ∀ Y : ℂ, (∏ l, (Y + ρ l)) * e + ∑ i, (∏ l ∈ univ.erase i, (Y + ρ l)) * a i
      + ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (∏ l ∈ (univ.erase i).erase j, (Y + ρ l)) * b i j
      + ∑ d ∈ range (n - 2), (Y + c) ^ d * r d = (∏ l, (Y + μ l)) * e) :
    (∑ l, ρ l) * e + ∑ i, a i = (∑ l, μ l) * e ∧
    ((∑ l, ρ l) ^ 2 - ∑ l, ρ l ^ 2) * e + 2 * ∑ i, (∑ l ∈ univ.erase i, ρ l) * a i
      + 2 * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), b i j
      = ((∑ l, μ l) ^ 2 - ∑ l, μ l ^ 2) * e := by
  have key : C e * rev univ ρ + X * ∑ i, C (a i) * rev (univ.erase i) ρ
      + X ^ 2 * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), C (b i j) * rev ((univ.erase i).erase j) ρ
      + X ^ 3 * ∑ d ∈ range (n - 2), C (r d) * X ^ (n - 3 - d) * (1 + C c * X) ^ d
      = C e * rev univ μ := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono (s := {0}ᶜ) ?_ (Set.finite_singleton (0:ℂ)).infinite_compl
    intro t ht
    have ht : t ≠ 0 := ht
    simp only [Set.mem_setOf_eq, eval_add, eval_mul, eval_C, eval_X, eval_pow, Polynomial.eval_finsetSum,
      eval_one, rev_eval _ _ _ ht, card_univ, Fintype.card_fin]
    have := congrArg (fun z => t ^ n * z) (h t⁻¹)
    simp only [mul_add, mul_sum] at this ⊢
    refine Eq.trans ?_ (this.trans (by ring))
    congr 1
    · congr 1
      · congr 1
        · ring
        · refine sum_congr rfl fun i _ => ?_
          rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
          obtain ⟨m, hm⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
          have : t ^ n = t * t ^ (n - 1) := by
            rw [← pow_succ']; congr 1; omega
          rw [this]; ring
      · refine sum_congr rfl fun i _ => sum_congr rfl fun j hj => ?_
        have hij : j ≠ i := (mem_filter.1 hj).2.ne'
        rw [card_erase_of_mem (mem_erase.2 ⟨hij, mem_univ _⟩), card_erase_of_mem (mem_univ _),
          card_univ, Fintype.card_fin]
        have : t ^ n = t ^ 2 * t ^ (n - 1 - 1) := by
          rw [← pow_add]; congr 1; omega
        rw [this]; ring
    · refine sum_congr rfl fun d hd => ?_
      have hd := mem_range.1 hd
      have h1 : t ^ n = t ^ 3 * t ^ (n - 3 - d) * t ^ d := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      have h2 : (1 + c * t) = t * (t⁻¹ + c) := by field_simp
      rw [h1, h2, mul_pow]; ring
  have k1 := congrArg (fun p => p.coeff 1) key
  have k2 := congrArg (fun p => p.coeff 2) key
  simp only [coeff_add, coeff_C_mul, coeff_X_pow_mul'] at k1 k2
  have c1 : ∀ p : ℂ[X], (X * p).coeff 1 = p.coeff 0 := fun p => coeff_X_mul p 0
  have c2 : ∀ p : ℂ[X], (X * p).coeff 2 = p.coeff 1 := fun p => coeff_X_mul p 1
  rw [c1] at k1
  rw [c2] at k2
  simp only [Polynomial.finsetSum_coeff, coeff_C_mul, (rev_coeff _ _).1, (rev_coeff _ _).2.1, le_refl, if_true,
    Nat.sub_self, mul_one] at k1 k2
  norm_num at k1 k2
  constructor
  · linear_combination k1
  · have p1 := (rev_coeff univ ρ).2.2
    have p2 := (rev_coeff univ μ).2.2
    have : ∑ i, (∑ l ∈ univ.erase i, ρ l) * a i = ∑ i, a i * (∑ l, ρ l - ρ i) := by
      refine sum_congr rfl fun i _ => ?_
      rw [sum_erase_eq_sub (mem_univ _), mul_comm]
    rw [this]
    linear_combination 2 * k2 - e * p1 + e * p2

theorem sum_sq_split {A : Type} [AddCommGroup A] {n : ℕ} (F : Fin n → Fin n → A) :
    ∑ i, ∑ j, F i j = ∑ i, F i i + ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (F i j + F j i) := by
  have h1 : ∀ i j, F i j = (if i = j then F i j else 0) + (if i < j then F i j else 0)
      + (if j < i then F i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, h.not_gt]
    · simp [h]
    · simp [h, h.ne', h.not_gt]
  rw [sum_congr rfl fun i _ => sum_congr rfl fun j _ => h1 i j]
  simp only [sum_add_distrib, sum_filter, sum_ite_eq, mem_univ, if_true]
  rw [add_assoc, sum_comm (f := fun i j => if j < i then F i j else 0)]

theorem sum_diff {A : Type} [AddCommGroup A] [Module ℂ A] {n : ℕ} (x : Fin n → A) :
    ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (x i - x j)
      = ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) • x i := by
  simp only [sum_sub_distrib]
  have : ∑ i, ∑ j ∈ univ.filter (fun j => i < j), x j
      = ∑ j, ∑ i ∈ univ.filter (fun i => i < j), x j := by
    simp only [sum_filter]; exact sum_comm
  rw [this, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_const, sum_const, filter_lt_eq_Ioi, filter_gt_eq_Iio, Fin.card_Ioi, Fin.card_Iio,
    ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, ← sub_smul]
  congr 1
  have := i.2
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast; ring

theorem sq_sub_cas {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (hE : Formalism.REAL.GlRel E) :
    (∑ i, E i i) * (∑ i, E i i) - Formalism.REAL.Cas E
      = (2 : ℂ) • ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (E i i * E j j - E j i * E i j)
        - ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) • E i i := by
  rw [← sum_diff, Formalism.REAL.Cas, sum_mul_sum, ← sum_sub_distrib]
  simp only [← sum_sub_distrib]
  rw [sum_sq_split]
  simp only [sub_self, sum_const_zero, zero_add, smul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j hj => ?_
  have hij : i ≠ j := (mem_filter.1 hj).2.ne
  have h1 := hE i j j i
  have h2 := hE i i j j
  simp only [if_true, hij, hij.symm, if_false, sub_zero] at h1 h2
  rw [two_smul, ← h1, ← sub_eq_zero.1 h2]
  abel


end GlobalTheory.CompanionTheory.Inh.CapelliCasimir
end

-- bundled from Development.AutomorphicSpectrum.Proofs.HermitianForms.ExistsIsCharAFOfStd
section
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.AdelicChar

theorem exists_isCharAF_of_std :
    HeckeCharacterZeroLocus.StdAdditiveCharExists → ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F →
      ∃ ψ, IsCharAF F ψ := by
  intro h F _ _ hF
  obtain ⟨ψ, h1, h2, h3, h4, -⟩ := h F hF
  exact ⟨ψ, h1, h2, h3, h4⟩

theorem exists_isCharAF (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyReal F) :
    ∃ ψ, IsCharAF F ψ :=
  exists_isCharAF_of_std PI.Bridge.bridge_stdAddChar F hF

end GlobalTheory.CompanionTheory.AdelicChar
end

