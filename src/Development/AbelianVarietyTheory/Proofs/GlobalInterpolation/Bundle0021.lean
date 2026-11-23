module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqTransposeMulMapOfIdempotent
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0017

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NcardSumBinaryFormNeZero
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.BinaryFormCount

open Finset

variable {k : Type} [Field k] [Fintype k] [DecidableEq k]

theorem card_fibre_eq {t n : k} (hD : t ^ 2 - 4 * n ≠ 0) {c : k} (hc : c ≠ 0) :
    #{p : k × k | p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2 = c}
      = #{p : k × k | p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2 = 1} := by
  obtain ⟨u, v, huv⟩ := UnramifiedHermitian.exists_binary_eq_of_finite hD c
  symm
  refine Finset.card_nbij' (fun p => (p.1 * u - n * p.2 * v, p.1 * v + p.2 * u + t * p.2 * v))
    (fun p => ((p.1 * (u + t * v) + n * p.2 * v) / c, (p.2 * u - p.1 * v) / c)) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp ⊢
    linear_combination (u ^ 2 + t * u * v + n * v ^ 2) * hp + huv
  · intro p hp
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hp ⊢
    field_simp
    linear_combination (u ^ 2 + t * u * v + n * v ^ 2) * hp + c * huv
  · intro p _
    ext
    · simp only; field_simp; linear_combination p.1 * huv
    · simp only; field_simp; linear_combination p.2 * huv
  · intro p _
    ext
    · simp only; field_simp; linear_combination p.1 * huv
    · simp only; field_simp; linear_combination p.2 * huv

theorem card_zero {t n : k} (hD : t ^ 2 - 4 * n ≠ 0) {η : ℝ}
    (h1 : (∃ r : k, r ^ 2 - t * r + n = 0) → η = 1)
    (h2 : (¬ ∃ r : k, r ^ 2 - t * r + n = 0) → η = -1) :
    (#{p : k × k | p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2 = 0} : ℝ)
      = Fintype.card k - η + η * Fintype.card k := by
  by_cases h : ∃ r : k, r ^ 2 - t * r + n = 0
  · rw [h1 h]
    obtain ⟨r, hr⟩ := h
    have hne : t - 2 * r ≠ 0 := by
      intro h0
      apply hD
      linear_combination (t - 2 * r) * h0 - 4 * hr
    have e : ({p : k × k | p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2 = 0} : Finset (k × k))
        = (univ.image fun b : k => (-r * b, b)) ∪ (univ.image fun b : k => (-(t - r) * b, b)) := by
      ext ⟨a, b⟩
      simp only [mem_filter, mem_univ, true_and, mem_union, mem_image, Prod.mk.injEq,
        exists_eq_right]
      constructor
      · intro hab
        have : (-r * b - a) * (-(t - r) * b - a) = 0 := by linear_combination hab - b ^ 2 * hr
        rcases mul_eq_zero.1 this with h | h
        · exact Or.inl (sub_eq_zero.1 h)
        · exact Or.inr (sub_eq_zero.1 h)
      · rintro (rfl | rfl) <;> linear_combination b ^ 2 * hr
    have i : (univ.image fun b : k => (-r * b, b)) ∩ (univ.image fun b : k => (-(t - r) * b, b))
        = {((0 : k), (0 : k))} := by
      ext ⟨a, b⟩
      simp only [mem_univ, true_and, mem_inter, mem_image, Prod.mk.injEq,
        exists_eq_right, mem_singleton]
      constructor
      · rintro ⟨rfl, h⟩
        have : (t - 2 * r) * b = 0 := by linear_combination -h
        have hb := (mul_eq_zero.1 this).resolve_left hne
        simp [hb]
      · rintro ⟨rfl, rfl⟩; simp
    have := Finset.card_union_add_card_inter (univ.image fun b : k => (-r * b, b))
      (univ.image fun b : k => (-(t - r) * b, b))
    rw [i, ← e, card_image_of_injective _ (fun a b h => congrArg Prod.snd h),
      card_image_of_injective _ (fun a b h => congrArg Prod.snd h), card_singleton,
      card_univ] at this
    have h3 := congrArg (Nat.cast : ℕ → ℝ) this
    push_cast at h3
    linarith
  · rw [h2 h]
    have e : ({p : k × k | p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2 = 0} : Finset (k × k))
        = {((0 : k), (0 : k))} := by
      ext ⟨a, b⟩
      simp only [mem_filter, mem_univ, true_and, Prod.mk.injEq, mem_singleton]
      constructor
      · intro hab
        by_cases hb : b = 0
        · subst hb
          simpa using hab
        · refine (h ⟨-a / b, ?_⟩).elim
          field_simp
          linear_combination hab
      · rintro ⟨rfl, rfl⟩; simp
    rw [e, card_singleton]
    push_cast
    ring

theorem card_fibre {t n : k} (hD : t ^ 2 - 4 * n ≠ 0) {η : ℝ}
    (h1 : (∃ r : k, r ^ 2 - t * r + n = 0) → η = 1)
    (h2 : (¬ ∃ r : k, r ^ 2 - t * r + n = 0) → η = -1) (c : k) :
    (#{p : k × k | p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2 = c} : ℝ)
      = Fintype.card k - η + if c = 0 then η * Fintype.card k else 0 := by
  have hz := card_zero hD h1 h2
  by_cases hc : c = 0
  · rw [if_pos hc, hc, hz]
  rw [if_neg hc, card_fibre_eq hD hc, add_zero]
  have tot := Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (k × k))) (t := univ)
    (f := fun p : k × k => p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2) (fun _ _ => mem_univ _)
  rw [← Finset.add_sum_erase _ _ (mem_univ (0 : k)),
    Finset.sum_congr rfl (fun d hd => card_fibre_eq hD (Finset.ne_of_mem_erase hd)),
    sum_const, card_erase_of_mem (mem_univ _), card_univ, card_univ, Fintype.card_prod,
    smul_eq_mul] at tot
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  have h3 := congrArg (Nat.cast : ℕ → ℝ) tot
  push_cast [Nat.cast_sub hq.le] at h3
  rw [hz] at h3
  have hq' : (Fintype.card k : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < Fintype.card k := by exact_mod_cast hq
    linarith
  apply mul_left_cancel₀ hq'
  linear_combination -h3

theorem card_sum_zero {α : Type} [Fintype α] [DecidableEq α] (Q : α → k) (q η : ℝ)
    (hα : (Fintype.card α : ℝ) = q ^ 2)
    (hQ : ∀ c, (#{p : α | Q p = c} : ℝ) = q - η + if c = 0 then η * q else 0) (M : ℕ) :
    (#{x : Fin M → α | ∑ i, Q (x i) = 0} : ℝ) * q = q ^ (2 * M) + (q - 1) * (η * q) ^ M := by
  induction M with
  | zero => simp
  | succ M ih =>
    have key : (#{x : Fin (M + 1) → α | ∑ i, Q (x i) = 0} : ℝ)
        = q ^ (2 * M) * (q - η) + η * q * #{x : Fin M → α | ∑ i, Q (x i) = 0} := by
      rw [Finset.card_filter, Finset.card_filter]
      push_cast
      rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type_right]
      have : ∀ y : Fin M → α, (∑ a : α, if ∑ i, Q ((Fin.consEquiv fun _ => α) (a, y) i) = 0
          then (1 : ℝ) else 0) = q - η + η * q * if ∑ i, Q (y i) = 0 then 1 else 0 := by
        intro y
        have := hQ (-∑ i, Q (y i))
        rw [Finset.card_filter] at this
        push_cast at this
        simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
          ← eq_neg_iff_add_eq_zero, this, neg_eq_zero, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_congr rfl fun y _ => this y, sum_add_distrib, ← mul_sum, sum_const,
        card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      rw [hα, ← pow_mul]
    rw [key, show 2 * (M + 1) = 2 * M + 2 by ring]
    linear_combination (η * q) * ih

end GlobalTheory.BinaryFormCount

namespace GlobalTheory


open Finset in
theorem ncard_sum_binary_form_ne_zero (k : Type) [Field k] [Finite k] (t n : k)
    (hD : t ^ 2 - 4 * n ≠ 0) (η : ℝ) (h1 : (∃ r : k, r ^ 2 - t * r + n = 0) → η = 1)
    (h2 : (¬ ∃ r : k, r ^ 2 - t * r + n = 0) → η = -1) (M : ℕ) :
    ({x : Fin M × Fin 2 → k | ∑ i : Fin M,
        (x (i, 0) ^ 2 + t * x (i, 0) * x (i, 1) + n * x (i, 1) ^ 2) ≠ 0}.ncard : ℝ)
      * (Nat.card k : ℝ)
      = ((Nat.card k : ℝ) - 1) * ((Nat.card k : ℝ) ^ (2 * M) - (η * (Nat.card k : ℝ)) ^ M) := by
  classical
  haveI := Fintype.ofFinite k
  have hz := BinaryFormCount.card_sum_zero
    (fun p : k × k => p.1 ^ 2 + t * p.1 * p.2 + n * p.2 ^ 2) (Fintype.card k) η
    (by rw [Fintype.card_prod]; push_cast; ring) (BinaryFormCount.card_fibre hD h1 h2) M
  have hs := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin M → k × k)))
    (fun x => ∑ i, ((x i).1 ^ 2 + t * (x i).1 * (x i).2 + n * (x i).2 ^ 2) = 0)
  have hb : {x : Fin M × Fin 2 → k | ∑ i : Fin M,
        (x (i, 0) ^ 2 + t * x (i, 0) * x (i, 1) + n * x (i, 1) ^ 2) ≠ 0}.ncard
      = #{x : Fin M → k × k |
        ¬ ∑ i, ((x i).1 ^ 2 + t * (x i).1 * (x i).2 + n * (x i).2 ^ 2) = 0} := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
    refine Finset.card_nbij' (fun x i => (x (i, 0), x (i, 1)))
      (fun x p => ![(x p.1).1, (x p.1).2] p.2) ?_ ?_ ?_ ?_
    · intro x hx
      simpa using hx
    · intro x hx
      simpa using hx
    · intro x _
      ext ⟨i, j⟩
      fin_cases j <;> simp
    · intro x _
      ext i <;> simp
  rw [card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin] at hs
  have h3 := congrArg (Nat.cast : ℕ → ℝ) hs
  push_cast at h3
  rw [hb, Nat.card_eq_fintype_card, pow_mul, pow_two]
  rw [pow_mul, pow_two] at hz
  linear_combination (Fintype.card k : ℝ) * h3 - hz

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NegReLogDerivPrincipalLFunctionLe
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.PrincipalLogDeriv

lemma norm_cpow_neg_le {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖(p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
  calc (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    _ = 1 / p := by rw [Real.rpow_neg_one, one_div]
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2

lemma half_le_norm_one_sub {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    1 / 2 ≤ ‖1 - (p : ℂ) ^ (-s)‖ := by
  have h := norm_cpow_neg_le hp hs
  have h' := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-s))
  rw [norm_one] at h'
  linarith

lemma one_sub_ne_zero {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    1 - (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h' := half_le_norm_one_sub hp hs
  rw [h, norm_zero] at h'
  norm_num at h'

lemma hasDerivAt_factor {p : ℕ} (hp : p.Prime) (s : ℂ) :
    HasDerivAt (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) ((p : ℂ) ^ (-s) * Complex.log p) s := by
  have hc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h : HasDerivAt (fun z : ℂ => (p : ℂ) ^ (-z)) ((p : ℂ) ^ (-s) * Complex.log p * (-1)) s :=
    ((hasDerivAt_id' s).neg).const_cpow (Or.inl hc)
  have h2 : HasDerivAt (fun z : ℂ => 1 - (p : ℂ) ^ (-z))
      (-((p : ℂ) ^ (-s) * Complex.log p * (-1))) s := h.const_sub 1
  convert h2 using 1
  ring

lemma norm_logDeriv_factor_le {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ ≤ Real.log p := by
  have h1 := norm_cpow_neg_le hp hs
  have h2 := half_le_norm_one_sub hp hs
  have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hlog : ‖Complex.log (p : ℂ)‖ = Real.log p := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg p), Complex.norm_real,
      Real.norm_of_nonneg hl]
  rw [logDeriv_apply, (hasDerivAt_factor hp s).deriv, norm_div, norm_mul, hlog,
    div_le_iff₀ (by linarith)]
  nlinarith

lemma sum_log_primeFactors_le (q : ℕ) [NeZero q] :
    ∑ p ∈ q.primeFactors, Real.log p ≤ Real.log q := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [← Real.log_prod (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]
  apply Real.log_le_log
  · exact Finset.prod_pos fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  · have h := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
    rw [← Nat.cast_prod]
    exact_mod_cast h

lemma norm_logDeriv_sub_le (q : ℕ) [NeZero q] {s : ℂ} (hs : 1 < s.re) :
    ‖deriv (LFunction (1 : DirichletCharacter ℂ q)) s / LFunction (1 : DirichletCharacter ℂ q) s
      - deriv riemannZeta s / riemannZeta s‖ ≤ Real.log q := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    exact lt_irrefl _ hs
  have hre : 1 ≤ s.re := hs.le
  have hev : LFunction (1 : DirichletCharacter ℂ q) =ᶠ[nhds s]
      fun z => (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) * riemannZeta z := by
    filter_upwards [isOpen_ne.mem_nhds hs1] with z hz
    exact LFunctionTrivChar_eq_mul_riemannZeta hz
  have hfac : ∀ p ∈ q.primeFactors, (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s ≠ 0 :=
    fun p hp => one_sub_ne_zero (Nat.prime_of_mem_primeFactors hp) hre
  have hdfac : ∀ p ∈ q.primeFactors, DifferentiableAt ℂ (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s :=
    fun p hp => (hasDerivAt_factor (Nat.prime_of_mem_primeFactors hp) s).differentiableAt
  have hF0 : (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hfac
  have hFd : DifferentiableAt ℂ (fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s :=
    DifferentiableAt.fun_finsetProd hdfac
  have hζ0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hζd : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hL : deriv (LFunction (1 : DirichletCharacter ℂ q)) s /
      LFunction (1 : DirichletCharacter ℂ q) s =
      logDeriv (fun z => (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) * riemannZeta z) s := by
    rw [logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [hL, logDeriv_fun_mul (f := fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s hF0 hζ0
    hFd hζd, ← logDeriv_apply riemannZeta, add_sub_cancel_right,
    logDeriv_fun_prod (f := fun (p : ℕ) (z : ℂ) => 1 - (p : ℂ) ^ (-z)) hfac hdfac]
  calc ‖∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖
      ≤ ∑ p ∈ q.primeFactors, ‖logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ q.primeFactors, Real.log p :=
        Finset.sum_le_sum fun p hp => norm_logDeriv_factor_le (Nat.prime_of_mem_primeFactors hp) hre
    _ ≤ Real.log q := sum_log_primeFactors_le q

theorem neg_re_logDeriv_le : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (σ t : ℝ), 1 < σ → σ ≤ 2 → -(deriv (LFunction (1 : DirichletCharacter ℂ q)) (σ + t * I) / LFunction (1 : DirichletCharacter ℂ q) (σ + t * I)).re ≤ (1 / ((σ : ℂ) + t * I - 1)).re + C * Real.log (q * (|t| + 2)) := by
  obtain ⟨C, hC, hZ⟩ := _root_.GlobalTheory.ZetaLocal.logDeriv_riemannZeta_local
  refine ⟨C + 1, by linarith, ?_⟩
  intro q _ σ t hσ1 hσ2
  set s : ℂ := (σ : ℂ) + t * I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hs1 : 1 < s.re := by rw [hsre]; exact hσ1
  have hsne : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs1
    exact lt_irrefl _ hs1
  have hζ0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs1
  have hdist : ‖s - (3 / 2 + t * I)‖ ≤ 2 / 3 := by
    have h1 : s - (3 / 2 + t * I) = ((σ - 3 / 2 : ℝ) : ℂ) := by
      rw [hsdef]; push_cast; ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  obtain ⟨hfin, hbound⟩ := hZ t s hdist hsne hζ0
  set Z := {w : ℂ | ‖w - (3 / 2 + t * I)‖ ≤ 5 / 6 ∧ w ≠ 1 ∧ riemannZeta w = 0} with hZdef
  set S := ∑ᶠ w ∈ Z, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w) with hSdef
  have hterm : ∀ w ∈ Z, 0 ≤ ((analyticOrderNatAt riemannZeta w : ℂ) / (s - w)).re := by
    intro w hw
    have hw1 : w.re ≤ 1 := by
      by_contra h
      push Not at h
      exact riemannZeta_ne_zero_of_one_lt_re h hw.2.2
    have hpos : 0 ≤ (s - w).re := by rw [Complex.sub_re, hsre]; linarith
    rw [Complex.div_re]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hpos) (Complex.normSq_nonneg _)
  have hS : 0 ≤ S.re := by
    rw [hSdef, finsum_mem_eq_finite_toFinset_sum _ hfin, Complex.re_sum]
    exact Finset.sum_nonneg fun w hw => hterm w (hfin.mem_toFinset.mp hw)
  set E := deriv riemannZeta s / riemannZeta s + 1 / (s - 1) - S with hEdef
  have hζ : deriv riemannZeta s / riemannZeta s = E - 1 / (s - 1) + S := by
    rw [hEdef]; ring
  have hE : -E.re ≤ C * Real.log (|t| + 2) :=
    le_trans (neg_le_abs _) (le_trans (Complex.abs_re_le_norm E) hbound)
  set D := deriv (LFunction (1 : DirichletCharacter ℂ q)) s / LFunction (1 : DirichletCharacter ℂ q) s
    - deriv riemannZeta s / riemannZeta s with hDdef
  have hD : ‖D‖ ≤ Real.log q := norm_logDeriv_sub_le q hs1
  have hDre : -D.re ≤ Real.log q := le_trans (neg_le_abs _) (le_trans (Complex.abs_re_le_norm D) hD)
  have hLsplit : deriv (LFunction (1 : DirichletCharacter ℂ q)) s /
      LFunction (1 : DirichletCharacter ℂ q) s = D + (E - 1 / (s - 1) + S) := by
    rw [hDdef, ← hζ]; ring
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have ht2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hlt : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith)
  have hlog : Real.log (q * (|t| + 2)) = Real.log q + Real.log (|t| + 2) :=
    Real.log_mul (by linarith) (by linarith)
  rw [hLsplit, hlog]
  simp only [Complex.add_re, Complex.sub_re]
  nlinarith

end GlobalTheory.PrincipalLogDeriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelfDualRealMulRealDualEqOne
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory

theorem selfDual_real_mul_real_dual_eq_one :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (χ : V → V → ℂ), SelfDual μ χ → (∀ x x' y, χ (x + x') y = χ x y * χ x' y) → (∀ y, χ y 0 = 1) → ∀ L L' : AddSubgroup V, IsCompact (L : Set V) → IsOpen (L : Set V) → IsCompact (L' : Set V) → IsOpen (L' : Set V) → (∀ y, y ∈ L' ↔ ∀ x ∈ L, χ x y = 1) → μ.real (L : Set V) * μ.real (L' : Set V) = 1 := by
  intro V _ _ _ _ _ μ χ hsd hadd h0 L L' hLc hLo hL'c hL'o hdual
  obtain ⟨hH, hinv⟩ := hsd
  set Φ : V → ℂ := (L : Set V).indicator (fun _ => (1 : ℂ)) with hΦ
  have hclopen : IsClopen (L : Set V) := ⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩
  have hcont : Continuous Φ := hclopen.continuous_indicator continuous_const
  have hsupp : HasCompactSupport Φ :=
    HasCompactSupport.intro hLc (fun x hx => Set.indicator_of_notMem hx _)
  have htr : (fun y => ∫ x, Φ x * χ x y ∂μ)
      = (L' : Set V).indicator (fun _ => ((μ.real (L : Set V) : ℝ) : ℂ)) := by
    funext y
    by_cases hy : y ∈ L'
    · rw [Set.indicator_of_mem (show y ∈ (L' : Set V) from hy)]
      have : (fun x => Φ x * χ x y) = Φ := by
        funext x
        by_cases hx : x ∈ L
        · rw [(hdual y).1 hy x hx, mul_one]
        · simp [hΦ, Set.indicator_of_notMem (show x ∉ (L : Set V) from hx)]
      rw [this, hΦ, integral_indicator_const _ hLo.measurableSet]
      simp
    · rw [Set.indicator_of_notMem (show y ∉ (L' : Set V) from hy)]
      have hy' := mt (hdual y).2 hy
      push Not at hy'
      obtain ⟨x0, hx0, hne⟩ := hy'
      have h1 := integral_add_left_eq_self (μ := μ) (fun x => Φ x * χ x y) x0
      have h2 : (fun x => Φ (x0 + x) * χ (x0 + x) y) = fun x => χ x0 y * (Φ x * χ x y) := by
        funext x
        have : Φ (x0 + x) = Φ x := by
          by_cases hx : x ∈ L
          · simp [hΦ, Set.indicator_of_mem (show x ∈ (L : Set V) from hx),
              Set.indicator_of_mem (show x0 + x ∈ (L : Set V) from L.add_mem hx0 hx)]
          · have hx' : x0 + x ∉ L := fun h => hx ((L.add_mem_cancel_left hx0).1 h)
            simp [hΦ, Set.indicator_of_notMem (show x ∉ (L : Set V) from hx),
              Set.indicator_of_notMem (show x0 + x ∉ (L : Set V) from hx')]
        rw [this, hadd]; ring
      rw [h2, integral_const_mul] at h1
      have h3 : (χ x0 y - 1) * ∫ x, Φ x * χ x y ∂μ = 0 := by rw [sub_mul, h1]; ring
      exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hne)
  have hint : Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ := by
    rw [htr, integrable_indicator_iff hL'o.measurableSet]
    exact integrableOn_const hL'c.measure_lt_top.ne
  have key := hinv Φ hcont hsupp hint 0
  simp only [h0, mul_one, neg_zero] at key
  rw [htr, integral_indicator_const _ hL'o.measurableSet, hΦ,
    Set.indicator_of_mem (show (0 : V) ∈ (L : Set V) from L.zero_mem)] at key
  rw [Complex.real_smul, mul_comm] at key
  exact_mod_cast key

end GlobalTheory
end

