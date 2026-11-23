module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ProjectiveOfIsLocallyConstantFinrankFiber
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0039

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimeNatCastCompletedLaurentRingOfPrime
section
noncomputable section

namespace GlobalTheory.K5

variable (p : ℕ) [Fact p.Prime]

theorem natCast_dvd_iff_evalₐ_one (x : O0 p) :
    (p : O0 p) ∣ x ↔ AdicCompletion.evalₐ (pI p) 1 x = 0 := by
  rw [GlobalTheory.ValCompletion.evalₐ_eq_zero_iff rfl, pow_one, map_natCast]

theorem prime_natCast_completedLaurentRing : Prime (p : O0 p) := by
  haveI : (pI p ^ 1).IsPrime := by
    rw [pow_one]; exact (Ideal.span_singleton_prime (Basic.prime_lau p).ne_zero).2 (Basic.prime_lau p)
  refine ⟨?_, Basic.not_isUnit_p p, ?_⟩
  · exact_mod_cast (Nat.Prime.ne_zero Fact.out : p ≠ 0)
  · intro a b h
    rw [natCast_dvd_iff_evalₐ_one, map_mul] at h
    rw [natCast_dvd_iff_evalₐ_one, natCast_dvd_iff_evalₐ_one]
    exact mul_eq_zero.1 h

theorem prime_natCast_completedLaurentRing_of_prime : ∀ (p : ℕ) [Fact p.Prime], Prime (p : O0 p) := fun p _ => prime_natCast_completedLaurentRing p

end GlobalTheory.K5
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProdSmoothedThetaQProductDistribution
section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

noncomputable section

namespace GlobalTheory.Sieg.Distr

open Filter Topology Finset

def E (q u : ℂ) : ℂ := ∏' n : ℕ, (1 - q ^ n * u)

def T (q u : ℂ) : ℂ := E q u * E q (q * u⁻¹)

lemma summ {q : ℂ} (hq : ‖q‖ < 1) (u : ℂ) : Summable fun n : ℕ => ‖-(q ^ n * u)‖ := by
  simp only [norm_neg, norm_mul, norm_pow]
  exact (summable_geometric_of_lt_one (norm_nonneg _) hq).mul_right _

lemma mult {q : ℂ} (hq : ‖q‖ < 1) (u : ℂ) : Multipliable fun n : ℕ => (1 - q ^ n * u) := by
  simp only [sub_eq_add_neg]
  exact multipliable_one_add_of_summable (summ hq u)

lemma E_ne {q : ℂ} (hq : ‖q‖ < 1) {u : ℂ} (h : ∀ n : ℕ, q ^ n * u ≠ 1) : E q u ≠ 0 := by
  unfold E
  simp only [sub_eq_add_neg]
  refine tprod_one_add_ne_zero_of_summable (fun n => ?_) (summ hq u)
  rw [← sub_eq_add_neg]
  exact sub_ne_zero.mpr (h n).symm

lemma E_tend {q : ℂ} (hq : ‖q‖ < 1) (u : ℂ) :
    Tendsto (fun N => ∏ n ∈ range N, (1 - q ^ n * u)) atTop (𝓝 (E q u)) :=
  (mult hq u).hasProd.tendsto_prod_nat

lemma E_step {q : ℂ} (hq : ‖q‖ < 1) (u : ℂ) : E q u = (1 - u) * E q (q * u) := by
  have h1 := (E_tend hq u).comp (tendsto_add_atTop_nat 1)
  have h2 := (E_tend hq (q * u)).const_mul (1 - u)
  refine tendsto_nhds_unique h1 (h2.congr fun N => ?_)
  simp only [Function.comp, prod_range_succ', pow_zero, one_mul, pow_succ, mul_assoc]
  ring

lemma E_split {q : ℂ} (hq : ‖q‖ < 1) {m : ℕ} (hm : 0 < m) (u : ℂ) :
    ∏ j ∈ range m, E (q ^ m) (q ^ j * u) = E q u := by
  have hqm : ‖q ^ m‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq hm.ne'
  have h1 := (E_tend hq u).comp (tendsto_id.const_mul_atTop' hm)
  have h2 := tendsto_finsetProd (range m) fun j _ => E_tend hqm (q ^ j * u)
  refine tendsto_nhds_unique (h2.congr fun N => ?_) h1
  simp only [Function.comp, id]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, prod_range_add, ← ih, ← prod_mul_distrib]
    refine prod_congr rfl fun j _ => ?_
    rw [prod_range_succ, ← pow_mul, pow_add, mul_assoc]

lemma T_step {q : ℂ} (hq : ‖q‖ < 1) (h0 : q ≠ 0) {u : ℂ} (hu : u ≠ 0) :
    T q u = (-u) * T q (q * u) := by
  unfold T
  have : q * (q * u)⁻¹ = u⁻¹ := by field_simp
  rw [this, E_step hq u, E_step hq u⁻¹]
  field_simp
  ring

lemma T_steps {q : ℂ} (hq : ‖q‖ < 1) (h0 : q ≠ 0) {u : ℂ} (hu : u ≠ 0) (k : ℕ) :
    T q u = (-u) ^ k * q ^ (k.choose 2) * T q (q ^ k * u) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih, T_step hq h0 (mul_ne_zero (pow_ne_zero k h0) hu), Nat.choose_succ_succ' k 1, Nat.choose_one_right]
    rw [← mul_assoc q, ← pow_succ']
    ring

lemma T_split {q : ℂ} (hq : ‖q‖ < 1) (h0 : q ≠ 0) {m : ℕ} (hm : 0 < m) {u : ℂ} (hu : u ≠ 0) :
    ∏ j ∈ range m, T (q ^ m) (q ^ j * u) = T q u := by
  unfold T
  rw [prod_mul_distrib, E_split hq hm, ← E_split hq hm (q * u⁻¹), ← prod_range_reflect _ m]
  congr 1
  refine prod_congr rfl fun j hj => ?_
  have hj' := mem_range.mp hj
  congr 1
  have : q ^ m = q ^ (m - 1 - j) * q ^ j * q := by
    rw [← pow_add, ← pow_succ]; congr 1; omega
  rw [this]
  field_simp

lemma cth_eq {q : ℂ} (hq : ‖q‖ < 1) (c : ℕ) {t : ℂ} (h : ∀ n : ℕ, q ^ n * t ^ c ≠ 1)
    (h' : ∀ n : ℕ, q ^ n * (q * (t ^ c)⁻¹) ≠ 1) :
    cth c q t = q ^ ((c ^ 2 - 1) / 12) * (-t) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) * T q t ^ (c ^ 2) / T q (t ^ c) := by
  have h1 : E q (q * t ^ c) ≠ 0 := E_ne hq fun n => by
    rw [← mul_assoc, ← pow_succ]; exact h _
  have h2 : E q (q * (t ^ c)⁻¹) ≠ 0 := E_ne hq h'
  have hp : HasProd (fun m : ℕ => cthFac c q t (m + 1))
      (E q (q * t) ^ (c ^ 2) * E q (q * t⁻¹) ^ (c ^ 2) / (E q (q * t ^ c) * E q (q * (t ^ c)⁻¹))) := by
    have a := (((mult hq (q * t)).hasProd.pow (c ^ 2)).mul ((mult hq (q * t⁻¹)).hasProd.pow (c ^ 2)))
    have b := ((mult hq (q * t ^ c)).hasProd.mul (mult hq (q * (t ^ c)⁻¹)).hasProd)
    have := Tendsto.div a b (mul_ne_zero h1 h2)
    unfold HasProd
    refine this.congr fun s => ?_
    simp only [Pi.div_apply, cthFac, prod_div_distrib, pow_succ, mul_assoc]
  unfold cth T
  rw [hp.tprod_eq, E_step hq t, E_step hq (t ^ c)]
  simp only [mul_pow, div_eq_mul_inv, mul_inv]
  ring

lemma image_mod {c m : ℕ} (hm : 0 < m) (h : Nat.Coprime c m) :
    (range m).image (fun j => c * j % m) = range m ∧ Set.InjOn (fun j => c * j % m) (range m : Set ℕ) := by
  have hi : Set.InjOn (fun j => c * j % m) (range m : Set ℕ) := by
    intro a ha b hb hab
    have h1 : a ≡ b [MOD m] := Nat.ModEq.cancel_left_of_coprime h.symm hab
    exact Nat.ModEq.eq_of_lt_of_lt h1 (by simpa using ha) (by simpa using hb)
  refine ⟨eq_of_subset_of_card_le (fun x hx => ?_) (by rw [card_image_of_injOn hi]), hi⟩
  obtain ⟨j, -, rfl⟩ := mem_image.mp hx
  exact mem_range.mpr (Nat.mod_lt _ hm)

lemma prod_mod {M : Type*} [CommMonoid M] {c m : ℕ} (hm : 0 < m) (h : Nat.Coprime c m) (f : ℕ → M) :
    ∏ j ∈ range m, f (c * j % m) = ∏ j ∈ range m, f j := by
  obtain ⟨h1, h2⟩ := image_mod hm h
  conv_rhs => rw [← h1, prod_image h2]

lemma sum_mod {c m : ℕ} (hm : 0 < m) (h : Nat.Coprime c m) (f : ℕ → ℤ) :
    ∑ j ∈ range m, f (c * j % m) = ∑ j ∈ range m, f j := by
  obtain ⟨h1, h2⟩ := image_mod hm h
  conv_rhs => rw [← h1, sum_image h2]

lemma two_choose (k : ℕ) : 2 * (k.choose 2 : ℤ) = k * (k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.choose_succ_succ' k 1, Nat.choose_one_right]
    push_cast
    linear_combination ih

lemma sum_one (m : ℕ) : 2 * ∑ j ∈ range m, (j : ℤ) = m * (m - 1) := by
  induction m with
  | zero => simp
  | succ k ih => rw [sum_range_succ]; push_cast; linear_combination ih

lemma sum_two (m : ℕ) : 6 * ∑ j ∈ range m, (j : ℤ) ^ 2 = m * (m - 1) * (2 * m - 1) := by
  induction m with
  | zero => simp
  | succ k ih => rw [sum_range_succ]; push_cast; linear_combination ih

lemma divmod (c m j : ℕ) : (c : ℤ) * j = m * ((c * j / m : ℕ) : ℤ) + ((c * j % m : ℕ) : ℤ) := by
  exact_mod_cast (Nat.div_add_mod (c * j) m).symm

lemma smoothedTheta_distribution_t_exponent_eq {c m : ℕ} (hm : 0 < m) (h : Nat.Coprime c m) {b : ℤ} (hb : 2 * b = c - c ^ 2) :
    m * b + c * ((∑ j ∈ range m, c * j / m : ℕ) : ℤ) = b := by
  have h1 : m * ∑ j ∈ range m, ((c * j / m : ℕ) : ℤ) = (c - 1) * ∑ j ∈ range m, (j : ℤ) := by
    rw [sub_mul, one_mul, mul_sum, mul_sum]
    conv_rhs => rw [← sum_mod hm h (fun j => (j : ℤ)), ← sum_sub_distrib]
    exact sum_congr rfl fun j _ => by linear_combination -divmod c m j
  have hm' : (2 * m : ℤ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hm'
  rw [Nat.cast_sum]
  linear_combination (2 * c) * h1 + (c * (c - 1)) * sum_one m + (m * (m - 1)) * hb

lemma expo_q {c m : ℕ} (hm : 0 < m) (h : Nat.Coprime c m) {a b : ℤ} (ha : 12 * a = c ^ 2 - 1) (hb : 2 * b = c - c ^ 2) :
    m * a * m + (∑ j ∈ range m, (j : ℤ)) * b +
      ((∑ j ∈ range m, ((c * j % m) * (c * j / m) + m * (c * j / m).choose 2) : ℕ) : ℤ) = a := by
  have h1 : 2 * m * ((∑ j ∈ range m, ((c * j % m) * (c * j / m) + m * (c * j / m).choose 2) : ℕ) : ℤ) =
      (c ^ 2 - 1) * ∑ j ∈ range m, (j : ℤ) ^ 2 - m * (c - 1) * ∑ j ∈ range m, (j : ℤ) := by
    have e : ∀ S₁ S₂ : ℤ, (c ^ 2 - 1) * S₂ - m * (c - 1) * S₁ = c ^ 2 * S₂ - m * c * S₁ - (S₂ - m * S₁) := by
      intros; ring
    rw [e, Nat.cast_sum, mul_sum, mul_sum, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib,
      ← sum_mod hm h (fun j => (j : ℤ) ^ 2 - m * j), ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    have h2 := divmod c m j
    have h3 := two_choose (c * j / m)
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul m]
    generalize ((c * j / m).choose 2 : ℤ) = C at *
    generalize ((c * j / m : ℕ) : ℤ) = k at *
    generalize ((c * j % m : ℕ) : ℤ) = r at *
    linear_combination m ^ 2 * h3 - (c * j + m * k + r - m) * h2
  have hm' : (12 * m : ℤ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hm'
  linear_combination 6 * h1 + (c ^ 2 - 1) * sum_two m + (6 * m * b - 3 * m * (c - 1)) * sum_one m
    + (m ^ 3 - m) * ha + 3 * m ^ 2 * (m - 1) * hb

theorem _root_.GlobalTheory.Sieg.prod_cth_mul_pow : ∀ (c m : ℕ) (Q t : ℂ), 1 < c → Nat.Coprime c 6 → 0 < m → Nat.Coprime c m → ‖Q‖ < 1 → Q ≠ 0 → t ≠ 0 → (∀ n : ℤ, Q ^ n * t ^ c ≠ 1) → ∏ j ∈ Finset.range m, cth c (Q ^ m) (t * Q ^ j) = cth c Q t := by
  intro c m Q t hc h6 hm hcm hQ h0 ht hn
  have hqm : ‖Q ^ m‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hQ hm.ne'
  have hs : t ^ c ≠ 0 := pow_ne_zero _ ht
  have hodd : Odd c := (Nat.coprime_two_right).mp (h6.coprime_dvd_right (by norm_num))
  have hinv : ∀ n : ℤ, Q ^ n * (t ^ c)⁻¹ ≠ 1 := fun n hh => by
    apply hn (-n)
    rw [← inv_inj, mul_inv, ← zpow_neg, neg_neg, hh, inv_one]
  have h12 : 12 ∣ c ^ 2 - 1 := by
    have h2 : c % 2 = 1 := Nat.odd_iff.mp hodd
    have h3 : ¬ 3 ∣ c := fun hd => by
      have := Nat.dvd_gcd hd (show 3 ∣ 6 by norm_num)
      rw [h6] at this; omega
    have : c % 12 = 1 ∨ c % 12 = 5 ∨ c % 12 = 7 ∨ c % 12 = 11 := by omega
    have h4 : c ^ 2 % 12 = 1 := by
      rw [Nat.pow_mod]; rcases this with h | h | h | h <;> rw [h]
    omega
  obtain ⟨a, ha⟩ := h12
  have ha' : 12 * (a : ℤ) = c ^ 2 - 1 := by
    have : 1 ≤ c ^ 2 := Nat.one_le_pow _ _ (by omega)
    have h2 : c ^ 2 = 12 * a + 1 := by omega
    have h3 : (c : ℤ) ^ 2 = 12 * a + 1 := by exact_mod_cast h2
    linarith
  have haa : (c ^ 2 - 1) / 12 = a := by omega
  obtain ⟨b, hb⟩ : ∃ b : ℤ, 2 * b = c - c ^ 2 := by
    obtain ⟨d, hd⟩ := hodd
    exact ⟨-(c * d), by rw [hd]; push_cast; ring⟩
  have hbb : ((c : ℤ) - (c : ℤ) ^ 2) / 2 = b := by omega
  have hL : ∀ j ∈ range m, cth c (Q ^ m) (t * Q ^ j) =
      (Q ^ m) ^ a * ((-t) ^ b * (Q ^ j) ^ b) * T (Q ^ m) (Q ^ j * t) ^ (c ^ 2) / T (Q ^ m) (Q ^ (c * j) * t ^ c) := by
    intro j _
    rw [cth_eq hqm c, haa, hbb, ← neg_mul, mul_zpow, mul_pow t, ← pow_mul Q j, mul_comm t, mul_comm (t ^ c),
      mul_comm j c]
    · intro n hh
      apply hn ((m * n + j * c : ℕ) : ℤ)
      rw [← hh, zpow_natCast]; ring
    · intro n hh
      apply hinv ((m * n + m : ℕ) - (j * c : ℕ) : ℤ)
      rw [← hh, zpow_sub₀ h0, zpow_natCast, zpow_natCast]; field_simp; ring
  have hD : T Q (t ^ c) = (-t) ^ (c * ∑ j ∈ range m, c * j / m) *
      Q ^ (∑ j ∈ range m, ((c * j % m) * (c * j / m) + m * (c * j / m).choose 2)) *
      ∏ j ∈ range m, T (Q ^ m) (Q ^ (c * j) * t ^ c) := by
    rw [← T_split hQ h0 hm hs, ← prod_mod hm hcm (fun j => T (Q ^ m) (Q ^ j * t ^ c)), mul_sum,
      ← prod_pow_eq_pow_sum, ← prod_pow_eq_pow_sum, ← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_congr rfl fun j _ => ?_
    rw [T_steps hqm (pow_ne_zero _ h0) (mul_ne_zero (pow_ne_zero _ h0) hs) (c * j / m), ← mul_assoc, ← pow_mul,
      ← pow_mul, ← pow_add, Nat.div_add_mod, pow_mul (-t), hodd.neg_pow, ← mul_neg, mul_pow, ← pow_mul, pow_add]
    ring
  rw [prod_congr rfl hL, cth_eq hQ c (fun n => by simpa using hn n)
    (fun n => by rw [← mul_assoc, ← pow_succ, ← zpow_natCast]; exact hinv _), haa, hbb, hD, prod_div_distrib,
    prod_mul_distrib, prod_mul_distrib, prod_mul_distrib, prod_const, prod_const, prod_pow, T_split hQ h0 hm ht, card_range,
    prod_zpow, prod_pow_eq_pow_sum]
  have e1 := congrArg (fun z : ℤ => (-t) ^ z) (smoothedTheta_distribution_t_exponent_eq hm hcm hb)
  have e2 := congrArg (fun z : ℤ => Q ^ z) (expo_q hm hcm ha' hb)
  have hnt : -t ≠ 0 := neg_ne_zero.mpr ht
  rw [mul_comm (m : ℤ) b, ← Nat.cast_mul c] at e1
  rw [← Nat.cast_sum] at e2
  simp only [zpow_add₀ hnt, zpow_add₀ h0, zpow_natCast, zpow_mul] at e1 e2
  conv_rhs => rw [← e1, ← e2]
  generalize (∏ j ∈ range m, T (Q ^ m) (Q ^ (c * j) * t ^ c)) = P
  by_cases hP : P = 0
  · simp [hP]
  field_simp

end GlobalTheory.Sieg.Distr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjectiveCokerOfIsLocallyConstantFinrankRange
section
open TensorProduct Module Function Filter Topology

namespace GlobalTheory

open Semicont

section FiniteModule

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

theorem exists_away_equiv_of_eventually_finrank_fiber_eq [IsReduced R] [Module.Finite R M]
    (p : PrimeSpectrum R)
    (h : ∀ᶠ q : PrimeSpectrum R in 𝓝 p,
      finrank q.asIdeal.ResidueField (q.asIdeal.ResidueField ⊗[R] M) =
        finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M)) :
    ∃ f ∉ p.asIdeal, Nonempty
      ((Fin (finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M)) →
        Localization.Away f) ≃ₗ[Localization.Away f] LocalizedModule.Away f M) := by
  obtain ⟨φ, hφ⟩ := exists_baseChange_surjective (R := R) (M := M) p.asIdeal.ResidueField
  have h1 := h.and ((isOpen_setOf_baseChange_surjective φ).mem_nhds hφ)
  obtain ⟨_, ⟨f, rfl⟩, hpf, hf⟩ := (PrimeSpectrum.isTopologicalBasis_basic_opens.mem_nhds_iff).1 h1
  have hker : ∀ x, φ x = 0 → f • x = 0 := by
    intro x hx
    ext j
    refine IsReduced.eq_zero _ (nilpotent_iff_mem_prime.2 fun J hJ => ?_)
    by_cases hfJ : f ∈ J
    · exact J.mul_mem_right _ hfJ
    obtain ⟨h2, h3⟩ := hf (show (⟨J, hJ⟩ : PrimeSpectrum R) ∈ _ from hfJ)
    have hinj : Injective (φ.baseChange J.ResidueField) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        ((finrank_baseChange_fin _ _).trans h2.symm)).2 h3
    have h4 : (1 : J.ResidueField) ⊗ₜ[R] x = 0 := hinj (by simp [hx])
    have h5 :=
      congrFun (congrArg (TensorProduct.piScalarRight R J.ResidueField J.ResidueField _) h4) j
    refine J.mul_mem_left _ ?_
    rw [← Ideal.algebraMap_residueField_eq_zero]
    simpa [Algebra.smul_def] using h5
  let A := Localization.Away f
  have hsurj : Surjective (φ.baseChange A) := by
    rw [baseChange_surjective_iff]
    have : Subsingleton (LocalizedModule.Away f (M ⧸ LinearMap.range φ)) := by
      rw [LocalizedModule.subsingleton_iff_disjoint, Set.disjoint_left]
      intro q hq
      have h3 : Surjective (φ.baseChange q.asIdeal.ResidueField) := (hf hq).2
      rwa [baseChange_surjective_iff, ← not_nontrivial_iff_subsingleton,
        ← Module.mem_support_iff_nontrivial_residueField_tensorProduct] at h3
    exact (LocalizedModule.equivTensorProduct (Submonoid.powers f) _).symm.toEquiv.subsingleton
  have hinj : Injective (φ.baseChange A) := by
    have : Module.Flat R A := IsLocalization.flat A (Submonoid.powers f)
    rw [← LinearMap.ker_eq_bot, ← baseChange_ker, Submodule.baseChange_eq_span, eq_bot_iff,
      Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have hu : IsUnit (algebraMap R A f) := IsLocalization.Away.algebraMap_isUnit f
    refine (hu.smul_eq_zero).1 ?_
    rw [algebraMap_smul, ← map_smul, hker x hx, map_zero]
  exact ⟨f, hpf, ⟨(TensorProduct.piScalarRight R A A _).symm ≪≫ₗ
    LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩ ≪≫ₗ
    (LocalizedModule.equivTensorProduct (Submonoid.powers f) M).symm⟩⟩

theorem finitePresentation_of_isLocallyConstant_finrank_fiber [IsReduced R] [Module.Finite R M]
    (h : IsLocallyConstant fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M)) :
    Module.FinitePresentation R M := by
  refine Module.FinitePresentation.of_localizationSpan
    {f | Module.FinitePresentation (Localization.Away f) (LocalizedModule.Away f M)} ?_
    fun g => g.2
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨f, hf, ⟨e⟩⟩ := exists_away_equiv_of_eventually_finrank_fiber_eq (M := M)
    ⟨m, hm.isPrime⟩ (h.eventually_eq _)
  exact hf (hle (Ideal.subset_span (Module.FinitePresentation.of_equiv e)))

theorem projective_of_finite_of_isLocallyConstant_finrank_fiber [IsReduced R] [Module.Finite R M]
    (h : IsLocallyConstant fun p : PrimeSpectrum R =>
      finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M)) :
    Module.Projective R M :=
  have := finitePresentation_of_isLocallyConstant_finrank_fiber h
  projective_of_isLocallyConstant_finrank_fiber h

theorem finrank_tensorProduct_eq_finrank_fiber (k : Type*) [Field k] [Algebra R k]
    (p : PrimeSpectrum R) (hp : p.asIdeal = RingHom.ker (algebraMap R k)) :
    finrank k (k ⊗[R] M) = finrank p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[R] M) := by
  letI : Algebra p.asIdeal.ResidueField k :=
    (Ideal.ResidueField.lift p.asIdeal (algebraMap R k) hp.le (fun x hx => by
      refine IsUnit.mk0 _ fun h0 => hx ?_
      rw [hp]
      exact h0)).toAlgebra
  have : IsScalarTower R p.asIdeal.ResidueField k :=
    IsScalarTower.of_algebraMap_eq fun x => (Ideal.ResidueField.lift_algebraMap ..).symm
  rw [← (AlgebraTensorModule.cancelBaseChange R p.asIdeal.ResidueField k k M).finrank_eq,
    Module.finrank_baseChange]

end FiniteModule

section Map

variable {R : Type*} [CommRing R] {E F : Type*} [AddCommGroup E] [Module R E]
  [AddCommGroup F] [Module R F]

theorem finrank_baseChange_coker_add_finrank_range [Module.Finite R F]
    (k : Type*) [Field k] [Algebra R k] (φ : E →ₗ[R] F) :
    finrank k (k ⊗[R] (F ⧸ LinearMap.range φ)) + finrank k (LinearMap.range (φ.baseChange k)) =
      finrank k (k ⊗[R] F) := by
  rw [(baseChangeQuotEquiv k _).finrank_eq, baseChange_range]
  exact Submodule.finrank_quotient_add_finrank _

theorem projective_coker_of_isLocallyConstant_finrank_range [IsReduced R]
    [Module.Finite R F] [Module.Projective R F] (φ : E →ₗ[R] F)
    (h : IsLocallyConstant fun p : PrimeSpectrum R => finrank p.asIdeal.ResidueField
      (LinearMap.range (φ.baseChange p.asIdeal.ResidueField))) :
    Module.Projective R (F ⧸ LinearMap.range φ) := by
  refine projective_of_finite_of_isLocallyConstant_finrank_fiber
    ((IsLocallyConstant.iff_eventually_eq _).2 fun p => ?_)
  filter_upwards [h.eventually_eq p, (Semicont.isLocallyConstant_finrank_fiber F).eventually_eq p]
    with q h1 h2
  have h3 := finrank_baseChange_coker_add_finrank_range p.asIdeal.ResidueField φ
  have h4 := finrank_baseChange_coker_add_finrank_range q.asIdeal.ResidueField φ
  omega

theorem exists_comp_comp_eq_of_isLocallyConstant_finrank_range [IsReduced R]
    [Module.Finite R F] [Module.Projective R F] (φ : E →ₗ[R] F)
    (h : IsLocallyConstant fun p : PrimeSpectrum R => finrank p.asIdeal.ResidueField
      (LinearMap.range (φ.baseChange p.asIdeal.ResidueField))) :
    ∃ s : F →ₗ[R] E, φ ∘ₗ s ∘ₗ φ = φ :=
  have := projective_coker_of_isLocallyConstant_finrank_range φ h
  exists_comp_comp_eq_of_projective φ

theorem exists_retraction_ker_of_generalizedInverse (φ : E →ₗ[R] F) (s : F →ₗ[R] E)
    (hs : φ ∘ₗ s ∘ₗ φ = φ) :
    ∃ r : E →ₗ[R] LinearMap.ker φ, r ∘ₗ (LinearMap.ker φ).subtype = LinearMap.id := by
  have hs' : ∀ x, φ (s (φ x)) = φ x := LinearMap.congr_fun hs
  refine ⟨(LinearMap.id - s ∘ₗ φ).codRestrict _ fun x => by simp [hs'], ?_⟩
  ext x
  simp

theorem lTensor_subtype_injective_of_retraction (P : Submodule R E) (r : E →ₗ[R] P)
    (hr : r ∘ₗ P.subtype = LinearMap.id) (N : Type*) [AddCommGroup N] [Module R N] :
    Injective (P.subtype.lTensor N) :=
  LeftInverse.injective (g := r.lTensor N) fun x => by
    rw [← LinearMap.lTensor_comp_apply, hr, LinearMap.lTensor_id, LinearMap.id_apply]

theorem baseChange_ker_of_comp_comp_eq (φ : E →ₗ[R] F) (s : F →ₗ[R] E)
    (hs : φ ∘ₗ s ∘ₗ φ = φ) (S : Type*) [CommRing S] [Algebra R S] :
    (LinearMap.ker φ).baseChange S = LinearMap.ker (φ.baseChange S) := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
      LinearMap.comp_ker_subtype, LinearMap.baseChange_zero, LinearMap.zero_apply]
  · intro hz
    obtain ⟨y, hy⟩ := (tensorKer_bijective_of_comp_comp_eq S S φ s hs).2 ⟨z, hz⟩
    exact ⟨y, (LinearMap.tensorKer_coe S S φ y).symm.trans (congrArg Subtype.val hy)⟩

universe u v

end Map

universe u v w

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelFunctionNeZero
section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.Sieg

theorem sg_ne_zero : ∀ (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ), admitted c x → sg c x τ ≠ 0 :=
  fun _ _ τ h => (GlobalTheory.Sieg.Model.multipliable_and_sg_ne_zero h τ).2.2

end GlobalTheory.Sieg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashQExpansionCoeffWidthTransformStatement
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slashQExpansionCoeffWidth_transform : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ℍ → ℂ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → IsMF Γ k f → (∀ (x : SL(2, ℤ)) (n : ℕ), co M k f (x * ModularGroup.T) n = Complex.exp (2 * Real.pi * Complex.I / M) ^ n * co M k f x n) ∧ (∀ γ ∈ Γ, ∀ (x : SL(2, ℤ)) (n : ℕ), co M k f (γ * x) n = co M k f x n) ∧ (Odd k → ∀ (x : SL(2, ℤ)) (n : ℕ), co M k f (-x) n = -co M k f x n) := by
  first | exact @GlobalTheory.OddFrame.co_transform | exact GlobalTheory.OddFrame.co_transform | (intros; apply GlobalTheory.OddFrame.co_transform <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumFinrankLevelOneLeFinrankCuspFormOfFrameStatement
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_finrank_levelOne_le_finrank_cuspForm_of_frame : ∀ (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ) (k : ℤ), Γ.FiniteIndex → FiniteDimensional ℂ (CuspForm Γ k) → (∀ j, IsCF Γ (w j) (F j)) → (∀ τ, (evM s w F τ).det ≠ 0) → ∑ j, Module.finrank ℂ (ModularForm 𝒮ℒ (k - w j)) ≤ Module.finrank ℂ (CuspForm Γ k) := by
  first | exact @GlobalTheory.OddFrame.sum_finrank_le_finrank_cuspForm | exact GlobalTheory.OddFrame.sum_finrank_le_finrank_cuspForm | (intros; apply GlobalTheory.OddFrame.sum_finrank_le_finrank_cuspForm <;> assumption)
end

