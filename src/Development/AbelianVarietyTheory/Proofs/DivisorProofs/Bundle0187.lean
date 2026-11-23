module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0098

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CyclotomicSumNormSqEqOneSingleNonzero
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory

theorem cycloSq_mod_eq_zero_iff {l a b : ℕ} (hl : 0 < l) (ha : a < l) (hb : b < l) :
    (a + (l - 1) * b) % l = 0 ↔ b = a := by
  rw [← Nat.dvd_iff_mod_eq_zero]
  constructor
  · intro h
    have h2 : (l : ℤ) ∣ ((a + (l - 1) * b : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h
    have h3 : ((a + (l - 1) * b : ℕ) : ℤ) = ((a : ℤ) - b) + l * b := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ l)]; ring
    rw [h3] at h2
    have h' : (l : ℤ) ∣ (a : ℤ) - b := (dvd_add_left (dvd_mul_right _ _)).mp h2
    have := Int.eq_zero_of_abs_lt_dvd h' (by rw [abs_lt]; constructor <;> omega)
    omega
  · rintro rfl
    obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
    exact ⟨b, by simp; ring⟩

theorem cycloSq_coeff_eq {l : ℕ} (hl : l.Prime) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ l) (a : ℕ → ℤ)
    (h : ∑ d ∈ Finset.range l, (a d : ℂ) * ζ ^ d = 0) : ∀ d < l, a d = a (l - 1) := by
  have hl1 : 1 < l := hl.one_lt
  have hgeom : ∑ d ∈ Finset.range l, ζ ^ d = 0 := hζ.geom_sum_eq_zero hl1
  set Q : ℚ[X] := ∑ d ∈ Finset.range (l - 1), C (((a d - a (l - 1) : ℤ)) : ℚ) * X ^ d with hQdef
  have hQ : aeval ζ Q = 0 := by
    have h1 : ∑ d ∈ Finset.range l, (((a d - a (l - 1) : ℤ)) : ℂ) * ζ ^ d = 0 := by
      simp only [Int.cast_sub, sub_mul, Finset.sum_sub_distrib, h, ← Finset.mul_sum, hgeom,
        mul_zero, sub_zero]
    have hl' : l = (l - 1) + 1 := by omega
    rw [hl', Finset.sum_range_succ] at h1
    simp only [Nat.add_sub_cancel, sub_self, Int.cast_zero, zero_mul, add_zero] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hQdef, map_sum]
    simpa using h1
  have hdvd : minpoly ℚ ζ ∣ Q := minpoly.dvd ℚ ζ hQ
  have hdeg : (minpoly ℚ ζ).natDegree = l - 1 := by
    rw [← cyclotomic_eq_minpoly_rat hζ hl.pos, natDegree_cyclotomic, Nat.totient_prime hl]
  have hQ0 : Q = 0 := by
    by_contra hne
    have h1 := natDegree_le_of_dvd hdvd hne
    have h2 : Q.natDegree ≤ l - 2 := natDegree_sum_le_of_forall_le _ _ (fun d hd =>
      (natDegree_C_mul_X_pow_le _ _).trans (by rw [Finset.mem_range] at hd; omega))
    omega
  intro d hd
  by_cases hd' : d = l - 1
  · rw [hd']
  have h1 : Q.coeff d = 0 := by rw [hQ0]; simp
  rw [hQdef, finsetSum_coeff] at h1
  simp only [coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range] at h1
  rw [if_pos (by omega)] at h1
  have : ((a d - a (l - 1) : ℤ) : ℚ) = 0 := h1
  exact_mod_cast sub_eq_zero.mp (by exact_mod_cast this)

end GlobalTheory

namespace GlobalTheory

def cycloSqCoeff (l : ℕ) (f : ℕ → ℤ) (d : ℕ) : ℤ :=
  ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l,
    if (a + (l - 1) * b) % l = d then f a * f b else 0

theorem cycloSq_mul_star {l : ℕ} (hl : 0 < l) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ l) (f : ℕ → ℤ) :
    (∑ a ∈ Finset.range l, (f a : ℂ) * ζ ^ a) * star (∑ a ∈ Finset.range l, (f a : ℂ) * ζ ^ a)
      = ∑ d ∈ Finset.range l, (cycloSqCoeff l f d : ℂ) * ζ ^ d := by
  have hnorm : ‖ζ‖ = 1 := hζ.norm'_eq_one hl.ne'
  have hinv : ζ⁻¹ = ζ ^ (l - 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ', Nat.sub_add_cancel hl, hζ.pow_eq_one]
  have hstar : star ζ = ζ ^ (l - 1) := by
    rw [← hinv, Complex.inv_eq_conj hnorm]; rfl
  have hpow : ∀ m, ζ ^ m = ζ ^ (m % l) := by
    intro m
    conv_lhs => rw [← Nat.div_add_mod m l]
    rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  rw [star_sum, Finset.sum_mul_sum]
  calc ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l, (f a : ℂ) * ζ ^ a * star ((f b : ℂ) * ζ ^ b)
      = ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l,
          ((f a * f b : ℤ) : ℂ) * ζ ^ ((a + (l - 1) * b) % l) := by
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
        rw [← hpow, star_mul', star_pow, hstar, star_intCast, pow_add, pow_mul]
        push_cast; ring
    _ = ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l, ∑ d ∈ Finset.range l,
          (if (a + (l - 1) * b) % l = d then ((f a * f b : ℤ) : ℂ) * ζ ^ d else 0) := by
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
        rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (Nat.mod_lt _ hl))]
    _ = ∑ d ∈ Finset.range l, ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l,
          (if (a + (l - 1) * b) % l = d then ((f a * f b : ℤ) : ℂ) * ζ ^ d else 0) := by
        exact (Finset.sum_congr rfl (fun a _ => Finset.sum_comm)).trans Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        simp only [cycloSqCoeff, Int.cast_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
        split_ifs <;> simp

theorem cycloSq_sum_coeff {l : ℕ} (hl : 0 < l) (f : ℕ → ℤ) :
    ∑ d ∈ Finset.range l, cycloSqCoeff l f d
      = ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l, f a * f b := by
  simp only [cycloSqCoeff]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr (Nat.mod_lt _ hl))]

theorem cycloSq_coeff_zero {l : ℕ} (hl : 0 < l) (f : ℕ → ℤ) :
    cycloSqCoeff l f 0 = ∑ a ∈ Finset.range l, f a ^ 2 := by
  simp only [cycloSqCoeff]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  rw [Finset.mem_range] at ha
  rw [Finset.sum_congr rfl (g := fun b => if b = a then f a * f b else 0) (fun b hb => by
    simp only [cycloSq_mod_eq_zero_iff hl ha (Finset.mem_range.mp hb)])]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr ha), sq]

theorem cycloSq_two_mul {l : ℕ} (f : ℕ → ℤ) :
    ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l, (f a - f b) ^ 2
      = 2 * ((l : ℤ) * ∑ a ∈ Finset.range l, f a ^ 2
          - ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l, f a * f b) := by
  have : ∀ a b : ℕ, (f a - f b) ^ 2 = f a ^ 2 + f b ^ 2 - 2 * (f a * f b) := fun a b => by ring
  simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
  ring

theorem cycloSq_le_of_ne_zero {l : ℕ} (hl : 1 < l) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ l)
    (f : ℕ → ℤ) (hc : ∑ a ∈ Finset.range l, (f a : ℂ) * ζ ^ a ≠ 0) :
    (l : ℤ) ≤ ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l, (f a - f b) ^ 2 := by
  have hne : ∃ x ∈ Finset.range l, f x ≠ f 0 := by
    by_contra hall
    push_neg at hall
    apply hc
    rw [Finset.sum_congr rfl (fun a ha => by rw [hall a ha]), ← Finset.mul_sum,
      hζ.geom_sum_eq_zero hl, mul_zero]
  obtain ⟨x, hx, hfx⟩ := hne
  have h0 : 0 ∈ Finset.range l := Finset.mem_range.mpr (by omega)
  have hx0 : x ≠ 0 := by rintro rfl; exact hfx rfl
  have hR : ∀ a ∈ Finset.range l, 0 ≤ ∑ b ∈ Finset.range l, (f a - f b) ^ 2 :=
    fun a _ => Finset.sum_nonneg (fun b _ => sq_nonneg _)
  have hsum := Finset.add_le_sum hR hx h0 hx0
  have hxy : (l : ℤ) ≤ ∑ b ∈ Finset.range l, (f x - f b) ^ 2
      + ∑ b ∈ Finset.range l, (f 0 - f b) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    calc (l : ℤ) = ∑ b ∈ Finset.range l, (1 : ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun b _ => by
        have h1 := sq_nonneg (f x - f b)
        have h2 := sq_nonneg (f 0 - f b)
        by_cases h : f x = f b
        · have : f 0 - f b ≠ 0 := by omega
          rcases lt_or_gt_of_ne this with h3 | h3 <;> nlinarith
        · have : f x - f b ≠ 0 := by omega
          rcases lt_or_gt_of_ne this with h3 | h3 <;> nlinarith)
  linarith

end GlobalTheory

namespace GlobalTheory

theorem cyclo_sum_mul_star_eq_one_single : ∀ (l : ℕ) (ζ : ℂ), l.Prime → IsPrimitiveRoot ζ l →
    ∀ (I : Type) (S : Finset I) (n : I → ℕ → ℤ),
      ∑ i ∈ S, (∑ a ∈ Finset.range l, (n i a : ℂ) * ζ ^ a) *
          star (∑ a ∈ Finset.range l, (n i a : ℂ) * ζ ^ a) = 1 →
      ∃ i₀ ∈ S, ∀ i ∈ S, i ≠ i₀ → ∑ a ∈ Finset.range l, (n i a : ℂ) * ζ ^ a = 0 := by
  intro l ζ hl hζ I S n hsum
  have hl0 : 0 < l := hl.pos
  have hl1 : 1 < l := hl.one_lt
  set N : ℕ → ℤ := fun d => ∑ i ∈ S, cycloSqCoeff l (n i) d with hN
  have hT : ∑ d ∈ Finset.range l, (N d : ℂ) * ζ ^ d = 1 := by
    rw [← hsum, Finset.sum_congr rfl (fun i _ => cycloSq_mul_star hl0 hζ (n i))]
    simp only [hN, Int.cast_sum, Finset.sum_mul]
    exact Finset.sum_comm
  set A : ℕ → ℤ := fun d => N d - if d = 0 then 1 else 0 with hAdef
  have hA : ∑ d ∈ Finset.range l, (A d : ℂ) * ζ ^ d = 0 := by
    simp only [hAdef, Int.cast_sub, sub_mul, Finset.sum_sub_distrib, hT]
    simp [hl0]
  have hAeq := cycloSq_coeff_eq hl hζ A hA
  have hNd : ∀ d ∈ (Finset.range l).erase 0, N d = N 0 - 1 := by
    intro d hd
    rw [Finset.mem_erase, Finset.mem_range] at hd
    have h3 : A d = A 0 := (hAeq d hd.2).trans (hAeq 0 hl0).symm
    simp only [hAdef, if_neg hd.1, if_true, sub_zero] at h3
    linarith
  have h0mem : 0 ∈ Finset.range l := Finset.mem_range.mpr hl0
  have hsumN : ∑ d ∈ Finset.range l, N d = N 0 + ((l : ℤ) - 1) * (N 0 - 1) := by
    rw [← Finset.add_sum_erase _ _ h0mem, Finset.sum_congr rfl hNd, Finset.sum_const,
      Finset.card_erase_of_mem h0mem, Finset.card_range, nsmul_eq_mul,
      Nat.cast_sub (by omega : 1 ≤ l)]
    push_cast; ring
  have hsumN' : ∑ d ∈ Finset.range l, N d
      = ∑ i ∈ S, ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l, n i a * n i b := by
    simp only [hN]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => cycloSq_sum_coeff hl0 (n i))
  have hN0 : N 0 = ∑ i ∈ S, ∑ a ∈ Finset.range l, n i a ^ 2 :=
    Finset.sum_congr rfl (fun i _ => cycloSq_coeff_zero hl0 (n i))
  have hQsum : ∑ i ∈ S, ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l, (n i a - n i b) ^ 2
      = 2 * ((l : ℤ) - 1) := by
    rw [Finset.sum_congr rfl (fun i _ => cycloSq_two_mul (n i)), ← Finset.mul_sum,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← hN0, ← hsumN', hsumN]
    ring
  have hQnn : ∀ i ∈ S, 0 ≤ ∑ a ∈ Finset.range l, ∑ b ∈ Finset.range l, (n i a - n i b) ^ 2 :=
    fun i _ => Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => sq_nonneg _))
  obtain ⟨i₀, hi₀, hc₀⟩ : ∃ i₀ ∈ S, ∑ a ∈ Finset.range l, (n i₀ a : ℂ) * ζ ^ a ≠ 0 := by
    by_contra H
    push_neg at H
    rw [Finset.sum_eq_zero (fun i hi => by rw [H i hi, zero_mul])] at hsum
    exact zero_ne_one hsum
  refine ⟨i₀, hi₀, fun i hi hne => ?_⟩
  by_contra hci
  have h1 := cycloSq_le_of_ne_zero hl1 hζ (n i) hci
  have h2 := cycloSq_le_of_ne_zero hl1 hζ (n i₀) hc₀
  have h3 := Finset.add_le_sum hQnn hi hi₀ hne
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivAt0SubstLinearLipschitz
section
open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth

namespace GlobalTheory.FGDepth

theorem exists_lipschitz_eval {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {ι : Type}
    (Q : MvPolynomial ι C) :
    ∃ K : ℝ, (∀ a : ι → C, (∀ i, IsIntV v (a i)) →
        ((-K : ℝ) : WithTop ℝ) ≤ v (MvPolynomial.eval a Q)) ∧
      ∀ (M : ℝ) (a a' : ι → C), (∀ i, IsIntV v (a i)) → (∀ i, IsIntV v (a' i)) →
        (∀ i, ((M : ℝ) : WithTop ℝ) ≤ v (a i - a' i)) →
        ((M - K : ℝ) : WithTop ℝ) ≤ v (MvPolynomial.eval a Q - MvPolynomial.eval a' Q) := by
  induction Q using MvPolynomial.induction_on with
  | C c =>
    by_cases hc : v c = ⊤
    · exact ⟨0, fun a _ => by simp [hc], fun M a a' _ _ _ => by simp⟩
    · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hc
      exact ⟨-r, fun a _ => by simp [hr], fun M a a' _ _ _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨K₁, h₁, h₁'⟩ := hp
    obtain ⟨K₂, h₂, h₂'⟩ := hq
    refine ⟨max K₁ K₂, fun a ha => ?_, fun M a a' ha ha' hM => ?_⟩
    · rw [map_add (f := _)]
      refine v.map_le_add (le_trans ?_ (h₁ a ha)) (le_trans ?_ (h₂ a ha))
      · exact WithTop.coe_le_coe.mpr (neg_le_neg (le_max_left _ _))
      · exact WithTop.coe_le_coe.mpr (neg_le_neg (le_max_right _ _))
    · rw [map_add (f := _), map_add (f := _), add_sub_add_comm]
      refine v.map_le_add (le_trans ?_ (h₁' M a a' ha ha' hM))
        (le_trans ?_ (h₂' M a a' ha ha' hM))
      · exact WithTop.coe_le_coe.mpr (sub_le_sub_left (le_max_left _ _) _)
      · exact WithTop.coe_le_coe.mpr (sub_le_sub_left (le_max_right _ _) _)
  | mul_X p i hp =>
    obtain ⟨K, h, h'⟩ := hp
    refine ⟨K, fun a ha => ?_, fun M a a' ha ha' hM => ?_⟩
    · rw [map_mul, MvPolynomial.eval_X, v.map_mul]
      exact le_add_of_le_of_nonneg (h a ha) (ha i)
    · rw [map_mul, map_mul, MvPolynomial.eval_X, MvPolynomial.eval_X]
      have e : MvPolynomial.eval a p * a i - MvPolynomial.eval a' p * a' i =
          (MvPolynomial.eval a p - MvPolynomial.eval a' p) * a i +
            MvPolynomial.eval a' p * (a i - a' i) := by ring
      rw [e]
      refine v.map_le_add ?_ ?_
      · rw [v.map_mul]
        exact le_add_of_le_of_nonneg (h' M a a' ha ha' hM) (ha i)
      · rw [v.map_mul]
        have e2 : ((M - K : ℝ) : WithTop ℝ) = ((-K : ℝ) : WithTop ℝ) + ((M : ℝ) : WithTop ℝ) := by
          rw [← WithTop.coe_add]; congr 1; ring
        rw [e2]
        exact add_le_add (h a' ha') (hM i)

theorem exists_poly_derivAt0_subst {C : Type} [Field C] {σ Λ : Type} [Fintype σ] [Fintype Λ]
    (P : MvPolynomial Λ C) (Z : MvPowerSeries σ C) :
    ∃ Q : MvPolynomial (σ × Λ) C, ∀ a : σ → Λ → C,
      derivAt0 P (MvPowerSeries.subst
        (fun s => ∑ l, a s l • (MvPowerSeries.X l : MvPowerSeries Λ C)) Z) =
      MvPolynomial.eval (fun x : σ × Λ => a x.1 x.2) Q := by
  let u : σ → MvPowerSeries Λ (MvPolynomial (σ × Λ) C) :=
    fun s => ∑ l, (MvPolynomial.X (s, l) : MvPolynomial (σ × Λ) C) • MvPowerSeries.X l
  have hu : HasSubst u := hasSubst_of_constantCoeff_zero fun s => by simp [u]
  let Zu : MvPowerSeries Λ (MvPolynomial (σ × Λ) C) :=
    subst u (MvPowerSeries.map (MvPolynomial.C : C →+* MvPolynomial (σ × Λ) C) Z)
  refine ⟨∑ α ∈ P.support, MvPolynomial.C (P.coeff α * mfact α) * coeff α Zu, fun a => ?_⟩
  have key : MvPowerSeries.map (MvPolynomial.eval (fun x : σ × Λ => a x.1 x.2)) Zu =
      MvPowerSeries.subst (fun s => ∑ l, a s l • (MvPowerSeries.X l : MvPowerSeries Λ C)) Z := by
    rw [MvPowerSeries.map_subst hu]
    congr 1
    · funext s
      simp [u, MvPowerSeries.smul_eq_C_mul]
    · ext d
      simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← key, derivAt0, map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_mul, MvPolynomial.eval_C, coeff_map]

theorem derivAt0_subst_linear_lipschitz :
    ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (σ Λ : Type) [Fintype σ] [Fintype Λ] (P : MvPolynomial Λ C) (Z : MvPowerSeries σ C), ∃ K : ℝ, ∀ (M : ℝ) (a a' : σ → Λ → C), (∀ s l, IsIntV v (a s l)) → (∀ s l, IsIntV v (a' s l)) → (∀ s l, ((M : ℝ) : WithTop ℝ) ≤ v (a s l - a' s l)) → ((M - K : ℝ) : WithTop ℝ) ≤ v (derivAt0 P (MvPowerSeries.subst (fun s => ∑ l, a s l • (MvPowerSeries.X l : MvPowerSeries Λ C)) Z) - derivAt0 P (MvPowerSeries.subst (fun s => ∑ l, a' s l • (MvPowerSeries.X l : MvPowerSeries Λ C)) Z)) := by
  intro C _ v σ Λ _ _ P Z
  obtain ⟨Q, hQ⟩ := exists_poly_derivAt0_subst P Z
  obtain ⟨K, -, hK⟩ := exists_lipschitz_eval v Q
  refine ⟨K, fun M a a' ha ha' hM => ?_⟩
  rw [hQ, hQ]
  exact hK M _ _ (fun x => ha x.1 x.2) (fun x => ha' x.1 x.2) (fun x => hM x.1 x.2)

end GlobalTheory.FGDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivConstClosedPts
section
open IsLocalRing Polynomial

namespace GlobalTheory.VertUnits

def DivConst (T O : Type) [CommRing T] [CommRing O] [Algebra T O] : Prop :=
  ∀ (b c : O) (s : T), s ≠ 0 → b * c = algebraMap T O s →
    ∃ (a : T) (w : Oˣ), b = algebraMap T O a * (w : O)

def DivConstAll : Prop :=
  ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → DivConst T O

def DivConstWith (S : ∀ (T : Type) [CommRing T] [IsLocalRing T], Ideal (Polynomial T) → Prop) :
    Prop :=
  ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ →
    P.comap (Polynomial.C : T →+* Polynomial T) = maximalIdeal T → S T P → DivConst T O

def DivConstLocal : Prop := DivConstWith (fun _ _ _ _ => True)

def DivConstGeneric : Prop :=
  DivConstWith (fun T _ _ P => P = (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T))

def DivConstClosedPts : Prop :=
  DivConstWith (fun T _ _ P => P ≠ (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T))

def DivConstOrigin : Prop :=
  DivConstWith (fun T _ _ P =>
    P = (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T) ⊔ Ideal.span {Polynomial.X})

theorem divConstLocal_of (h₁ : DivConstClosedPts) (h₂ : DivConstGeneric) : DivConstLocal := by
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP _
  by_cases hg : P = (maximalIdeal T).map (Polynomial.C : T →+* Polynomial T)
  · exact h₂ T O hT P φ hφ hsh hP hg
  · exact h₁ T O hT P φ hφ hsh hP hg

end GlobalTheory.VertUnits
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedFrobLogForm
section
set_option autoImplicit false

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem divided_frob_logForm : ∀ {K Kt : Type} [Field K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p] (π : Kt →+* K) {ι : Type} (F : ι → Kt →+* Kt) (f : ι → Ω[K⁄ℤ] →+ Ω[K⁄ℤ]) (h : ι → ι → Ω[K⁄ℤ] →+ K) (s : Finset ι) (A : Subring K) (g : K), (∀ i, IsF p π (F i) (f i)) → (∀ i j, IsH p π (F i) (F j) (h i j)) → LogLift p π F s (A : Set K) g → (∀ i ∈ s, ∃ w ∈ A, g ≠ 0 → f i (g⁻¹ • KaehlerDifferential.D ℤ K g) = g⁻¹ • KaehlerDifferential.D ℤ K g + KaehlerDifferential.D ℤ K w) ∧ ∀ i ∈ s, ∀ j ∈ s, h i j (g⁻¹ • KaehlerDifferential.D ℤ K g) ∈ A := by
  intro K Kt _ _ p hp _ π ι F f h s A g hF hH hL
  obtain ⟨z, hz, hw⟩ := hL
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hDp : KaehlerDifferential.D ℤ K (g ^ p) = 0 := by
    rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]
  have e2 : ∀ hg : g ≠ 0, g⁻¹ ^ p * g ^ p = 1 := fun hg => by
    rw [← mul_pow, inv_mul_cancel₀ hg, one_pow]
  refine ⟨fun i hi => ?_, fun i hi j hj => ?_⟩
  · obtain ⟨w, hwA, hFw⟩ := hw i hi
    refine ⟨π w, hwA, fun hg => ?_⟩
    have key := (hF i).2 z (z ^ p * w) (by rw [hFw]; ring)
    rw [map_mul, map_pow, hz] at key
    have e1 : g⁻¹ ^ p * g ^ (p - 1) = g⁻¹ := by
      obtain ⟨n, hn⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
      rw [hn, Nat.add_sub_cancel, pow_succ, mul_comm (g⁻¹ ^ n), mul_assoc, ← mul_pow, inv_mul_cancel₀ hg,
        one_pow, mul_one]
    rw [(hF i).1, key, Derivation.leibniz, hDp, smul_zero, add_zero, smul_add, smul_smul, smul_smul, e1,
      e2 hg, one_smul]
  · obtain ⟨wi, hwiA, hFi⟩ := hw i hi
    obtain ⟨wj, hwjA, hFj⟩ := hw j hj
    have key := (hH i j).2 z (z ^ p * (wj - wi)) (by rw [hFj, hFi]; ring)
    rw [map_mul, map_pow, map_sub, hz] at key
    rw [(hH i j).1, key]
    by_cases hg : g = 0
    · subst hg
      simp [hp0]
    · rw [← mul_assoc, e2 hg, one_mul]
      exact A.sub_mem hwjA hwiA

end GlobalTheory.DI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenSublatticeFreeLatticeIffEval
section
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge

namespace GlobalTheory.EigenSubEval

variable {C : Type} [Field C] {w : Valuation C ℝ≥0} {v : AddValuation C (WithTop ℝ)}
  {S : Type} [Fintype S] [DecidableEq S]

theorem evalVec_rsmul (b : S → Int0 v) (N : ℕ) (r : RS b) (z : Fin N → RS b) (s : S) (i : Fin N) :
    evalVec b N (r • z) s i = ((ev b s r : Int0 v) : C) * evalVec b N z s i := by
  simp only [evalVec, Pi.smul_apply, smul_eq_mul, map_mul, Subring.coe_mul]

theorem mem_eigSub_iff (b : S → Int0 v) (N : ℕ) (τ : S) (z : Fin N → RS b) :
    z ∈ eigSub b τ (Fin N → RS b) ↔ lin b τ • z = 0 := Iff.rfl

theorem eigenSub_iff_eval (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ))
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S]
    (a : S → w.valuationSubring) (N : ℕ) (τ : S) (ha : Function.Injective a)
    (hinj : Function.Injective (evalVec (liftA hv a) N))
    (hrange : ∀ y, y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N ↔ ∃ x, evalVec (liftA hv a) N x = y)
    (y : Fin N → C) :
    y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin N → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N) τ ↔
      ∃ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.eigSub (liftA hv a) τ (Fin N → RS (liftA hv a)),
        (fun i => ((GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity.comp (liftA hv a) N τ z i : Int0 v) : C)) = y := by
  have hev : ∀ s t, ((ev (liftA hv a) s (lin (liftA hv a) t) : Int0 v) : C) = (a s : C) - a t := by
    intro s t
    rw [ev_lin]; rfl
  have hne : ∀ s, s ≠ τ → (a s : C) - a τ ≠ 0 := by
    intro s hs h
    exact hs (ha (Subtype.ext (sub_eq_zero.1 h)))
  have hmem : y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin N → C)
      (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N) τ ↔
      (Pi.single τ y : S → Fin N → C) ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N := Iff.rfl
  rw [hmem]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := (hrange _).1 h
    refine ⟨x, ?_, ?_⟩
    · rw [mem_eigSub_iff]
      apply hinj
      funext s i
      rw [evalVec_rsmul, hev, hx]
      have h0 : evalVec (liftA hv a) N (0 : Fin N → RS (liftA hv a)) s i = 0 := by
        simp [evalVec]
      rw [h0]
      by_cases e : s = τ
      · subst e; simp
      · simp [e]
    · rw [comp_coe, hx]; simp
  · rintro ⟨z, hz, rfl⟩
    rw [mem_eigSub_iff] at hz
    have key : evalVec (liftA hv a) N z = Pi.single τ (evalVec (liftA hv a) N z τ) := by
      funext s i
      by_cases e : s = τ
      · subst e; simp
      · have h1 := congrFun (congrFun (congrArg (evalVec (liftA hv a) N) hz) s) i
        rw [evalVec_rsmul, hev] at h1
        have h0 : evalVec (liftA hv a) N (0 : Fin N → RS (liftA hv a)) s i = 0 := by
          simp [evalVec]
        rw [h0] at h1
        rw [Pi.single_eq_of_ne e]
        exact (mul_eq_zero.1 h1).resolve_left (hne s e)
    rw [comp_coe, ← key]
    exact (hrange _).2 ⟨z, rfl⟩

end GlobalTheory.EigenSubEval
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsActionFactorThroughTensorCharacterStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_action_factor_through_tensor_character : ∀ (k : Type) [Field k] (C O B : Type) [CommRing C] [Ring O] [Algebra C O] [Algebra C k] [Ring B] [Algebra k B] (e : (k ⊗[C] O) ≃ₐ[k] B) (X : Type) [AddCommGroup X] [Module k X] (σX : O →+* Module.End k X), (∀ c, σX (algebraMap C O c) = algebraMap C k c • 1) → ∃ ρX : B →ₐ[k] Module.End k X, ∀ o, ρX (e (1 ⊗ₜ[C] o)) = σX o := by
  first | (exact @GlobalTheory.tensor_action_factors) | (exact GlobalTheory.tensor_action_factors) | (intros; apply GlobalTheory.tensor_action_factors  <;> assumption)
end

