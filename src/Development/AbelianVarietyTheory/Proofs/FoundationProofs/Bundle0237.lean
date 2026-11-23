module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleIntegralSeparatedComplete
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0218
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIdeleGenerator
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Nat

namespace GlobalTheory.IdealIdele

theorem pow_factorial_mul {M : Type} [Monoid M] [Fintype M] (a : M) (t : ℕ) (ht : 0 < t) :
    a ^ ((Fintype.card M)! * t) = a ^ (Fintype.card M)! := by
  obtain ⟨i, j, hij, hj, e⟩ : ∃ i j : ℕ, i < j ∧ j ≤ Fintype.card M ∧ a ^ i = a ^ j := by
    obtain ⟨i, j, hne, e⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun i : Fin (Fintype.card M + 1) => a ^ (i : ℕ)) (by simp)
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨i, j, h, Nat.lt_succ_iff.1 j.2, e⟩
    · exact ⟨j, i, h, Nat.lt_succ_iff.1 i.2, e.symm⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij.le
  have hd : 0 < d := by omega
  have key : ∀ u : ℕ, a ^ (i + d * u) = a ^ i := by
    intro u
    induction u with
    | zero => simp
    | succ u ih => rw [Nat.mul_succ, ← add_assoc, pow_add, ih, ← pow_add, ← e]
  obtain ⟨c, hc⟩ : d ∣ (Fintype.card M)! := Nat.dvd_factorial hd (by omega)
  obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le
    (show i ≤ (Fintype.card M)! from le_trans (by omega) (Nat.self_le_factorial _))
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  have : (Fintype.card M)! * t.succ = i + d * (c * t) + s := by
    rw [Nat.mul_succ, ← mul_assoc, ← hc]; omega
  rw [this, pow_add, key, ← pow_add, ← hs]

theorem int_dvd_pow_sub (m N t : ℕ) (hN : 0 < N) (ht : 0 < t) :
    ∃ c : ℤ, (m : ℤ) ^ (N ! * t) = (m : ℤ) ^ N ! + N * c := by
  haveI : NeZero N := ⟨hN.ne'⟩
  have h := pow_factorial_mul (m : ZMod N) t ht
  rw [ZMod.card] at h
  obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd ((m : ℤ) ^ (N ! * t) - (m : ℤ) ^ N !) N).1
    (by push_cast; rw [h, sub_self])
  exact ⟨c, by linear_combination hc⟩

section Abstract

variable {A : Type} [CommRing A] (S : Subring A)

theorem exists_idem
    (hsep : ∀ y : A, (∀ N : ℕ, 0 < N → ∃ w ∈ S, y = (N : A) * w) → y = 0)
    (hcpl : ∀ x : ℕ → A, (∀ N, x N ∈ S) →
      (∀ N m : ℕ, 0 < N → 0 < m → ∃ w ∈ S, x (N * m) = x N + (N : A) * w) →
      ∃ y ∈ S, ∀ N : ℕ, 0 < N → ∃ w ∈ S, y = x N + (N : A) * w)
    (m : ℕ) (hm : 0 < m) :
    ∃ f ∈ S, f * f = f ∧ (∃ w ∈ S, f = (m : A) * w) ∧
      ∀ n : ℕ, 0 < n → m.Coprime n → ∃ w ∈ S, 1 - f = (n : A) * w := by
  have hc : ∀ N t : ℕ, 0 < N → 0 < t →
      ∃ c : ℤ, (m : A) ^ (N ! * t) = (m : A) ^ N ! + N * c := fun N t hN ht => by
    obtain ⟨c, h⟩ := int_dvd_pow_sub m N t hN ht
    refine ⟨c, ?_⟩
    have := congrArg (Int.cast : ℤ → A) h
    push_cast at this
    exact this
  have hx : ∀ k : ℕ, (m : A) ^ k ∈ S := fun k => pow_mem (natCast_mem S m) k
  obtain ⟨f, hf, h⟩ := hcpl (fun N => (m : A) ^ N !) (fun N => hx _) (by
    intro N k hN hk
    obtain ⟨t, ht⟩ := Nat.factorial_dvd_factorial (Nat.le_mul_of_pos_right N hk)
    have ht0 : 0 < t := Nat.pos_of_ne_zero (by
      rintro rfl
      exact (Nat.factorial_ne_zero _) (by simpa using ht))
    obtain ⟨c, hc⟩ := hc N t hN ht0
    exact ⟨c, intCast_mem S c, by simp only [ht, hc]⟩)
  refine ⟨f, hf, ?_, ?_, fun n hn hmn => ?_⟩
  · rw [← sub_eq_zero]
    refine hsep _ fun N hN => ?_
    obtain ⟨w, hw, hh⟩ := h N hN
    obtain ⟨c, hc⟩ := hc N 2 hN two_pos
    refine ⟨c + (2 * (m : A) ^ N ! * w + N * w * w - w), ?_, ?_⟩
    · exact add_mem (intCast_mem S c) (sub_mem (add_mem (mul_mem (mul_mem (ofNat_mem _ 2) (hx _)) hw)
        (mul_mem (mul_mem (natCast_mem _ _) hw) hw)) hw)
    · rw [pow_mul] at hc
      rw [hh]; linear_combination hc
  · obtain ⟨w, hw, hh⟩ := h m hm
    obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.factorial_ne_zero m)
    refine ⟨(m : A) ^ s + w, add_mem (hx s) hw, ?_⟩
    rw [hh, hs, pow_succ]; ring
  · obtain ⟨w, hw, hh⟩ := h n hn
    obtain ⟨t, ht⟩ := Nat.dvd_factorial (Nat.totient_pos.2 hn) (Nat.totient_le n)
    have h1 : m ^ n ! ≡ 1 [MOD n] := by
      have := (Nat.ModEq.pow_totient hmn).pow t
      rwa [← pow_mul, ← ht, one_pow] at this
    obtain ⟨c, hc⟩ := h1.dvd
    have hc' := congrArg (Int.cast : ℤ → A) hc
    push_cast at hc'
    refine ⟨c - w, sub_mem (intCast_mem S c) hw, ?_⟩
    rw [hh]; linear_combination hc'

end Abstract

theorem exists_local_generator {E : Type} [Field E] [NumberField E] (B : Ideal (𝓞 E)) (hB : B ≠ ⊥) :
    ∃ (m n : ℕ) (β : 𝓞 E), 0 < m ∧ 0 < n ∧ m.Coprime n ∧ (m : 𝓞 E) ∈ B ∧ β ∈ B ∧ β ≠ 0 ∧
      ∀ b ∈ B, β ∣ (n : 𝓞 E) * b := by
  set m := 2 * Ideal.absNorm B with hm
  have hN : 0 < Ideal.absNorm B := Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using hB)
  have hm2 : 2 ≤ m := by omega
  have hmB : (m : 𝓞 E) ∈ B := by
    rw [hm, Nat.cast_mul]; exact Ideal.mul_mem_left _ _ (Ideal.absNorm_mem B)
  have hm0 : (m : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨β, hβ⟩ := IsDedekindDomain.exists_sup_span_eq (I := B * Ideal.span {(m : 𝓞 E)}) (J := B)
    Ideal.mul_le_left (mul_ne_zero hB (by simpa using hm0))
  have hβB : β ∈ B := hβ ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self β)
  obtain ⟨C, hC⟩ : B ∣ Ideal.span {β} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hβB)
  have hsup : Ideal.span {(m : 𝓞 E)} ⊔ C = ⊤ := by
    apply mul_left_cancel₀ hB
    rw [Ideal.mul_sup, ← hC, hβ, Ideal.mul_top]
  have hC0 : C ≠ ⊥ := by
    rintro rfl
    rw [sup_bot_eq, Ideal.span_singleton_eq_top] at hsup
    have h1 := Ideal.absNorm_eq_one_iff.2 (Ideal.span_singleton_eq_top.2 hsup)
    rw [Ideal.absNorm_span_natCast] at h1
    have h2 := (Nat.pow_eq_one.1 h1).resolve_left (by omega)
    exact Module.finrank_pos.ne' h2
  have hβ0 : β ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hB hC0 (by rw [← hC]; simp)
  haveI : Finite (𝓞 E ⧸ C) := Ideal.finiteQuotientOfFreeOfNeBot C hC0
  have hu : IsUnit (Ideal.Quotient.mk C (m : 𝓞 E)) := by
    obtain ⟨x, hx, c, hc, e⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hsup)
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk C a) ?_
    rw [← map_mul, ← map_one (Ideal.Quotient.mk C), Ideal.Quotient.eq]
    rw [show (m : 𝓞 E) * a - 1 = -c by linear_combination e]
    exact neg_mem hc
  obtain ⟨k, hk, e⟩ := isOfFinOrder_iff_pow_eq_one.1 (isOfFinOrder_of_finite hu.unit)
  have e' : (m : 𝓞 E) ^ k - 1 ∈ C := by
    rw [← Ideal.Quotient.eq, map_pow, map_one]
    simpa using congrArg Units.val e
  have h1 : 1 < m ^ k := Nat.one_lt_pow hk.ne' (by omega)
  refine ⟨m, m ^ k - 1, β, by omega, by omega, ?_, hmB, hβB, hβ0, fun b hb => ?_⟩
  · refine Nat.Coprime.of_dvd_left (dvd_pow_self m hk.ne') ?_
    exact (Nat.coprime_self_sub_right h1.le).2 (Nat.coprime_one_right _)
  · rw [← Ideal.mem_span_singleton, hC, mul_comm (((m ^ k - 1 : ℕ)) : 𝓞 E)]
    refine Ideal.mul_mem_mul hb ?_
    rw [Nat.cast_sub h1.le]
    push_cast
    exact e'

theorem exists_idele_generator : ∀ (D : D7) (B : Ideal (𝓞 D.host.E)), B ≠ ⊥ → ∃ y : (AE D)ˣ, (∀ b ∈ B, ((y⁻¹ : (AE D)ˣ) : AE D) * inc D (b : D.host.E) ∈ OhE D) ∧ ∃ (k : ℕ) (b : Fin k → 𝓞 D.host.E) (w : Fin k → AE D), (∀ i, b i ∈ B) ∧ (∀ i, w i ∈ OhE D) ∧ (y : AE D) = ∑ i, inc D (b i : D.host.E) * w i := by
  intro D B hB
  obtain ⟨m, n, β, hm, hn, hmn, hmB, hβB, hβ0, hdvd⟩ := exists_local_generator B hB
  obtain ⟨hsep, hcpl⟩ := GlobalTheory.IntAdeleComplete.integral_separated_complete D
  obtain ⟨f, hf, hff, ⟨w, hw, hfw⟩, h3⟩ := exists_idem (OhE D) hsep hcpl m hm
  obtain ⟨v, hv, hfv⟩ := h3 n hn hmn
  have hint : ∀ b : 𝓞 D.host.E, inc D (b : D.host.E) ∈ OhE D := fun b =>
    (GlobalTheory.HeckeVal.inc_mem_iff D _).2 b.isIntegral_coe
  have hβE : (β : D.host.E) ≠ 0 := by simpa using hβ0
  have hinv : inc D (β : D.host.E) * inc D (β : D.host.E)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hβE, map_one]
  have hy : ((1 - f) * inc D (β : D.host.E) + f) * ((1 - f) * inc D (β : D.host.E)⁻¹ + f) = 1 := by
    linear_combination (1 - f) ^ 2 * hinv +
      (2 - inc D (β : D.host.E) - inc D (β : D.host.E)⁻¹) * hff
  refine ⟨⟨_, _, hy, by rw [mul_comm, hy]⟩, fun b hb => ?_, 2, ![β, m], ![1 - f, w], ?_, ?_, ?_⟩
  · obtain ⟨d, hd⟩ := hdvd b hb
    have hd' : (n : AE D) * inc D (b : D.host.E) = inc D (β : D.host.E) * inc D (d : D.host.E) := by
      rw [← map_natCast (inc D), ← map_mul, ← map_mul]
      congr 1
      exact_mod_cast congrArg (fun x : 𝓞 D.host.E => (x : D.host.E)) hd
    change ((1 - f) * inc D (β : D.host.E)⁻¹ + f) * inc D (b : D.host.E) ∈ OhE D
    rw [show ((1 - f) * inc D (β : D.host.E)⁻¹ + f) * inc D (b : D.host.E) =
      v * inc D (d : D.host.E) + f * inc D (b : D.host.E) by
        rw [hfv]
        linear_combination v * inc D (β : D.host.E)⁻¹ * hd' + v * inc D (d : D.host.E) * hinv]
    exact add_mem (mul_mem hv (hint d)) (mul_mem hf (hint b))
  · intro i
    fin_cases i
    · exact hβB
    · exact hmB
  · intro i
    fin_cases i
    · exact sub_mem (one_mem _) hf
    · exact hw
  · have : inc D (((m : 𝓞 D.host.E)) : D.host.E) = (m : AE D) := by
      rw [← map_natCast (inc D)]; congr 1
    change (1 - f) * inc D (β : D.host.E) + f = _
    rw [Fin.sum_univ_two]
    change _ = inc D (β : D.host.E) * (1 - f) + inc D (((m : 𝓞 D.host.E)) : D.host.E) * w
    rw [this, ← hfw]; ring

end GlobalTheory.IdealIdele
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNonzeroThetaOfFiniteLevelAverage
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.GalTheta.Avg

theorem sum_out_translate {A M : Type*} [AddCommGroup A] [AddCommMonoid M] (S : AddSubgroup A) [Fintype (A ⧸ S)]
    (f : A → M) (hf : ∀ a, ∀ s ∈ S, f (a + s) = f a) (x : A) :
    ∑ q : A ⧸ S, f (x + q.out) = ∑ q : A ⧸ S, f q.out := by
  rw [← Equiv.sum_comp (Equiv.addLeft (x : A ⧸ S)) (fun q : A ⧸ S => f q.out)]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h : ((x + q.out : A) : A ⧸ S) = (((x : A ⧸ S) + q).out : A) := by simp
  rw [QuotientAddGroup.eq] at h
  have := hf (x + q.out) _ h
  simp only [Equiv.coe_addLeft]
  rw [← this]
  congr 1
  abel

variable (D : D7) (T : Tor D) {N N' : ℕ}

def W (x : VC D N N') (G : VC D N N' → ℂ) : VC D N N' → ℂ := fun z => al D T x * U D T x G z

theorem Wm_mul_Wm_comm {x y : VC D N N'}
    (h : al D T (x + y) = al D T x * al D T y *
      Complex.exp (-(Real.pi : ℂ) * Complex.I * ((Hf D T x y).im : ℂ))) (G : VC D N N' → ℂ) :
    W D T x (W D T y G) = W D T (x + y) G := by
  funext z
  have := U_mul D T x (al D T y) (U D T y G) z
  unfold W
  rw [this, U_U, h]
  ring

theorem U_comm (x y : VC D N N') (G : VC D N N' → ℂ) (z : VC D N N') :
    U D T x (U D T y G) z =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((Hf D T x y).im : ℂ)) * U D T y (U D T x G) z := by
  rw [U_U, U_U, add_comm y x, Hf_im_swap D T x y, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem eq_zero_of_U {x : VC D N N'} {G : VC D N N' → ℂ} (h : ∀ z, U D T x G z = 0) (z : VC D N N') :
    G z = 0 := by
  have := h (z - x)
  simpa [U] using this

theorem al_two_mul {x : VC D N N'} (hx : ∃ m : ℤ, qH D T x = m) (n : ℕ) : al D T ((2 * n) • x) = 1 := by
  obtain ⟨m, hm⟩ := hx
  unfold qH at hm
  have : √↑D.host.d / 2 * (Hf D T ((2 * n) • x) ((2 * n) • x)).re = ((2 * (2 * n * n * m) : ℤ) : ℝ) := by
    rw [Hf_nsmul_left, Hf_nsmul_right, ← mul_assoc, ← Nat.cast_mul, ← Complex.ofReal_natCast,
      Complex.re_ofReal_mul, mul_left_comm, hm]
    push_cast
    ring
  unfold al
  rw [this, round_intCast, zpow_mul]
  norm_num

theorem im_smul_right (c : ℝ) (x y : VC D N N') : (Hf D T x ((c : ℂ) • y)).im = c * (Hf D T x y).im := by
  rw [Hf_smul_right, Complex.conj_ofReal, Complex.im_ofReal_mul]

theorem im_smul_left (c : ℝ) (x y : VC D N N') : (Hf D T ((c : ℂ) • x) y).im = c * (Hf D T x y).im := by
  rw [Hf_smul_left, Complex.im_ofReal_mul]

theorem im_nsmul_right (c : ℕ) (x y : VC D N N') : (Hf D T x (c • y)).im = c * (Hf D T x y).im := by
  rw [← im_smul_right, Complex.ofReal_natCast, Nat.cast_smul_eq_nsmul]

theorem im_nsmul_left (c : ℕ) (x y : VC D N N') : (Hf D T (c • x) y).im = c * (Hf D T x y).im := by
  rw [← im_smul_left, Complex.ofReal_natCast, Nat.cast_smul_eq_nsmul]

theorem exp_int (t : ℝ) (m : ℤ) (h : t = m) : Complex.exp (-(2 * Real.pi * Complex.I) * (t : ℂ)) = 1 := by
  rw [Complex.exp_eq_one_iff]
  exact ⟨-m, by rw [h]; push_cast; ring⟩

theorem int_of_exp (t : ℝ) (h : Complex.exp (-(2 * Real.pi * Complex.I) * (t : ℂ)) = 1) : ∃ m : ℤ, t = m := by
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨m, hm⟩ := h
  refine ⟨-m, ?_⟩
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have : (t : ℂ) = ((-m : ℤ) : ℝ) := by
    apply mul_left_cancel₀ h2
    push_cast
    linear_combination -hm
  exact_mod_cast this

end GlobalTheory.GalTheta.Avg

namespace GlobalTheory.GalTheta

open Avg

theorem exists_theta_of_level : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N')), A.FG → (∀ x ∈ A, ∀ y ∈ A, ∃ m : ℤ, (Hf D T x y).im = m) → (∀ x, (∀ y ∈ A, ∃ m : ℤ, (Hf D T x y).im = m) → x ∈ A) → (∀ x ∈ A, ∃ m : ℤ, qH D T x = m) → (∀ x ∈ A, ∀ y ∈ A, al D T (x + y) = al D T x * al D T y * Complex.exp (-(Real.pi : ℂ) * Complex.I * ((Hf D T x y).im : ℂ))) → ∀ F : VC D N N' → ℂ, Differentiable ℂ F → F ≠ 0 → ∀ n : ℕ, 0 < n → (∀ x ∈ A, U D T (n • x) F = F) → ∃ P, IsTr D T A F P ∧ P ∈ ThSp D T A ∧ P ≠ 0 := by
  intro D T N N' A hfg hint hdual hq hal F hF hF0 n hn hlev
  have hn2 : 0 < 2 * n := by omega
  haveI : AddGroup.FG A := (AddGroup.fg_iff_addSubgroup_fg A).2 hfg
  set S : AddSubgroup A := (nsmulAddMonoidHom (α := A) (2 * n)).range with hS
  haveI : S.FiniteIndex := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg A hn2.ne'
  letI : Fintype (A ⧸ S) := Fintype.ofFinite _
  set c : ℝ := ((2 * n : ℕ) : ℝ)⁻¹ with hc
  have hcn : ((2 * n : ℕ) : ℝ) * c = 1 := mul_inv_cancel₀ (by exact_mod_cast hn2.ne')
  have hcs : ∀ y : VC D N N', (2 * n) • ((c : ℂ) • y) = y := by
    intro y
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, hcn]
    simp
  have hUF : ∀ x ∈ A, U D T ((2 * n) • x) F = F := by
    intro x hx
    rw [mul_comm, mul_smul]
    exact hlev _ (A.nsmul_mem hx 2)

  have hfix : ∀ y ∈ A, ∀ x ∈ A, W D T ((2 * n) • x) (U D T ((c : ℂ) • y) F) = U D T ((c : ℂ) • y) F := by
    intro y hy x hx
    funext z
    obtain ⟨m, hm⟩ := hint x hx y hy
    unfold W
    rw [al_two_mul D T (hq x hx), one_mul, U_comm, hUF x hx, exp_int _ m, one_mul]
    rw [im_nsmul_left, im_smul_right, ← mul_assoc, hcn, one_mul, hm]
  have hcls : ∀ y ∈ A, ∀ a : A, ∀ s ∈ S,
      W D T ((a + s : A) : VC D N N') (U D T ((c : ℂ) • y) F) = W D T a (U D T ((c : ℂ) • y) F) := by
    rintro y hy a s ⟨b, rfl⟩
    have e : ((a + nsmulAddMonoidHom (2 * n) b : A) : VC D N N') = (a : VC D N N') + (2 * n) • (b : VC D N N') := by
      simp
    rw [e, ← Wm_mul_Wm_comm D T (hal _ a.2 _ (A.nsmul_mem b.2 _)), hfix y hy b b.2]

  set P : VC D N N' → VC D N N' → ℂ :=
    fun y z => ∑ q : A ⧸ S, W D T (q.out : A) (U D T ((c : ℂ) • y) F) z with hP
  have hTr : ∀ y ∈ A, IsTr D T A F (P y) := by
    intro y hy
    refine IsTr.trans D T (IsTr.single D T F 1 ((c : ℂ) • y) (2 * n) hn2 (by rw [hcs]; exact hy)) ?_
    let e := Fintype.equivFin (A ⧸ S)
    refine ⟨_, fun i => al D T (((e.symm i).out : A) : VC D N N'), fun i => (((e.symm i).out : A) : VC D N N'), 1, one_pos,
      fun i => by simp, ?_⟩
    funext z
    simp only [hP, comb, one_mul, W]
    exact (Equiv.sum_comp e.symm _).symm
  have hTh : ∀ y ∈ A, P y ∈ ThSp D T A := by
    intro y hy
    refine ⟨?_, fun x hx z => ?_⟩
    · exact Differentiable.fun_sum fun q _ =>
        (differentiable_U D T _ (differentiable_U D T ((c : ℂ) • y) hF)).const_mul _
    · have h1 := sum_out_translate S (fun a : A => W D T (a : VC D N N') (U D T ((c : ℂ) • y) F) z)
        (fun a s hs => by simp only [hcls y hy a s hs]) ⟨x, hx⟩
      simp only [hP]
      rw [← h1, U_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      exact congrFun (Wm_mul_Wm_comm D T (hal x hx _ (q.out).2) _) z
  by_contra hcon
  push Not at hcon
  have hP0 : ∀ y ∈ A, P y = 0 := fun y hy => hcon _ (hTr y hy) (hTh y hy)

  set χ : A → A → ℂ := fun a y =>
    Complex.exp (-(2 * Real.pi * Complex.I) * ((c * (Hf D T (a : VC D N N') y).im : ℝ) : ℂ)) with hχ
  have hsum : ∀ y : A, ∀ z, ∑ q : A ⧸ S, χ q.out y * W D T (q.out : A) F z = 0 := by
    intro y
    apply eq_zero_of_U D T (x := (c : ℂ) • (y : VC D N N'))
    intro z
    have h0 := congrFun (hP0 y y.2) z
    simp only [hP, Pi.zero_apply] at h0
    rw [U_sum, ← h0]
    refine Finset.sum_congr rfl fun q _ => ?_
    have h2 := U_mul D T ((c : ℂ) • (y : VC D N N')) (al D T ((q.out : A) : VC D N N')) (U D T (q.out : A) F) z
    rw [U_mul]
    unfold W
    rw [h2, U_comm D T ((q.out : A) : VC D N N'), im_smul_right]
    simp only [hχ]
    ring
  have hadd : ∀ a x y : A, χ a (x + y) = χ a x * χ a y := by
    intro a x y
    simp only [hχ]
    rw [← Complex.exp_add, AddSubgroup.coe_add, Hf_add_right, Complex.add_im]
    congr 1
    push_cast
    ring
  have hS1 : ∀ a : A, ∀ s ∈ S, χ a s = 1 := by
    rintro a s ⟨b, rfl⟩
    obtain ⟨m, hm⟩ := hint a a.2 b b.2
    have e : ((nsmulAddMonoidHom (2 * n) b : A) : VC D N N') = (2 * n) • (b : VC D N N') := by simp
    refine exp_int _ m ?_
    rw [e, im_nsmul_right, ← mul_assoc, mul_comm c, hcn, one_mul, hm]
  have hS2 : ∀ s ∈ S, ∀ a : A, χ s a = 1 := by
    rintro s ⟨b, rfl⟩ a
    obtain ⟨m, hm⟩ := hint b b.2 a a.2
    have e : ((nsmulAddMonoidHom (2 * n) b : A) : VC D N N') = (2 * n) • (b : VC D N N') := by simp
    refine exp_int _ m ?_
    rw [e, im_nsmul_left, ← mul_assoc, mul_comm c, hcn, one_mul, hm]
  have hvan : ∀ q : A ⧸ S, q ≠ 0 → ∑ r : A ⧸ S, χ q.out r.out = 0 := by
    intro q hq0
    by_contra hne
    apply hq0
    have hall : ∀ y : A, χ q.out y = 1 := by
      intro y
      have h1 := sum_out_translate S (χ q.out) (fun a s hs => by rw [hadd, hS1 _ s hs, mul_one]) y
      simp only [hadd, ← Finset.mul_sum] at h1
      exact mul_right_cancel₀ hne (by rw [h1, one_mul])
    have hmem : (c : ℂ) • ((q.out : A) : VC D N N') ∈ A := by
      refine hdual _ fun y hy => ?_
      rw [im_smul_left]
      exact int_of_exp _ (hall ⟨y, hy⟩)
    rw [← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq_zero_iff]
    exact ⟨⟨_, hmem⟩, Subtype.ext (by simpa using hcs _)⟩
  have h0S : (0 : A ⧸ S).out ∈ S := by
    rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.out_eq']
  have hW0 : W D T ((0 : A ⧸ S).out : A) F = F := by
    obtain ⟨b, hb⟩ := h0S
    have := hfix 0 A.zero_mem b b.2
    rw [smul_zero, U_zero] at this
    rw [← hb]
    simpa using this
  apply hF0
  funext z
  have h3 : ∑ r : A ⧸ S, ∑ q : A ⧸ S, χ q.out r.out * W D T (q.out : A) F z = 0 :=
    Finset.sum_eq_zero fun r _ => hsum _ z
  rw [Finset.sum_comm, Finset.sum_eq_single 0 (fun q _ hq0 => by rw [← Finset.sum_mul, hvan q hq0, zero_mul])
    (by simp)] at h3
  simp only [hS2 _ h0S, hW0, one_mul, Finset.sum_const, nsmul_eq_mul, mul_eq_zero, Nat.cast_eq_zero,
    Finset.card_univ, Fintype.card_ne_zero, false_or] at h3
  exact h3

end GlobalTheory.GalTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSmulMemOfLeLocP
section
open GlobalTheory.DualWeyl MvPolynomial NumberField IsDedekindDomain
open Formalism.L2.DIV (colLat IsBasisAt dualFr)
open Formalism.HermitianLatticesTheory (localization₂)
open scoped Matrix

namespace GlobalTheory.DualWeylDual

variable {K : Type} [Field K] {N : ℕ}

theorem exists_smul_mem_of_le_locP (w : HeightOneSpectrum (𝓞 K)) {M M' : Submodule (𝓞 K) (Fin N → K)}
    (hM : M.FG) (h : M ≤ localization₂ w.asIdeal M') : ∃ t ∈ w.asIdeal.primeCompl, ∀ x ∈ M, t • x ∈ M' := by
  classical
  obtain ⟨s, rfl⟩ := hM
  have h1 : ∀ y : s, ∃ a ∈ w.asIdeal.primeCompl, a • (y : Fin N → K) ∈ M' := fun y =>
    h (Submodule.subset_span y.2)
  choose a ha0 ha using h1
  refine ⟨∏ y, a y, Submonoid.prod_mem _ fun y _ => ha0 y, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem y hy =>
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨y, hy⟩ : s)), mul_smul]
    exact M'.smul_mem _ (ha ⟨y, hy⟩)
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact M'.add_mem hy hz
  | smul c y _ hy => rw [smul_comm]; exact M'.smul_mem _ hy

theorem localization_dualFr_le (w : HeightOneSpectrum (𝓞 K)) {M M' : Submodule (𝓞 K) (Fin N → K)}
    (hM : M.FG) (h : localization₂ w.asIdeal M ≤ localization₂ w.asIdeal M') :
    localization₂ w.asIdeal (dualFr M') ≤ localization₂ w.asIdeal (dualFr M) := by
  obtain ⟨t, ht, htM⟩ := exists_smul_mem_of_le_locP w hM
    (fun x hx => h ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩)
  rintro φ ⟨s, hs, hφ⟩
  refine ⟨t * s, Submonoid.mul_mem _ ht hs, fun x hx => ?_⟩
  have h1 : (s • φ) ⬝ᵥ (t • x) ∈ (1 : Submodule (𝓞 K) K) := hφ _ (htM x hx)
  rwa [dotProduct_smul, ← smul_dotProduct, smul_smul] at h1

theorem dualFr_colLat (B : GL (Fin N) K) : dualFr (colLat B) = colLat (Formalism.BasicNotions.inside₂ K N B) := by
  apply SetLike.ext
  intro φ
  rw [mem_colLat_iff]
  constructor
  · intro h
    have h1 : ∀ j, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = φ ⬝ᵥ fun a => (B : Matrix (Fin N) (Fin N) K) a j := fun j =>
      Submodule.mem_one.mp (h _ (Submodule.subset_span ⟨j, rfl⟩))
    choose c hc using h1
    refine ⟨c, ?_⟩
    have h2 : (fun j => (c j : K)) = (B : Matrix (Fin N) (Fin N) K)ᵀ *ᵥ φ := by
      funext j
      rw [Matrix.mulVec_transpose]
      exact hc j
    rw [h2, Matrix.mulVec_mulVec]
    change (((B⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)ᵀ * _) *ᵥ φ = φ
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mulVec]
  · rintro ⟨c, rfl⟩ x hx
    obtain ⟨d, rfl⟩ := (mem_colLat_iff _ _).mp hx
    change (((B⁻¹ : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)ᵀ *ᵥ _) ⬝ᵥ _ ∈ _
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    refine Submodule.mem_one.mpr ⟨c ⬝ᵥ d, ?_⟩
    simp [dotProduct]

theorem isBasisAt_dualFr (w : HeightOneSpectrum (𝓞 K)) {L : Submodule (𝓞 K) (Fin N → K)} (hL : L.FG)
    {B : GL (Fin N) K} (hB : IsBasisAt w L B) : IsBasisAt w (dualFr L) (Formalism.BasicNotions.inside₂ K N B) := by
  unfold IsBasisAt at hB ⊢
  rw [← dualFr_colLat]
  exact le_antisymm (localization_dualFr_le w (Submodule.fg_span (Set.finite_range _)) hB.ge) (localization_dualFr_le w hL hB.le)

end GlobalTheory.DualWeylDual
end

