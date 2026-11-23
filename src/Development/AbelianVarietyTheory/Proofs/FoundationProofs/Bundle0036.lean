module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormAddOfLt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MovesIntegersAlmostUnitDistanceFixedSubfield
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

open Polynomial

theorem moves_fix_of_moves : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G]
    [MulSemiringAction G L] [Finite G], (∀ (g : G) (x : L), v (g • x) = v x) →
    ∀ (N : Subgroup G) (i : ℝ≥0), i < 1 → (∀ τ ∈ N, ∀ x : L, v x ≤ 1 → v (τ • x - x) ≤ i) →
    ∀ σ : G, Moves v ⊤ σ → Moves v (Fix L N) σ := by
  intro L _ v G _ _ _ hinv N i hi hN σ hσ r hr
  classical
  by_contra hcon
  push_neg at hcon
  haveI := Fintype.ofFinite G
  set n := Fintype.card N with hn_def
  have hn : n ≠ 0 := Fintype.card_ne_zero
  set t : ℝ≥0 := max i (r ^ ((n : ℝ)⁻¹)) with ht_def
  have ht1 : t < 1 := max_lt hi (NNReal.rpow_lt_one hr (by positivity))
  have hrt : r ≤ t ^ n := by
    calc r = (r ^ ((n : ℝ)⁻¹)) ^ n := (NNReal.rpow_inv_natCast_pow r hn).symm
      _ ≤ t ^ n := pow_le_pow_left₀ zero_le (le_max_right _ _) n
  obtain ⟨x, -, hx1, hxt⟩ := hσ t ht1

  have hfac : ∀ τ : N, v (x - σ • ((τ : G) • x)) = v (σ • x - x) := by
    intro τ
    have h1 : v (σ • x - σ • ((τ : G) • x)) < v (x - σ • x) := by
      rw [← smul_sub, hinv, Valuation.map_sub_swap, Valuation.map_sub_swap v x]
      exact lt_of_le_of_lt (le_trans (hN τ τ.2 x hx1) (le_max_left _ _)) hxt
    have h2 : x - σ • ((τ : G) • x) = (x - σ • x) + (σ • x - σ • ((τ : G) • x)) := by ring
    rw [h2, Valuation.map_add_eq_of_lt_left v h1, Valuation.map_sub_swap]

  set P : L[X] := ∏ τ : N, (X - C ((τ : G) • x)) with hP_def
  have hint : ∀ τ : N, (τ : G) • x ∈ v.integer := fun τ => by
    rw [Valuation.mem_integer_iff, hinv]; exact hx1
  set Q : (v.integer)[X] := ∏ τ : N, (X - C (⟨(τ : G) • x, hint τ⟩ : v.integer)) with hQ_def
  have hPQ : P = Q.map (v.integer.subtype) := by
    simp [hP_def, hQ_def, Polynomial.map_prod]
  have hcint : ∀ k, v (P.coeff k) ≤ 1 := by
    intro k
    rw [hPQ, coeff_map]
    exact (Q.coeff k).2
  have hcfix : ∀ k, P.coeff k ∈ Fix L N := by
    intro k m
    have hmap : P.map (MulSemiringAction.toRingHom G L (m : G)) = P := by
      rw [hP_def, Polynomial.map_prod]
      simp only [Polynomial.map_sub, map_X, map_C, MulSemiringAction.toRingHom_apply, smul_smul]
      exact Fintype.prod_equiv (Equiv.mulLeft m) _ _ (fun τ => by simp)
    have := congrArg (fun p => p.coeff k) hmap
    have h' : (m : G) • P.coeff k = P.coeff k := by simpa [coeff_map] using this
    exact h'
  have hPx : P.eval x = 0 := by
    rw [hP_def, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ 1) (by simp)
  have hPσx : (P.map (MulSemiringAction.toRingHom G L σ)).eval x = ∏ τ : N, (x - σ • ((τ : G) • x)) := by
    simp [hP_def, Polynomial.map_prod, eval_prod]

  have hdiff : v ((P.map (MulSemiringAction.toRingHom G L σ) - P).eval x) ≤ r := by
    rw [eval_eq_sum, Polynomial.sum_def]
    apply Valuation.map_sum_le
    intro k _
    rw [map_mul, map_pow, coeff_sub, coeff_map, MulSemiringAction.toRingHom_apply]
    calc v (σ • P.coeff k - P.coeff k) * v x ^ k ≤ r * 1 :=
          mul_le_mul' (hcon _ (hcfix k) (hcint k)) (pow_le_one₀ zero_le hx1)
      _ = r := mul_one r
  rw [eval_sub, hPx, sub_zero, hPσx, map_prod] at hdiff
  simp only [hfac, Finset.prod_const, Finset.card_univ] at hdiff
  have := pow_lt_pow_left₀ hxt zero_le hn
  exact absurd (lt_of_le_of_lt (hdiff.trans hrt) this) (lt_irrefl _)

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NatCastEqOneOfCoprime
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem valuation_nnreal_natCast_le_one {L : Type} [Field L] (v : Valuation L ℝ≥0) (n : ℕ) : v (n : L) ≤ 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    push_cast
    exact le_trans (v.map_add _ _) (max_le ih (by simp))

theorem valuation_nnreal_intCast_le_one {L : Type} [Field L] (v : Valuation L ℝ≥0) (z : ℤ) : v (z : L) ≤ 1 := by
  cases z with
  | ofNat n => simpa using valuation_nnreal_natCast_le_one v n
  | negSucc n =>
    rw [Int.cast_negSucc, Valuation.map_neg]
    exact_mod_cast valuation_nnreal_natCast_le_one v (n + 1)

theorem natCast_eq_one_of_coprime :
    ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p l : ℕ), v (p : L) < 1 → Nat.Coprime l p → v (l : L) = 1 := by
  intro L _ v p l hp hlp
  refine le_antisymm (valuation_nnreal_natCast_le_one v l) ?_
  by_contra hlt
  push_neg at hlt
  have hb : ((Nat.gcd l p : ℕ) : ℤ) = (l : ℤ) * Nat.gcdA l p + (p : ℤ) * Nat.gcdB l p := Nat.gcd_eq_gcd_ab l p
  rw [hlp, Nat.cast_one] at hb
  have hL : (1 : L) = (l : L) * (Nat.gcdA l p : L) + (p : L) * (Nat.gcdB l p : L) := by
    have := congrArg (fun z : ℤ => (z : L)) hb
    push_cast at this
    exact this
  have h1 : v (1 : L) < 1 := by
    rw [hL]
    refine lt_of_le_of_lt (v.map_add _ _) (max_lt ?_ ?_)
    · rw [v.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (valuation_nnreal_intCast_le_one v (Nat.gcdA l p))) hlt
    · rw [v.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (valuation_nnreal_intCast_le_one v (Nat.gcdB l p))) hp
  simp at h1

end GlobalTheory.AlmostEt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormXLeOneOfNsmulEqZero
section
namespace GlobalTheory.TorsionIntegral

open IsUltrametricDist WeierstrassCurve

variable {K : Type} [NormedField K] [IsUltrametricDist K]

lemma norm_sub_le_max' (a b : K) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  have := norm_add_le_max a (-b)
  rwa [norm_neg, ← sub_eq_add_neg] at this

lemma norm_add_eq_of_lt {a b : K} (h : ‖b‖ < ‖a‖) : ‖a + b‖ = ‖a‖ := by
  rw [norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

lemma norm_y_sq {A B x y : K} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hx : 1 < ‖x‖)
    (h : y ^ 2 = x ^ 3 + A * x + B) : ‖y‖ ^ 2 = ‖x‖ ^ 3 := by
  have h1 : ‖x‖ < ‖x‖ ^ 3 := by
    have := pow_lt_pow_right₀ hx (show 1 < 3 by norm_num)
    simpa using this
  rw [← norm_pow, h, add_assoc, norm_add_eq_of_lt, norm_pow]
  rw [norm_pow]
  refine (norm_add_le_max _ _).trans_lt (max_lt ?_ (by linarith))
  rw [norm_mul]
  nlinarith [norm_nonneg A]

lemma norm_sum_three_le (a b c : K) : ‖a + b + c‖ ≤ max (max ‖a‖ ‖b‖) ‖c‖ :=
  (norm_add_le_max _ _).trans (max_le_max (norm_add_le_max _ _) le_rfl)

lemma norm_two_le : ‖(2 : K)‖ ≤ 1 := by
  simpa using IsUltrametricDist.norm_natCast_le_one K 2

lemma norm_three_le : ‖(3 : K)‖ ≤ 1 := by
  simpa using IsUltrametricDist.norm_natCast_le_one K 3

noncomputable def param {W : Affine K} : W.Point → K
  | .zero => 0
  | .some x y _ => x / y

def Near {W : Affine K} (M : ℝ) : W.Point → Prop
  | .zero => True
  | .some x _ _ => M ≤ ‖x‖

lemma add_step [DecidableEq K] {A B : K} {M : ℝ} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hM : 1 < M)
    (P Q : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Point) (hP : Near M P)
    (hQ : Near M Q) : Near M (P + Q) ∧ ‖param (P + Q) - param P - param Q‖ ≤ M⁻¹ := by
  first
  | exact @_root_.GlobalTheory.UltrametricLineBounds.large_add
  | exact _root_.GlobalTheory.UltrametricLineBounds.large_add
  | (apply _root_.GlobalTheory.UltrametricLineBounds.large_add <;> assumption)
  | (intros; apply _root_.GlobalTheory.UltrametricLineBounds.large_add <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UltrametricLineBounds.large_add <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UltrametricLineBounds.large_add ..)

theorem norm_x_le_one_of_nsmul_eq_zero (K : Type) [NormedField K] [IsUltrametricDist K]
    [DecidableEq K] (A B : K) (N : ℕ) (x y : K)
    (h : (⟨0, 0, 0, A, B⟩ : WeierstrassCurve K).toAffine.Nonsingular x y)
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hN : ‖(N : K)‖ = 1)
    (h0 : N • (WeierstrassCurve.Affine.Point.some x y h) = 0) : ‖x‖ ≤ 1 := by
  by_contra hx
  push Not at hx
  have M0 : 0 ≤ ‖x‖⁻¹ := by positivity
  have hP : Near ‖x‖ (Affine.Point.some x y h) := le_refl _
  have key : ∀ k : ℕ, Near ‖x‖ (k • Affine.Point.some x y h) ∧
      ‖param (k • Affine.Point.some x y h) - (k : K) * (x / y)‖ ≤ ‖x‖⁻¹ := by
    intro k
    induction k with
    | zero =>
      rw [zero_nsmul]
      exact ⟨trivial, by simp [Affine.Point.zero_def, param]⟩
    | succ k ih =>
      obtain ⟨s1, s2⟩ := add_step hA hB hx _ _ ih.1 hP
      rw [succ_nsmul]
      refine ⟨s1, ?_⟩
      have := (norm_add_le_max _ _).trans (max_le s2 ih.2)
      refine le_of_eq_of_le (congrArg norm ?_) this
      simp only [param]
      push_cast
      ring
  have h1 := (key N).2
  rw [h0] at h1
  simp only [Affine.Point.zero_def, param, zero_sub, norm_neg, norm_mul, hN, one_mul,
    norm_div] at h1
  have he : y ^ 2 = x ^ 3 + A * x + B := by
    have := (Affine.equation_iff _ _).1 h.1
    simp only at this
    linear_combination this
  have hy := norm_y_sq hA hB hx he
  have x0 : 0 < ‖x‖ := by linarith
  have y0 : 0 < ‖y‖ := by
    refine lt_of_le_of_ne (norm_nonneg _) fun h => ?_
    rw [← h] at hy
    have : 0 < ‖x‖ ^ 3 := by positivity
    simp at hy
    linarith
  rw [inv_eq_one_div, div_le_div_iff₀ y0 x0, one_mul] at h1
  have h2 : (‖x‖ * ‖x‖) ^ 2 ≤ ‖y‖ ^ 2 := by gcongr
  rw [hy] at h2
  have : ‖x‖ ^ 3 * 1 < ‖x‖ ^ 3 * ‖x‖ := by gcongr
  nlinarith

end GlobalTheory.TorsionIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PerfectPairingQuotients
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem exists_addChar_quotient {G : Type} [AddCommGroup G] (H : AddSubgroup G) (f : G → ℂ)
    (h0 : f 0 = 1) (hadd : ∀ x y, f (x + y) = f x * f y) (hH : ∀ x ∈ H, f x = 1) :
    ∃ χ : AddChar (G ⧸ H) ℂ, ∀ g : G, χ (g : G ⧸ H) = f g := by
  have hout : ∀ g : G, f (Quotient.out (g : G ⧸ H)) = f g := by
    intro g
    obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_mul H g
    rw [hh, hadd, hH _ h.2, mul_one]
  refine ⟨⟨fun q => f (Quotient.out q), ?_, ?_⟩, hout⟩
  · rw [← QuotientAddGroup.mk_zero, hout, h0]
  · intro a b
    induction a using QuotientAddGroup.induction_on
    induction b using QuotientAddGroup.induction_on
    rw [← QuotientAddGroup.mk_add, hout, hout, hout, hadd]

theorem exists_injective_addChar {G K : Type} [AddCommGroup G] [AddCommGroup K] (H : AddSubgroup G)
    (L : AddSubgroup K) (p : G → K → ℂ)
    (hl : ∀ x y z, p (x + y) z = p x z * p y z) (hr : ∀ x y z, p x (y + z) = p x y * p x z)
    (h0 : ∀ x, p x 0 = 1) (h0' : ∀ y, p 0 y = 1)
    (hH : ∀ g, g ∈ H ↔ ∀ k, p g k = 1) (hL : ∀ k ∈ L, ∀ g, p g k = 1) :
    ∃ Φ : G ⧸ H → AddChar (K ⧸ L) ℂ, Function.Injective Φ ∧
      ∀ (g : G) (k : K), Φ (g : G ⧸ H) (k : K ⧸ L) = p g k := by
  choose χ hχ using fun g : G =>
    exists_addChar_quotient L (p g) (h0 g) (hr g) (fun k hk => hL k hk g)
  have hout : ∀ (g : G) (k : K), p (Quotient.out (g : G ⧸ H)) k = p g k := by
    intro g k
    obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_mul H g
    rw [hh, hl, (hH _).1 h.2, mul_one]
  have hΦ : ∀ (g : G) (k : K), χ (Quotient.out (g : G ⧸ H)) (k : K ⧸ L) = p g k := by
    intro g k
    rw [hχ, hout]
  refine ⟨fun q => χ (Quotient.out q), ?_, hΦ⟩
  intro a b hab
  induction a using QuotientAddGroup.induction_on with | _ a
  induction b using QuotientAddGroup.induction_on with | _ b
  rw [QuotientAddGroup.eq, hH]
  intro k
  have h1 : p a k = p b k := by
    rw [← hΦ, ← hΦ]
    exact congrArg (fun ψ : AddChar (K ⧸ L) ℂ => ψ (k : K ⧸ L)) hab
  rw [hl, ← h1, ← hl, neg_add_cancel, h0']

theorem perfect_pairing_quotients : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (S A T₀ T : AddSubgroup X), (∀ a ∈ A, a ∈ S ↔ ∀ t ∈ T, γ a t = 1) → (∀ t ∈ T, t ∈ T₀ ↔ ∀ a ∈ A, γ a t = 1) → T₀.relIndex T ≠ 0 → S.relIndex A = T₀.relIndex T ∧ (∀ y : X, (∀ a ∈ A, a ∈ S → γ a y = 1) → ∃ t ∈ T, ∀ a ∈ A, γ a y = γ a t) ∧ ∀ t ∈ T, (∑ᶠ q : A ⧸ S.addSubgroupOf A, γ ((Quotient.out q : A) : X) t) = if t ∈ T₀ then (S.relIndex A : ℂ) else 0 := by
  intro R X M _ _ _ _ _ σ w γ W h S A T₀ T hS hT hfin
  have hS' : ∀ a : A, a ∈ S.addSubgroupOf A ↔ ∀ t : T, γ a t = 1 := by
    intro a
    rw [AddSubgroup.mem_addSubgroupOf, hS a a.2]
    simp
  have hT' : ∀ t : T, t ∈ T₀.addSubgroupOf T ↔ ∀ a : A, γ a t = 1 := by
    intro t
    rw [AddSubgroup.mem_addSubgroupOf, hT t t.2]
    simp
  obtain ⟨Φ, hΦi, hΦ⟩ := exists_injective_addChar (S.addSubgroupOf A) (T₀.addSubgroupOf T)
    (fun a t => γ a t) (fun x y z => h.add_left _ _ _) (fun x y z => h.add_right _ _ _)
    (fun x => h.zero_right _) (fun x => h.zero_left _) hS' (fun k hk => (hT' k).1 hk)
  obtain ⟨Ψ, hΨi, hΨ⟩ := exists_injective_addChar (T₀.addSubgroupOf T) (S.addSubgroupOf A)
    (fun t a => γ a t) (fun x y z => h.add_right _ _ _) (fun x y z => h.add_left _ _ _)
    (fun x => h.zero_left _) (fun x => h.zero_right _) hT' (fun k hk => (hS' k).1 hk)
  haveI : Finite (T ⧸ T₀.addSubgroupOf T) := Nat.finite_of_card_ne_zero hfin
  haveI : Finite (A ⧸ S.addSubgroupOf A) := Finite.of_injective Φ hΦi
  letI := Fintype.ofFinite (T ⧸ T₀.addSubgroupOf T)
  letI := Fintype.ofFinite (A ⧸ S.addSubgroupOf A)
  have c1 := Fintype.card_le_of_injective Φ hΦi
  have c2 := Fintype.card_le_of_injective Ψ hΨi
  have c3 := c2
  rw [AddChar.card_eq] at c1 c2
  have hc : Fintype.card (A ⧸ S.addSubgroupOf A) = Fintype.card (T ⧸ T₀.addSubgroupOf T) :=
    le_antisymm c1 c2
  have eA : S.relIndex A = Fintype.card (A ⧸ S.addSubgroupOf A) := Nat.card_eq_fintype_card
  have eT : T₀.relIndex T = Fintype.card (T ⧸ T₀.addSubgroupOf T) := Nat.card_eq_fintype_card
  refine ⟨by rw [eA, eT, hc], ?_, ?_⟩
  · intro y hy
    obtain ⟨χ, hχ⟩ := exists_addChar_quotient (S.addSubgroupOf A) (fun a : A => γ a y)
      (h.zero_left _) (fun a b => h.add_left _ _ _)
      (fun a ha => hy a a.2 (AddSubgroup.mem_addSubgroupOf.1 ha))
    have hb : Function.Bijective Ψ :=
      (Fintype.bijective_iff_injective_and_card Ψ).2 ⟨hΨi, by rw [AddChar.card_eq, hc]⟩
    obtain ⟨q, hq⟩ := hb.2 χ
    induction q using QuotientAddGroup.induction_on with | _ t
    refine ⟨t, t.2, fun a ha => ?_⟩
    have h1 := hΨ t ⟨a, ha⟩
    rw [hq, hχ] at h1
    exact h1
  · intro t ht
    rw [finsum_eq_sum_of_fintype]
    have h1 : ∀ q : A ⧸ S.addSubgroupOf A,
        γ ((Quotient.out q : A) : X) t = Ψ ((⟨t, ht⟩ : T) : T ⧸ T₀.addSubgroupOf T) q := by
      intro q
      conv_rhs => rw [← QuotientAddGroup.out_eq' q]
      rw [hΨ]
    rw [Finset.sum_congr rfl fun q _ => h1 q, AddChar.sum_eq_ite, eA]
    refine if_congr ?_ rfl rfl
    rw [hT t ht]
    constructor
    · intro h0 a ha
      have h2 := hΨ ⟨t, ht⟩ ⟨a, ha⟩
      rw [h0] at h2
      simpa using h2.symm
    · intro h0
      ext q
      rw [← h1, h0 _ (Quotient.out q).2]
      simp

end GlobalTheory.FinWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PieceUnitSetEqSmoothingMulPieceRaw
section
noncomputable section

open Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois.Smoothing

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
theorem zpow_congr_of_pow_eq_one {ζ : K} {M : ℕ} (hM : 0 < M) (hζ : ζ ^ M = 1) {a b : ℤ}
    (h : a ≡ b [ZMOD M]) : ζ ^ a = ζ ^ b := by
  have hz : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne'] at hζ
    exact zero_ne_one hζ
  obtain ⟨s, hs⟩ := h.dvd
  have hb : b = a + M * s := by linarith
  rw [hb, zpow_add₀ hz, zpow_mul, zpow_natCast, hζ, one_zpow, mul_one]

theorem eisF_congr_mod {j M : ℕ} (hM : 0 < M) {ζ : K} (hζ : ζ ^ M = 1) {a₁ a₂ b₁ b₂ : ℤ}
    (h₁ : a₁ ≡ b₁ [ZMOD M]) (h₂ : a₂ ≡ b₂ [ZMOD M]) :
    eisF j M ζ a₁ a₂ = eisF j M ζ b₁ b₂ := by
  funext n
  have h₁' : a₁ % (M : ℤ) = b₁ % (M : ℤ) := h₁
  have hc : const0 j M ζ a₁ a₂ = const0 j M ζ b₁ b₂ := by
    have hd : ((M : ℤ) ∣ a₁) ↔ ((M : ℤ) ∣ b₁) := by
      rw [Int.dvd_iff_emod_eq_zero, Int.dvd_iff_emod_eq_zero, h₁']
    have hf : frc M a₁ = frc M b₁ := by unfold frc; rw [h₁']
    unfold const0
    rw [zpow_congr_of_pow_eq_one hM hζ h₂, hf]
    simp only [hd]
  have hp : coefPos j M ζ a₁ a₂ n = coefPos j M ζ b₁ b₂ n := by
    unfold coefPos
    refine Finset.sum_congr rfl (fun d _ => ?_)
    have e1 : ∀ z : ℤ, z ≡ a₁ [ZMOD M] ↔ z ≡ b₁ [ZMOD M] :=
      fun z => ⟨fun h => h.trans h₁, fun h => h.trans h₁.symm⟩
    rw [zpow_congr_of_pow_eq_one hM hζ (h₂.mul_right (d : ℤ)),
      zpow_congr_of_pow_eq_one hM hζ (h₂.mul_right (d : ℤ)).neg]
    simp only [e1]
  unfold eisF
  rw [hc, hp]

omit [CharZero K] in
theorem cmul_expand (a b a' b' : K) (f g h l : ℕ → K) (r : ℕ) :
    cmul (fun i => a * f i - b * g i) (fun i => a' * h i - b' * l i) r =
      a * a' * cmul f h r - a * b' * cmul f l r - b * a' * cmul g h r + b * b' * cmul g l r := by
  unfold cmul
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem not_dvd_val_iff_isUnit {p n : ℕ} [hp : Fact p.Prime] (hn : 0 < n) (y : ZMod (p ^ n)) :
    ¬ p ∣ y.val ↔ IsUnit y := by
  have h := ZMod.isUnit_iff_coprime y.val (p ^ n)
  rw [ZMod.natCast_zmod_val] at h
  rw [h, Nat.coprime_pow_right_iff hn, Nat.coprime_comm, hp.out.coprime_iff_not_dvd]

theorem isUnit_intCast_of_not_dvd {p n : ℕ} [hp : Fact p.Prime] {c : ℤ}
    (hc : ¬ (p : ℤ) ∣ c) : IsUnit (c : ZMod (p ^ n)) := by
  have h1 : IsCoprime (p : ℤ) c :=
    (Nat.prime_iff_prime_int.mp hp.out).irreducible.coprime_iff_not_dvd.mpr hc
  obtain ⟨a, b, hab⟩ := (h1.pow_left (m := n))
  have h2 : ((a * (p : ℤ) ^ n + b * c : ℤ) : ZMod (p ^ n)) = 1 := by rw [hab]; simp
  have h3 : ((p : ZMod (p ^ n))) ^ n = 0 := by
    rw [← Nat.cast_pow]; exact ZMod.natCast_self _
  push_cast at h2
  rw [h3, mul_zero, zero_add, mul_comm] at h2
  exact IsUnit.of_mul_eq_one _ h2

def diagGL {R : Type*} [CommRing R] (u v : Rˣ) : GL (Fin 2) R :=
  ⟨Matrix.diagonal ![(u : R), v], Matrix.diagonal ![((u⁻¹ : Rˣ) : R), ((v⁻¹ : Rˣ) : R)],
   by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext i; fin_cases i <;> simp,
   by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext i; fin_cases i <;> simp⟩

theorem diagGL_mul_zero {R : Type*} [CommRing R] (u v : Rˣ) (γ : GL (Fin 2) R) (j : Fin 2) :
    ((diagGL u v * γ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 0 j =
      (u : R) * (γ : Matrix (Fin 2) (Fin 2) R) 0 j := by
  rw [Units.val_mul]
  exact Matrix.diagonal_mul _ _ _ _

theorem diagGL_mul_one {R : Type*} [CommRing R] (u v : Rˣ) (γ : GL (Fin 2) R) (j : Fin 2) :
    ((diagGL u v * γ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 j =
      (v : R) * (γ : Matrix (Fin 2) (Fin 2) R) 1 j := by
  rw [Units.val_mul]
  exact Matrix.diagonal_mul _ _ _ _

theorem diagGL_mul_det {R : Type*} [CommRing R] (u v : Rˣ) (γ : GL (Fin 2) R) :
    ((diagGL u v * γ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).det =
      (u : R) * v * (γ : Matrix (Fin 2) (Fin 2) R).det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [diagGL_mul_zero, diagGL_mul_one]
  ring

theorem diagGL_mul_mem {p n : ℕ} [Fact p.Prime] (hn : 0 < n) (u v : (ZMod (p ^ n))ˣ)
    (γ : GL (Fin 2) (ZMod (p ^ n))) : diagGL u v * γ ∈ unitSet p n ↔ γ ∈ unitSet p n := by
  simp only [unitSet, Finset.mem_filter, Finset.mem_univ, true_and, not_dvd_val_iff_isUnit hn,
    diagGL_mul_zero, diagGL_mul_one, Units.isUnit_units_mul]

end GlobalTheory.KummerEisensteinGalois.Smoothing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowSmulHeckeVOperatorExplicitEqSlashDiag
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem smul_vOp_eq_slash (q : ℕ) (k : ℤ) (f : ℍ → ℂ) (hq : 0 < q) : (q : ℂ) ^ (k - 1) • vOp q f = f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℚ), 0; 0, 1] (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq.ne'))) := by
  set g := (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℚ), 0; 0, 1] (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq.ne'))) with hg
  have h00 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = q := by simp [hg, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have h01 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := by simp [hg, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have h10 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by simp [hg, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have h11 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1 := by simp [hg, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have hdet : (g.det : ℝ) = q := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h00, h01, h10, h11]; ring
  have hdpos : 0 < (g.det : ℝ) := by rw [hdet]; exact_mod_cast hq
  ext τ
  have hden : denom g τ = 1 := by simp [denom, h10, h11]
  have hnum : num g τ = q * τ := by simp [num, h00, h01]
  have hsmul : ((g • τ : ℍ) : ℂ) = q * τ := by
    rw [UpperHalfPlane.coe_smul_of_det_pos hdpos, hnum, hden, div_one]
  have hof : ofComplex ((q : ℂ) * τ) = g • τ := by
    rw [← hsmul]; exact ofComplex_apply _
  rw [slash_apply, hden, one_zpow, mul_one, hdet, abs_of_pos (by exact_mod_cast hq : (0:ℝ) < q)]
  simp only [σ, hdpos, if_true, RingHom.id_apply, Pi.smul_apply, smul_eq_mul, vOp, hof]
  push_cast
  ring_nf
  rfl

end GlobalTheory.Hk
end

