module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSubProdLeSumOfLe
section
open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory

open scoped BigOperators Matrix in
open Polynomial in
private lemma one_sub_prod_le_sum_one_sub_of_mem_Icc {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∏ i ∈ s, f i ≤ ∑ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have h0' : ∀ i ∈ s, 0 ≤ f i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have h1' : ∀ i ∈ s, f i ≤ 1 := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
    have hP1 : ∏ i ∈ s, f i ≤ 1 := Finset.prod_le_one₀ h0' h1'
    have ha1 := h1 a (Finset.mem_insert_self a s)
    have key := ih h0' h1'
    nlinarith [mul_nonneg (sub_nonneg.2 hP1) (sub_nonneg.2 ha1)]


open scoped BigOperators Matrix in
open Polynomial in
theorem _root_.GlobalTheory.degree_ratio_shift_bound : ∀ (Pl : Type) [Fintype Pl] (N p kc : ℕ) (u1 : Pl → ℕ → ℝ) (g1 w : Pl → ℝ) (T : ℝ), kc ≤ p → p ≤ N → 0 < T → (∀ τ, 0 < w τ) → (∀ τ, 3 * (N : ℝ) < g1 τ) → (∀ τ i l, i < l → l < N → u1 τ l < u1 τ i) → (∀ τ i l, i < p → p ≤ l → l < N → g1 τ ≤ u1 τ i - u1 τ l) → (∀ τ i l, i < kc → p ≤ l → l < N → w τ / (2 * T) ≤ u1 τ i - u1 τ l) → let u' : Pl → ℕ → ℝ := fun τ i => if i < p then u1 τ i else u1 τ i + 3 * N; let deg : (Pl → ℕ → ℝ) → ℝ := fun v => ∏ τ, ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, (v τ i - v τ l); 0 < deg u' ∧ 0 ≤ 1 - deg u' / deg u1 ∧ 1 - deg u' / deg u1 ≤ 3 * N * ∑ τ, (((p - kc : ℕ) : ℝ) * ((N - p : ℕ) : ℝ) / g1 τ + 2 * kc * ((N - p : ℕ) : ℝ) * T / w τ) := by
  intro Pl inst N p kc u1 g1 w T hkc hpN hT hw hg hmono hgap hwgap u' deg
  have hN : (0 : ℝ) ≤ 3 * N := by positivity
  have hd : ∀ τ l i, l ∈ Finset.range N → i ∈ Finset.range l → 0 < u1 τ i - u1 τ l := by
    intro τ l i hl hi
    exact sub_pos.2 (hmono τ i l (Finset.mem_range.1 hi) (Finset.mem_range.1 hl))
  obtain ⟨F, hF⟩ : ∃ F : Pl → ℕ → ℕ → ℝ,
      ∀ τ l i, F τ l i = (u' τ i - u' τ l) / (u1 τ i - u1 τ l) := ⟨_, fun _ _ _ => rfl⟩
  have hfac : ∀ τ l i, l ∈ Finset.range N → i ∈ Finset.range l →
      u' τ i - u' τ l = (u1 τ i - u1 τ l) * F τ l i := by
    intro τ l i hl hi
    have hne := (hd τ l i hl hi).ne'
    rw [hF]
    field_simp
  have hFeq : ∀ τ l i, l ∈ Finset.range N → i ∈ Finset.range l →
      F τ l i = if i < p ∧ p ≤ l then 1 - 3 * (N : ℝ) / (u1 τ i - u1 τ l) else 1 := by
    intro τ l i hl hi
    have hne := (hd τ l i hl hi).ne'
    rw [Finset.mem_range] at hl hi
    rw [hF]
    by_cases hip : i < p
    · by_cases hpl : p ≤ l
      · have hl' : ¬ l < p := not_lt.2 hpl
        simp only [u', hip, hl', hpl, and_self, ↓reduceIte]
        field_simp <;> ring
      · have hl' : l < p := lt_of_not_ge hpl
        simp only [u', hip, hl', hpl, and_false, ↓reduceIte]
        exact div_self hne
    · have hl' : ¬ l < p := by omega
      simp only [u', hip, hl', false_and, ↓reduceIte]
      rw [show u1 τ i + 3 * (N : ℝ) - (u1 τ l + 3 * N) = u1 τ i - u1 τ l by ring]
      exact div_self hne
  have hF01 : ∀ τ l i, l ∈ Finset.range N → i ∈ Finset.range l →
      0 < F τ l i ∧ F τ l i ≤ 1 := by
    intro τ l i hl hi
    rw [hFeq τ l i hl hi]
    split_ifs with h
    · have hdp := hd τ l i hl hi
      have hlt : 3 * (N : ℝ) < u1 τ i - u1 τ l :=
        (hg τ).trans_le (hgap τ i l h.1 h.2 (Finset.mem_range.1 hl))
      have h3 : 3 * (N : ℝ) / (u1 τ i - u1 τ l) < 1 := (div_lt_one hdp).2 hlt
      have h4 : 0 ≤ 3 * (N : ℝ) / (u1 τ i - u1 τ l) := div_nonneg hN hdp.le
      constructor <;> linarith
    · exact ⟨one_pos, le_rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Pl → ℕ → ℝ, ∀ τ i, c τ i = if i < kc then 2 * T / w τ else 1 / g1 τ :=
    ⟨_, fun _ _ => rfl⟩
  have hbound : ∀ τ l i, l ∈ Finset.range N → i ∈ Finset.range l →
      1 - F τ l i ≤ 3 * (N : ℝ) * (if i < p ∧ p ≤ l then c τ i else 0) := by
    intro τ l i hl hi
    have hdp := hd τ l i hl hi
    rw [hFeq τ l i hl hi]
    split_ifs with h
    · rw [sub_sub_cancel, div_eq_mul_one_div]
      refine mul_le_mul_of_nonneg_left ?_ hN
      rw [hc]
      split_ifs with hk
      · have h1 : w τ ≤ (u1 τ i - u1 τ l) * (2 * T) :=
          (div_le_iff₀ (by linarith)).1 (hwgap τ i l hk h.2 (Finset.mem_range.1 hl))
        rw [div_le_div_iff₀ hdp (hw τ)]
        nlinarith
      · have hgpos : 0 < g1 τ := lt_of_le_of_lt hN (hg τ)
        exact one_div_le_one_div_of_le hgpos (hgap τ i l h.1 h.2 (Finset.mem_range.1 hl))
    · simp
  have hsum : ∀ τ, ∑ l ∈ Finset.range N, ∑ i ∈ Finset.range l,
      3 * (N : ℝ) * (if i < p ∧ p ≤ l then c τ i else 0) =
      3 * (N : ℝ) * (((p - kc : ℕ) : ℝ) * ((N - p : ℕ) : ℝ) / g1 τ
        + 2 * kc * ((N - p : ℕ) : ℝ) * T / w τ) := by
    intro τ
    simp_rw [← Finset.mul_sum]
    congr 1
    have hS : ∑ i ∈ Finset.range p, c τ i =
        (kc : ℝ) * (2 * T / w τ) + ((p - kc : ℕ) : ℝ) * (1 / g1 τ) := by
      rw [← Finset.sum_range_add_sum_Ico _ hkc]
      have e1 : ∑ i ∈ Finset.range kc, c τ i = ∑ i ∈ Finset.range kc, 2 * T / w τ :=
        Finset.sum_congr rfl fun i hi => by rw [hc, if_pos (Finset.mem_range.1 hi)]
      have e2 : ∑ i ∈ Finset.Ico kc p, c τ i = ∑ i ∈ Finset.Ico kc p, 1 / g1 τ :=
        Finset.sum_congr rfl fun i hi => by rw [hc, if_neg (not_lt.2 (Finset.mem_Ico.1 hi).1)]
      rw [e1, e2, Finset.sum_const, Finset.sum_const, Finset.card_range, Nat.card_Ico,
        nsmul_eq_mul, nsmul_eq_mul]
    have hinner : ∀ l, ∑ i ∈ Finset.range l, (if i < p ∧ p ≤ l then c τ i else 0) =
        if p ≤ l then ∑ i ∈ Finset.range p, c τ i else 0 := by
      intro l
      by_cases hl : p ≤ l
      · rw [if_pos hl, ← Finset.sum_range_add_sum_Ico _ hl]
        have e1 : ∑ i ∈ Finset.range p, (if i < p ∧ p ≤ l then c τ i else 0) =
            ∑ i ∈ Finset.range p, c τ i :=
          Finset.sum_congr rfl fun i hi => if_pos ⟨Finset.mem_range.1 hi, hl⟩
        have e2 : ∑ i ∈ Finset.Ico p l, (if i < p ∧ p ≤ l then c τ i else 0) = 0 :=
          Finset.sum_eq_zero fun i hi =>
            if_neg fun h => absurd h.1 (not_lt.2 (Finset.mem_Ico.1 hi).1)
        rw [e1, e2, add_zero]
      · rw [if_neg hl]
        exact Finset.sum_eq_zero fun i _ => if_neg fun h => hl h.2
    rw [Finset.sum_congr rfl fun l _ => hinner l, ← Finset.sum_range_add_sum_Ico _ hpN]
    have e3 : ∑ l ∈ Finset.range p, (if p ≤ l then ∑ i ∈ Finset.range p, c τ i else 0) = 0 :=
      Finset.sum_eq_zero fun l hl => if_neg (not_le.2 (Finset.mem_range.1 hl))
    have e4 : ∑ l ∈ Finset.Ico p N, (if p ≤ l then ∑ i ∈ Finset.range p, c τ i else 0) =
        ∑ l ∈ Finset.Ico p N, ∑ i ∈ Finset.range p, c τ i :=
      Finset.sum_congr rfl fun l hl => if_pos (Finset.mem_Ico.1 hl).1
    rw [e3, e4, zero_add, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, hS]
    ring
  have hQ : ∀ τ l, l ∈ Finset.range N →
      0 < ∏ i ∈ Finset.range l, F τ l i ∧ ∏ i ∈ Finset.range l, F τ l i ≤ 1 := fun τ l hl =>
    ⟨Finset.prod_pos fun i hi => (hF01 τ l i hl hi).1,
      Finset.prod_le_one₀ (fun i hi => (hF01 τ l i hl hi).1.le) fun i hi => (hF01 τ l i hl hi).2⟩
  have hR : ∀ τ, 0 < ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, F τ l i ∧
      ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, F τ l i ≤ 1 := fun τ =>
    ⟨Finset.prod_pos fun l hl => (hQ τ l hl).1,
      Finset.prod_le_one₀ (fun l hl => (hQ τ l hl).1.le) fun l hl => (hQ τ l hl).2⟩
  have hP0 : 0 < ∏ τ, ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, F τ l i :=
    Finset.prod_pos fun τ _ => (hR τ).1
  have hP1 : ∏ τ, ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, F τ l i ≤ 1 :=
    Finset.prod_le_one₀ (fun τ _ => (hR τ).1.le) fun τ _ => (hR τ).2
  have hdeg1 : 0 < deg u1 := by
    simp only [deg]
    exact Finset.prod_pos fun τ _ => Finset.prod_pos fun l hl =>
      Finset.prod_pos fun i hi => hd τ l i hl hi
  have hdeg : deg u' = deg u1 * ∏ τ, ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, F τ l i := by
    simp only [deg, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun τ _ => Finset.prod_congr rfl fun l hl =>
      Finset.prod_congr rfl fun i hi => hfac τ l i hl hi
  have hratio : deg u' / deg u1 = ∏ τ, ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, F τ l i := by
    have hne := hdeg1.ne'
    rw [hdeg]
    field_simp
  refine ⟨by rw [hdeg]; exact mul_pos hdeg1 hP0, by rw [hratio]; linarith, ?_⟩
  rw [hratio]
  calc 1 - ∏ τ, ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, F τ l i
      ≤ ∑ τ, (1 - ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range l, F τ l i) :=
        one_sub_prod_le_sum_one_sub_of_mem_Icc _ _ (fun τ _ => (hR τ).1.le) fun τ _ => (hR τ).2
    _ ≤ ∑ τ, ∑ l ∈ Finset.range N, (1 - ∏ i ∈ Finset.range l, F τ l i) :=
        Finset.sum_le_sum fun τ _ => one_sub_prod_le_sum_one_sub_of_mem_Icc _ _
          (fun l hl => (hQ τ l hl).1.le) fun l hl => (hQ τ l hl).2
    _ ≤ ∑ τ, ∑ l ∈ Finset.range N, ∑ i ∈ Finset.range l, (1 - F τ l i) :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun l hl =>
          one_sub_prod_le_sum_one_sub_of_mem_Icc _ _ (fun i hi => (hF01 τ l i hl hi).1.le)
            fun i hi => (hF01 τ l i hl hi).2
    _ ≤ ∑ τ, ∑ l ∈ Finset.range N, ∑ i ∈ Finset.range l,
          3 * (N : ℝ) * (if i < p ∧ p ≤ l then c τ i else 0) :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun l hl =>
          Finset.sum_le_sum fun i hi => hbound τ l i hl hi
    _ = ∑ τ, 3 * (N : ℝ) * (((p - kc : ℕ) : ℝ) * ((N - p : ℕ) : ℝ) / g1 τ
          + 2 * kc * ((N - p : ℕ) : ℝ) * T / w τ) :=
        Finset.sum_congr rfl fun τ _ => hsum τ
    _ = _ := by rw [Finset.mul_sum]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OptionEquivLeftRenameSomeComplexEqC
section
open MvPolynomial

namespace GlobalTheory

theorem optionEquivLeft_rename_some_complex_eq_C {τ : Type} (c : MvPolynomial τ ℂ) :
    MvPolynomial.optionEquivLeft ℂ τ (MvPolynomial.rename some c) = Polynomial.C c := by
  induction c using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.rename_C, MvPolynomial.optionEquivLeft_C, Polynomial.C_eq_algebraMap]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, Polynomial.C_add]
  | mul_X p n hp => rw [map_mul, map_mul, hp, MvPolynomial.rename_X, MvPolynomial.optionEquivLeft_X_some, Polynomial.C_mul]

theorem coeff_optionEquivLeft_extDerivation {τ : Type}
    (E : Derivation ℂ (MvPolynomial τ ℂ) (MvPolynomial τ ℂ)) (k : ℕ) (s : MvPolynomial (Option τ) ℂ) :
    (MvPolynomial.optionEquivLeft ℂ τ (MvPolynomial.mkDerivation ℂ (fun w : Option τ => match w with
      | none => (0 : MvPolynomial (Option τ) ℂ)
      | some v => MvPolynomial.rename some (E (MvPolynomial.X v))) s)).coeff k
      = E ((MvPolynomial.optionEquivLeft ℂ τ (s)).coeff k) := by
  induction s using MvPolynomial.induction_on generalizing k with
  | C a =>
    have h1 : (MvPolynomial.C a : MvPolynomial (Option τ) ℂ) = algebraMap ℂ _ a := rfl
    have h2 : (MvPolynomial.C a : MvPolynomial τ ℂ) = algebraMap ℂ _ a := rfl
    rw [h1, Derivation.map_algebraMap, ← h1, MvPolynomial.optionEquivLeft_C, Polynomial.coeff_C]
    split_ifs <;> simp [h2, Derivation.map_algebraMap]
  | add p q hp hq => simp only [map_add (f := _), Polynomial.coeff_add, hp, hq]
  | mul_X p n hp =>
    rw [Derivation.leibniz, MvPolynomial.mkDerivation_X]
    rcases n with _ | v
    · simp only [smul_zero, zero_add, smul_eq_mul, mul_zero, map_mul, MvPolynomial.optionEquivLeft_X_none]
      rcases k with _ | k
      · simp [Polynomial.coeff_mul_X_zero, mul_comm (Polynomial.X) _]
      · rw [mul_comm Polynomial.X, Polynomial.coeff_mul_X, Polynomial.coeff_mul_X, hp]
    · simp only [smul_eq_mul, map_add (f := _), map_mul, MvPolynomial.optionEquivLeft_X_some, optionEquivLeft_rename_some_complex_eq_C,
        Polynomial.coeff_add, Polynomial.coeff_mul_C, Polynomial.coeff_C_mul, hp, Derivation.leibniz]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitCountParabolicUnfoldLevi
section
namespace GlobalTheory

theorem orbit_count_parabolic_unfold : ∀ (P M N : Type) [Group P] [Group M] [Group N] (s : M →* P) (π : P →* M) (u : N →* P), (∀ m, π (s m) = m) → Function.Injective u → (∀ p, π p = 1 ↔ ∃ X, u X = p) → ∀ (KP : Subgroup P) (KM : Subgroup M) (L : Subgroup N), (∀ k ∈ KM, s k ∈ KP) → (∀ k ∈ KP, π k ∈ KM) → (∀ X, u X ∈ KP ↔ X ∈ L) → ∀ (TM CM : Subgroup M) (TP CP : Subgroup P), CM ≤ TM → (∀ p, p ∈ TP ↔ ∃ t ∈ TM, s t = p) → (∀ p, p ∈ CP ↔ ∃ t ∈ CM, s t = p) → (∀ q : M, TM ⊓ KM.map (MulAut.conj q).toMonoidHom ≤ CM) → ∀ (q : M) (X : N), Nat.card {x : N ⧸ L // DoubleCoset.mk TP KP (s q * u (Quotient.out x)) = DoubleCoset.mk TP KP (s q * u X)} = (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM ⊓ KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s)).relIndex (TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM) := by
  intro P M N _ _ _ s π u hπs hu hker KP KM L hsK hπK huK TM CM TP CP _ hTP _ _ q X
  set S : Subgroup M := TM.map (MulAut.conj q⁻¹).toMonoidHom ⊓ KM with hS
  set C : Subgroup M := KP.comap ((MulAut.conj (u X)⁻¹).toMonoidHom.comp s) with hC
  letI : MulAction M (P ⧸ KP) := MulAction.compHom (P ⧸ KP) s
  have hsmul : ∀ (r : M) (p : P), r • (QuotientGroup.mk p : P ⧸ KP) = QuotientGroup.mk (s r * p) := by
    intro r p; rfl
  have memS : ∀ r : M, r ∈ S ↔ (∃ t ∈ TM, q⁻¹ * t * q = r) ∧ r ∈ KM := by
    intro r
    simp only [hS, Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hπu : ∀ Y, π (u Y) = 1 := fun Y => (hker _).2 ⟨Y, rfl⟩
  set x0 : P ⧸ KP := QuotientGroup.mk (u X) with hx0
  have key : ∀ Y : N, DoubleCoset.mk TP KP (s q * u Y) = DoubleCoset.mk TP KP (s q * u X) ↔
      (QuotientGroup.mk (u Y) : P ⧸ KP) ∈ MulAction.orbit S x0 := by
    intro Y
    rw [eq_comm, DoubleCoset.eq]
    constructor
    · rintro ⟨h, hh, k, hk, e⟩
      obtain ⟨t, ht, rfl⟩ := (hTP h).1 hh
      have e2 : u Y = s (q⁻¹ * t * q) * u X * k := by
        apply mul_left_cancel (a := s q)
        rw [e, map_mul, map_mul, map_inv]
        group
      have e3 := congrArg π e2
      simp only [map_mul, hπs, hπu, mul_one] at e3
      have e4 : q⁻¹ * t * q = (π k)⁻¹ := eq_inv_of_mul_eq_one_left e3.symm
      have hr : q⁻¹ * t * q ∈ S := (memS _).2 ⟨⟨t, ht, rfl⟩, e4 ▸ KM.inv_mem (hπK k hk)⟩
      refine ⟨⟨_, hr⟩, ?_⟩
      show (q⁻¹ * t * q) • x0 = _
      rw [hx0, hsmul, QuotientGroup.eq, e2]
      convert hk using 1
      group
    · rintro ⟨⟨r, hr⟩, e⟩
      change r • x0 = _ at e
      rw [hx0, hsmul, QuotientGroup.eq] at e
      obtain ⟨⟨t, ht, rfl⟩, -⟩ := (memS r).1 hr
      refine ⟨s t, (hTP _).2 ⟨t, ht, rfl⟩, _, e, ?_⟩
      simp only [map_mul, map_inv]
      group
  have hinj : ∀ x y : N ⧸ L, (QuotientGroup.mk (u (Quotient.out x)) : P ⧸ KP) = QuotientGroup.mk (u (Quotient.out y)) → x = y := by
    intro x y h
    rw [QuotientGroup.eq, ← map_inv, ← map_mul, huK] at h
    rw [← Quotient.out_eq' x, ← Quotient.out_eq' y]
    exact (QuotientGroup.eq (s := L)).2 h
  have hcard : Nat.card {x : N ⧸ L // DoubleCoset.mk TP KP (s q * u (Quotient.out x)) = DoubleCoset.mk TP KP (s q * u X)} = Nat.card (MulAction.orbit S x0) := by
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨QuotientGroup.mk (u (Quotient.out x.1)), (key _).1 x.2⟩) ⟨?_, ?_⟩)
    · intro x y h
      exact Subtype.ext (hinj _ _ (congrArg Subtype.val h))
    · rintro ⟨y, ⟨⟨r, hr⟩, rfl⟩⟩
      have hk : π (s r * u X * (s r)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_inv, hπs, hπu]; group
      obtain ⟨Z, hZ⟩ := (hker _).1 hk
      have hrK : (r : M) ∈ KM := ((memS r).1 hr).2
      have hyo : (QuotientGroup.mk (u (Quotient.out (QuotientGroup.mk Z : N ⧸ L))) : P ⧸ KP) = r • x0 := by
        obtain ⟨l, hl⟩ := QuotientGroup.mk_out_eq_mul L Z
        change _ = r • x0
        rw [hx0, hsmul, hl, QuotientGroup.eq, map_mul, hZ]
        have h1 : s (r : M) ∈ KP := hsK _ hrK
        have h2 : u (l : N) ∈ KP := (huK _).2 l.2
        convert KP.mul_mem (KP.inv_mem h2) h1 using 1
        group
      refine ⟨⟨QuotientGroup.mk Z, (key _).2 ?_⟩, ?_⟩
      · rw [hyo]; exact ⟨⟨r, hr⟩, rfl⟩
      · exact Subtype.ext hyo
  have hstab : MulAction.stabilizer S x0 = (S ⊓ C).subgroupOf S := by
    ext ⟨r, hr⟩
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf, hC, Subgroup.mem_comap]
    change (r • x0 = x0) ↔ _
    rw [hx0, hsmul, QuotientGroup.eq]
    simp only [hr, true_and, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, MulAut.conj_apply, inv_inv]
    rw [← KP.inv_mem_iff]
    constructor <;> intro h <;> convert h using 1 <;> group
  rw [hcard, Subgroup.relIndex, ← hstab, MulAction.index_stabilizer, Nat.card_coe_set_eq]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitMassFormulaFiniteIndexSubgroup
section
open MulAction

namespace GlobalTheory.OrbitMass

variable {G H D : Type} [Group G] [Group H] [MulAction G D] [MulAction H D]

def toG (ι : H →* G) (hc : ∀ (h : H) (d : D), ι h • d = h • d) :
    orbitRel.Quotient H D → orbitRel.Quotient G D :=
  Quotient.map' id (fun a b hab => by
    change a ∈ orbit H b at hab
    change a ∈ orbit G b
    obtain ⟨h, rfl⟩ := hab
    exact ⟨ι h, hc h b⟩)

def toCoset (ι : H →* G) (hc : ∀ (h : H) (d : D), ι h • d = h • d) (x : D) :
    G ⧸ ι.range → orbitRel.Quotient H D :=
  fun ω => Quotient.liftOn' ω (fun g => (Quotient.mk'' (g⁻¹ • x) : orbitRel.Quotient H D)) (by
    intro g₁ g₂ hg
    rw [QuotientGroup.leftRel_apply, MonoidHom.mem_range] at hg
    obtain ⟨h, hh⟩ := hg
    apply Quotient.sound'
    change g₁⁻¹ • x ∈ orbit H (g₂⁻¹ • x)
    refine ⟨h, ?_⟩
    change h • g₂⁻¹ • x = g₁⁻¹ • x
    rw [← hc, smul_smul, hh, mul_inv_cancel_right])

theorem toCoset_mk (ι : H →* G) (hc : ∀ (h : H) (d : D), ι h • d = h • d) (x : D) (g : G) :
    toCoset ι hc x (g : G ⧸ ι.range) = Quotient.mk'' (g⁻¹ • x) := rfl

theorem toCoset_eq_iff (ι : H →* G) (hc : ∀ (h : H) (d : D), ι h • d = h • d) (x : D) (a g : G) :
    toCoset ι hc x (g : G ⧸ ι.range) = Quotient.mk'' (a⁻¹ • x) ↔
      (g : G ⧸ ι.range) ∈ orbit (stabilizer G x) (a : G ⧸ ι.range) := by
  rw [toCoset_mk, Quotient.eq'']
  change g⁻¹ • x ∈ orbit H (a⁻¹ • x) ↔ _
  rw [mem_orbit_iff, mem_orbit_iff]
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨⟨g * ι h * a⁻¹, ?_⟩, ?_⟩
    · rw [mem_stabilizer_iff, mul_smul, mul_smul, hc, hh, smul_inv_smul]
    · change ((g * ι h * a⁻¹ : G) • (a : G ⧸ ι.range)) = g
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
      exact ⟨h⁻¹, by simp [mul_assoc]⟩
  · rintro ⟨⟨s, hs⟩, hsa⟩
    change ((s : G) • (a : G ⧸ ι.range)) = g at hsa
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, MonoidHom.mem_range] at hsa
    obtain ⟨k, hk⟩ := hsa
    have hg : g = s * a * ι k := by rw [hk, smul_eq_mul, mul_inv_cancel_left]
    subst hg
    have hs' : s⁻¹ • x = x := by rw [inv_smul_eq_iff]; exact (mem_stabilizer_iff.mp hs).symm
    refine ⟨k⁻¹, ?_⟩
    rw [← hc, map_inv, mul_inv_rev, mul_inv_rev, mul_smul, mul_smul, hs']

theorem card_stab (ι : H →* G) (hinj : Function.Injective ι)
    (hc : ∀ (h : H) (d : D), ι h • d = h • d) (x : D) (a : G) :
    Nat.card (stabilizer (stabilizer G x) (a : G ⧸ ι.range)) =
      Nat.card (stabilizer H (a⁻¹ • x)) := by
  symm
  refine Nat.card_eq_of_bijective
    (fun h => ⟨⟨a * ι h.1 * a⁻¹, by
      rw [mem_stabilizer_iff, mul_smul, mul_smul, hc, mem_stabilizer_iff.mp h.2, smul_inv_smul]⟩,
      by
        rw [mem_stabilizer_iff]
        change ((a * ι h.1 * a⁻¹ : G) • (a : G ⧸ ι.range)) = a
        rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
        exact ⟨h.1⁻¹, by simp [mul_assoc]⟩⟩) ⟨?_, ?_⟩
  · intro h₁ h₂ he
    have e : a * ι h₁.1 * a⁻¹ = a * ι h₂.1 * a⁻¹ := congrArg (fun s => ((s.1 : stabilizer G x) : G)) he
    exact Subtype.ext (hinj (mul_left_cancel (mul_right_cancel e)))
  · rintro ⟨⟨s, hs⟩, hsa⟩
    rw [mem_stabilizer_iff] at hsa
    change ((s : G) • (a : G ⧸ ι.range)) = a at hsa
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, MonoidHom.mem_range] at hsa
    obtain ⟨k, hk⟩ := hsa
    have e : ι k⁻¹ = a⁻¹ * s * a := by
      rw [map_inv, hk, smul_eq_mul]; group
    refine ⟨⟨k⁻¹, ?_⟩, ?_⟩
    · rw [mem_stabilizer_iff, ← hc, e, mul_smul, mul_smul, smul_inv_smul, mem_stabilizer_iff.mp hs]
    · apply Subtype.ext; apply Subtype.ext
      change a * ι k⁻¹ * a⁻¹ = s
      rw [e]; group

theorem toG_mk (ι : H →* G) (hc : ∀ (h : H) (d : D), ι h • d = h • d) (y : D) :
    toG ι hc (Quotient.mk'' y) = Quotient.mk'' y := rfl

theorem sum_fiber (ι : H →* G) (hinj : Function.Injective ι)
    (hc : ∀ (h : H) (d : D), ι h • d = h • d) [ι.range.FiniteIndex]
    (c' : orbitRel.Quotient G D) [Finite (stabilizer G (Quotient.out c'))]
    [Fintype (orbitRel.Quotient H D)] [DecidableEq (orbitRel.Quotient G D)] :
    ∑ c ∈ Finset.univ.filter (fun c => toG ι hc c = c'),
        ((Nat.card (stabilizer H (Quotient.out c)) : ℂ))⁻¹
      = (ι.range.index : ℂ) / Nat.card (stabilizer G (Quotient.out c')) := by
  classical
  set x := Quotient.out c' with hx
  haveI : Fintype (G ⧸ ι.range) := Fintype.ofFinite _
  have hS0 : 0 < Nat.card (stabilizer G x) := Nat.card_pos
  have hidx : (ι.range.index : ℂ) / Nat.card (stabilizer G x) =
      ∑ _ω : G ⧸ ι.range, ((Nat.card (stabilizer G x) : ℂ))⁻¹ := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Subgroup.index_eq_card,
      Nat.card_eq_fintype_card, div_eq_mul_inv]
  rw [hidx, ← Finset.sum_fiberwise Finset.univ (toCoset ι hc x), Finset.sum_filter]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  split_ifs with hcx
  · have hmem : Quotient.out c ∈ orbit G x := by
      have h1 : (Quotient.mk'' (Quotient.out c) : orbitRel.Quotient G D) = Quotient.mk'' x := by
        rw [← toG_mk ι hc, Quotient.out_eq', hcx, hx, Quotient.out_eq']
      exact Quotient.exact' h1
    obtain ⟨b, hb⟩ := hmem
    have hy : (b⁻¹)⁻¹ • x = Quotient.out c := by rw [inv_inv]; exact hb
    have hfib : (Finset.univ.filter (fun ω => toCoset ι hc x ω = c)) =
        (orbit (stabilizer G x) ((b⁻¹ : G) : G ⧸ ι.range)).toFinset := by
      ext ω
      induction ω using QuotientGroup.induction_on with
      | H g =>
        rw [Finset.mem_filter, Set.mem_toFinset, ← toCoset_eq_iff ι hc x b⁻¹ g, hy,
          Quotient.out_eq']
        simp
    have hcard := Subgroup.card_mul_index (stabilizer (stabilizer G x) ((b⁻¹ : G) : G ⧸ ι.range))
    rw [index_stabilizer, card_stab ι hinj hc x b⁻¹, hy] at hcard
    rw [hfib, ← Set.ncard_eq_toFinset_card']
    have hm0 : Nat.card (stabilizer H (Quotient.out c)) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hcard; omega
    have hn0 : (orbit (stabilizer G x) ((b⁻¹ : G) : G ⧸ ι.range)).ncard ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hcard; omega
    rw [← hcard]
    push_cast
    field_simp
  · rw [Finset.card_eq_zero.mpr, Nat.cast_zero, zero_mul]
    rw [Finset.filter_eq_empty_iff]
    intro ω _ hω
    apply hcx
    rw [← hω]
    induction ω using QuotientGroup.induction_on with
    | H g =>
      rw [toCoset_mk, toG_mk, hx]
      conv_rhs => rw [← Quotient.out_eq' c']
      exact Quotient.sound' ⟨g⁻¹, rfl⟩

theorem mass_formula : ∀ {G H D : Type} [Group G] [Group H] [MulAction G D] [MulAction H D] (ι : H →* G), Function.Injective ι → (∀ (h : H) (d : D), ι h • d = h • d) → ι.range.FiniteIndex → (∀ d : D, Finite (MulAction.stabilizer G d)) → ∀ [Fintype (MulAction.orbitRel.Quotient G D)] [Fintype (MulAction.orbitRel.Quotient H D)] (f : D → ℂ), (∀ (g : G) (d : D), f (g • d) = f d) → ∑ c : MulAction.orbitRel.Quotient H D, ((Nat.card (MulAction.stabilizer H (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c) = (ι.range.index : ℂ) * ∑ c : MulAction.orbitRel.Quotient G D, ((Nat.card (MulAction.stabilizer G (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c) := by
  intro G H D _ _ _ _ ι hinj hc hfi hfin _ _ f hf
  classical
  rw [← Finset.sum_fiberwise Finset.univ (toG ι hc)
    (fun c => ((Nat.card (MulAction.stabilizer H (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c' _ => ?_)
  have hconst : ∀ c ∈ Finset.univ.filter (fun c => toG ι hc c = c'),
      ((Nat.card (MulAction.stabilizer H (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c) =
      ((Nat.card (MulAction.stabilizer H (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c') := by
    intro c hc'
    rw [Finset.mem_filter] at hc'
    have h1 : (Quotient.mk'' (Quotient.out c) : orbitRel.Quotient G D) = Quotient.mk'' (Quotient.out c') := by
      rw [← toG_mk ι hc, Quotient.out_eq', hc'.2, Quotient.out_eq']
    obtain ⟨g, hg⟩ := (Quotient.exact' h1 : Quotient.out c ∈ orbit G (Quotient.out c'))
    rw [← hg]
    change _ * f (g • Quotient.out c') = _
    rw [hf]
  haveI := hfin (Quotient.out c')
  rw [Finset.sum_congr rfl hconst, ← Finset.sum_mul, sum_fiber ι hinj hc c', div_eq_mul_inv, mul_assoc]

end GlobalTheory.OrbitMass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PluckerMinorsProportional
section
open Matrix

namespace GlobalTheory

theorem det_mul_det_toBlocks₂₂_of_mul_eq_one {K : Type} [Field K] {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X Y : Matrix (m ⊕ n) (m ⊕ n) K) (h : X * Y = 1) :
    X.det * Y.toBlocks₂₂.det = X.toBlocks₁₁.det := by
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, X = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks X).symm⟩
  obtain ⟨A', B', C', D', rfl⟩ : ∃ A B C D, Y = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks Y).symm⟩
  rw [fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at h
  obtain ⟨-, h12, -, h22⟩ := h
  have key : fromBlocks A B C D * fromBlocks (1 : Matrix m m K) B' 0 D' = fromBlocks A 0 C 1 := by
    rw [fromBlocks_multiply, h12, h22]
    simp
  have := congrArg Matrix.det key
  rw [det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂] at this
  simpa using this

end GlobalTheory
end

