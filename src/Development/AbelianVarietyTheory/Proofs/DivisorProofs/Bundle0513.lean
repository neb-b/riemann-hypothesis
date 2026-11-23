module

public import Mathlib
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinear
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0201
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0504
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0503

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirFockAct1SubCasimirFockAct2
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.FockCasimir

theorem sum_mul_normal_order {A ι κ : Type} [Ring A] [Algebra ℂ A] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (x d : ι → κ → A)
    (h : ∀ b c e, d b c * x b e = x b e * d b c + if c = e then 1 else 0) :
    ∑ a, ∑ b, (∑ c, (x a c * d b c + if a = b then (1 / 2 : ℂ) • (1 : A) else 0)) *
        (∑ e, (x b e * d a e + if b = a then (1 / 2 : ℂ) • (1 : A) else 0)) =
      (∑ a, ∑ b, ∑ c, ∑ e, x a c * x b e * (d b c * d a e)) +
        ((Fintype.card ι : ℂ) + (Fintype.card κ : ℂ)) • (∑ a, ∑ c, x a c * d a c) +
        ((Fintype.card ι : ℂ) * (Fintype.card κ : ℂ) ^ 2 / 4) • (1 : A) := by
  have h0 : ∀ a b, (∑ c, x a c * d b c) * (∑ e, x b e * d a e) =
      (∑ c, ∑ e, x a c * x b e * (d b c * d a e)) + ∑ c, x a c * d a c := by
    intro a b
    rw [Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    have h1 : ∀ e, x a c * d b c * (x b e * d a e) =
        x a c * x b e * (d b c * d a e) + if c = e then x a c * d a e else 0 := by
      intro e
      have : x a c * d b c * (x b e * d a e) = x a c * (d b c * x b e) * d a e := by
        simp only [mul_assoc]
      rw [this, h, mul_add, add_mul]
      split_ifs <;> simp [mul_assoc]
    simp only [h1, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have h2 : ∀ a b, (∑ c, (x a c * d b c + if a = b then (1 / 2 : ℂ) • (1 : A) else 0)) *
        (∑ e, (x b e * d a e + if b = a then (1 / 2 : ℂ) • (1 : A) else 0)) =
      ((∑ c, ∑ e, x a c * x b e * (d b c * d a e)) + ∑ c, x a c * d a c) +
        if a = b then (Fintype.card κ : ℂ) • (∑ c, x a c * d a c) +
          ((Fintype.card κ : ℂ) ^ 2 / 4) • (1 : A) else 0 := by
    intro a b
    rw [← h0]
    by_cases hab : a = b
    · subst hab
      simp only [if_true, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        ← Nat.cast_smul_eq_nsmul ℂ, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
      module
    · simp [hab, Ne.symm hab]
  simp only [h2]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, ← Finset.smul_sum]
  module

variable {p q r s : ℕ}

theorem pderiv_pderiv_comm {σ : Type} (l m : σ) (P : MvPolynomial σ ℂ) :
    pderiv l (pderiv m P) = pderiv m (pderiv l P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P n hP =>
    simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add (f := _), hP, Pi.single_apply]
    split_ifs <;> simp <;> ring

theorem lowB_comm (l m : Ln p q r s) : lowB l * lowB m = lowB m * lowB l := by
  by_cases hlm : l = m
  · rw [hlm]
  refine LinearMap.ext fun P => ?_
  cases hl : linePos l <;> cases hm : linePos m <;>
    simp [lowB, hl, hm, pderiv_X, Pi.single_apply, hlm, Ne.symm hlm, pderiv_pderiv_comm l m,
      mul_left_comm]

theorem lowB_mul_raiB (l m : Ln p q r s) :
    lowB l * raiB m = raiB m * lowB l + if l = m then 1 else 0 := by
  refine LinearMap.ext fun P => ?_
  by_cases hlm : l = m
  · subst hlm
    cases hl : linePos l <;> simp [lowB, raiB, hl, add_comm]
  · cases hl : linePos l <;> cases hm : linePos m <;>
      simp [lowB, raiB, hl, hm, pderiv_X, Pi.single_apply, hlm, Ne.symm hlm, pderiv_pderiv_comm l m,
        mul_left_comm]

theorem casimir_fockAct1_sub_casimir_fockAct2 : ∀ (p q r s : ℕ),
    casimir (fockAct1 p q r s) - casimir (fockAct2 p q r s) =
      ((((p + q : ℕ) : ℂ) * ((r + s : ℕ) : ℂ) * (((r + s : ℕ) : ℂ) - ((p + q : ℕ) : ℂ))) / 4) •
        (1 : Module.End ℂ (Pol p q r s)) := by
  intro p q r s
  have h1 := sum_mul_normal_order (fun (a : Ix p q) (c : Ix r s) => raiB (a, c))
    (fun (a : Ix p q) (c : Ix r s) => lowB (a, c)) (fun b c e => by simp [lowB_mul_raiB])
  have h2 := sum_mul_normal_order (fun (c : Ix r s) (a : Ix p q) => raiB (a, c))
    (fun (c : Ix r s) (a : Ix p q) => lowB (a, c)) (fun b c e => by simp [lowB_mul_raiB])
  have hQ : (∑ c : Ix r s, ∑ e : Ix r s, ∑ a : Ix p q, ∑ b : Ix p q,
        raiB (a, c) * raiB (b, e) * (lowB (a, e) * lowB (b, c))) =
      ∑ a : Ix p q, ∑ b : Ix p q, ∑ c : Ix r s, ∑ e : Ix r s,
        raiB (a, c) * raiB (b, e) * (lowB (b, c) * lowB (a, e)) := by
    rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type' (α₁ := Ix p q) (α₂ := Ix p q)]
    simp only [← Fintype.sum_prod_type' (α₁ := Ix p q) (α₂ := Ix p q),
      ← Fintype.sum_prod_type' (α₁ := Ix r s) (α₂ := Ix r s)]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [lowB_comm]
  have hE : (∑ c : Ix r s, ∑ a : Ix p q, raiB (a, c) * lowB (a, c)) =
      ∑ a : Ix p q, ∑ c : Ix r s, raiB (a, c) * lowB (a, c) := Finset.sum_comm
  rw [hQ, hE] at h2
  simp only [Formalism.BasicNotions.TH.casimir, fockAct1_Eab, fockAct2_Eab, Formalism.BasicNotions.TH.omE, Prod.mk.injEq, and_true, true_and]
  rw [h1, h2]
  simp only [Fintype.card_sum, Fintype.card_fin]
  module

end GlobalTheory.FockCasimir
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CliffordSemidirectPrimeIndexIrreducibleCharacter
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem clifford_prime_index : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ),
    (Nat.card Γ).Prime → s ≠ 1 → ∀ χ : G ⋊[φ] Γ → ℂ, IsIrrChar ℂ ℂ χ →
      (∀ δ, χ (inl δ * inr s) = 0) ∨ (IsIrrChar ℂ ℂ (fun g => χ (inl g)) ∧
        ∑ᶠ g, χ (inl g * inr s) * star (χ (inl g * inr s)) = (Nat.card G : ℂ)) := by
  intro G Γ _ _ _ _ φ s hl hs χ hχ
  haveI : Finite (G ⋊[φ] Γ) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  haveI := Fintype.ofFinite (G ⋊[φ] Γ)
  have hH : Nat.card (G ⋊[φ] Γ) = Nat.card G * Nat.card Γ := by
    rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
  have hHne : (Nat.card (G ⋊[φ] Γ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hord : orderOf s = Nat.card Γ := by
    rcases (Nat.dvd_prime hl).1 (orderOf_dvd_natCard s) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hs
    · exact h
  have hgen : ∀ t : Γ, t ∈ Subgroup.zpowers s := by
    have htop : Subgroup.zpowers s = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord])
    intro t
    rw [htop]
    trivial
  have hl0 : Nat.card Γ ≠ 0 := hl.ne_zero
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / (Nat.card Γ : ℂ))) (Nat.card Γ) :=
    Complex.isPrimitiveRoot_exp _ hl0
  obtain ⟨η, hη1, hηs, hF⟩ := GlobalTheory.Shin.CosetFourier.fourier_coset_sums G Γ φ s hgen _ hζ
  set ζ := Complex.exp (2 * Real.pi * Complex.I / (Nat.card Γ : ℂ)) with hζdef
  have hχchar : IsChar ℂ ℂ χ := by
    obtain ⟨n, ρ, -, h⟩ := hχ
    exact ⟨n, ρ, h⟩
  have hVR := virt_mul_comap_conj_ind_linear (G ⋊[φ] Γ)
  have hnorm : ∑ᶠ x, χ x * star (χ x) = (Nat.card (G ⋊[φ] Γ) : ℂ) := by
    obtain ⟨n, ρ, hρ, h⟩ := hχ
    haveI := hρ
    haveI : Invertible (Nat.card (G ⋊[φ] Γ) : ℂ) := invertibleOfNonzero hHne
    have ho := Representation.char_orthonormal ρ ρ
    rw [if_pos ⟨Representation.Equiv.refl ρ⟩] at ho
    have hc : χ = ρ.character := funext fun g => by simpa using h g
    rw [finsum_eq_sum_of_fintype]
    have hst : ∀ x, star (χ x) = χ x⁻¹ := star_virt_eq_inv _ χ (isChar_mem_virt_complex hχchar)
    simp_rw [hst]
    rw [hc]
    exact ((inv_mul_eq_one₀ hHne).1 (by simpa using ho)).symm
  have hηstar : ∀ x, (η x : ℂ) * star (η x : ℂ) = 1 := by
    intro x
    have h := star_virt_eq_inv _ (fun x => (η x : ℂ)) (hVR.2.2.2.2 η) x
    rw [h, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have hψchar : ∀ a : ℕ, IsChar ℂ ℂ (fun x => χ x * (η x : ℂ) ^ a) := by
    intro a
    have h := isChar_mul_complex hχchar (isChar_monoidHom_complex (η ^ a))
    convert h using 1
  have hψnorm : ∀ a : ℕ, ∑ᶠ x, (fun x => χ x * (η x : ℂ) ^ a) x * star ((fun x => χ x * (η x : ℂ) ^ a) x) =
      (Nat.card (G ⋊[φ] Γ) : ℂ) := by
    intro a
    rw [← hnorm]
    congr 1
    funext x
    dsimp only
    rw [star_mul, star_pow]
    calc χ x * (η x : ℂ) ^ a * (star (η x : ℂ) ^ a * star (χ x))
        = χ x * star (χ x) * ((η x : ℂ) * star (η x : ℂ)) ^ a := by ring
      _ = χ x * star (χ x) := by rw [hηstar, one_pow, mul_one]
  have hψirr : ∀ a : ℕ, IsIrrChar ℂ ℂ (fun x => χ x * (η x : ℂ) ^ a) := fun a =>
    ((irr_of_norm_one _ _ (isChar_mem_virt_complex (hψchar a)) (hψnorm a)).2 (hψchar a)).1
  by_cases hcase : ∃ a, 0 < a ∧ a < Nat.card Γ ∧ (fun x => χ x * (η x : ℂ) ^ a) = χ
  · left
    obtain ⟨a, ha0, hal, he⟩ := hcase
    intro δ
    have h1 := congrFun he (inl δ * inr s)
    have hv : (η (inl δ * inr s) : ℂ) = ζ := by rw [map_mul, hη1, one_mul, hηs]
    rw [hv] at h1
    have hζa : ζ ^ a ≠ 1 := hζ.pow_ne_one_of_pos_of_lt ha0.ne' hal
    have h2 : χ (inl δ * inr s) * (ζ ^ a - 1) = 0 := by rw [mul_sub, h1, mul_one, sub_self]
    exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 hζa)
  · right
    push_neg at hcase
    have hNa : ∀ a ∈ Finset.range (Nat.card Γ), a ≠ 0 →
        ∑ᶠ x, χ x * star (χ x * (η x : ℂ) ^ a) = 0 := by
      intro a ha ha0
      have hne := hcase a (Nat.pos_of_ne_zero ha0) (Finset.mem_range.1 ha)
      have hp := pair_eq_zero_of_isIrrChar_ne _ χ _ hχ (hψirr a) (Ne.symm hne)
      unfold pair at hp
      have hs0 := (mul_eq_zero.1 hp).resolve_left (inv_ne_zero hHne)
      rw [← hs0]
      congr 1
      funext x
      have h := star_virt_eq_inv _ _ (isChar_mem_virt_complex (hψchar a)) x
      rw [h]
    have hN0 : ∑ᶠ x, χ x * star (χ x * (η x : ℂ) ^ 0) = (Nat.card (G ⋊[φ] Γ) : ℂ) := by
      simpa using hnorm
    have h0mem : 0 ∈ Finset.range (Nat.card Γ) := Finset.mem_range.2 (Nat.pos_of_ne_zero hl0)
    obtain ⟨hA, hB⟩ := hF χ χ
    rw [Finset.sum_eq_single 0 (fun a ha ha0 => hNa a ha ha0) (fun h => absurd h0mem h), hN0, hH] at hA
    rw [Finset.sum_eq_single 0 (fun a ha ha0 => by rw [hNa a ha ha0, mul_zero]) (fun h => absurd h0mem h),
      pow_zero, one_mul, hN0, hH] at hB
    have hlc : (Nat.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hl0
    push_cast at hA hB
    have hSG : ∑ᶠ g, χ (inl g) * star (χ (inl g)) = (Nat.card G : ℂ) :=
      mul_left_cancel₀ hlc (by rw [hA, mul_comm])
    refine ⟨?_, mul_left_cancel₀ hlc (by rw [hB, mul_comm])⟩
    have hrchar : IsChar ℂ ℂ (fun g => χ (inl g)) := by
      obtain ⟨n, ρ, h⟩ := hχchar
      exact ⟨n, ρ.comp SemidirectProduct.inl, fun g => h _⟩
    exact ((irr_of_norm_one G _ (isChar_mem_virt_complex hrchar) hSG).2 hrchar).1

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegWBlattnerLeOfBlattnerCone
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FlowLemma

open MvPolynomial in
private lemma shiftNu_add_right {p q : ℕ} (c : ℚ) (f g : _root_.Formalism.BasicNotions.TH.Ix p q → ℚ) (a : _root_.Formalism.BasicNotions.TH.Ix p q) :
    _root_.Formalism.BasicNotions.TH.shiftNu c (fun x => f x + g x) a = _root_.Formalism.BasicNotions.TH.shiftNu c f a + g a := by
  cases a <;> simp only [_root_.Formalism.BasicNotions.TH.shiftNu] <;> ring

open MvPolynomial in
private lemma degW_blattner_le_of_sign_lemma {p q : ℕ} (M : _root_.Formalism.BasicNotions.TH.GKMod p q) (lam : _root_.Formalism.BasicNotions.TH.Ix p q → ℚ)
    (c : ℚ) (hC : _root_.GlobalTheory.FockAlg.ConeTypes M lam) (s : _root_.Formalism.BasicNotions.TH.Ix p q → ℚ)
    (hs : ∀ a, s a = 1 ∨ s a = -1)
    (hsν : ∀ a, s a * _root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a = |_root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a|)
    (hmono : ∀ a b, lam b < lam a → s b ≤ s a)
    (μ : _root_.Formalism.BasicNotions.TH.Ix p q → ℚ) (v : M.V) (hv : _root_.Formalism.BasicNotions.TH.IsHW M.act μ v) :
    _root_.Formalism.BasicNotions.TH.degW c (_root_.Formalism.BasicNotions.TH.blattner lam) ≤ _root_.Formalism.BasicNotions.TH.degW c μ := by
  obtain ⟨m, hm, rfl⟩ := hC μ v hv
  set Δ : _root_.Formalism.BasicNotions.TH.Ix p q → ℚ := fun x =>
    ∑ a, ∑ b, (m a b : ℚ) * ((if x = a then 1 else 0) - if x = b then 1 else 0) with hΔ
  have key : ∑ x, s x * Δ x = ∑ a, ∑ b, (m a b : ℚ) * (s a - s b) := by
    simp only [hΔ, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hnn : 0 ≤ ∑ x, s x * Δ x := by
    rw [key]
    refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
    by_cases h0 : m a b = 0
    · simp [h0]
    · exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.2 (hmono a b (hm a b h0)))
  have habs : ∀ x y : ℚ, ∀ a, s a * (x + y) ≤ |x + y| := by
    intro x y a
    rcases hs a with h | h <;> rw [h]
    · simpa using le_abs_self (x + y)
    · simpa using neg_le_abs (x + y)
  unfold _root_.Formalism.BasicNotions.TH.degW
  calc ∑ a, |_root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a|
      = ∑ a, s a * _root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a := by simp [hsν]
    _ ≤ ∑ a, s a * _root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a + ∑ x, s x * Δ x := le_add_of_nonneg_right hnn
    _ = ∑ a, s a * (_root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a + Δ a) := by
        rw [← Finset.sum_add_distrib]; simp [mul_add]
    _ ≤ ∑ a, |_root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a + Δ a| :=
        Finset.sum_le_sum fun a _ => habs _ _ a
    _ = ∑ a, |_root_.Formalism.BasicNotions.TH.shiftNu c (fun x => _root_.Formalism.BasicNotions.TH.blattner lam x + Δ x) a| := by
        simp [shiftNu_add_right]


open MvPolynomial in
theorem _root_.GlobalTheory.FlowLemma.degW_blattner_le (p q : ℕ) (M : _root_.Formalism.BasicNotions.TH.GKMod p q) (lam : _root_.Formalism.BasicNotions.TH.Ix p q → ℚ)
    (c θ : ℚ)
    (hC : _root_.GlobalTheory.FockAlg.ConeTypes M lam)
    (hs : ∀ a, (θ < lam a → 0 ≤ _root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a) ∧
      (lam a ≤ θ → _root_.Formalism.BasicNotions.TH.shiftNu c (_root_.Formalism.BasicNotions.TH.blattner lam) a ≤ 0))
    (μ : _root_.Formalism.BasicNotions.TH.Ix p q → ℚ) (v : M.V) (hv : _root_.Formalism.BasicNotions.TH.IsHW M.act μ v) :
    _root_.Formalism.BasicNotions.TH.degW c (_root_.Formalism.BasicNotions.TH.blattner lam) ≤ _root_.Formalism.BasicNotions.TH.degW c μ := by
  refine degW_blattner_le_of_sign_lemma M lam c hC (fun a => if θ < lam a then 1 else -1)
    (fun a => ?_) (fun a => ?_) (fun a b hab => ?_) μ v hv
  · split_ifs <;> simp
  · split_ifs with h
    · simp [abs_of_nonneg ((hs a).1 h)]
    · simp [abs_of_nonpos ((hs a).2 (not_lt.1 h))]
  · beta_reduce
    split_ifs with h1 h2 h2 <;> first | exact absurd (h1.trans hab) h2 | norm_num

end GlobalTheory.FlowLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbRegOfIsBaseChange
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module

namespace GlobalTheory.BadCount

theorem embReg_of_isBaseChange : ∀ (K L Γ V W : Type) [Field K] [Field L] [Algebra K L] [Group Γ] [Finite Γ] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [Module L W] [IsScalarTower K L W] (f : V →ₗ[K] W), IsBaseChange L f → ∀ (ρ : Representation K Γ V) (ρ' : Representation L Γ W), (∀ g v, ρ' g (f v) = f (ρ g v)) → ∀ (H : Subgroup Γ) (n : ℕ), EmbReg ρ H n → EmbReg ρ' H n := by
  intro K L Γ V W _ _ _ _ _ _ _ _ _ _ _ f hf ρ ρ' hρ H n hE
  obtain ⟨j, hj, hje⟩ := hE
  let eK : MonoidAlgebra K H ≃ₗ[K] (H →₀ K) := MonoidAlgebra.coeffLinearEquiv K
  let eL : MonoidAlgebra L H ≃ₗ[L] (H →₀ L) := MonoidAlgebra.coeffLinearEquiv L
  let m0 : (H →₀ K) →ₗ[K] (H →₀ L) := Finsupp.mapRange.linearMap (Algebra.linearMap K L)
  let φ0 : MonoidAlgebra K H →ₗ[K] MonoidAlgebra L H :=
    (eL.restrictScalars K).symm.toLinearMap ∘ₗ m0 ∘ₗ eK.toLinearMap
  have h0 : IsBaseChange L φ0 := by
    refine (IsBaseChange.iff_of_equiv_comm eK eL (f' := m0) ?_).mpr
      (IsBaseChange.finsuppPow H (IsBaseChange.linearMap K L))
    exact LinearMap.ext fun x => (eL.apply_symm_apply (m0 (eK x))).symm
  have hφ0 : ∀ x, φ0 x = MonoidAlgebra.mapRingHom H (algebraMap K L) x := by
    intro x
    ext g
    simp [φ0, eK, eL, m0]
  let φ : (Fin n → MonoidAlgebra K H) →ₗ[K] (Fin n → MonoidAlgebra L H) := φ0.compLeft (Fin n)
  have hφ : IsBaseChange L φ := IsBaseChange.finitePow (Fin n) h0
  obtain ⟨p, hp⟩ := LinearMap.exists_leftInverse_of_injective j (LinearMap.ker_eq_bot.mpr hj)
  let j' : W →ₗ[L] (Fin n → MonoidAlgebra L H) := hf.lift (φ ∘ₗ j)
  have hj'f : ∀ v, j' (f v) = φ (j v) := fun v => hf.lift_eq _ v
  let P : (Fin n → MonoidAlgebra L H) →ₗ[L] W := hφ.lift (f ∘ₗ p)
  have hPj : ∀ w, P (j' w) = w := by
    intro w
    have : P ∘ₗ j' = LinearMap.id := hf.algHom_ext _ _ (fun v => by
      rw [LinearMap.comp_apply, hj'f]
      change hφ.lift (f ∘ₗ p) (φ (j v)) = f v
      rw [hφ.lift_eq, LinearMap.comp_apply, ← LinearMap.comp_apply p j, hp, LinearMap.id_apply])
    exact LinearMap.congr_fun this w
  refine ⟨j', fun a b hab => by rw [← hPj a, ← hPj b, hab], ?_⟩
  intro h w i
  have key : (LinearMap.proj i ∘ₗ j' ∘ₗ (ρ' h)) =
      (LinearMap.mulLeft L (MonoidAlgebra.single h (1 : L)) ∘ₗ LinearMap.proj i ∘ₗ j') := by
    refine hf.algHom_ext _ _ (fun v => ?_)
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.mulLeft_apply, hρ, hj'f]
    change φ0 (j (ρ h v) i) = MonoidAlgebra.single h 1 * φ0 (j v i)
    rw [hje, hφ0, hφ0, map_mul, MonoidAlgebra.mapRingHom_single, map_one]
  exact LinearMap.congr_fun key w

end GlobalTheory.BadCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsInRegularRepresentationCopiesComplexEmbedd
section
open Module NumberField

namespace GlobalTheory.BadCount

theorem semilin_eq_sum {K V : Type} [Field K] [AddCommGroup V] [Module ℂ V] {N : ℕ} {σ : K →+* ℂ}
    (f : (Fin N → K) →ₛₗ[σ] V) (x : Fin N → K) : f x = ∑ k, σ (x k) • f (Pi.single k 1) := by
  conv_lhs => rw [pi_eq_sum_univ' x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smulₛₗ]

theorem top_le_span_single {K V : Type} [Field K] [AddCommGroup V] [Module ℂ V] {N : ℕ} {σ : K →+* ℂ}
    (f : (Fin N → K) →ₛₗ[σ] V) (h : Submodule.span ℂ (Set.range f) = ⊤) :
    ⊤ ≤ Submodule.span ℂ (Set.range fun k => f (Pi.single k 1)) := by
  rw [← h, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  rw [semilin_eq_sum f x]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

theorem embReg_of_semilinear {V V' G : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    [Group G] (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') (τ : ℂ ≃+* ℂ) (T : V' →+ V)
    (hs : ∀ (c : ℂ) v, T (c • v) = τ.symm c • T v) (hi : Function.Injective T)
    (he : ∀ g v, T (ρ' g v) = ρ g (T v)) (H : Subgroup G) (n : ℕ) (h : EmbReg ρ H n) : EmbReg ρ' H n := by
  obtain ⟨j, hj, hje⟩ := h
  let m : MonoidAlgebra ℂ H →+* MonoidAlgebra ℂ H := MonoidAlgebra.mapRingHom H (τ : ℂ →+* ℂ)
  have hm : ∀ x a, (m x).coeff a = τ (x.coeff a) := fun x a => MonoidAlgebra.coeff_mapRingHom _ _ _
  have hmi : Function.Injective m := by
    intro x y hxy
    ext a
    apply τ.injective
    rw [← hm, ← hm, hxy]
  refine ⟨{ toFun := fun v i => m (j (T v) i)
            map_add' := fun v w => ?_
            map_smul' := fun c v => ?_ }, fun v w hvw => ?_, fun g v i => ?_⟩
  · funext i
    simp
  · funext i
    ext a
    simp [hs, hm]
  · exact hi (hj (funext fun i => hmi (congrFun hvw i)))
  · show m (j (T (ρ' g v)) i) = _ * m (j (T v) i)
    rw [he, hje, map_mul]
    congr 1
    exact (MonoidAlgebra.mapRingHom_single _ _ _).trans (by rw [map_one])

theorem embReg_of_baseChange : ∀ (K V V' G : Type) [Field K] [NumberField K] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [Group G] [Finite G] (N : ℕ) (ρK : Representation K G (Fin N → K))
    (σ σ' : K →+* ℂ) (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') (f : (Fin N → K) →ₛₗ[σ] V)
    (f' : (Fin N → K) →ₛₗ[σ'] V'), (LinearIndependent ℂ fun k => f (Pi.single k 1)) →
    Submodule.span ℂ (Set.range f) = ⊤ → (LinearIndependent ℂ fun k => f' (Pi.single k 1)) →
    Submodule.span ℂ (Set.range f') = ⊤ → (∀ g v, ρ g (f v) = f (ρK g v)) →
    (∀ g v, ρ' g (f' v) = f' (ρK g v)) → ∀ (H : Subgroup G) (n : ℕ),
    GlobalTheory.BadCount.EmbReg ρ H n → GlobalTheory.BadCount.EmbReg ρ' H n := by
  intro K V V' G _ _ _ _ _ _ _ _ N ρK σ σ' ρ ρ' f f' hl _ hl' hsp' he he' H n h
  haveI : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq K σ σ'
  let b' : Basis (Fin N) ℂ V' := Basis.mk hl' (top_le_span_single f' hsp')
  have hb' : ∀ k, b' k = f' (Pi.single k 1) := fun k => Basis.mk_apply _ _ k
  let T : V' →+ V :=
    { toFun := fun v => ∑ k, τ.symm (b'.repr v k) • f (Pi.single k 1)
      map_zero' := by simp
      map_add' := fun v w => by simp [add_smul, Finset.sum_add_distrib] }
  have hT : ∀ v, T v = ∑ k, τ.symm (b'.repr v k) • f (Pi.single k 1) := fun _ => rfl
  have hs : ∀ (c : ℂ) v, T (c • v) = τ.symm c • T v := fun c v => by
    simp [hT, Finset.smul_sum, mul_smul]
  have hTf : ∀ x, T (f' x) = f x := fun x => by
    have hr : ∀ k, b'.repr (f' x) k = σ' (x k) := fun k => by
      rw [semilin_eq_sum f' x]
      simp only [← hb']
      exact congrFun (b'.repr_sum_self _) k
    rw [hT, semilin_eq_sum f x]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hr, ← hτ, RingEquiv.symm_apply_apply]
  refine embReg_of_semilinear ρ ρ' τ T hs ?_ (fun g v => ?_) H n h
  · rw [injective_iff_map_eq_zero]
    intro v hv
    rw [hT] at hv
    have h0 := Fintype.linearIndependent_iff.1 hl _ hv
    apply b'.repr.injective
    ext k
    simpa using h0 k
  · have hv : v ∈ Submodule.span ℂ (Set.range f') := hsp' ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, rfl⟩ := hx
      rw [he', hTf, hTf, he]
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy]
    | smul c x _ hx => rw [map_smul, hs, hs, map_smul, hx]

end GlobalTheory.BadCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCocycleCoboundaryIffStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_cocycle_coboundary_iff : ∀ (R : Type) [CommRing R] (F : Shv R) (A : Type) [CommRing A], ∃ γ : ∀ (B : Type) [CommRing B] [Algebra A B], Z1 F A B →+ H R (sp A) F 1, ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.Etale A B] [Module.FaithfullyFlat A B], (∀ u : Z1 F A B, γ B u = 0 ↔ ∃ v : (onRings F).obj (CommRingCat.of B), (u : (onRings F).obj (CommRingCat.of (B ⊗[A] B))) = ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom)).hom v - ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toRingHom)).hom v) ∧ (∀ x : H R (sp A) F 1, pull R (spMap (algebraMap A B)) F 1 x = 0 → ∃ u, γ B u = x) ∧ (∀ u, pull R (spMap (algebraMap A B)) F 1 (γ B u) = 0) ∧ ∀ (B' : Type) [CommRing B'] [Algebra A B'] [Algebra.Etale A B'] [Module.FaithfullyFlat A B'] (φ : B →ₐ[A] B') (u : Z1 F A B) (u' : Z1 F A B'), (u' : (onRings F).obj (CommRingCat.of (B' ⊗[A] B'))) = ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map φ φ).toRingHom)).hom u → γ B' u' = γ B u := by
  first | (exact @GlobalTheory.CechOne.cech1) | (exact GlobalTheory.CechOne.cech1) | (intros; apply GlobalTheory.CechOne.cech1  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBaseChangeCechAugmentaStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomologyEquivalence_baseChange_cechAugmentation : ∀ (R : Type) [CommRing R] (F : Shv R) (S W V : Scheme.{0}) (r : W ⟶ S) (f : V ⟶ W), Etale f → Surjective f → ∀ U : Over S, Eqv R ((bcMap (cechAug f) (sch.map r)).app U) F := by
  first | (exact @GlobalTheory.EtC.bc_cechAug_eqv) | (exact GlobalTheory.EtC.bc_cechAug_eqv) | (intros; apply GlobalTheory.EtC.bc_cechAug_eqv  <;> assumption)
end

