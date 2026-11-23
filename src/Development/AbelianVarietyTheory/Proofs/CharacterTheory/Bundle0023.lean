module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.IrreducibleOfVirtualCharacterNormOne
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.BI

theorem finsupp_eq_single_of_sum_sq_eq_one {α : Type} (c : α →₀ ℤ)
    (h : (c.sum fun _ m => m ^ 2) = 1) :
    ∃ a, c.support = {a} ∧ (c a = 1 ∨ c a = -1) := by
  simp only [Finsupp.sum] at h
  have hge : ∀ b ∈ c.support, (1 : ℤ) ≤ c b ^ 2 := by
    intro b hb
    have hb' : c b ≠ 0 := Finsupp.mem_support_iff.mp hb
    rcases lt_or_gt_of_ne hb' with hlt | hgt <;> nlinarith
  have hle : (c.support.card : ℤ) ≤ 1 := by
    calc (c.support.card : ℤ) = ∑ _b ∈ c.support, (1 : ℤ) := by simp
      _ ≤ ∑ b ∈ c.support, c b ^ 2 := Finset.sum_le_sum hge
      _ = 1 := h
  have hne : c.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he, Finset.sum_empty] at h
    exact zero_ne_one h
  have hcard : c.support.card = 1 := by
    have := hne.card_pos
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  refine ⟨a, ha, ?_⟩
  rw [ha, Finset.sum_singleton] at h
  have h1 : c a ≤ 1 := by nlinarith
  have h2 : -1 ≤ c a := by nlinarith
  have h3 : c a ≠ 0 := by
    intro h0
    rw [h0] at h
    norm_num at h
  omega

private theorem exists_pos_nat_apply_one_of_isIrrChar {G : Type} [Group G] (χ : G → ℂ) (h : IsIrrChar ℂ ℂ χ) :
    ∃ n : ℕ, 0 < n ∧ χ 1 = n := by
  obtain ⟨n, ρ, hρ, hχ⟩ := h
  refine ⟨n, ?_, ?_⟩
  · have hs : IsSimpleModule (MonoidAlgebra ℂ G) ρ.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hρ
    have hnt : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) _
    rcases Nat.eq_zero_or_pos n with h0 | hn
    · exfalso
      subst h0
      obtain ⟨x, y, hxy⟩ := hnt
      exact hxy (Subsingleton.elim (α := Fin 0 → ℂ) x y)
    · exact hn
  · rw [hχ, Representation.char_one]
    simp

theorem irr_of_norm_one : ∀ (G : Type) [Group G] [Finite G] (φ : G → ℂ), φ ∈ Virt ℂ ℂ G → ∑ᶠ g, φ g * star (φ g) = (Nat.card G : ℂ) → (IsIrrChar ℂ ℂ φ ∨ IsIrrChar ℂ ℂ (-φ)) ∧ (IsChar ℂ ℂ φ → IsIrrChar ℂ ℂ φ ∧ ∃ n : ℕ, 0 < n ∧ φ 1 = n) := by
  intro G _ _ φ hφ hnorm
  obtain ⟨c, hirr, hsum, hsq⟩ := _root_.GlobalTheory.BI.virt_expand G φ hφ
  have hG : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have h1 : (c.sum fun _ m => (m : ℂ) ^ 2) = 1 :=
    mul_right_cancel₀ hG ((hsq.symm.trans hnorm).trans (one_mul _).symm)
  have h2 : (c.sum fun _ m => m ^ 2) = 1 := by
    simp only [Finsupp.sum] at h1 ⊢
    exact_mod_cast h1
  obtain ⟨χ, hsupp, hc⟩ := finsupp_eq_single_of_sum_sq_eq_one c h2
  have hχ : IsIrrChar ℂ ℂ χ := hirr χ (by rw [hsupp]; exact Finset.mem_singleton_self χ)
  have hφχ : φ = c χ • χ := by
    rw [hsum, Finsupp.sum, hsupp, Finset.sum_singleton]
  have key : φ = χ ∨ φ = -χ := by
    rcases hc with h | h
    · left
      rw [hφχ, h, one_smul]
    · right
      rw [hφχ, h, neg_smul, one_smul]
  obtain ⟨n, hn, hn1⟩ := exists_pos_nat_apply_one_of_isIrrChar χ hχ
  rcases key with rfl | rfl
  · exact ⟨Or.inl hχ, fun _ => ⟨hχ, n, hn, hn1⟩⟩
  · refine ⟨Or.inr (by simpa using hχ), fun hc' => ?_⟩
    exfalso
    obtain ⟨-, -, m, hm, -⟩ := GlobalTheory.isChar_restrict_conj_one ℂ ℂ G (-χ) hc'
    have h3 : ((m + n : ℕ) : ℂ) = 0 := by
      push_cast
      rw [← hm, ← hn1, Pi.neg_apply]
      ring
    have h4 : m + n = 0 := by exact_mod_cast h3
    omega

end GlobalTheory.BI
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CharacterTheory.OneMemVirtualCharactersOfIntegralCombination
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.BI

theorem one_mem_of_integral_combination : ∀ (G : Type) [Group G] [Finite G] (S : AddSubgroup (G → ℂ)), S ≤ Virt ℂ ℂ G → ∀ (ι : Type) [Fintype ι] (r : ι → ℂ) (s : ι → G → ℂ), (∀ i, IsIntegral ℤ (r i)) → (∀ i, s i ∈ S) → (∀ g, ∑ i, r i * s i g = 1) → (1 : G → ℂ) ∈ S := by
  intro G _ _ S hS ι _ r s hr hs hsum
  classical
  have := Fintype.ofFinite G
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.CuspGL.exists_int_retraction_of_isIntegral ι r hr
  have hone : (1 : G → ℂ) ∈ Virt ℂ ℂ G := AddSubgroup.subset_closure (isChar_one ℂ ℂ G)
  have hcomb : (∑ i, c i • s i) ∈ S := S.sum_mem fun i _ => S.zsmul_mem (hs i) (c i)
  set f : G → ℂ := (∑ i, c i • s i) - 1 with hf
  have hfV : f ∈ Virt ℂ ℂ G := (Virt ℂ ℂ G).sub_mem (hS hcomb) hone
  have hN : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := G)).ne'
  choose m hm using fun i => _root_.GlobalTheory.BI.finsum_mul_star_virt_int G (s i) f (hS (hs i)) hfV
  obtain ⟨d, hd⟩ := _root_.GlobalTheory.BI.finsum_mul_star_virt_int G 1 f hone hfV
  simp only [finsum_eq_sum_of_fintype] at hm hd
  have h1 : ∑ i, r i * (m i : ℂ) = d := by
    apply mul_right_cancel₀ hN
    rw [← hd, Finset.sum_mul]
    simp only [mul_assoc, ← hm, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [← mul_assoc, ← Finset.sum_mul, hsum g, Pi.one_apply]
  have h2 : ∑ i, (c i : ℂ) * (m i : ℂ) = d := by exact_mod_cast hc m d h1
  have hfg : ∀ g, f g = ∑ i, (c i : ℂ) * s i g - 1 := by
    intro g
    simp [hf, Finset.sum_apply]
  have h3 : ∑ g, f g * star (f g) = 0 := by
    have e : ∀ g, f g * star (f g) = ∑ i, (c i : ℂ) * (s i g * star (f g)) - (1 : G → ℂ) g * star (f g) := by
      intro g
      conv_lhs => enter [1]; rw [hfg g]
      simp only [sub_mul, Finset.sum_mul, mul_assoc, Pi.one_apply]
    simp only [e, Finset.sum_sub_distrib]
    rw [Finset.sum_comm, hd, ← h2, Finset.sum_mul, sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, hm, mul_assoc]
  have h4 : ∑ g, Complex.normSq (f g) = 0 := by
    have : ((∑ g, Complex.normSq (f g) : ℝ) : ℂ) = 0 := by
      rw [← h3]; push_cast
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [← Complex.mul_conj]; rfl
    exact_mod_cast this
  have h5 : f = 0 := by
    funext g
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun g _ => Complex.normSq_nonneg (f g))).1 h4 g (Finset.mem_univ g)
    exact Complex.normSq_eq_zero.1 this
  have : (∑ i, c i • s i) = 1 := sub_eq_zero.1 (hf.symm.trans h5)
  exact this ▸ hcomb
end GlobalTheory.BI
end

