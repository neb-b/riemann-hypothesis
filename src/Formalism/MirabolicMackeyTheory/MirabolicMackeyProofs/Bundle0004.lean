module

public import Mathlib
public import Formalism.MirabolicMackeyTheory.Bundle0003
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.Bundle0003
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0005
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0003
public import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.IdxRules
public import Formalism.HermitianLattices.HermitianLatticesProofs.Bundle0001

@[expose] public section

-- bundled from Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.AbsorbLocalConditionsOfExact
section
open Module NumberField IsDedekindDomain

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

theorem primeBoundsExact (Y X2 : ℝ) (hY : 1 < Y) (hX2 : 0 < X2) :
    (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ Y) →
      ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ≤ Real.log Y) ∧
    (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ Y) → ∑ p ∈ Q, Real.log (p : ℝ) ≤ Real.log 4 * Y) ∧
    (∀ Q : Finset ℕ, (∀ p ∈ Q, p.Prime ∧ X2 < (p : ℝ)) →
      ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 2.04 / X2) :=
  ⟨_root_.sum_log_p_over_p Y hY, chebyshev_theta_log_four Y (by linarith),
    _root_.prime_log_over_sq_tail X2 hX2⟩

theorem error_sum_good_places_exact : ErrSumGoodExact := by
  intro PI hPI Y X2 A1 A2 kw T Cth Cadd th add hY hX2 hA1 hA2 hkw hT hth hadd hD
  obtain ⟨hB1, hB2, hB3⟩ := primeBoundsExact Y X2 hY hX2
  obtain ⟨hD1, hD2⟩ := hD
  have hQ : ∀ p ∈ PI.filter (fun p : ℕ => (p : ℝ) ≤ Y), p.Prime ∧ (p : ℝ) ≤ Y := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact ⟨hPI p hp.1, hp.2⟩
  have hQ' : ∀ p ∈ PI.filter (fun p : ℕ => (p : ℝ) ≤ Y), p.Prime := fun p hp => (hQ p hp).1
  have hR : ∀ p ∈ (PI.filter (fun p : ℕ => (p : ℝ) ≤ Y)).filter (fun p : ℕ => X2 < (p : ℝ)),
      p.Prime ∧ X2 < (p : ℝ) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    exact ⟨(hQ p hp.1).1, hp.2⟩
  have e1 := hB1 _ hQ
  have e2 := hB2 _ hQ
  have e3 := hB3 _ hR
  have e4 := hD1 _ hQ'
  have e5 := hD2 _ hQ'
  rw [Finset.sum_filter] at e1 e2 e4 e5
  rw [Finset.sum_filter, Finset.sum_filter] at e3
  have hsum : ∑ p ∈ PI, Real.log (p : ℝ) * errGood Y X2 A1 A2 kw T th add p =
      2 * A1 * (∑ p ∈ PI, if (p : ℝ) ≤ Y then Real.log (p : ℝ) / (p : ℝ) else 0) +
      2 * kw * (∑ p ∈ PI, if (p : ℝ) ≤ Y then th p * Real.log (p : ℝ) else 0) +
      2 * (T * ∑ p ∈ PI, if (p : ℝ) ≤ Y then add p * Real.log (p : ℝ) else 0) +
      2 * A2 * (∑ p ∈ PI, if (p : ℝ) ≤ Y then
        (if X2 < (p : ℝ) then Real.log (p : ℝ) / (p : ℝ) ^ 2 else 0) else 0) +
      2 * (∑ p ∈ PI, if (p : ℝ) ≤ Y then Real.log (p : ℝ) else 0) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    unfold errGood
    split_ifs <;> ring
  rw [hsum]
  have h1 := mul_le_mul_of_nonneg_left e1 hA1
  have h2 := mul_le_mul_of_nonneg_left e4 hkw
  have h4 := mul_le_mul_of_nonneg_left e3 hA2
  have h4' : A2 * (2.04 / X2) = 2.04 * A2 / X2 := by ring
  linarith

theorem onSumExact_of (hP : PlaceSum) (hR : RamBasic) (hE : ErrSumGoodExact) : OnSumExact := by
  intro K _ _ _ S Bad eb heb Y X2 A1 A2 kw T Cth Cadd th add hY hX2 hA1 hA2 hkw hT hth hadd hD errl herr
  have hG : ∀ p : ℕ, 0 ≤ errGood Y X2 A1 A2 kw T th add p := by
    intro p
    have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    unfold errGood
    split_ifs <;>
      linarith [div_nonneg hA1 hp, mul_nonneg hkw (hth p), mul_nonneg hT (hadd p),
        div_nonneg hA2 (pow_nonneg hp 2)]
  have hX : ∀ p : ℕ, 0 ≤ (if p ∈ Bad then eb p else errGood Y X2 A1 A2 kw T th add p) := by
    intro p
    split_ifs
    · exact heb p
    · exact hG p
  have step1 : ∑ w ∈ S, lw w * ((ramw w : ℝ) * errl w) ≤
      ∑ w ∈ S, lw w * ((ramw w : ℝ) *
        (if plc w ∈ Bad then eb (plc w) else errGood Y X2 A1 A2 kw T th add (plc w))) := by
    apply Finset.sum_le_sum
    intro w hw
    have hl : 0 ≤ lw w := by
      unfold lw
      exact div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)
    have hr : (0 : ℝ) ≤ (ramw w : ℝ) :=
      by exact_mod_cast (le_trans zero_le_one (hR K w).2.1)
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (herr w hw) hr) hl
  have step2 := hP K S (fun p => if p ∈ Bad then eb p else errGood Y X2 A1 A2 kw T th add p) hX
  have hprime : ∀ p ∈ S.image plc, p.Prime := by
    intro p hp
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp hp
    exact (hR K w).1
  have hbadpart : ∑ p ∈ S.image plc, (if p ∈ Bad then Real.log (p : ℝ) * eb p else 0) ≤
      ∑ p ∈ Bad, Real.log (p : ℝ) * eb p := by
    have hsub : (S.image plc).filter (fun p => p ∈ Bad) ⊆ Bad := by
      intro p hp
      exact (Finset.mem_filter.mp hp).2
    have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => Real.log (p : ℝ) * eb p) hsub
      (fun p _ _ => mul_nonneg (Real.log_natCast_nonneg p) (heb p))
    rwa [Finset.sum_filter] at h
  have hgoodpart : ∑ p ∈ S.image plc,
      (if p ∉ Bad then Real.log (p : ℝ) * errGood Y X2 A1 A2 kw T th add p else 0) ≤
      2 * (A1 * Real.log Y + kw * Cth + Cadd + 2.04 * A2 / X2 + Real.log 4 * Y) := by
    have h := hE ((S.image plc).filter (fun p => p ∉ Bad))
      (fun p hp => hprime p (Finset.mem_filter.mp hp).1) Y X2 A1 A2 kw T Cth Cadd th add
      hY hX2 hA1 hA2 hkw hT hth hadd hD
    rwa [Finset.sum_filter] at h
  have hsplit : ∑ p ∈ S.image plc, Real.log (p : ℝ) *
        (if p ∈ Bad then eb p else errGood Y X2 A1 A2 kw T th add p) =
      ∑ p ∈ S.image plc, (if p ∈ Bad then Real.log (p : ℝ) * eb p else 0) +
      ∑ p ∈ S.image plc,
        (if p ∉ Bad then Real.log (p : ℝ) * errGood Y X2 A1 A2 kw T th add p else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases h : p ∈ Bad <;> simp [h]
  linarith

theorem local_sum_exact : OnSumExact := onSumExact_of place_sum ramified_basic_bound error_sum_good_places_exact

private theorem lead_exact : LeadExact := by
  intro C L f m b k ws Se Y X2 hC hf hm hb hk hws0 hws hSe hkS hY hlY hYb hX2
  have hl4 : Real.log 4 < 1.3863 := by
    have h := Real.log_two_lt_d9
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    rw [h4]
    linarith
  have hC0 : 0 ≤ C := by linarith
  have hf0 : 0 ≤ f := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hk0 : 0 < k := by linarith
  have hX0 : 0 < X2 := by linarith
  have hY0 : 0 < Y := by linarith
  have hlk : 0 ≤ Real.log k := Real.log_nonneg hk
  have hmb : 0 ≤ m * b := mul_nonneg hm0 hb.le
  have hfb : 0 ≤ f * b := mul_nonneg hf0 hb.le
  have e1 : C * (Real.log k * m * ws) * Real.log Y ≤ C * (Real.log k * m * ws) * (2 * L) :=
    mul_le_mul_of_nonneg_left hlY (mul_nonneg hC0 (mul_nonneg (mul_nonneg hlk hm0) hws0))
  have e2 : C * (f * k * Se) * Real.log Y ≤ C * (f * k * Se) * (2 * L) :=
    mul_le_mul_of_nonneg_left hlY (mul_nonneg hC0 (mul_nonneg (mul_nonneg hf0 hk0.le) hSe))
  have e2b : C * f * (k * Se * L) ≤ C * f * (m * b) :=
    mul_le_mul_of_nonneg_left hkS (mul_nonneg hC0 hf0)
  have e3 : C * k * ws * (C / k) = C ^ 2 * ws := by
    rw [show C * k * ws * (C / k) = C ^ 2 * ws * (k / k) by ring, div_self hk0.ne', mul_one]
  have e3b : C ^ 2 * ws ≤ C ^ 2 * (2 * (f * b)) :=
    mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg C)
  have hfbm : f * b ≤ f * b * m := le_mul_of_one_le_right hfb hm
  have e3c : C ^ 2 * (f * b) ≤ C ^ 2 * (f * b * m) := mul_le_mul_of_nonneg_left hfbm (sq_nonneg C)
  have hmbf : m * b ≤ f * (m * b) := le_mul_of_one_le_left hmb hf
  have e4 : C * (m * b) ≤ C * (f * (m * b)) := mul_le_mul_of_nonneg_left hmbf hC0
  have hCws : 0 ≤ C * ws := mul_nonneg hC0 hws0
  have hkX : k / X2 ≤ 1 := (div_le_one hX0).mpr hX2
  have e5 : C * k * ws / X2 ≤ C * ws := by
    calc C * k * ws / X2 = C * ws * (k / X2) := by ring
      _ ≤ C * ws * 1 := mul_le_mul_of_nonneg_left hkX hCws
      _ = C * ws := mul_one _
  have e5' : 2.04 * (C * k * ws) / X2 ≤ 2.04 * (C * ws) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left e5 (by norm_num)
  have e5b : C * ws ≤ C * (2 * (f * b)) := mul_le_mul_of_nonneg_left (by linarith) hC0
  have e5c : C * (f * b) ≤ C * (f * b * m) := mul_le_mul_of_nonneg_left hfbm hC0
  have e6 : Real.log 4 * Y ≤ 1.3863 * Y := mul_le_mul_of_nonneg_right hl4.le hY0.le
  have hCf : 1 ≤ C * f := one_le_mul_of_one_le_of_one_le hC hf
  have e6b : m * b ≤ C * f * (m * b) := le_mul_of_one_le_left hmb hCf
  have e7 : 0 ≤ C * f * (m * b) := mul_nonneg (mul_nonneg hC0 hf0) hmb
  linarith

theorem absorb_local_conditions_exact : AbsorbOnExact := by
  intro C Cb L xe f m b k ws Se Y X2 bad hC hCb hL hxe hf hm hb hk hlk hws0 hws hSe hkS hY hlY hYb hX2 hbad
  have hlead := lead_exact C L f m b k ws Se Y X2 hC hf hm hb hk hws0 hws hSe hkS hY hlY hYb hX2
  have hC0 : 0 ≤ C := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hf0 : 0 ≤ f := by linarith
  have hZ : 0 ≤ f * m * b := mul_nonneg (mul_nonneg hf0 hm0) hb.le
  have hxe1 : 1 ≤ xe := by linarith
  have hxL : 1 ≤ xe * L := one_le_mul_of_one_le_of_one_le hxe1 hL
  have a1 : Real.log k * (C * L * (m * ws)) ≤ L * (C * L * (m * ws)) :=
    mul_le_mul_of_nonneg_right hlk (mul_nonneg (mul_nonneg hC0 hL0) (mul_nonneg hm0 hws0))
  have a2 : C * L * L * (m * ws) ≤ C * L * L * (m * (2 * f * b)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hws hm0) (mul_nonneg (mul_nonneg hC0 hL0) hL0)
  have a3 : C * (f * m * b) * (L * L) ≤ C * (f * m * b) * (xe * L) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hxe hL0) (mul_nonneg hC0 hZ)
  have hq : 0 ≤ 4 * C ^ 2 + 17 * C := add_nonneg (by positivity) (by linarith)
  have a5 : (4 * C ^ 2 + 17 * C) * (f * m * b) ≤ (4 * C ^ 2 + 17 * C) * (f * m * b) * (xe * L) :=
    le_mul_of_one_le_right (mul_nonneg hq hZ) hxL
  have a6 : Cb * (f * m * b * L) ≤ Cb * (f * m * b * L) * xe :=
    le_mul_of_one_le_right (mul_nonneg hCb (mul_nonneg hZ hL0)) hxe1
  have a7 : 12 * (f * m * b) ≤ 12 * (f * m * b) * (xe * L) :=
    le_mul_of_one_le_right (by linarith) hxL
  linarith

end Formalism.EigenvalueLevelCeiling
end

-- bundled from Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.LocalConditionsWeightedConditional
section
open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues Formalism.HermitianLatticesTheory

section Gen

theorem locLen_congr {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime]
    {A A' C C' : Submodule R W} (hA : localization₂ p A = localization₂ p A') (hC : localization₂ p C = localization₂ p C') :
    locLen p A C = locLen p A' C' := by
  unfold Formalism.HermitianLatticesTheory.locLen
  rw [hA, hC]

private theorem mem_localization_iff_exists_smul_mem {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R)
    [p.IsPrime] (L : Submodule R W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ s ∈ p.primeCompl, s • x ∈ L := Iff.rfl

private theorem locP_locP' {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R)
    [p.IsPrime] (A : Submodule R W) :
    Formalism.HermitianLatticesTheory.localization₂ p (Formalism.HermitianLatticesTheory.localization₂ p A) = Formalism.HermitianLatticesTheory.localization₂ p A := by
  ext x
  rw [mem_localization_iff_exists_smul_mem, mem_localization_iff_exists_smul_mem]
  constructor
  · rintro ⟨s, hs, h⟩
    rw [mem_localization_iff_exists_smul_mem] at h
    obtain ⟨t, ht, h⟩ := h
    exact ⟨t * s, p.primeCompl.mul_mem ht hs, by rw [mul_smul]; exact h⟩
  · intro hx
    exact ⟨1, p.primeCompl.one_mem, by rw [one_smul, mem_localization_iff_exists_smul_mem]; exact hx⟩

private theorem locP_inf' {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R)
    [p.IsPrime] (A B : Submodule R W) :
    Formalism.HermitianLatticesTheory.localization₂ p (A ⊓ B) = Formalism.HermitianLatticesTheory.localization₂ p A ⊓ Formalism.HermitianLatticesTheory.localization₂ p B := by
  ext x
  rw [Submodule.mem_inf, mem_localization_iff_exists_smul_mem, mem_localization_iff_exists_smul_mem, mem_localization_iff_exists_smul_mem]
  constructor
  · rintro ⟨s, hs, h⟩
    rw [Submodule.mem_inf] at h
    exact ⟨⟨s, hs, h.1⟩, ⟨s, hs, h.2⟩⟩
  · rintro ⟨⟨s, hs, h1⟩, ⟨t, ht, h2⟩⟩
    refine ⟨t * s, p.primeCompl.mul_mem ht hs, Submodule.mem_inf.mpr ⟨?_, ?_⟩⟩
    · rw [mul_smul]
      exact A.smul_mem t h1
    · rw [mul_comm, mul_smul]
      exact B.smul_mem s h2

theorem lidx_locP {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R) [p.IsPrime]
    (A B : Submodule R W) : lidx p A B = lidx p (localization₂ p A) (localization₂ p B) := by
  have e1 := locP_locP' p A
  have e3 := locP_locP' p B
  have e2 : Formalism.HermitianLatticesTheory.localization₂ p (Formalism.HermitianLatticesTheory.localization₂ p A ⊓ Formalism.HermitianLatticesTheory.localization₂ p B) = Formalism.HermitianLatticesTheory.localization₂ p (A ⊓ B) := by
    rw [locP_inf', locP_locP', locP_locP', locP_inf']
  unfold Formalism.HermitianLatticesTheory.lidx
  rw [locLen_congr p e1.symm e2.symm, locLen_congr p e3.symm e2.symm]

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem lix_locP {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] (w : HeightOneSpectrum (𝓞 K))
    (A B : Submodule (𝓞 K) Z) :
    lix w A B = lix w (localization₂ w.asIdeal A) (localization₂ w.asIdeal B) := by
  unfold lix
  exact lidx_locP _ A B

theorem locP {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z]
    (w : HeightOneSpectrum (𝓞 K)) (A X₃ X₄ : Submodule (𝓞 K) Z)
    (h : localization₂ w.asIdeal X₃ ≤ localization₂ w.asIdeal X₄) :
    lix w A (X₃ ⊓ X₄) = lix w A X₃ := by
  rw [lix_locP w A (X₃ ⊓ X₄), lix_locP w A X₃, locP_inf', inf_eq_left.mpr h]

end Gen

theorem local_conditions_weighted_at_place : LocalConditionsWeightedAtPlace := by
  intro K _ _ _ Z _ _ _ _ _ w P _ _ ρ U ψ hMk V₀ e he hr M Th1 Th ThK Th0 ThJ X₃ hM hTh1 hTh hThK h1le hle hFG hEig
    hMs hTs σ hσ hsc hdata a E r ha hE hT0 h0 hJ h0J h3 X _ _ _ _ θ' eX pr Mt hc hpr h4 h34 ε hTW d φ hinj hrng
    Mj Tj hMj hTj
  exact local_conditions_weighted K Z w P ρ U ψ hMk V₀ e he hr M Th1 Th ThK Th0 ThJ
    (X₃ ⊓ (Mt.map (θ'.restrictScalars (𝓞 K))).map (e.restrictScalars (𝓞 K)))
    hM hTh1 hTh hThK h1le hle hFG hEig hMs hTs σ hσ hsc hdata a E r ha hE hT0 h0 hJ h0J
    (idxRules_inf_lat h3 h4) X θ' eX pr Mt hc hpr h4 inf_le_right ε
    (by rw [locP w _ _ _ h34]; exact hTW) d φ hinj hrng Mj Tj hMj hTj

section Instance

variable (K : Type) [Field K] [NumberField K] [StarRing K]

end Instance

end Formalism.EigenvalueLevelCeiling
end
end

