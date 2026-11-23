module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0193
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0052
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0198
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0188

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLimitRep
section
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.Cong

theorem exists_limit_rep : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (J : Type) (x : J → Γ), DenseRange x → ∀ (θ : J → PadicAlgCl l) (L : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] L → (∀ j, θ j ∈ L) → ∀ (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), (∀ ρ ∈ C, Continuous ρ) → PolyApprox θ ((fun ρ j => trc ρ (x j)) '' C) → ∃ r : Γ →* GL (Fin a) (PadicAlgCl l), Continuous r ∧ IsSSRep r ∧ (∀ j, trc r (x j) = θ j) ∧ PolyApprox (trc r) (trc '' C) := by
  intro l _ Γ _ _ _ _ a J x hx θ L hL hθL C hC hA
  have hU := _root_.GlobalTheory.polyApprox_trc_locally_cauchy l Γ a J x θ C hC hA
  obtain ⟨T, hTc, hTx⟩ := GlobalTheory.Cong.extend_of_locallyCauchy l Γ J x hx θ L hL hθL hU
  have hA' : PolyApprox (fun j => T (x j)) ((fun ρ j => trc ρ (x j)) '' C) := by
    have : (fun j => T (x j)) = θ := funext hTx
    rw [this]; exact hA
  have hT : PolyApprox T (trc '' C) := GlobalTheory.Cong.polyApprox_of_denseRange l Γ a J x hx T hTc C hC hA'
  have hP : IsPsChar a T := _root_.GlobalTheory.PsChar.isPsChar_of_polyApprox_trc l Γ a T C hT
  obtain ⟨r, hr, htr⟩ := GlobalTheory.PsChar.exists_ssRep Γ (PadicAlgCl l) a T hP
  have htrc : trc r = T := funext fun g => htr g
  refine ⟨r, ?_, hr, fun j => by rw [htrc]; exact hTx j, by rw [htrc]; exact hT⟩
  refine GlobalTheory.SSCont.continuous_of_continuous_trace Γ (PadicAlgCl l) a r hr ?_
  have : (fun g => ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)).trace) = T := htrc
  rw [this]; exact hTc

end GlobalTheory.Cong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupMonomialHolderLogConvex
section
noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

variable {l : ℕ} [Fact l.Prime]

theorem gA_teichmuller (ρ : ℝ) (y : Formalism.Per.Fl l) :
    gA l ρ (Formalism.Per.tm y) = ‖((y.untilt : Formalism.Per.OC l) : ℂ_[l])‖ := by
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have h : ∀ n : ℕ, ‖((((Formalism.Per.tm y : Formalism.Per.Ainf l).coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^
      ((1 : ℝ) / (l : ℝ) ^ n) * ρ ^ n = if n = 0 then ‖((y.untilt : Formalism.Per.OC l) : ℂ_[l])‖ else 0 := by
    intro n
    split_ifs with h
    · subst h
      simp
    · rw [WittVector.teichmuller_coeff_pos l y n (Nat.pos_of_ne_zero h), GlobalTheory.GaussSlope.untilt_zero]
      have : (1 : ℝ) / (l : ℝ) ^ n ≠ 0 := by positivity
      simp only [ZeroMemClass.coe_zero, norm_zero, Real.zero_rpow this, zero_mul]
  unfold gA
  simp only [h]
  have hall : ∀ n : ℕ, (if n = 0 then ‖((y.untilt : Formalism.Per.OC l) : ℂ_[l])‖ else 0) ≤
      ‖((y.untilt : Formalism.Per.OC l) : ℂ_[l])‖ := fun n => by split_ifs <;> simp
  exact le_antisymm (ciSup_le hall)
    (le_ciSup_of_le (f := fun n : ℕ => if n = 0 then ‖((y.untilt : Formalism.Per.OC l) : ℂ_[l])‖ else 0)
      ⟨_, Set.forall_mem_range.2 hall⟩ 0 (by simp))

theorem isGauss_unit_eq_one {ρ : ℝ} (hρ : 0 < ρ) {N : Formalism.Per.Acris l → ℝ} (hN : IsGauss l ρ N)
    {x : Formalism.Per.Acris l} (hx : IsUnit x) : N x = 1 := by
  obtain ⟨h01, -, -, hmul, halg⟩ := hN
  have hl : N (l : Formalism.Per.Acris l) = ρ := by
    rw [← map_natCast (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)) l, halg]
    exact GlobalTheory.GaussSlope.gauss_l l hρ.le
  have h1 : N 1 = 1 := by
    have := hmul (l : Formalism.Per.Acris l) 1
    rw [mul_one, hl] at this
    exact (mul_left_cancel₀ hρ.ne' (this.symm.trans (mul_one ρ).symm))
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  have h2 := hmul x y
  rw [hy, h1] at h2
  refine le_antisymm (h01 x).2 ?_
  rw [h2]
  exact mul_le_of_le_one_right (h01 x).1 (h01 y).2

theorem gC_basic_values : ∀ (l : ℕ) [Fact l.Prime] (ρ : ℝ), (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ 1 = 1 ∧ gC l ρ (l : Formalism.Per.Acris l) = ρ ∧ (∀ c : ℤ_[l], c ≠ 0 → gC l ρ (zc l c) = ρ ^ c.valuation) ∧ (∀ y : Formalism.Per.Fl l, gC l ρ (tc l y) = ‖(((y).untilt : Formalism.Per.OC l) : ℂ_[l])‖) ∧ ∀ a : Formalism.Per.Ainf l, IsUnit a → gC l ρ (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a) = 1 := by
  intro l _ ρ h0 h1
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hρ : 0 < ρ := (inv_pos.2 hl0).trans_le h0
  have hN := isGauss_gC_of_le l ρ h0 h1
  have hl : gC l ρ (l : Formalism.Per.Acris l) = ρ := by
    rw [← map_natCast (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)) l, hN.2.2.2.2]
    exact GlobalTheory.GaussSlope.gauss_l l hρ.le
  refine ⟨isGauss_unit_eq_one hρ hN isUnit_one, hl, fun c hc => ?_, fun y => ?_,
    fun a ha => isGauss_unit_eq_one hρ hN (ha.map _)⟩
  · have e : zc l c = (l : Formalism.Per.Acris l) ^ c.valuation * zc l (PadicInt.unitCoeff hc : ℤ_[l]) := by
      conv_lhs => rw [PadicInt.unitCoeff_spec hc]
      rw [map_mul, map_pow, map_natCast, mul_comm]
    rw [e, GlobalTheory.GaussSlope.map_pow_mul _ hN.2.2.2.1, hl,
      isGauss_unit_eq_one hρ hN ((PadicInt.unitCoeff hc).isUnit.map (zc l)), mul_one]
  · rw [tc, hN.2.2.2.2, gA_teichmuller]

end GlobalTheory.PMon.Gauss

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupPowEqPowISupNonneg
section
noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

namespace Lead

theorem mono_lt {a C ρ₁ ρ₂ ρ : ℝ} {n : ℕ} {e : ℤ} (h1 : 0 < ρ₁) (hl : ρ₁ < ρ) (hr : ρ < ρ₂) (ha : 0 < a)
    (hne : (n : ℤ) ≠ e) (b1 : a * ρ₁ ^ n ≤ C * ρ₁ ^ e) (b2 : a * ρ₂ ^ n ≤ C * ρ₂ ^ e) :
    a * ρ ^ n < C * ρ ^ e := by
  have hρ : 0 < ρ := h1.trans hl
  have hρ2 : 0 < ρ₂ := hρ.trans hr
  set d : ℤ := (n : ℤ) - e with hd
  have key : ∀ t : ℝ, 0 < t → a * t ^ n = t ^ e * (a * t ^ d) := by
    intro t ht
    rw [← zpow_natCast, show (n : ℤ) = e + d by omega, zpow_add₀ ht.ne']
    ring
  have red : ∀ t : ℝ, 0 < t → a * t ^ n ≤ C * t ^ e → a * t ^ d ≤ C := by
    intro t ht h
    rw [key t ht, mul_comm C] at h
    exact le_of_mul_le_mul_left h (zpow_pos ht e)
  rw [key ρ hρ, mul_comm C]
  refine mul_lt_mul_of_pos_left ?_ (zpow_pos hρ e)
  rcases lt_or_gt_of_ne (show d ≠ 0 by omega) with hneg | hpos
  · have c1 := red ρ₁ h1 b1
    refine lt_of_lt_of_le (mul_lt_mul_of_pos_left ?_ ha) c1
    have e1 : ρ ^ d = (ρ ^ (-d))⁻¹ := by rw [zpow_neg, inv_inv]
    have e2 : ρ₁ ^ d = (ρ₁ ^ (-d))⁻¹ := by rw [zpow_neg, inv_inv]
    rw [e1, e2]
    exact inv_strictAnti₀ (zpow_pos h1 _) (zpow_lt_zpow_left₀ (by omega) h1.le hl)
  · have c2 := red ρ₂ hρ2 b2
    exact lt_of_lt_of_le (mul_lt_mul_of_pos_left (zpow_lt_zpow_left₀ hpos hρ.le hr) ha) c2

theorem iSup_lt {d : ℕ → ℝ} {ρ T : ℝ} (h0 : ∀ n, 0 ≤ d n) (h1 : ∀ n, d n ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hT : 0 < T) (h : ∀ n, d n * ρ ^ n < T) : (⨆ n, d n * ρ ^ n) < T := by
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hT hρ1
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.range (M + 1)) (fun n => d n * ρ ^ n)
    ⟨0, by simp⟩
  refine lt_of_le_of_lt (ciSup_le fun n => ?_ : (⨆ n, d n * ρ ^ n) ≤ max (d i * ρ ^ i) (ρ ^ M))
    (max_lt (h i) hM)
  by_cases hn : n < M + 1
  · exact le_max_of_le_left (hi n (Finset.mem_range.2 hn))
  · refine le_max_of_le_right ?_
    calc d n * ρ ^ n ≤ 1 * ρ ^ n := by gcongr; exact h1 n
      _ = ρ ^ n := one_mul _
      _ ≤ ρ ^ M := pow_le_pow_of_le_one hρ.le hρ1.le (by omega)

theorem lead (c : ℕ → ℝ) (h0 : ∀ n, 0 ≤ c n) (h1 : ∀ n, c n ≤ 1) {ρ₁ ρ₂ C : ℝ} {e : ℤ} (hρ₁ : 0 < ρ₁)
    (h12 : ρ₁ < ρ₂) (hρ₂ : ρ₂ < 1) (hC : 0 < C) (hs : ∀ ρ ∈ Set.Icc ρ₁ ρ₂, (⨆ n, c n * ρ ^ n) = C * ρ ^ e) :
    ∃ m : ℕ, (m : ℤ) = e ∧ c m = C ∧ ∀ ρ ∈ Set.Ioo ρ₁ ρ₂, ∀ d : ℕ → ℝ, (∀ n, 0 ≤ d n) → (∀ n, d n ≤ c n) →
      d m = 0 → (⨆ n, d n * ρ ^ n) < C * ρ ^ e := by
  have hb : ∀ ρ ∈ Set.Icc ρ₁ ρ₂, ∀ n, c n * ρ ^ n ≤ C * ρ ^ e := by
    intro ρ hρ n
    rw [← hs ρ hρ]
    have hρ0 : 0 ≤ ρ := hρ₁.le.trans hρ.1
    have hρ1 : ρ ≤ 1 := hρ.2.trans hρ₂.le
    refine le_ciSup (f := fun n => c n * ρ ^ n) ⟨1, Set.forall_mem_range.2 fun n => ?_⟩ n
    calc c n * ρ ^ n ≤ 1 * 1 := mul_le_mul (h1 n) (pow_le_one₀ hρ0 hρ1) (pow_nonneg hρ0 _) zero_le_one
      _ = 1 := one_mul 1
  have B : ∀ ρ ∈ Set.Ioo ρ₁ ρ₂, ∀ d : ℕ → ℝ, (∀ n, 0 ≤ d n) → (∀ n, d n ≤ c n) →
      (∀ n : ℕ, (n : ℤ) = e → d n < C) → (⨆ n, d n * ρ ^ n) < C * ρ ^ e := by
    intro ρ hρ d hd0 hdc hde
    have hρ0 : 0 < ρ := hρ₁.trans hρ.1
    have hρ1 : ρ < 1 := hρ.2.trans hρ₂
    refine iSup_lt hd0 (fun n => (hdc n).trans (h1 n)) hρ0 hρ1 (mul_pos hC (zpow_pos hρ0 e)) fun n => ?_
    by_cases hn : (n : ℤ) = e
    · rw [← hn, zpow_natCast]
      exact mul_lt_mul_of_pos_right (hde n hn) (pow_pos hρ0 n)
    · rcases (h0 n).eq_or_lt with hc | hc
      · have : d n = 0 := le_antisymm (hc ▸ hdc n) (hd0 n)
        rw [this, zero_mul]
        exact mul_pos hC (zpow_pos hρ0 e)
      · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hdc n) (pow_nonneg hρ0.le n))
          (mono_lt hρ₁ hρ.1 hρ.2 hc hn (hb ρ₁ ⟨le_rfl, h12.le⟩ n) (hb ρ₂ ⟨h12.le, le_rfl⟩ n))
  set ρm := (ρ₁ + ρ₂) / 2 with hρm
  have hm : ρm ∈ Set.Ioo ρ₁ ρ₂ := ⟨by rw [hρm]; linarith, by rw [hρm]; linarith⟩
  have hex : ∃ m : ℕ, (m : ℤ) = e ∧ c m = C := by
    by_contra hno
    push_neg at hno
    have hle : ∀ n : ℕ, (n : ℤ) = e → c n ≤ C := by
      intro n hn
      have := hb ρ₁ ⟨le_rfl, h12.le⟩ n
      rw [← hn, zpow_natCast] at this
      exact le_of_mul_le_mul_right this (pow_pos hρ₁ n)
    have := B ρm hm c h0 (fun _ => le_rfl) fun n hn => lt_of_le_of_ne (hle n hn) (hno n hn)
    rw [hs ρm (Set.Ioo_subset_Icc_self hm)] at this
    exact lt_irrefl _ this
  obtain ⟨m, hme, hcm⟩ := hex
  refine ⟨m, hme, hcm, fun ρ hρ d hd0 hdc hdm => B ρ hρ d hd0 hdc fun n hn => ?_⟩
  have : n = m := by omega
  subst this
  rw [hdm]
  exact hC

end Lead


open GlobalTheory.GaussSlope in
theorem lead_target : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l) (c ρ₁ ρ₂ : ℝ) (k : ℤ), (l : ℝ)⁻¹ ≤ ρ₁ → ρ₁ < ρ₂ →
    ρ₂ < 1 → 0 < c → (∀ ρ ∈ Set.Icc ρ₁ ρ₂, gC l ρ x = c * ρ ^ k) → ∃ (y : Formalism.Per.Fl l) (j : ℕ), 0 ≤ k + j ∧
    ‖(((y).untilt : Formalism.Per.OC l) : ℂ_[l])‖ = c ∧ ∀ ρ ∈ Set.Ioo ρ₁ ρ₂, gC l ρ ((l : Formalism.Per.Acris l) ^ j * x -
    (l : Formalism.Per.Acris l) ^ (k + j).toNat * tc l y) < ρ ^ j * gC l ρ x := by
  intro l _ x c ρ₁ ρ₂ k hl1 h12 h21 hc hx
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hρ₁ : 0 < ρ₁ := lt_of_lt_of_le (by positivity) hl1
  have hG : ∀ ρ ∈ Set.Icc ρ₁ ρ₂, IsGauss l ρ (gC l ρ) := fun ρ hρ =>
    isGauss_gC_target l ρ (hl1.trans hρ.1) (hρ.2.trans_lt h21)
  have hGl : ∀ ρ ∈ Set.Icc ρ₁ ρ₂, gC l ρ (l : Formalism.Per.Acris l) = ρ := by
    intro ρ hρ
    rw [← map_natCast (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)) l, (hG ρ hρ).2.2.2.2, gA,
      gauss_l l (hρ₁.le.trans hρ.1)]
  have hpm : ∀ ρ ∈ Set.Icc ρ₁ ρ₂, ∀ (n : ℕ) (w : Formalism.Per.Acris l),
      gC l ρ ((l : Formalism.Per.Acris l) ^ n * w) = ρ ^ n * gC l ρ w := by
    intro ρ hρ n w
    rw [map_pow_mul _ (hG ρ hρ).2.2.2.1, hGl ρ hρ]
  have hkb : ∀ ρ ∈ Set.Icc ρ₁ ρ₂, ρ₁ ^ k.toNat ≤ ρ ^ k := by
    intro ρ hρ
    have hρ0 : 0 < ρ := hρ₁.trans_le hρ.1
    rcases k with n | n
    · rw [Int.ofNat_eq_coe, Int.toNat_natCast, zpow_natCast]
      exact pow_le_pow_left₀ hρ₁.le hρ.1 n
    · rw [Int.toNat_negSucc, pow_zero, zpow_negSucc]
      exact (one_le_inv₀ (pow_pos hρ0 _)).2 (pow_le_one₀ hρ0.le (hρ.2.trans h21.le))
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one (mul_pos hc (pow_pos hρ₁ k.toNat)) h21
  have hrb : ∀ ρ ∈ Set.Icc ρ₁ ρ₂, ρ ^ r < c * ρ ^ k := fun ρ hρ =>
    calc ρ ^ r ≤ ρ₂ ^ r := pow_le_pow_left₀ (hρ₁.le.trans hρ.1) hρ.2 r
      _ < c * ρ₁ ^ k.toNat := hr
      _ ≤ c * ρ ^ k := mul_le_mul_of_nonneg_left (hkb ρ hρ) hc.le
  obtain ⟨s, z, hxz⟩ := (GlobalTheory.MemLoc.acris_basic l).2.2.1 x r
  obtain ⟨j, a, ha⟩ := exists_pow_mul_eq l s
  have hjx : (l : Formalism.Per.Acris l) ^ j * x =
      algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a + (l : Formalism.Per.Acris l) ^ (j + r) * z := by
    rw [hxz, mul_add, ha, pow_add, mul_assoc]
  have hzb : ∀ ρ ∈ Set.Icc ρ₁ ρ₂, gC l ρ ((l : Formalism.Per.Acris l) ^ (j + r) * z) < ρ ^ j * (c * ρ ^ k) := by
    intro ρ hρ
    have hρ0 : 0 < ρ := hρ₁.trans_le hρ.1
    rw [hpm ρ hρ, pow_add, mul_assoc]
    refine mul_lt_mul_of_pos_left ?_ (pow_pos hρ0 j)
    exact lt_of_le_of_lt (mul_le_of_le_one_right (pow_nonneg hρ0.le r) ((hG ρ hρ).1 z).2) (hrb ρ hρ)
  set cc : ℕ → ℝ := fun n => ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) with hcc
  have hAn : ∀ ρ ∈ Set.Icc ρ₁ ρ₂, (⨆ n, cc n * ρ ^ n) = c * ρ ^ (k + j) := by
    intro ρ hρ
    have hρ0 : 0 < ρ := hρ₁.trans_le hρ.1
    obtain ⟨e1, e2, e3, e4, e5⟩ := hG ρ hρ
    have h3 : algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a =
        (l : Formalism.Per.Acris l) ^ j * x + -((l : Formalism.Per.Acris l) ^ (j + r) * z) := by rw [hjx]; ring
    have h4 : gC l ρ (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a) = ρ ^ j * (c * ρ ^ k) := by
      rw [h3, add_eq_of_lt _ e2 e3 (by rw [e3, hpm ρ hρ j x, hx ρ hρ]; exact hzb ρ hρ), hpm ρ hρ, hx ρ hρ]
    rw [e5, gA] at h4
    rw [h4, zpow_add₀ hρ0.ne', zpow_natCast]
    ring
  have hc1 : ∀ n, cc n ≤ 1 := fun n =>
    Real.rpow_le_one (norm_nonneg _) ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.prop _)) (by positivity)
  obtain ⟨m, hme, hcm, hlt⟩ := Lead.lead cc (fun n => by positivity) hc1 hρ₁ h12 h21 hc hAn
  have hmt : (k + j).toNat = m := by omega
  set y := (iterateFrobeniusEquiv (Formalism.Per.Fl l) l m).symm (a.coeff m) with hy
  have hym : y ^ l ^ m = a.coeff m := by
    rw [← iterateFrobenius_def, ← iterateFrobeniusEquiv_apply, hy, RingEquiv.apply_symm_apply]
  have hnorm : ‖((y.untilt : Formalism.Per.OC l) : ℂ_[l])‖ = c := by
    rw [← hcm, hcc]
    simp only
    rw [← hym, map_pow]
    push_cast
    rw [norm_pow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    have : ((l ^ m : ℕ) : ℝ) * (1 / (l : ℝ) ^ m) = 1 := by
      push_cast
      field_simp
    rw [this, Real.rpow_one]
  let b : Formalism.Per.Ainf l := WittVector.mk l fun n => if n = m then 0 else a.coeff n
  have hbc : ∀ n, b.coeff n = if n = m then 0 else a.coeff n := fun n => rfl
  have hab : a = b + Formalism.Per.tm y * (l : Formalism.Per.Ainf l) ^ m := by
    ext n
    rw [WittVector.coeff_add_of_disjoint]
    · by_cases hn : n = m
      · subst hn
        rw [hbc, if_pos rfl, zero_add, WittVector.teichmuller_mul_pow_coeff, hym]
      · rw [hbc, if_neg hn, WittVector.teichmuller_mul_pow_coeff_of_ne _ hn, add_zero]
    · intro n'
      by_cases hn : n' = m
      · left
        rw [hbc, if_pos hn]
      · right
        exact WittVector.teichmuller_mul_pow_coeff_of_ne _ hn
  refine ⟨y, j, by omega, hnorm, fun ρ hρ => ?_⟩
  have hρI : ρ ∈ Set.Icc ρ₁ ρ₂ := Set.Ioo_subset_Icc_self hρ
  have hρ0 : 0 < ρ := hρ₁.trans hρ.1
  obtain ⟨e1, e2, e3, e4, e5⟩ := hG ρ hρI
  have hsplit : (l : Formalism.Per.Acris l) ^ j * x - (l : Formalism.Per.Acris l) ^ (k + j).toNat * tc l y
      = algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) b + (l : Formalism.Per.Acris l) ^ (j + r) * z := by
    rw [hjx, hmt, tc]
    conv_lhs => rw [hab]
    rw [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  let d : ℕ → ℝ := fun n => if n = m then 0 else cc n
  have hbd : ∀ n, ‖(((b.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) = d n := by
    intro n
    by_cases hn : n = m
    · have : (1 : ℝ) / (l : ℝ) ^ n ≠ 0 := by positivity
      simp only [d, hbc, if_pos hn, untilt_zero, ZeroMemClass.coe_zero, norm_zero, Real.zero_rpow this]
    · simp only [d, hbc, if_neg hn, hcc]
  have hbn : gC l ρ (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) b) < ρ ^ j * (c * ρ ^ k) := by
    rw [e5, gA]
    simp_rw [hbd]
    refine lt_of_lt_of_le (hlt ρ hρ d (fun n => ?_) (fun n => ?_) (by simp [d])) (le_of_eq ?_)
    · by_cases hn : n = m
      · simp [d, hn]
      · simp only [d, if_neg hn]
        positivity
    · by_cases hn : n = m
      · simp only [d, if_pos hn]
        positivity
      · simp only [d, if_neg hn, le_refl]
    · rw [zpow_add₀ hρ0.ne', zpow_natCast]
      ring
  rw [hsplit, hx ρ hρI]
  exact lt_of_le_of_lt (e2 _ _) (max_lt hbn (hzb ρ hρI))

end GlobalTheory.PMon.Gauss
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KerOfLinApprox
section
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.Cong

theorem ker_of_linApprox : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) (PadicAlgCl l))
    (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), IsSSRep r → LinApprox r C → ∀ s : Γ, (∀ ρ ∈ C, ρ s = 1) → r s = 1 := by
  intro l _ Γ _ a r C hss hC s hs
  have htr : ∀ g, trc r (s * g) = trc r g := by
    intro g
    refine eq_of_forall_dist_le fun ε hε => ?_
    obtain ⟨t, c, ht, hb⟩ := hC (ε / 2) (by positivity)
    have hsum : ∑ ρ ∈ t, c ρ * trc ρ (s * g) = ∑ ρ ∈ t, c ρ * trc ρ g := by
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      simp [trc, map_mul, hs ρ (ht hρ)]
    rw [dist_eq_norm]
    calc ‖trc r (s * g) - trc r g‖
        = ‖(trc r (s * g) - ∑ ρ ∈ t, c ρ * trc ρ (s * g)) - (trc r g - ∑ ρ ∈ t, c ρ * trc ρ g)‖ := by
          rw [hsum]; congr 1; ring
      _ ≤ ‖trc r (s * g) - ∑ ρ ∈ t, c ρ * trc ρ (s * g)‖ + ‖trc r g - ∑ ρ ∈ t, c ρ * trc ρ g‖ := norm_sub_le _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add (hb _) (hb _)
      _ = ε := by ring
  set R : Γ → Matrix (Fin a) (Fin a) (PadicAlgCl l) := fun g => ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) with hR
  have hM : R s - 1 ∈ Submodule.span (PadicAlgCl l) (Set.range R) := by
    refine Submodule.sub_mem _ (Submodule.subset_span ⟨s, rfl⟩) ?_
    have : R 1 = 1 := by simp [hR]
    rw [← this]; exact Submodule.subset_span ⟨1, rfl⟩
  have h0 := _root_.GlobalTheory.TrFormNd.eq_zero_of_trace_mul_eq_zero (PadicAlgCl l) Γ a r hss (R s - 1) hM (fun g => by
    have := htr g
    simp only [trc, map_mul, Units.val_mul] at this
    rw [sub_mul, one_mul, Matrix.trace_sub]
    simpa [hR] using sub_eq_zero.2 this)
  ext i j
  have := congrFun (congrFun (sub_eq_zero.1 h0) i) j
  simpa [hR] using this

end GlobalTheory.Cong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapExactMiddleStatement
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exact_map_of_exact : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) (A B C : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin B.m → k) →ₗ[k] (Fin C.m → k)), F.Obj B → IsHom A B f → IsHom B C p → Function.Injective f → Function.Surjective p → Function.Exact f p → ∀ i, Function.Exact (F.map A B f i) (F.map B C p i) := by
  first | exact @GlobalTheory.Models.DFun.map_exact_middle | exact GlobalTheory.Models.DFun.map_exact_middle | (intros; apply GlobalTheory.Models.DFun.map_exact_middle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicityAdditiveExactSequence
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models

theorem sen_eq_sen_pre_add_sen_push : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) (A B C : Ob k G) (f : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin B.m → k) →ₗ[k] (Fin C.m → k)) (N : Lats k n B.m), F.Obj B → IsHom A B f → IsHom B C p → Function.Injective f → Function.Surjective p → Function.Exact f p → ∀ i, IsLat (N i) → CondC ((F.D B).γ i) (N i) → ∀ x, sen ((F.D B).γ i) (N i) x = sen ((F.D A).γ i) (F.pre A B f N i) x + sen ((F.D C).γ i) (F.push B C p N i) x := by
  intro k G _ _ l n _ _ _ R F A B C f p N hB hf hp hfi hps hex i hN hc x
  have hA : F.Obj A := F.obj_sub A B f hf hfi hB
  have hC : F.Obj C := F.obj_quot B C p hp hps hB
  exact GlobalTheory.PhiGam.SenAdd.main R ((F.D B).γ i) ((F.D A).γ i) ((F.D C).γ i) (F.map A B f i) (F.map B C p i)
    ((F.D B).γ_semi i) (F.map_inj A B f hA hB hf hfi i) (F.map_surj B C p hB hC hp hps i)
    (GlobalTheory.Models.DFun.map_exact_middle F A B C f p hB hf hp hfi hps hex i) (F.map_γ A B f hA hB hf i) (F.map_γ B C p hB hC hp i)
    (N i) hN hc x

end GlobalTheory.Models
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenWeightsCloseOfHeightGammaConditions
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Models

theorem sen_near_of_abc : ∀ {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n]
    {R : RingPG k l} (D : ModPG R n (Vc k m)) {r : ℕ} (Dt : TopData n r) (N₁ N₂ : Lats k n m),
    ABC D Dt.w Dt.wst N₁ → ABC D Dt.w Dt.wst N₂ → ∀ i y, sen (D.γ i) (N₂ i) y ≠ 0 →
      ∃ j : ℤ, |j| ≤ Dt.sg l i ∧ sen (D.γ i) (N₁ i) (y + j) ≠ 0 := by
  intro k _ l n m _ _ _ R D r Dt N₁ N₂ h₁ h₂ i y hy
  obtain ⟨hL₁, hAB₁, hC₁⟩ := h₁
  obtain ⟨hL₂, hAB₂, hC₂⟩ := h₂
  have e12 := CloseTw.main D Dt.h Dt.w N₁ N₂ hL₁ hL₂ hAB₁ hAB₂ i
  have e21 := CloseTw.main D Dt.h Dt.w N₂ N₁ hL₂ hL₁ hAB₂ hAB₁ i
  have hle : N₂ i ≤ sh (-(sg l Dt.h i : ℤ)) (N₁ i) := by
    have h' := sh_le_sh (-(sg l Dt.h i : ℤ)) e21
    rwa [sh_sh_eq, neg_add_cancel, sh_zero_eq] at h'
  exact Compare.sen_compare R (D.γ i) (D.γ_semi i) (N₁ i) (N₂ i) (hL₁ i) (hL₂ i) (hC₁ i) (hC₂ i) _ e12 hle y hy

end GlobalTheory.Models
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UltrametricNormDetOneAddSmulStatement
section
open GlobalTheory.UnitDiscAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ultrametric_norm_det_one_add_smul : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ) (x : Matrix (Fin n) (Fin n) E) (ϖ : E), ‖ϖ‖ < 1 → (∀ i j, ‖x i j‖ ≤ 1) → ‖(1 + ϖ • x).det‖ = 1 := by
  first | exact @GlobalTheory.UnitDiscAlg.norm_det_one_add_smul | exact GlobalTheory.UnitDiscAlg.norm_det_one_add_smul | (intros; apply GlobalTheory.UnitDiscAlg.norm_det_one_add_smul <;> assumption)
end

