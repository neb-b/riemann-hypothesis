module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HasQExpansionModularForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0149
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeProductInvariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0086
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesSubringCoeffMulInvMem
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.HahnSub

theorem coeff_mul_mem {Ω : Type} [Field Ω] (A : Subring Ω) (h h' : HahnSeries ℚ Ω)
    (hh : ∀ r, h.coeff r ∈ A) (hh' : ∀ r, h'.coeff r ∈ A) (r : ℚ) : (h * h').coeff r ∈ A := by
  rw [HahnSeries.coeff_mul]
  exact A.sum_mem fun ij _ => A.mul_mem (hh ij.1) (hh' ij.2)

theorem coeff_inv_mem {Ω : Type} [Field Ω] (A : Subring Ω) (h : HahnSeries ℚ Ω)
    (hh : ∀ r, h.coeff r ∈ A) (hl : h.leadingCoeff⁻¹ ∈ A) (r : ℚ) : (h⁻¹).coeff r ∈ A := by
  by_cases h0 : h = 0
  · subst h0
    simp

  let g : HahnSeries ℚ A :=
    { coeff := fun s => ⟨h.coeff s, hh s⟩
      isPWO_support' := h.isPWO_support.mono fun s hs e => hs (Subtype.ext e) }
  have hg : ∀ s, (g.coeff s : Ω) = h.coeff s := fun s => rfl
  have hg0 : g ≠ 0 := by
    intro e
    apply h0
    ext s
    rw [← hg, e]
    rfl
  have hord : g.order = h.order := by
    apply le_antisymm
    · apply HahnSeries.order_le_of_coeff_ne_zero
      intro e
      apply HahnSeries.leadingCoeff_ne_zero.2 h0
      rw [HahnSeries.leadingCoeff_eq, ← hg, e]
      rfl
    · apply HahnSeries.order_le_of_coeff_ne_zero
      rw [← hg]
      intro e
      apply HahnSeries.leadingCoeff_ne_zero.2 hg0
      rw [HahnSeries.leadingCoeff_eq]
      exact Subtype.ext e
  have hlead : (g.leadingCoeff : Ω) = h.leadingCoeff := by
    rw [HahnSeries.leadingCoeff_eq, HahnSeries.leadingCoeff_eq, hg, hord]
  have hunit : IsUnit g.leadingCoeff := by
    refine IsUnit.of_mul_eq_one (⟨h.leadingCoeff⁻¹, hl⟩ : A) ?_
    apply Subtype.ext
    show (g.leadingCoeff : Ω) * h.leadingCoeff⁻¹ = 1
    rw [hlead]
    exact mul_inv_cancel₀ (HahnSeries.leadingCoeff_ne_zero.2 h0)
  obtain ⟨v, hv⟩ := (HahnSeries.isUnit_iff.2 hunit).exists_right_inv
  let f : A →ₙ+* Ω := A.subtype.toNonUnitalRingHom
  have hgf : g.map f = h := by
    ext s
    rfl
  have hone : (1 : HahnSeries ℚ A).map f = 1 := by
    ext s
    rw [HahnSeries.map_coeff, HahnSeries.coeff_one, HahnSeries.coeff_one]
    split_ifs <;> rfl
  have key : h * v.map f = 1 := by
    rw [← hgf, ← HahnSeries.map_mul, hv, hone]
  rw [inv_eq_of_mul_eq_one_right key, HahnSeries.map_coeff]
  exact (v.coeff r).2

theorem coeff_mul_inv_mem : ∀ (Ω : Type) [Field Ω] (A : Subring Ω), (∀ h h' : HahnSeries ℚ Ω, (∀ r, h.coeff r ∈ A) → (∀ r, h'.coeff r ∈ A) → ∀ r, (h * h').coeff r ∈ A) ∧ ∀ h : HahnSeries ℚ Ω, (∀ r, h.coeff r ∈ A) → h.leadingCoeff⁻¹ ∈ A → ∀ r, (h⁻¹).coeff r ∈ A := by
  intro Ω _ A
  exact ⟨fun h h' hh hh' r => coeff_mul_mem A h h' hh hh' r,
    fun h hh hl r => coeff_inv_mem A h hh hl r⟩

end GlobalTheory.HahnSub
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasCommonExponentDenominatorRingOperations
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem den_scale_left {r : ℚ} {N M : ℕ} (hM : 0 < M) (h : ∃ n : ℤ, r = (n : ℚ) / N) :
    ∃ n : ℤ, r = (n : ℚ) / ((N * M : ℕ) : ℚ) := by
  obtain ⟨n, rfl⟩ := h
  refine ⟨n * M, ?_⟩
  have : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  push_cast
  rw [mul_div_mul_right _ _ this]

theorem den_scale_right {r : ℚ} {N M : ℕ} (hM : 0 < M) (h : ∃ n : ℤ, r = (n : ℚ) / N) :
    ∃ n : ℤ, r = (n : ℚ) / ((M * N : ℕ) : ℚ) := by
  rw [Nat.mul_comm]; exact den_scale_left hM h

theorem den_union {Ω : Type} [Field Ω] {h h' : HahnSeries ℚ Ω} (hh : Den h) (hh' : Den h')
    (x : HahnSeries ℚ Ω) (hx : x.support ⊆ h.support ∪ h'.support) : Den x := by
  obtain ⟨N, hN, H⟩ := hh
  obtain ⟨N', hN', H'⟩ := hh'
  refine ⟨N * N', Nat.mul_pos hN hN', fun r hr => ?_⟩
  rcases hx hr with h1 | h1
  · have := den_scale_left (M := N') hN' (H r h1)
    simpa using this
  · have := den_scale_right (M := N) hN (H' r h1)
    simpa using this

theorem den_mul {Ω : Type} [Field Ω] {h h' : HahnSeries ℚ Ω} (hh : Den h) (hh' : Den h') :
    Den (h * h') := by
  obtain ⟨N, hN, H⟩ := hh
  obtain ⟨N', hN', H'⟩ := hh'
  refine ⟨N * N', Nat.mul_pos hN hN', fun r hr => ?_⟩
  have hs := HahnSeries.support_mul_subset (x := h) (y := h') hr
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_add.mp hs
  obtain ⟨n, rfl⟩ := H a ha
  obtain ⟨m, rfl⟩ := H' b hb
  refine ⟨n * N' + m * N, ?_⟩
  have h1 : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have h2 : (N' : ℚ) ≠ 0 := by exact_mod_cast hN'.ne'
  push_cast
  field_simp

theorem den_single {Ω : Type} [Field Ω] (r : ℚ) (c : Ω) : Den (HahnSeries.single r c : HahnSeries ℚ Ω) := by
  refine ⟨r.den, r.den_pos, fun s hs => ⟨r.num, ?_⟩⟩
  rw [HahnSeries.coeff_single] at hs
  split_ifs at hs with hsr
  · rw [hsr]; exact (Rat.num_div_den r).symm
  · exact (hs rfl).elim

theorem den_ring : ∀ (Ω : Type) [Field Ω], (∀ h h' : HahnSeries ℚ Ω, Den h → Den h' → Den (h + h') ∧ Den (h - h') ∧ Den (h * h')) ∧ ∀ (r : ℚ) (c : Ω), Den (HahnSeries.single r c : HahnSeries ℚ Ω) := by
  intro Ω _
  refine ⟨fun h h' hh hh' => ⟨den_union hh hh' _ (HahnSeries.support_add_subset h h'),
    den_union hh hh' _ (HahnSeries.support_sub_subset h h'), den_mul hh hh'⟩, fun r c => den_single r c⟩

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionOfPeriodicBoundedHolomorphic
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
open Function

namespace GlobalTheory.FN

theorem periodic_comp_ofComplex_of_vadd_real {f : ℍ → ℂ} {h : ℝ}
    (hf : ∀ τ : ℍ, f (h +ᵥ τ) = f τ) :
    Periodic (f ∘ UpperHalfPlane.ofComplex) (h : ℂ) := by
  intro w
  by_cases! hw : 0 < Complex.im w
  · have : 0 < Complex.im (w + h) := by simp [hw]
    simp only [comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos this,
      UpperHalfPlane.ofComplex_apply_of_im_pos hw]
    convert! hf ⟨w, hw⟩ using 2
    ext
    simp [add_comm]
  · have : Complex.im (w + h) ≤ 0 := by simpa using hw
    simp [UpperHalfPlane.ofComplex_apply_of_im_nonpos this,
      UpperHalfPlane.ofComplex_apply_of_im_nonpos hw]

theorem hasQ_of_periodic_bounded : ∀ (N : ℕ) (f : ℍ → ℂ), 0 < N → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → (∀ τ : ℍ, f ((N : ℝ) +ᵥ τ) = f τ) → UpperHalfPlane.IsBoundedAtImInfty f → ∃ a, HasQ N f a := by
  intro N f hN hf hper hbdd
  refine ⟨fun n => PowerSeries.coeff n (UpperHalfPlane.qExpansion (N : ℝ) f), ?_⟩
  rw [GlobalTheory.QFam.hasQ_coeff_iff_hasQExpansion]
  exact GlobalTheory.HasQExpansion.of_periodic (by exact_mod_cast hN)
    (periodic_comp_ofComplex_of_vadd_real hper) hf hbdd

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionSumAboveBasicProperties
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNHS

theorem hs_props : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), (∀ (C C' : ℝ) (φ : ℂ → ℂ) (h : HahnSeries ℚ Ω), C ≤ C' → HS ε C φ h → HS ε C' φ h) ∧ (∀ (C : ℝ) (φ ψ : ℂ → ℂ) (h h' : HahnSeries ℚ Ω), HS ε C φ h → HS ε C ψ h' → HS ε C (φ + ψ) (h + h') ∧ HS ε C (φ - ψ) (h - h')) ∧ (∀ (C : ℝ) (r : ℚ) (c : Ω), HS ε C (fun z => ε c * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (HahnSeries.single r c)) ∧ (∀ (C : ℝ) (φ ψ : ℂ → ℂ) (h : HahnSeries ℚ Ω), (∀ z : ℂ, C < z.im → φ z = ψ z) → HS ε C φ h → HS ε C ψ h) := by
  intro Ω _ ε
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro C C' φ h hC hs z hz
    exact hs z (lt_of_le_of_lt hC hz)
  · intro C φ ψ h h' hφ hψ
    refine ⟨fun z hz => ?_, fun z hz => ?_⟩
    · have := (hφ z hz).add (hψ z hz)
      simpa [HahnSeries.coeff_add, map_add (f := _), add_mul] using this
    · have := (hφ z hz).sub (hψ z hz)
      simpa [HahnSeries.coeff_sub, map_sub, sub_mul] using this
  · intro C r c z _
    have := hasSum_single (f := fun s : ℚ => ε ((HahnSeries.single r c).coeff s) *
        Complex.exp (2 * Real.pi * Complex.I * (s : ℂ) * z)) r (by
      intro b hb
      simp [HahnSeries.coeff_single_of_ne hb])
    simpa [HahnSeries.coeff_single_same] using this
  · intro C φ ψ h hφψ hs z hz
    rw [← hφψ z hz]
    exact hs z hz

end GlobalTheory.FNHS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionSumAboveMul
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNProd

theorem hs_mul : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (C : ℝ) (φ ψ : ℂ → ℂ) (h h' : HahnSeries ℚ Ω),
    HS ε C φ h → HS ε C ψ h' → HS ε C (φ * ψ) (h * h') := by
  intro Ω _ ε C φ ψ h h' H H' z hz
  set e : ℚ → ℂ := fun r => Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z) with he
  set a : ℚ → ℂ := fun r => ε (h.coeff r) * e r with ha
  set b : ℚ → ℂ := fun r => ε (h'.coeff r) * e r with hb
  have hA : HasSum a (φ z) := H z hz
  have hB : HasSum b (ψ z) := H' z hz
  have hAn : Summable fun r => ‖a r‖ := summable_norm_iff.2 hA.summable
  have hBn : Summable fun r => ‖b r‖ := summable_norm_iff.2 hB.summable
  have hP : HasSum (fun p : ℚ × ℚ => a p.1 * b p.2) (φ z * ψ z) :=
    hA.mul hB (summable_mul_of_summable_norm hAn hBn)
  have hF := hP.tsum_fiberwise (fun p : ℚ × ℚ => p.1 + p.2)
  refine hF.congr_fun ?_
  intro s
  have hexp : ∀ p : ℚ × ℚ, p.1 + p.2 = s → a p.1 * b p.2 = ε (h.coeff p.1) * ε (h'.coeff p.2) * e s := by
    intro p hp
    simp only [ha, hb, he, ← hp]
    have : Complex.exp (2 * Real.pi * Complex.I * ((p.1 + p.2 : ℚ) : ℂ) * z) =
        Complex.exp (2 * Real.pi * Complex.I * (p.1 : ℂ) * z) * Complex.exp (2 * Real.pi * Complex.I * (p.2 : ℂ) * z) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [this]; ring
  rw [tsum_subtype (f := fun p : ℚ × ℚ => a p.1 * b p.2)]
  rw [tsum_eq_sum (s := Finset.antidiagonal h.isPWO_support h'.isPWO_support s)]
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [HahnSeries.coeff_mul, map_sum, map_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.mem_antidiagonal] at hp
      rw [Set.indicator_of_mem (by simpa using hp.2.2)]
      exact (hexp p hp.2.2).symm
  · intro p hp
    by_cases hs : p.1 + p.2 = s
    · rw [Set.indicator_of_mem (by simpa using hs), hexp p hs]
      rw [Finset.mem_antidiagonal] at hp
      simp only [HahnSeries.mem_support, not_and] at hp
      by_cases h1 : h.coeff p.1 = 0
      · simp [h1]
      · have h2 : h'.coeff p.2 = 0 := by
          by_contra h2; exact hp h1 h2 hs
        simp [h2]
    · exact Set.indicator_of_notMem (by simpa using hs) _

end GlobalTheory.FNProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumPowerSeriesInvOfConvergent
section
namespace GlobalTheory

namespace PowerSeriesInv

theorem coeff_inv_norm_le (a : ℕ → ℂ) (M R : ℝ) (hR : 0 < R) (ha0 : a 0 ≠ 0)
    (hM : ∀ n, ‖a n‖ ≤ M * R ^ n) (n : ℕ) :
    ‖PowerSeries.coeff n (PowerSeries.mk a)⁻¹‖ ≤ ‖a 0‖⁻¹ * (R * (1 + M / ‖a 0‖)) ^ n := by
  have hc0 : PowerSeries.constantCoeff (PowerSeries.mk a) = a 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
  set A := ‖a 0‖ with hA
  have hA0 : 0 < A := norm_pos_iff.mpr ha0
  have hMA : A ≤ M := by simpa using hM 0
  have hM0 : 0 < M := lt_of_lt_of_le hA0 hMA
  set m := M / A with hm
  have hm0 : 0 < m := div_pos hM0 hA0
  set K := R * (1 + m) with hK
  set q := (1 + m)⁻¹ with hq
  have hK0 : 0 < K := by positivity
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hRK : R = K * q := by
    rw [hK, hq, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
  have hqA : q / (1 - q) = A / M := by
    have hqpos : 0 < q := by positivity
    have h1q : 1 - q = m * q := by
      have : (1 + m) * q = 1 := mul_inv_cancel₀ (by positivity)
      linarith
    rw [h1q, hm]
    field_simp
  have hgeom : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 1), (if 1 ≤ k then q ^ k else 0) ≤ A / M := by
    intro n
    rw [Finset.sum_range_succ']
    simp only [show ∀ k : ℕ, 1 ≤ k + 1 from fun k => by omega, if_true,
      show ¬ (1 ≤ 0) from by omega, if_false, add_zero]
    simp_rw [pow_succ]
    rw [← Finset.sum_mul]
    have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) hq0 hq1
    rw [← Finset.range_eq_Ico, pow_zero] at h
    calc (∑ i ∈ Finset.range n, q ^ i) * q ≤ 1 / (1 - q) * q := by gcongr
      _ = q / (1 - q) := by ring
      _ = A / M := hqA
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rw [PowerSeries.coeff_inv]
  split_ifs with hn
  · subst hn
    simp [hc0, hA]
  · have hterm : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        ‖(if p.2 < n then PowerSeries.coeff p.1 (PowerSeries.mk a) *
            PowerSeries.coeff p.2 (PowerSeries.mk a)⁻¹ else 0)‖ ≤
          M * A⁻¹ * K ^ n * (if 1 ≤ p.1 then q ^ p.1 else 0) := by
      intro p hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      split_ifs with h1 h2 h2
      · rw [norm_mul, PowerSeries.coeff_mk]
        calc ‖a p.1‖ * ‖PowerSeries.coeff p.2 (PowerSeries.mk a)⁻¹‖
            ≤ (M * R ^ p.1) * (A⁻¹ * K ^ p.2) :=
              mul_le_mul (hM _) (ih _ h1) (norm_nonneg _) (by positivity)
          _ = M * A⁻¹ * K ^ n * q ^ p.1 := by
              rw [hRK, ← hp, mul_pow, pow_add]; ring
      · omega
      · simp only [norm_zero]; positivity
      · simp
    calc ‖-(PowerSeries.constantCoeff (PowerSeries.mk a))⁻¹ *
          ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (if p.2 < n then PowerSeries.coeff p.1 (PowerSeries.mk a) *
            PowerSeries.coeff p.2 (PowerSeries.mk a)⁻¹ else 0)‖
        = A⁻¹ * ‖∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (if p.2 < n then
            PowerSeries.coeff p.1 (PowerSeries.mk a) *
            PowerSeries.coeff p.2 (PowerSeries.mk a)⁻¹ else 0)‖ := by
          rw [norm_mul, norm_neg, norm_inv, hc0]
      _ ≤ A⁻¹ * ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, M * A⁻¹ * K ^ n * (if 1 ≤ p.1 then q ^ p.1 else 0) :=
          mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum hterm))
            (by positivity)
      _ = A⁻¹ * (M * A⁻¹ * K ^ n *
            ∑ k ∈ Finset.range (n + 1), (if 1 ≤ k then q ^ k else 0)) := by
          rw [← Finset.mul_sum, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      _ ≤ A⁻¹ * (M * A⁻¹ * K ^ n * (A / M)) := by
          gcongr
          exact hgeom n
      _ = A⁻¹ * K ^ n := by
          field_simp

theorem hasSum_inv :
    ∀ (a : ℕ → ℂ) (ρ : ℝ), 0 < ρ → a 0 ≠ 0 → (∀ x : ℂ, ‖x‖ < ρ → Summable fun n => a n * x ^ n) →
      ∃ ρ' : ℝ, 0 < ρ' ∧ ∀ x : ℂ, ‖x‖ < ρ' → (∑' n, a n * x ^ n) ≠ 0 ∧
        HasSum (fun n => PowerSeries.coeff n (PowerSeries.mk a)⁻¹ * x ^ n)
          (∑' n, a n * x ^ n)⁻¹ := by
  intro a ρ hρ ha0 hs
  set x0 : ℂ := ((ρ / 2 : ℝ) : ℂ) with hx0def
  have hx0 : ‖x0‖ = ρ / 2 := by
    rw [hx0def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hsum := hs x0 (by rw [hx0]; linarith)
  have htend := hsum.tendsto_atTop_zero.norm
  obtain ⟨M, hM⟩ := htend.bddAbove_range
  set R : ℝ := 2 / ρ with hRdef
  have hR : 0 < R := by positivity
  have hMa : ∀ n, ‖a n‖ ≤ M * R ^ n := by
    intro n
    have h1 : ‖a n * x0 ^ n‖ ≤ M := hM ⟨n, rfl⟩
    rw [norm_mul, norm_pow, hx0] at h1
    have h2 : (ρ / 2) ^ n * R ^ n = 1 := by
      rw [← mul_pow, hRdef, div_mul_div_comm, mul_comm ρ 2, div_self (by positivity), one_pow]
    calc ‖a n‖ = ‖a n‖ * (ρ / 2) ^ n * R ^ n := by rw [mul_assoc, h2, mul_one]
      _ ≤ M * R ^ n := by gcongr
  have hA0 : 0 < ‖a 0‖ := norm_pos_iff.mpr ha0
  have hM0 : 0 < M := lt_of_lt_of_le hA0 (by simpa using hMa 0)
  set K := R * (1 + M / ‖a 0‖) with hKdef
  have hK : 0 < K := by positivity
  refine ⟨min (ρ / 2) K⁻¹, by positivity, ?_⟩
  intro x hx
  have hx1 : ‖x‖ < ρ / 2 := lt_of_lt_of_le hx (min_le_left _ _)
  have hx2 : ‖x‖ < K⁻¹ := lt_of_lt_of_le hx (min_le_right _ _)
  have hRx : R * ‖x‖ < 1 := by
    rw [hRdef, div_mul_eq_mul_div, div_lt_one hρ]; linarith
  have hKx : K * ‖x‖ < 1 := by
    have := mul_lt_mul_of_pos_left hx2 hK
    rwa [mul_inv_cancel₀ hK.ne'] at this
  have hsa : Summable fun n => ‖a n * x ^ n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      ((summable_geometric_of_lt_one (by positivity) hRx).mul_left M)
    rw [norm_mul, norm_pow]
    calc ‖a n‖ * ‖x‖ ^ n ≤ M * R ^ n * ‖x‖ ^ n := by gcongr; exact hMa n
      _ = M * (R * ‖x‖) ^ n := by ring
  have hsb : Summable fun n => ‖PowerSeries.coeff n (PowerSeries.mk a)⁻¹ * x ^ n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      ((summable_geometric_of_lt_one (by positivity) hKx).mul_left ‖a 0‖⁻¹)
    rw [norm_mul, norm_pow]
    calc ‖PowerSeries.coeff n (PowerSeries.mk a)⁻¹‖ * ‖x‖ ^ n
        ≤ ‖a 0‖⁻¹ * K ^ n * ‖x‖ ^ n := by
          gcongr; exact coeff_inv_norm_le a M R hR ha0 hMa n
      _ = ‖a 0‖⁻¹ * (K * ‖x‖) ^ n := by ring_nf
  have hc0 : PowerSeries.constantCoeff (PowerSeries.mk a) ≠ 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]; exact ha0
  have hc : ∀ n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      a kl.1 * x ^ kl.1 * (PowerSeries.coeff kl.2 (PowerSeries.mk a)⁻¹ * x ^ kl.2) =
        (if n = 0 then 1 else 0) := by
    intro n
    have h := congrArg (PowerSeries.coeff n) (PowerSeries.mul_inv_cancel (PowerSeries.mk a) hc0)
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_one] at h
    calc ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
          a kl.1 * x ^ kl.1 * (PowerSeries.coeff kl.2 (PowerSeries.mk a)⁻¹ * x ^ kl.2)
        = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, (PowerSeries.coeff kl.1 (PowerSeries.mk a) *
            PowerSeries.coeff kl.2 (PowerSeries.mk a)⁻¹) * x ^ n := by
          refine Finset.sum_congr rfl (fun kl hkl => ?_)
          rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
          rw [← hkl, pow_add, PowerSeries.coeff_mk]; ring
      _ = (if n = 0 then 1 else 0) := by
          rw [← Finset.sum_mul, h]; split_ifs with hn <;> simp [hn]
  have key : (∑' n, a n * x ^ n) * (∑' n, PowerSeries.coeff n (PowerSeries.mk a)⁻¹ * x ^ n) = 1 := by
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hsa hsb, tsum_congr hc]
    exact tsum_ite_eq 0 1
  refine ⟨left_ne_zero_of_mul_eq_one key, ?_⟩
  rw [← eq_inv_of_mul_eq_one_right key]
  exact (Summable.of_norm hsb).hasSum

end PowerSeriesInv

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerHeckeProductInvariantPrincipalLevel
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem GlobalTheory.kronecker_product_level : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M q : ℕ) (σ : SL(2, ℤ)) (f : X.K), 0 < M → q.Prime → Nat.Coprime q M → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) → ((en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q) → ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f) = ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f) := by
  intro Ω _ _ ε X M q σ f hM hq hqM hf hσ γ hγ
  exact GlobalTheory.hecke_product_invariant ε X M q f hM hq hqM hf σ hσ γ hγ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerClassEqImpPowRatioStatement
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularTower_class_eq_imp_pow_ratio : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (f f' : X.Kˣ), X.cls l n f = X.cls l n f' → ∃ u : X.Kˣ, (f' : X.K) = f * (u : X.K) ^ (l ^ n) := by
  first | exact @GlobalTheory.Tower.cls_eq_pow | exact GlobalTheory.Tower.cls_eq_pow | (intros; apply GlobalTheory.Tower.cls_eq_pow <;> assumption)
end

