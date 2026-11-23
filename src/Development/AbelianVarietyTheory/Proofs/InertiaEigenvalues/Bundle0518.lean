module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0031
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimitiveGeneratorBoundedMultipleSet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0478
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0381
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0353
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0469

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormInertiaPartialTraceGeometricLe
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.PartialTraceGain

theorem sum_range_mul_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) (a b : ℕ) :
    ∑ i ∈ Finset.range (a * b), f i = ∑ i ∈ Finset.range a, ∑ j ∈ Finset.range b, f (i + a * j) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_range_succ, add_comm (a * b) i]

theorem norm_natCast_lt_one (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Om l)‖ < 1 := by
  have h : ((l : ℕ) : Om l) = algebraMap ℚ_[l] (Om l) (l : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']
  exact Padic.norm_p_lt_one

def fixedAdd {l : ℕ} [Fact l.Prime] (H : Subgroup (GQ l)) : AddSubgroup (Om l) where
  carrier := {x | ∀ g ∈ H, g x = x}
  add_mem' := fun {a b} ha hb g hg => by rw [map_add (f := _), ha g hg, hb g hg]
  zero_mem' := fun g _ => map_zero g
  neg_mem' := fun {a} ha g hg => by rw [map_neg, ha g hg]

theorem apply_mem_fixedAdd {l : ℕ} [Fact l.Prime] {H : Subgroup (GQ l)} (hH : H.Normal)
    (σ : GQ l) {x : Om l} (hx : x ∈ fixedAdd H) : σ x ∈ fixedAdd H := by
  intro g hg
  have h1 := hx _ (hH.conj_mem' g hg σ)
  have h2 : g * σ = σ * (σ⁻¹ * g * σ) := by group
  calc g (σ x) = (g * σ) x := rfl
    _ = σ ((σ⁻¹ * g * σ) x) := by rw [h2]; rfl
    _ = σ x := by rw [h1]

theorem apply_sum_pow {l : ℕ} [Fact l.Prime] (σ : GQ l) (m : ℕ) {x : Om l}
    (hx : (σ ^ m) x = x) :
    σ (∑ j ∈ Finset.range m, (σ ^ j) x) = ∑ j ∈ Finset.range m, (σ ^ j) x := by
  have h1 : σ (∑ j ∈ Finset.range m, (σ ^ j) x) = ∑ j ∈ Finset.range m, (σ ^ (j + 1)) x := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ']; rfl
  have h2 := Finset.sum_range_succ' (fun j => (σ ^ j) x) m
  rw [Finset.sum_range_succ, hx] at h2
  rw [h1]
  simpa using h2.symm

theorem pow_apply_of_fixed {l : ℕ} [Fact l.Prime] (σ : GQ l) {y : Om l} (hy : σ y = y) (i : ℕ) :
    (σ ^ i) y = y := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ]
    change (σ ^ i) (σ y) = y
    rw [hy, ih]

theorem norm_sum_pow_le : ∀ (l : ℕ) [Fact l.Prime] (γ : GQ l), γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup → ∀ (H : ℕ → Subgroup (GQ l)) (k : ℕ), (∀ n, (H n).Normal) → (∀ n, (H n).index ≠ 0) → (∀ n, (H n).index ≤ l ^ (k + n)) → (∀ n, γ ^ l ^ n ∈ H n) → (∀ n, ∀ h ∈ H n, ∃ i : ℕ, ((γ ^ l ^ n) ^ i)⁻¹ * h ∈ H (n + 1)) → ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ (n : ℕ) (x : Om l), (∀ g ∈ H n, g x = x) → ‖∑ i ∈ Finset.range (l ^ n), (γ ^ i) x‖ ≤ ρ ^ n * ‖x‖ := by
  intro l hl γ hγ H k hN hI hIle hpow hgen
  have hp : l.Prime := hl.out
  have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hp.one_le
  have ha0 : 0 ≤ ‖((l : ℕ) : Om l)‖ := norm_nonneg _
  have ha1 := norm_natCast_lt_one l
  have hpk : (1 : ℝ) ≤ (l : ℝ) ^ (k + 1) := one_le_pow₀ hl1
  have he0 : (0 : ℝ) < (1 : ℝ) / (l : ℝ) ^ (k + 1) := by positivity
  have he1 : (1 : ℝ) / (l : ℝ) ^ (k + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact hpk
  set ρ : ℝ := ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ (k + 1)) with hρ
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg ha0 _
  have hρ1 : ρ < 1 := Real.rpow_lt_one ha0 ha1 he0
  have haρ : ‖((l : ℕ) : Om l)‖ ≤ ρ := by
    have := Real.rpow_le_rpow_of_exponent_ge' ha0 ha1.le he0.le he1
    rwa [Real.rpow_one] at this
  have hmax : max (ρ ^ (l - 1)) ‖((l : ℕ) : Om l)‖ ≤ ρ := by
    refine max_le ?_ haρ
    have h2 := hp.two_le
    exact pow_le_of_le_one hρ0 hρ1.le (by omega)
  refine ⟨ρ, hρ0, hρ1, fun n => ?_⟩
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    set σ : GQ l := γ ^ l ^ n with hσ
    have hσl : σ ^ l = γ ^ l ^ (n + 1) := by rw [hσ, ← pow_mul, ← pow_succ]
    have hxS : x ∈ fixedAdd (H (n + 1)) := hx
    set y : Om l := ∑ j ∈ Finset.range l, (σ ^ j) x with hy
    have hyS : y ∈ fixedAdd (H (n + 1)) :=
      sum_mem fun j _ => apply_mem_fixedAdd (hN _) _ hxS
    have hσy : σ y = y := apply_sum_pow σ l (by rw [hσl]; exact hx _ (hpow _))
    have hyH : ∀ g ∈ H n, g y = y := by
      intro g hg
      obtain ⟨i, hi⟩ := hgen n g hg
      have h1 := hyS _ hi
      have h2 : g = σ ^ i * ((σ ^ i)⁻¹ * g) := by group
      calc g y = (σ ^ i) (((σ ^ i)⁻¹ * g) y) := by
            conv_lhs => rw [h2]
            rfl
        _ = y := by rw [h1, pow_apply_of_fixed σ hσy]
    have hmove : ∀ z ∈ fixedAdd (H (n + 1)), ‖σ z - z‖ ≤ ρ * ‖z‖ := by
      intro z hz
      have := _root_.GlobalTheory.InertiaMove.norm_pow_sub_le l γ hγ (H (n + 1)) (hN _) (hI _) (k + (n + 1)) (n + 1) (hIle _)
        (hpow _) n (by omega) z hz
      rwa [show k + (n + 1) - n = k + 1 by omega] at this
    have hyn : ‖y‖ ≤ ρ * ‖x‖ :=
      (GlobalTheory.T.norm_sum_pow_apply_le_and_norm_pow_prime_sub_le l σ (fixedAdd (H (n + 1))) ρ hρ0 hρ1.le
        (fun z hz => apply_mem_fixedAdd (hN _) σ hz) hmove x hxS).1.trans
        (mul_le_mul_of_nonneg_right hmax (norm_nonneg _))
    have hsum : ∑ i ∈ Finset.range (l ^ (n + 1)), (γ ^ i) x
        = ∑ i ∈ Finset.range (l ^ n), (γ ^ i) y := by
      rw [pow_succ, sum_range_mul_eq]
      refine Finset.sum_congr rfl fun i _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hy, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pow_add, pow_mul]; rfl
    rw [hsum]
    calc _ ≤ ρ ^ n * ‖y‖ := ih y hyH
      _ ≤ ρ ^ n * (ρ * ‖x‖) := mul_le_mul_of_nonneg_left hyn (pow_nonneg hρ0 _)
      _ = ρ ^ (n + 1) * ‖x‖ := by ring

end GlobalTheory.PartialTraceGain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowRamifiedUniformizerFieldZpowStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_pow_ramifiedUniformizerField_zpow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (y : Om l), y ∈ (ϖ.field a).1 → y ≠ 0 → ∃ j : ℤ, ‖y‖ ^ e = (l : ℝ) ^ j := by
  first | exact @GlobalTheory.ValGroupKprime.norm_pow_field | exact GlobalTheory.ValGroupKprime.norm_pow_field | (intros; apply GlobalTheory.ValGroupKprime.norm_pow_field <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneMemOfFrobeniusLinkedBoundedSeriesIdeals
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.BK.GcdCore

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem powerSeries_coeff_norm_le_one_mul {f g : K⟦X⟧} (hf : ∀ n, ‖coeff n f‖ ≤ 1) (hg : ∀ n, ‖coeff n g‖ ≤ 1) (n : ℕ) :
    ‖coeff n (f * g)‖ ≤ 1 := by
  simpa using norm_coeff_mul_le (w := fun _ => 1) (fun _ => zero_le_one) (fun _ _ => by simp)
    zero_le_one zero_le_one (f := f) (g := g) (by simpa using hf) (by simpa using hg) n

theorem powerSeries_coeff_norm_le_one_add {f g : K⟦X⟧} (hf : ∀ n, ‖coeff n f‖ ≤ 1) (hg : ∀ n, ‖coeff n g‖ ≤ 1) (n : ℕ) :
    ‖coeff n (f + g)‖ ≤ 1 := by
  rw [map_add (f := _)]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf n) (hg n))

theorem powerSeries_coeff_norm_le_one_pow {f : K⟦X⟧} (hf : ∀ n, ‖coeff n f‖ ≤ 1) (m : ℕ) : ∀ n, ‖coeff n (f ^ m)‖ ≤ 1 := by
  induction m with
  | zero => intro n; rw [pow_zero, coeff_one]; split_ifs <;> simp
  | succ m ih => intro n; rw [pow_succ]; exact powerSeries_coeff_norm_le_one_mul ih hf n

theorem powerSeries_coeff_norm_le_one_X_pow (i : ℕ) : ∀ n, ‖coeff n ((X : K⟦X⟧) ^ i)‖ ≤ 1 := by
  intro n; rw [coeff_X_pow]; split_ifs <;> simp

theorem powerSeries_coeff_norm_le_one_frobeniusExpand (l : ℕ) [Fact l.Prime] {f : K⟦X⟧} (hf : ∀ n, ‖coeff n f‖ ≤ 1) :
    ∀ n, ‖coeff n (frob K l f)‖ ≤ 1 := by
  intro n; rw [coeff_frob]; split_ifs
  · exact hf _
  · simp

theorem coeff_norm_le_one_eisensteinPolynomialPowPlusPrime (l e : ℕ) (hl : ‖(l : K)‖ < 1) : ∀ n, ‖coeff n (E K l e)‖ ≤ 1 := by
  intro n
  rw [E, ← map_natCast (C : K →+* K⟦X⟧)]
  refine powerSeries_coeff_norm_le_one_add (powerSeries_coeff_norm_le_one_X_pow e) (fun m => ?_) n
  rw [coeff_C]; split_ifs
  · exact hl.le
  · simp

theorem powerSeries_coeff_norm_le_one_finset_sum {ι : Type} (s : Finset ι) (f : ι → K⟦X⟧) (hf : ∀ i ∈ s, ∀ n, ‖coeff n (f i)‖ ≤ 1) :
    ∀ n, ‖coeff n (∑ i ∈ s, f i)‖ ≤ 1 :=
  Finset.sum_induction f (fun g => ∀ n, ‖coeff n g‖ ≤ 1) (fun _ _ ha hb => powerSeries_coeff_norm_le_one_add ha hb)
    (fun n => by simp) hf

theorem sum_X_pow_mul_frob_frobSlice (l : ℕ) [Fact l.Prime] (z : K⟦X⟧) :
    z = ∑ i ∈ Finset.range l, (X : K⟦X⟧) ^ i * frob K l (frobSlice l i z) := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  ext n
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp_rw [coeff_X_pow_mul', coeff_frob, coeff_frobSlice]
  rw [Finset.sum_eq_single (n % l)]
  · have h1 : n % l ≤ n := Nat.mod_le n l
    have h2 : l ∣ n - n % l := Nat.dvd_sub_mod n
    rw [if_pos h1, if_pos h2, Nat.mul_div_cancel' h2, Nat.sub_add_cancel h1]
  · intro i hi hne
    split_ifs with h1 h2
    · exfalso
      obtain ⟨c, hc⟩ := h2
      have hn : n = i + l * c := by omega
      apply hne
      rw [hn, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Finset.mem_range.1 hi)]
    · rfl
    · rfl
  · intro h; exact absurd (Finset.mem_range.2 (Nat.mod_lt n hl)) h

theorem one_mem_of_frobenius_stable_ideals_boundedPowerSeries (GEN : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (J : Set K⟦X⟧), (∀ x ∈ J, ∀ y ∈ J, x + y ∈ J) → (∀ x ∈ J, ∀ b : K⟦X⟧, (∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c) → b * x ∈ J) → (∃ g ∈ J, (∀ n, ‖coeff n g‖ ≤ 1) ∧ ∃ n, ‖coeff n g‖ = 1) → ∃ Δ ∈ J, (∀ n, ‖coeff n Δ‖ ≤ 1) ∧ (∃ n, ‖coeff n Δ‖ = 1) ∧ ∀ h ∈ J, (∀ n, ‖coeff n h‖ ≤ 1) → ∃ q : K⟦X⟧, (∀ n, ‖coeff n q‖ ≤ 1) ∧ h = Δ * q)
  (CYCLE : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (l e a M N : ℕ) [Fact l.Prime] [NeZero a], 0 < e → (l : K) ≠ 0 → ‖(l : K)‖ < 1 → ∀ (Δ k k' : ZMod a → K⟦X⟧), (∀ τ n, ‖coeff n (Δ τ)‖ ≤ 1) → (∀ τ, ∃ n, ‖coeff n (Δ τ)‖ = 1) → (∀ τ n, ‖coeff n (k τ)‖ ≤ 1) → (∀ τ n, ‖coeff n (k' τ)‖ ≤ 1) → (∀ τ, k τ * k' τ = E K l e ^ N) → (∀ τ, Δ τ * k τ = E K l e ^ M * frob K l (Δ (τ - 1))) → ∀ τ, ‖constantCoeff (Δ τ)‖ = 1)
  (UNITA : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (f : K⟦X⟧), (∀ n, ‖coeff n f‖ ≤ 1) → ‖constantCoeff f‖ = 1 → ∃ g : K⟦X⟧, (∀ n, ‖coeff n g‖ ≤ 1) ∧ f * g = 1) :
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (l e a M₁ M₂ : ℕ) [Fact l.Prime] [NeZero a], 0 < e → (l : K) ≠ 0 → ‖(l : K)‖ < 1 → ∀ (J : ZMod a → Set K⟦X⟧), (∀ τ, ∀ x ∈ J τ, ∀ y ∈ J τ, x + y ∈ J τ) → (∀ τ, ∀ x ∈ J τ, ∀ b : K⟦X⟧, (∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c) → b * x ∈ J τ) → (∀ τ, ∀ x ∈ J τ, ∃ c : ℝ, ∀ n, ‖coeff n x‖ ≤ c) → (∀ τ, ∃ g ∈ J τ, (∀ n, ‖coeff n g‖ ≤ 1) ∧ ∃ n, ‖coeff n g‖ = 1) → (∀ τ, ∀ h ∈ J (τ - 1), E K l e ^ M₁ * frob K l h ∈ J τ) → (∀ τ, ∀ h ∈ J τ, ∀ i < l, frobSlice l i (E K l e ^ M₂ * h) ∈ J (τ - 1)) → ∀ τ, (1 : K⟦X⟧) ∈ J τ := by
  intro K _ _ _ l e a M₁ M₂ _ _ he hl0 hl1 J hadd hmul _ hprim hphi hsl
  choose Δ hΔJ hΔ1 hΔp hΔdiv using fun τ => GEN K (J τ) (hadd τ) (hmul τ) (hprim τ)
  have hE := coeff_norm_le_one_eisensteinPolynomialPowPlusPrime (K := K) l e hl1

  have hk : ∀ τ, ∃ k : K⟦X⟧, (∀ n, ‖coeff n k‖ ≤ 1) ∧
      Δ τ * k = E K l e ^ M₁ * frob K l (Δ (τ - 1)) := by
    intro τ
    obtain ⟨q, hq1, hq⟩ := hΔdiv τ _ (hphi τ _ (hΔJ (τ - 1)))
      (powerSeries_coeff_norm_le_one_mul (powerSeries_coeff_norm_le_one_pow hE M₁) (powerSeries_coeff_norm_le_one_frobeniusExpand l (hΔ1 (τ - 1))))
    exact ⟨q, hq1, hq.symm⟩
  choose k hk1 hk using hk

  have hm : ∀ τ i, ∃ m : K⟦X⟧, i < l → (∀ n, ‖coeff n m‖ ≤ 1) ∧
      frobSlice l i (E K l e ^ M₂ * Δ τ) = Δ (τ - 1) * m := by
    intro τ i
    by_cases hi : i < l
    · have hs1 : ∀ n, ‖coeff n (frobSlice l i (E K l e ^ M₂ * Δ τ))‖ ≤ 1 := fun n => by
        rw [coeff_frobSlice]; exact powerSeries_coeff_norm_le_one_mul (powerSeries_coeff_norm_le_one_pow hE M₂) (hΔ1 τ) _
      obtain ⟨q, hq1, hq⟩ := hΔdiv (τ - 1) _ (hsl τ _ (hΔJ τ) i hi) hs1
      exact ⟨q, fun _ => ⟨hq1, hq⟩⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose m hm using hm
  set k' : ZMod a → K⟦X⟧ := fun τ => ∑ i ∈ Finset.range l, (X : K⟦X⟧) ^ i * frob K l (m τ i) with hk'def
  have hk'1 : ∀ τ n, ‖coeff n (k' τ)‖ ≤ 1 := fun τ =>
    powerSeries_coeff_norm_le_one_finset_sum _ _ fun i hi => powerSeries_coeff_norm_le_one_mul (powerSeries_coeff_norm_le_one_X_pow i) (powerSeries_coeff_norm_le_one_frobeniusExpand l (hm τ i (Finset.mem_range.1 hi)).1)
  have hk' : ∀ τ, E K l e ^ M₂ * Δ τ = frob K l (Δ (τ - 1)) * k' τ := by
    intro τ
    rw [sum_X_pow_mul_frob_frobSlice (K := K) l (E K l e ^ M₂ * Δ τ), hk'def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(hm τ i (Finset.mem_range.1 hi)).2, map_mul]
    ring
  have hne : ∀ τ, Δ τ ≠ 0 := fun τ h => by
    obtain ⟨n, hn⟩ := hΔp τ
    rw [h, map_zero, norm_zero] at hn
    exact zero_ne_one hn
  have hkk : ∀ τ, k τ * k' τ = E K l e ^ (M₁ + M₂) := by
    intro τ
    apply mul_left_cancel₀ (hne τ)
    calc Δ τ * (k τ * k' τ) = E K l e ^ M₁ * (frob K l (Δ (τ - 1)) * k' τ) := by
          rw [← mul_assoc, hk τ, mul_assoc]
      _ = Δ τ * E K l e ^ (M₁ + M₂) := by rw [← hk' τ, pow_add]; ring
  have hc := CYCLE K l e a M₁ (M₁ + M₂) he hl0 hl1 Δ k k' hΔ1 hΔp hk1 hk'1 hkk hk
  intro τ
  obtain ⟨g, hg1, hg⟩ := UNITA K (Δ τ) (hΔ1 τ) (hc τ)
  have := hmul τ _ (hΔJ τ) g ⟨1, hg1⟩
  rwa [mul_comm, hg] at this

theorem one_mem : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (l e a M₁ M₂ : ℕ) [Fact l.Prime] [NeZero a], 0 < e → (l : K) ≠ 0 → ‖(l : K)‖ < 1 → ∀ (J : ZMod a → Set K⟦X⟧), (∀ τ, ∀ x ∈ J τ, ∀ y ∈ J τ, x + y ∈ J τ) → (∀ τ, ∀ x ∈ J τ, ∀ b : K⟦X⟧, (∃ c : ℝ, ∀ n, ‖coeff n b‖ ≤ c) → b * x ∈ J τ) → (∀ τ, ∀ x ∈ J τ, ∃ c : ℝ, ∀ n, ‖coeff n x‖ ≤ c) → (∀ τ, ∃ g ∈ J τ, (∀ n, ‖coeff n g‖ ≤ 1) ∧ ∃ n, ‖coeff n g‖ = 1) → (∀ τ, ∀ h ∈ J (τ - 1), E K l e ^ M₁ * frob K l h ∈ J τ) → (∀ τ, ∀ h ∈ J τ, ∀ i < l, frobSlice l i (E K l e ^ M₂ * h) ∈ J (τ - 1)) → ∀ τ, (1 : K⟦X⟧) ∈ J τ :=
  one_mem_of_frobenius_stable_ideals_boundedPowerSeries _root_.GlobalTheory.exists_primitive_generator GlobalTheory.T.norm_constantCoeff_eq_one_of_eisenstein_frobenius_cycle _root_.GlobalTheory.powerSeries_inv_coeff_norm_le_one

end GlobalTheory.BK.GcdCore
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneNotMemFilOne
section
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Module

namespace GlobalTheory.NL.JumpsSES

section Trivial

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]

theorem fil_anti {a b : ℤ} (h : a ≤ b) : PD.Fil b ≤ PD.Fil a := by
  induction b, h using Int.leInduction with
  | base => exact le_rfl
  | succ n _ ih => exact (PD.Fil_anti n).trans ih

theorem one_not_mem_fil_one : (1 : BdR) ∉ PD.Fil 1 := by
  intro h
  have := PD.Fil_mul 1 1 _ _ PD.mem_filtration_one h
  rw [mul_one] at this
  exact PD.not_mem_filtration_two this

theorem ddR_of_trivial {V : Type} [AddCommGroup V] [Module Qp V] [Module LL V]
    [IsScalarTower Qp LL V] [FiniteDimensional Qp V] (ρ : Representation LL G V)
    (hρ : ∀ g x, ρ g x = x) (x : V ⊗[Qp] BdR) (hx : x ∈ DdR PD ρ) :
    x ∈ LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
        (IsScalarTower.toAlgHom Qp K BdR).toLinearMap) ∧
    (∀ a ≤ 0, x ∈ FilV PD (LL := LL) (V := V) a) ∧
    (∀ a, 1 ≤ a → x ∈ FilV PD (LL := LL) (V := V) a → x = 0) := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx
  let e := Module.finBasis Qp V
  let c : Fin (finrank Qp V) → V ⊗[Qp] BdR →ₗ[Qp] BdR := fun i =>
    (TensorProduct.lid Qp BdR).toLinearMap ∘ₗ (LinearMap.rTensor BdR (e.coord i))
  have hsum : ∀ y : V ⊗[Qp] BdR, y = ∑ i, e i ⊗ₜ[Qp] c i y := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul v b =>
      conv_lhs => rw [← e.sum_repr v, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [c, TensorProduct.smul_tmul]
    | add a b ha hb =>
      simp only [map_add (f := _), TensorProduct.tmul_add, Finset.sum_add_distrib, ← ha, ← hb]
  have hc : ∀ i g y, c i (actVdR PD ρ g y) = PD.actdR g (c i y) := by
    intro i g y
    induction y using TensorProduct.inductionOn with
    | tmul v b =>
      have := ((PD.actdR g).toAlgHom.toLinearMap.restrictScalars Qp).map_smul (e.coord i v) b
      have h2 : PD.actdR g (e.coord i v • b) = e.coord i v • PD.actdR g b := this
      simp only [c, actVdR, LinearMap.comp_apply, AlgebraTensorModule.map_tmul,
        LinearMap.rTensor_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul, h2, hρ]
      simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hk : ∀ i, ∃ k : K, algebraMap K BdR k = c i x := fun i =>
    PD.invdR (c i x) fun g => by rw [← hc, hx]
  refine ⟨?_, fun a ha => ?_, fun a ha hF => ?_⟩
  · rw [hsum x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨k, hk⟩ := hk i
    exact ⟨e i ⊗ₜ k, by simp [hk]⟩
  · rw [hsum x]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨k, hk⟩ := hk i
    have : c i x ∈ PD.Fil a := by
      rw [← hk, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (fil_anti PD ha PD.one_mem)
    exact ⟨e i ⊗ₜ ⟨c i x, this⟩, by simp⟩
  · have hF' : ∀ i, ∀ y ∈ FilV PD (LL := LL) (V := V) a, c i y ∈ PD.Fil a := by
      rintro i _ ⟨y, rfl⟩
      induction y using TensorProduct.inductionOn with
      | tmul v b =>
        have : (e.coord i v) • (b : BdR) ∈ (PD.Fil a).restrictScalars Qp := Submodule.smul_mem _ _ b.2
        simpa [c] using this
      | add y z hy hz => rw [map_add (f := _), map_add (f := _)]; exact Submodule.add_mem _ hy hz
    rw [hsum x]
    refine Finset.sum_eq_zero fun i _ => ?_
    obtain ⟨k, hk⟩ := hk i
    by_cases h0 : k = 0
    · rw [← hk, h0]; simp
    · exfalso
      apply one_not_mem_fil_one PD
      have h1 := Submodule.smul_mem _ k⁻¹ (fil_anti PD ha (hF' i x hF))
      rwa [← hk, Algebra.algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ h0, one_smul] at h1

theorem jumps_of_trivial {V : Type} [AddCommGroup V] [Module Qp V] [Module LL V]
    [IsScalarTower Qp LL V] [FiniteDimensional Qp V] (ρ : Representation LL G V)
    (hρ : ∀ g x, ρ g x = x) (τ : K →ₐ[Qp] LL) (a : ℤ) (ha : IsJumpV PD ρ τ a) : a = 0 := by
  by_contra h0
  apply ha
  ext x
  simp only [FildR, Submodule.mem_inf]
  refine and_congr_right fun hx => ?_
  obtain ⟨-, h1, h2⟩ := ddR_of_trivial PD ρ hρ x hx.1
  rcases lt_or_gt_of_ne h0 with h | h
  · exact ⟨fun _ => h1 a (by omega), fun _ => h1 (a + 1) (by omega)⟩
  · constructor
    · intro hF; rw [h2 _ (by omega) hF]; exact Submodule.zero_mem _
    · intro hF; rw [h2 _ (by omega) hF]; exact Submodule.zero_mem _

end Trivial

theorem jumps_ses_and_one : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (T₀ T₁ T₂ : Lt K LL) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L), IsCrys ((D.loc l).PD K) T₁.ρ → IsSESLat (Qp := ℚ_[l]) ι π → (∀ τ a, IsJumpV ((D.loc l).PD K) T₁.ρ τ a ↔ IsJumpV ((D.loc l).PD K) T₀.ρ τ a ∨ IsJumpV ((D.loc l).PD K) T₂.ρ τ a) ∧ ∀ τ a, IsJumpV ((D.loc l).PD K) W.one.ρ τ a → a = 0 := by
  intro D HW l _ K s LL h W T₀ T₁ T₂ ι π hc hS
  refine ⟨fun τ a => ?_, fun τ a ha => ?_⟩
  · have h0 : IsCrys ((D.loc l).PD K) T₀.ρ :=
      (GlobalTheory.Per.CrysSubQuot.crys_sub_quot l _ _ (D.locT l) K LL T₀.V T₀.ρ T₁.V T₁.ρ ι.f ι.equiv).1 hS.1 hc
    have h2 : IsCrys ((D.loc l).PD K) T₂.ρ :=
      ((GlobalTheory.Per.CrysSubQuot.crys_sub_quot l _ _ (D.locT l) K LL T₁.V T₁.ρ T₂.V T₂.ρ π.f π.equiv).2
        hS.2.1 hc).1
    exact GlobalTheory.T.isJumpV_iff_of_exact_crystalline_lattices l _ _ (D.locT l) K LL T₀ T₁ T₂ ι π hS h0 hc h2 τ a
  · haveI := LL.2
    haveI : FiniteDimensional ℚ_[l] W.one.V := Module.Finite.trans ↥LL.1 W.one.V
    exact jumps_of_trivial _ W.one.ρ W.one_triv τ a ha

end GlobalTheory.NL.JumpsSES
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimeDvdAinfEnvelopeOfGaloisSections
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP


set_option maxHeartbeats 1000000 in
theorem l_dvd_of_galois_sections : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)) (κ : Type) [Fintype κ] (x : κ → En.Q.A) (c : κ → κ → En.Q.A) (h : ℕ), (∀ j, En.inl.f (bk.ev bk.E) ^ h * x j = ∑ i, En.Q.D.φ (x i) * c i j) → (∀ (g : ↥(GK K)) (s : Hom En.Q (ainfObj K)), s.comp En.inl = Hom.id _ → s.comp En.inr = (ainfHom K g).comp bk.ι → ∀ j, ((l : ℕ) : (ainfObj K).A) ∣ s.f (x j)) → ∀ j, ((l : ℕ) : En.Q.A) ∣ x j := by
  intro l _ K bk En κ _ x c h hx hs
  obtain ⟨-, -, -, -, -, -, hA7⟩ := _root_.GlobalTheory.BSP.AinfDiv.main l K bk
  obtain ⟨-, hM2, hM3⟩ := _root_.GlobalTheory.BSP.env_ainf_mod l K bk En
  let I : Ideal En.Q.A := Ideal.span {((l : ℕ) : En.Q.A)}
  let π : En.Q.A →+* En.Q.A ⧸ I := Ideal.Quotient.mk I
  have hπ : ∀ y, π y = 0 ↔ ((l : ℕ) : En.Q.A) ∣ y := fun y =>
    Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton
  have hl0 : ((l : ℕ) : En.Q.A ⧸ I) = 0 := by
    rw [← map_natCast π]; exact (hπ _).2 dvd_rfl
  have hreg : π (En.inl.f (bk.ev X)) ∈ nonZeroDivisors (En.Q.A ⧸ I) := by
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have : π (En.inl.f (bk.ev X) * y) = 0 := by rw [map_mul, mul_comm]; exact hy
    exact (hπ _).2 (hM2 y ((hπ _).1 this))
  have hE : π (En.inl.f (bk.ev bk.E)) = π (En.inl.f (bk.ev X)) ^ bk.Ep.natDegree := by
    let ι : Ainf l →+* En.Q.A := En.inl.f
    have h1 : ((l : ℕ) : En.Q.A) ∣ ι (bk.ev bk.E - bk.ev X ^ bk.Ep.natDegree) := by
      have := map_dvd ι hA7
      rwa [map_natCast] at this
    have h2 := (hπ _).2 h1
    rw [map_sub, map_pow, map_sub, map_pow, sub_eq_zero] at h2
    exact h2
  have hl1 : π ((l : ℕ) : En.Q.A) = 0 := (hπ _).2 dvd_rfl
  have hφ : ∀ y, π (En.Q.D.φ y) = π y ^ l := fun y => by
    have e : π (En.Q.D.φ y - y ^ l) = 0 := (hπ _).2 ⟨En.Q.D.δ y, by rw [En.Q.D.φ_eq y]; ring⟩
    rwa [map_sub, map_pow, sub_eq_zero] at e
  have heq : ∀ j, π (En.inl.f (bk.ev X)) ^ (bk.Ep.natDegree * h) * π (x j) =
      ∑ i, π (x i) ^ l * π (c i j) := fun j => by
    have := congrArg π (hx j)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul π, map_pow π, hE, ← pow_mul, map_sum π] at this
    rw [this]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul π, hφ]
  have hpts : ∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l]
      (f : En.Q.A ⧸ I →+* O), f (π (En.inl.f (bk.ev X))) ≠ 0 → ¬ IsUnit (f (π (En.inl.f (bk.ev X)))) →
      IsAdicComplete (Ideal.span {f (π (En.inl.f (bk.ev X)))}) O → ∀ j, f (π (x j)) = 0 := by
    intro O _ _ _ _ _ f hf0 hfu hfc j
    obtain ⟨g, s, ψ, h1, h2, h3⟩ := GlobalTheory.T.breuilKisinEnvelope_point_factors_through_section l K bk En O (f.comp π) hf0 hfu hfc
    obtain ⟨z, hz⟩ := hs g s h1 h2 j
    have e := h3 (x j)
    rw [RingHom.comp_apply] at e
    rw [e, hz]
    have : WittVector.coeff (p := l) (R := OCb l) (((l : ℕ) : (ainfObj K).A) * z) 0 = 0 := by
      rw [mul_comm]; exact WittVector.mul_charP_coeff_zero (p := l) (R := OCb l) z
    rw [this, map_zero]
  have key := _root_.GlobalTheory.PointsKey.key l (En.Q.A ⧸ I) (π (En.inl.f (bk.ev X))) hl0 hreg κ (fun i => π (x i))
    (fun i j => π (c i j)) (bk.Ep.natDegree * h) heq (fun O _ _ _ _ _ f hf0 hfu hfc j => hpts O f hf0 hfu hfc j)
  intro j
  refine hM3 (x j) fun m => ?_
  obtain ⟨w, hw⟩ := key m j
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
  refine ⟨z, (hπ _).1 ?_⟩
  change π (x j) = π (En.inl.f (bk.ev X)) ^ m * π z at hw
  rw [map_sub π, map_mul π, map_pow π, hw, sub_self]

end GlobalTheory.BSP
end

