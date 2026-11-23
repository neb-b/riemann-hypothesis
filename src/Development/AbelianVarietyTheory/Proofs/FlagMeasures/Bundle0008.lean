module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GapThresholdPaysFarTerms
section
open Matrix Finset Real

namespace GlobalTheory

private theorem log_le_sqrt_of_one_le (x : ℝ) (hx : 1 ≤ x) :
    Real.log x ≤ Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hx2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith)
  have h1 : Real.log (Real.sqrt x / 2) ≤ Real.sqrt x / 2 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Real.log (Real.sqrt x / 2) = Real.log (Real.sqrt x) - Real.log 2 :=
    Real.log_div hs.ne' (by norm_num)
  have h3 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    conv_lhs => rw [← hx2]
    rw [Real.log_pow]
    push_cast
    ring
  have h4 := Real.log_two_lt_d9
  linarith


set_option maxHeartbeats 800000 in
theorem gap_threshold_pays_far_terms : ∀ (Cg : ℝ) (n f q : ℕ) (rd g b : ℝ) (h t : ℝ), 0 ≤ Cg → 3 ≤ n → 1 ≤ f → 1 ≤ q → q ^ 2 ≤ n → 1 ≤ rd → Real.log f ≤ Real.sqrt n → 2 ≤ b → 1 ≤ g → g ≤ b ^ Cg → 8 * 10 ^ 14 * (Cg + 4) * (n : ℝ) ^ 19 * (f : ℝ) ^ 5 * Real.log (b * rd) ≤ h → ((n : ℝ) * f * rd * g * b)⁻¹ ^ (11 * q) ≤ t → t ≤ 1 / 2 → let ep : ℝ := 1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2); 64 * (n : ℝ) ^ 2 ≤ h * ep ∧ 1 ≤ h * ep ^ 2 / 16 ∧ (3 * Real.sqrt n / t ^ 2) ^ (2 * (n ^ 2 * f)) * (2 * f * 3 ^ f * Real.exp (-(h * ep ^ 2 / 16))) ≤ Real.exp (-((n : ℝ) ^ 2 * f)) := by
  intro Cg n f q rd g b h t hCg hn hf hq hqn hrd hlogf hb hg1 hgb hh ht1 _ht2 ep
  have hep : ep = 1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2) := rfl
  clear_value ep
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hqnR : (q : ℝ) ^ 2 ≤ n := by exact_mod_cast hqn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hf0 : (f : ℝ) ≠ 0 := by positivity
  have hnpos : (0 : ℝ) < n := by linarith
  have hfpos : (0 : ℝ) < f := by linarith
  set s := Real.sqrt (n : ℝ) with hs_def
  have hs2 : s ^ 2 = n := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ s := Real.one_le_sqrt.2 (by linarith)
  have hsn : s ≤ n := by nlinarith
  have hqs : (q : ℝ) ≤ s := (Real.le_sqrt (by positivity) (by linarith)).2 hqnR
  set ℓ := Real.log (b * rd) with hℓ_def
  have hbrd : 2 ≤ b * rd := le_trans hb (le_mul_of_one_le_right (by linarith) hrd)
  have hℓ : 0.69 ≤ ℓ := by
    have e1 := Real.log_le_log (by norm_num) hbrd
    have e2 := Real.log_two_gt_d9
    linarith
  have hlogb : Real.log b ≤ ℓ := Real.log_le_log (by linarith) (le_mul_of_one_le_right (by linarith) hrd)
  have hlogb0 : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
  have hKl : 2.76 ≤ (Cg + 4) * ℓ := by nlinarith [mul_nonneg hCg (by linarith : (0 : ℝ) ≤ ℓ)]

  have hX : 50 * (Cg + 4) * (n : ℝ) ^ 3 * f * ℓ ≤ h * ep ^ 2 / 16 := by
    have e : 8 * 10 ^ 14 * (Cg + 4) * (n : ℝ) ^ 19 * (f : ℝ) ^ 5 * ℓ * ep ^ 2 / 16
        = 50 * (Cg + 4) * (n : ℝ) ^ 3 * f * ℓ := by
      rw [hep]
      field_simp
      norm_num
    rw [← e]
    have := mul_le_mul_of_nonneg_right hh (sq_nonneg ep)
    linarith
  have hn3f : 1 ≤ (n : ℝ) ^ 3 * f := by
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) hfR
  refine ⟨?_, ?_, ?_⟩
  · have e : 8 * 10 ^ 14 * (Cg + 4) * (n : ℝ) ^ 19 * (f : ℝ) ^ 5 * ℓ * ep
        = 800000000 * ((Cg + 4) * ℓ) * ((n : ℝ) ^ 11 * f ^ 3) := by
      rw [hep]
      field_simp
      norm_num
    have hep0 : 0 ≤ ep := by rw [hep]; positivity
    have h1 := mul_le_mul_of_nonneg_right hh hep0
    have hn11 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 11 := pow_le_pow_right₀ (by linarith) (by norm_num)
    have hf3 : (1 : ℝ) ≤ (f : ℝ) ^ 3 := one_le_pow₀ hfR
    have hP : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 11 * f ^ 3 :=
      le_trans hn11 (le_mul_of_one_le_right (by positivity) hf3)
    have h2 : 2.76 * (n : ℝ) ^ 2 ≤ ((Cg + 4) * ℓ) * ((n : ℝ) ^ 11 * f ^ 3) :=
      mul_le_mul hKl hP (by positivity) (by linarith)
    have hz : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
    linarith
  · have h2 : 2.76 * 1 ≤ ((Cg + 4) * ℓ) * ((n : ℝ) ^ 3 * f) :=
      mul_le_mul hKl hn3f (by norm_num) (by linarith)
    linarith
  · set X := h * ep ^ 2 / 16 with hX_def
    set M := (n : ℝ) * f * rd * g * b with hM_def
    have hgpos : 0 < g := by linarith
    have hMpos : 0 < M := by
      have : (0 : ℝ) < rd := by linarith
      have : (0 : ℝ) < b := by linarith
      positivity
    set Lb := s + s + Cg * ℓ + ℓ with hLb_def
    have hLb0 : 0 ≤ Lb := by
      have : 0 ≤ Cg * ℓ := mul_nonneg hCg (by linarith)
      linarith

    have hnexp : (n : ℝ) ≤ Real.exp s := by
      calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hnpos).symm
        _ ≤ Real.exp s := Real.exp_le_exp.2 (log_le_sqrt_of_one_le _ (by linarith))
    have hfexp : (f : ℝ) ≤ Real.exp s := by
      calc (f : ℝ) = Real.exp (Real.log f) := (Real.exp_log hfpos).symm
        _ ≤ Real.exp s := Real.exp_le_exp.2 hlogf
    have hgexp : g ≤ Real.exp (Cg * ℓ) := by
      calc g ≤ b ^ Cg := hgb
        _ = Real.exp (Real.log b * Cg) := Real.rpow_def_of_pos (by linarith) Cg
        _ ≤ Real.exp (Cg * ℓ) := by
          apply Real.exp_le_exp.2
          have := mul_le_mul_of_nonneg_right hlogb hCg
          linarith
    have hbrdexp : b * rd = Real.exp ℓ := (Real.exp_log (by linarith)).symm
    have hMle : M ≤ Real.exp Lb := by
      have e1 : M = (n : ℝ) * f * g * (b * rd) := by rw [hM_def]; ring
      have e2 : Real.exp Lb = Real.exp s * Real.exp s * Real.exp (Cg * ℓ) * Real.exp ℓ := by
        rw [hLb_def, Real.exp_add, Real.exp_add, Real.exp_add]
      rw [e1, e2, hbrdexp]
      have a1 : (n : ℝ) * f ≤ Real.exp s * Real.exp s :=
        mul_le_mul hnexp hfexp (by positivity) (by positivity)
      have a2 : (n : ℝ) * f * g ≤ Real.exp s * Real.exp s * Real.exp (Cg * ℓ) :=
        mul_le_mul a1 hgexp (by linarith) (by positivity)
      exact mul_le_mul_of_nonneg_right a2 (by positivity)

    have htpos : 0 < t := lt_of_lt_of_le (pow_pos (inv_pos.2 hMpos) _) ht1
    have hinvt : t⁻¹ ≤ Real.exp (11 * s * Lb) := by
      rw [inv_pow] at ht1
      have a1 : t⁻¹ ≤ M ^ (11 * q) := inv_le_of_inv_le₀ (pow_pos hMpos _) ht1
      have a2 : M ^ (11 * q) ≤ Real.exp Lb ^ (11 * q) := pow_le_pow_left₀ hMpos.le hMle _
      have a3 : Real.exp Lb ^ (11 * q) = Real.exp (((11 * q : ℕ) : ℝ) * Lb) :=
        (Real.exp_nat_mul Lb (11 * q)).symm
      have a4 : ((11 * q : ℕ) : ℝ) * Lb ≤ 11 * s * Lb := by
        push_cast
        have : 11 * (q : ℝ) ≤ 11 * s := by linarith
        exact mul_le_mul_of_nonneg_right this hLb0
      calc t⁻¹ ≤ M ^ (11 * q) := a1
        _ ≤ Real.exp Lb ^ (11 * q) := a2
        _ = Real.exp (((11 * q : ℕ) : ℝ) * Lb) := a3
        _ ≤ Real.exp (11 * s * Lb) := Real.exp_le_exp.2 a4

    have hA : 3 * s / t ^ 2 ≤ Real.exp (2 + s + 22 * s * Lb) := by
      have e1 : 3 * s / t ^ 2 = 3 * s * (t⁻¹) ^ 2 := by rw [div_eq_mul_inv, inv_pow]
      have e2 : Real.exp (2 + s + 22 * s * Lb)
          = Real.exp 2 * Real.exp s * (Real.exp (11 * s * Lb)) ^ 2 := by
        rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [e1, e2]
      have b1 : (3 : ℝ) ≤ Real.exp 2 := by
        have := Real.add_one_le_exp 2
        linarith
      have b2 : s ≤ Real.exp s := by
        have := Real.add_one_le_exp s
        linarith
      have b3 : (t⁻¹) ^ 2 ≤ (Real.exp (11 * s * Lb)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hinvt 2
      have b4 : 3 * s ≤ Real.exp 2 * Real.exp s :=
        mul_le_mul b1 b2 (by linarith) (by positivity)
      exact mul_le_mul b4 b3 (by positivity) (by positivity)
    have hpow : (3 * s / t ^ 2) ^ (2 * (n ^ 2 * f))
        ≤ Real.exp (((2 * (n ^ 2 * f) : ℕ) : ℝ) * (2 + s + 22 * s * Lb)) := by
      rw [Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by positivity) hA _

    have hsmall : 2 * (f : ℝ) * 3 ^ f ≤ Real.exp (4 * f) := by
      have c1 : 2 * (f : ℝ) ≤ Real.exp (2 * f) := by
        have := Real.add_one_le_exp (2 * (f : ℝ))
        linarith
      have c2 : (3 : ℝ) ^ f ≤ Real.exp (f * 2) := by
        rw [Real.exp_nat_mul]
        have : (3 : ℝ) ≤ Real.exp 2 := by
          have := Real.add_one_le_exp 2
          linarith
        exact pow_le_pow_left₀ (by norm_num) this f
      have e : Real.exp (4 * f) = Real.exp (2 * f) * Real.exp (f * 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [e]
      exact mul_le_mul c1 c2 (by positivity) (by positivity)

    have hexp : ((2 * (n ^ 2 * f) : ℕ) : ℝ) * (2 + s + 22 * s * Lb) + (4 * f + -X)
        ≤ -((n : ℝ) ^ 2 * f) := by
      push_cast
      have hP0 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * f := by positivity
      have hKl0 : 0 ≤ (Cg + 1) * ℓ := mul_nonneg (by linarith) (by linarith)
      have k1 : (n : ℝ) ^ 2 * f * s * ((Cg + 1) * ℓ) ≤ (n : ℝ) ^ 2 * f * n * ((Cg + 1) * ℓ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsn hP0) hKl0
      have k2 : (n : ℝ) ^ 2 * f * s ≤ (n : ℝ) ^ 2 * f * n := mul_le_mul_of_nonneg_left hsn hP0
      have k3 : (f : ℝ) ≤ (n : ℝ) ^ 2 * f :=
        le_mul_of_one_le_left hfpos.le (one_le_pow₀ (by linarith))
      have k4 : (n : ℝ) ^ 2 * f * 3 ≤ (n : ℝ) ^ 2 * f * n := mul_le_mul_of_nonneg_left hnR hP0
      have k5 : (n : ℝ) ^ 2 * f * n * 107 ≤ (n : ℝ) ^ 2 * f * n * (156 * ℓ) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have k6 : 0 ≤ (n : ℝ) ^ 2 * f * n * (Cg * ℓ) :=
        mul_nonneg (by positivity) (mul_nonneg hCg (by linarith))
      have k7 : (n : ℝ) ^ 2 * f * s ^ 2 = (n : ℝ) ^ 2 * f * n := by rw [hs2]
      have k8 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * f * n := by positivity
      rw [hLb_def]
      linarith
    calc (3 * s / t ^ 2) ^ (2 * (n ^ 2 * f)) * (2 * f * 3 ^ f * Real.exp (-X))
        ≤ Real.exp (((2 * (n ^ 2 * f) : ℕ) : ℝ) * (2 + s + 22 * s * Lb))
            * (Real.exp (4 * f) * Real.exp (-X)) := by
          apply mul_le_mul hpow (mul_le_mul_of_nonneg_right hsmall (by positivity))
            (by positivity) (by positivity)
      _ = Real.exp (((2 * (n ^ 2 * f) : ℕ) : ℝ) * (2 + s + 22 * s * Lb) + (4 * f + -X)) := by
          rw [Real.exp_add, Real.exp_add]
      _ ≤ Real.exp (-((n : ℝ) ^ 2 * f)) := Real.exp_le_exp.2 hexp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.Imports
section
namespace GlobalTheory.TargetStatementBis

open NumberField

theorem main {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Λ : Submodule (𝓞 K) V)
    (h : Submodule.span K (Λ : Set V) = ⊤) (v : V) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • v ∈ Λ := by
  have hv : v ∈ Submodule.span K (Λ : Set V) := h ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.smul_mem _ h₁
    · rw [mul_smul]; exact Λ.smul_mem _ h₂
  | smul c x _ hx =>
    obtain ⟨d, hd, h₁⟩ := hx
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 K)) c
    refine ⟨d * b, mul_ne_zero hd (nonZeroDivisors.ne_zero b.2), ?_⟩
    have key : ((b : 𝓞 K)) • (c • x) = a • x := by
      rw [← algebraMap_smul K (b : 𝓞 K) (c • x), smul_smul, mul_comm, hab, algebraMap_smul]
    rw [mul_smul, key, smul_comm d a x]
    exact Λ.smul_mem a h₁

theorem target : ∀ {K V : Type} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V] [inst_3 : Module K V] [inst_4 : Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V] (Λ : Submodule (NumberField.RingOfIntegers K) V), Submodule.span K (↑Λ : Set V) = ⊤ → ∀ (v : V), ∃ (d : NumberField.RingOfIntegers K), d ≠ (0 : NumberField.RingOfIntegers K) ∧ d • v ∈ Λ :=
  fun Λ h v => main Λ h v

end GlobalTheory.TargetStatementBis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsBisBis
section
universe u_1 u_2

namespace GlobalTheory.NonzeroSmulMemSpanLattice

theorem exists_ne_zero_smul_mem {E : Type u_1} {V : Type u_2} [Field E] [NumberField E]
    [AddCommGroup V] [Module E V] [Module (NumberField.RingOfIntegers E) V]
    [IsScalarTower (NumberField.RingOfIntegers E) E V]
    (Λ : Submodule (NumberField.RingOfIntegers E) V) (hΛ : Submodule.IsFullLattice E Λ) (v : V) :
    ∃ o : NumberField.RingOfIntegers E, o ≠ 0 ∧ o • v ∈ Λ := by
  have hv : v ∈ Submodule.span E (Λ : Set V) := by
    rw [hΛ.span_eq_top]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.smul_mem b hax
    · rw [mul_smul]; exact Λ.smul_mem a hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨n, d, hd, hc⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers E) c
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hd1 : algebraMap (NumberField.RingOfIntegers E) E d ≠ 0 := by
      intro h
      exact hd0 ((IsFractionRing.injective (NumberField.RingOfIntegers E) E) (by simpa using h))
    refine ⟨d * a, mul_ne_zero hd0 ha, ?_⟩
    have key : (d * a) • c • x = n • a • x := by
      rw [← algebraMap_smul E (d * a), ← algebraMap_smul E n, ← algebraMap_smul E a,
        smul_smul, smul_smul, ← hc, map_mul]
      congr 1
      field_simp
    rw [key]
    exact Λ.smul_mem n hax

end GlobalTheory.NonzeroSmulMemSpanLattice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsBisExtra
section
namespace GlobalTheory.SublatticeFacts

open Matrix

theorem finiteRing_sq_sub_mul_sq_eq_of_card {A : Type} [CommRing A] {S : Subring A} {n : Type} [Fintype n] [DecidableEq n]
    (Λ : Submodule (↥S) (n → A)) (hfg : Submodule.FG Λ)
    (hden : ∀ (v : n → A), ∃ (N : ℕ), (1 : ℕ) ≤ N ∧ (↑N : A) • v ∈ Λ) (X : Matrix n n A) :
    ∃ (N : ℕ), (1 : ℕ) ≤ N ∧ ∀ y ∈ Λ, (↑N : A) • Matrix.mulVec X y ∈ Λ := by
  classical
  obtain ⟨t, rfl⟩ := hfg
  choose f hf1 hf using fun v : n → A => hden (X *ᵥ v)
  refine ⟨∏ v ∈ t, f v, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun v _ => by have := hf1 v; omega)
  · intro y hy
    rw [Nat.cast_smul_eq_nsmul A]
    induction hy using Submodule.span_induction with
    | mem x hx =>
      rw [← Finset.mul_prod_erase t f hx, mul_nsmul, ← Nat.cast_smul_eq_nsmul A (f x)]
      exact Submodule.smul_of_tower_mem _ (∏ v ∈ t.erase x, f v) (hf x)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [Matrix.mulVec_add, smul_add]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      have : X *ᵥ (a • x) = a • (X *ᵥ x) := by
        ext i
        simp [Matrix.mulVec, dotProduct, Finset.mul_sum, Subring.smul_def, mul_left_comm]
      rw [this, smul_comm]
      exact Submodule.smul_mem _ a hx

theorem main : ∀ {A : Type} [inst : CommRing A] {S : Subring A} {n : Type} [inst_1 : Fintype n] [DecidableEq n]
    (Λ : Submodule (↥S) (n → A)), Submodule.FG Λ →
    (∀ (v : n → A), ∃ (N : ℕ), (1 : ℕ) ≤ N ∧ (↑N : A) • v ∈ Λ) →
    ∀ (X : Matrix n n A), ∃ (N : ℕ), (1 : ℕ) ≤ N ∧ ∀ y ∈ Λ, (↑N : A) • Matrix.mulVec X y ∈ Λ :=
  fun Λ hfg hden X => finiteRing_sq_sub_mul_sq_eq_of_card Λ hfg hden X

end GlobalTheory.SublatticeFacts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsBisMore
section
namespace GlobalTheory.LatticeFactsFlagMeasures

theorem main : ∀ {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (a b : ℝ), (∀ (i j : Fin n), ‖A i j‖ ≤ a) → (∀ (i j : Fin n), ‖B i j‖ ≤ b) → ∀ (i j : Fin n), ‖(A * B) i j‖ ≤ (↑n : ℝ) * (a * b) := by
  intro n A B a b hA hB i j
  rw [Matrix.mul_apply]
  calc ‖∑ k, A i k * B k j‖ ≤ ∑ k, ‖A i k * B k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin n, a * b := by
        apply Finset.sum_le_sum
        intro k _
        rw [norm_mul]
        have ha : 0 ≤ a := le_trans (norm_nonneg _) (hA i k)
        exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) ha
    _ = (n : ℝ) * (a * b) := by simp

end GlobalTheory.LatticeFactsFlagMeasures
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsBisSide
section
namespace GlobalTheory.IntSmulMemSubmodule

theorem exists_int_smul_mem {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsFullLattice E L)
    (w : Fin n → E) : ∃ (N : ℤ), N ≠ (0 : ℤ) ∧ N • w ∈ L := by
  have hw : w ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩
  | zero => exact ⟨1, one_ne_zero, by rw [one_smul]; exact L.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h : (a * b) • (x + y) = b • (a • x) + a • (b • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm b a]
    rw [h]
    exact L.add_mem (zsmul_mem hax b) (zsmul_mem hby a)
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    have hc : IsAlgebraic ℤ c :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)
    obtain ⟨d, hd, hdc⟩ := hc.exists_integral_multiple
    refine ⟨d * a, mul_ne_zero hd ha, ?_⟩
    let r : NumberField.RingOfIntegers E := ⟨d • c, hdc⟩
    have h : (d * a) • (c • x) = r • (a • x) := by
      have h1 : r • (a • x) = (d • c) • (a • x) := rfl
      rw [h1, smul_assoc, mul_smul, smul_comm a c x]
    rw [h]
    exact L.smul_mem r hax

end GlobalTheory.IntSmulMemSubmodule
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsBisTer
section
open NumberField

namespace GlobalTheory.IntMulIntegral

theorem exists_int_mul_integral {K : Type} [Field K] [NumberField K] (z : K) :
    ∃ M : ℤ, M ≠ 0 ∧ IsIntegral ℤ ((M : K) * z) := by
  have hz : IsAlgebraic ℤ z :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic z)
  obtain ⟨y, hy, hint⟩ := hz.exists_integral_multiple
  refine ⟨y, hy, ?_⟩
  simpa [zsmul_eq_mul] using hint

theorem main : ∀ {K V : Type} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V] [inst_3 : Module K V]
    [inst_4 : Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    {A : Submodule (NumberField.RingOfIntegers K) V}, Submodule.span K (↑A : Set V) = ⊤ →
    ∀ (x : V), ∃ (N : ℤ), N ≠ (0 : ℤ) ∧ N • x ∈ A := by
  intro K V _ _ _ _ _ _ A hA x
  have hx : x ∈ Submodule.span K (↑A : Set V) := by rw [hA]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y w _ _ hy hw =>
    obtain ⟨N₁, h₁, m₁⟩ := hy
    obtain ⟨N₂, h₂, m₂⟩ := hw
    refine ⟨N₁ * N₂, mul_ne_zero h₁ h₂, ?_⟩
    rw [smul_add]
    refine A.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact A.smul_of_tower_mem N₂ m₁
    · rw [mul_smul]; exact A.smul_of_tower_mem N₁ m₂
  | smul c y _ hy =>
    obtain ⟨N, hN, m⟩ := hy
    obtain ⟨M, hM, hint⟩ := exists_int_mul_integral c
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    let o : NumberField.RingOfIntegers K := ⟨(M : K) * c, hint⟩
    have key : (M * N) • (c • y) = o • (N • y) := by
      rw [← algebraMap_smul K o (N • y)]
      have : algebraMap (NumberField.RingOfIntegers K) K o = (M : K) * c := rfl
      rw [this, mul_smul, mul_smul, ← Int.cast_smul_eq_zsmul K M, ← Int.cast_smul_eq_zsmul K N,
        ← Int.cast_smul_eq_zsmul K N, smul_comm c ((N : K)) y]
    rw [key]
    exact A.smul_mem o m

end GlobalTheory.IntMulIntegral
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsExtra
section
namespace GlobalTheory.ClearingDenominatorsInOrder

theorem main {E W : Type} [Field E] [NumberField E] [AddCommGroup W] [Module E W]
    [Module (NumberField.RingOfIntegers E) W]
    [IsScalarTower (NumberField.RingOfIntegers E) E W]
    (L : Submodule (NumberField.RingOfIntegers E) W) :
    ∀ v ∈ Submodule.span E (↑L : Set W),
      ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ c • v ∈ L := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c1, hc1, h1⟩ := hx
    obtain ⟨c2, hc2, h2⟩ := hy
    refine ⟨c1 * c2, mul_ne_zero hc1 hc2, ?_⟩
    rw [smul_add]
    apply L.add_mem
    · rw [mul_comm, mul_smul]; exact L.smul_mem c2 h1
    · rw [mul_smul]; exact L.smul_mem c1 h2
  | smul a x _ hx =>
    obtain ⟨c, hc, h⟩ := hx
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) a
    simp only at hnd
    have hd : (d : NumberField.RingOfIntegers E) ≠ 0 := nonZeroDivisors.coe_ne_zero d
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    have key : (d : NumberField.RingOfIntegers E) • (a • x) = n • x := by
      rw [← algebraMap_smul E (d : NumberField.RingOfIntegers E), smul_smul, mul_comm, hnd,
        algebraMap_smul]
    rw [mul_smul, key, smul_comm]
    exact L.smul_mem n h

end GlobalTheory.ClearingDenominatorsInOrder
end

