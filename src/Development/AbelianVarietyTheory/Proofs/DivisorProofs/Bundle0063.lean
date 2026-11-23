module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsBisLast
section
namespace GlobalTheory.IsotropicVectorExistence

theorem key {z : ℂ} (k : ℕ) (h : ∀ n : ℕ, ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) :
    (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : z ^ (2 ^ (k + 1)) - 1 = (z ^ (2 ^ k) - 1) * (z ^ (2 ^ k) + 1) := by
      rw [show 2 ^ (k + 1) = 2 ^ k * 2 from pow_succ 2 k, pow_mul]; ring
    have h2 : (3 / 2 : ℝ) ≤ ‖z ^ (2 ^ k) + 1‖ := by
      have h3 : (2 : ℂ) = (z ^ (2 ^ k) + 1) - (z ^ (2 ^ k) - 1) := by ring
      have h4 : ‖(2 : ℂ)‖ ≤ ‖z ^ (2 ^ k) + 1‖ + ‖z ^ (2 ^ k) - 1‖ := by
        rw [h3]; exact norm_sub_le _ _
      have h5 : ‖(2 : ℂ)‖ = 2 := by norm_num
      have h6 := h (2 ^ k)
      linarith
    rw [e, norm_mul, pow_succ]
    calc (3 / 2 : ℝ) ^ k * (3 / 2) * ‖z - 1‖ = ((3 / 2) ^ k * ‖z - 1‖) * (3 / 2) := by ring
      _ ≤ ‖z ^ (2 ^ k) - 1‖ * ‖z ^ (2 ^ k) + 1‖ :=
        mul_le_mul ih h2 (by norm_num) (norm_nonneg _)

theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / (2 * ‖z - 1‖)) (by norm_num : (1 : ℝ) < 3 / 2)
  rw [div_lt_iff₀ (by positivity)] at hk
  have a := key k h
  have b := h (2 ^ k)
  nlinarith

end GlobalTheory.IsotropicVectorExistence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsBisRest
section
namespace GlobalTheory.HermitianEigenvalueInequality

theorem main : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ} (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)), ∀ x ∈ Submodule.span E (↑L : Set (Fin n → E)), ∃ (d : NumberField.RingOfIntegers E), d ≠ (0 : NumberField.RingOfIntegers E) ∧ d • x ∈ L := by
  intro E _ _ n L x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d₁, hd₁, h₁⟩ := hy
    obtain ⟨d₂, hd₂, h₂⟩ := hz
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    have e : (d₁ * d₂) • (y + z) = d₂ • (d₁ • y) + d₁ • (d₂ • z) := by
      rw [smul_add, mul_comm, mul_smul, mul_comm, mul_smul]
    rw [e]
    exact L.add_mem (L.smul_mem _ h₁) (L.smul_mem _ h₂)
  | smul c y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers E)) c
    refine ⟨(b : NumberField.RingOfIntegers E) * d, mul_ne_zero (nonZeroDivisors.coe_ne_zero b) hd, ?_⟩
    have e : ((b : NumberField.RingOfIntegers E) * d) • (c • y) = a • (d • y) := by
      simp only at hab
      rw [← algebraMap_smul E ((b : NumberField.RingOfIntegers E) * d), ← algebraMap_smul E a,
        ← algebraMap_smul E d, smul_smul, smul_smul, map_mul, ]
      congr 1
      rw [← hab]
      ring
    rw [e]
    exact L.smul_mem _ h

end GlobalTheory.HermitianEigenvalueInequality
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsBisSide
section
namespace GlobalTheory.PositiveFormRecursion

theorem step (w : ℂ) (h : ‖w - 1‖ < 1/2) : (3/2 : ℝ) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by
  have h1 : w ^ 2 - 1 = (w - 1) * (w + 1) := by ring
  have h2 : (3/2 : ℝ) ≤ ‖w + 1‖ := by
    have e : (2 : ℂ) = (w + 1) - (w - 1) := by ring
    have h3 : ‖(2 : ℂ)‖ ≤ ‖w + 1‖ + ‖w - 1‖ := by
      rw [e]; exact norm_sub_le _ _
    have h4 : ‖(2 : ℂ)‖ = 2 := by norm_num
    linarith
  rw [h1, norm_mul]
  nlinarith [norm_nonneg (w - 1)]

theorem main : ∀ {z : ℂ}, (∀ (n : ℕ), ‖z ^ (2 : ℕ) ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z hz
  have key : ∀ n : ℕ, (3/2 : ℝ) ^ n * ‖z - 1‖ ≤ ‖z ^ (2 : ℕ) ^ n - 1‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : z ^ (2 : ℕ) ^ (n + 1) = (z ^ (2 : ℕ) ^ n) ^ 2 := by rw [pow_succ, pow_mul]
      rw [e]
      have hs := step (z ^ (2 : ℕ) ^ n) (hz n)
      calc (3/2 : ℝ) ^ (n + 1) * ‖z - 1‖ = (3/2) * ((3/2) ^ n * ‖z - 1‖) := by ring
        _ ≤ (3/2) * ‖z ^ (2 : ℕ) ^ n - 1‖ := by gcongr
        _ ≤ _ := hs
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1 / (2 * ‖z - 1‖)) (by norm_num : (1 : ℝ) < 3/2)
  have hn' := (div_lt_iff₀ (by positivity)).mp hn
  have h1 := key n
  have h2 := hz n
  nlinarith

end GlobalTheory.PositiveFormRecursion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraAlt
section
namespace GlobalTheory.TargetLemmaCollection

open NumberField

theorem main {K : Type} [Field K] [NumberField K] {Z : Type} [AddCommGroup Z] [Module K Z]
    [Module (RingOfIntegers K) Z] [IsScalarTower (RingOfIntegers K) K Z]
    {A : Submodule (RingOfIntegers K) Z} {x : Z} (hx : x ∈ Submodule.span K (A : Set Z)) :
    ∃ d : RingOfIntegers K, d ≠ 0 ∧ d • x ∈ A := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d₁, hd₁, h₁⟩ := hy
    obtain ⟨d₂, hd₂, h₂⟩ := hz
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    have e1 : (d₁ * d₂) • y = d₂ • (d₁ • y) := by rw [mul_comm, mul_smul]
    have e2 : (d₁ * d₂) • z = d₁ • (d₂ • z) := by rw [mul_smul]
    rw [e1, e2]
    exact A.add_mem (A.smul_mem _ h₁) (A.smul_mem _ h₂)
  | smul c y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (RingOfIntegers K)) c
    simp only at hab
    have hb : (b : RingOfIntegers K) ≠ 0 := nonZeroDivisors.coe_ne_zero b
    refine ⟨(b : RingOfIntegers K) * d, mul_ne_zero hb hd, ?_⟩
    have key : ((b : RingOfIntegers K) * d) • (c • y) = a • (d • y) := by
      rw [← smul_assoc, Algebra.smul_def, map_mul, mul_comm (algebraMap _ K (b : RingOfIntegers K)),
        mul_assoc, mul_comm _ c, hab, ← map_mul, algebraMap_smul, mul_comm, mul_smul]
    rw [key]
    exact A.smul_mem _ h

end GlobalTheory.TargetLemmaCollection

theorem GlobalTheory.TargetLemmaCollection.target : ∀ {K : Type} [inst : Field K] [NumberField K] {Z : Type} [inst_2 : AddCommGroup Z] [inst_3 : Module K Z] [inst_4 : Module (NumberField.RingOfIntegers K) Z] [IsScalarTower (NumberField.RingOfIntegers K) K Z] {A : Submodule (NumberField.RingOfIntegers K) Z} {x : Z}, x ∈ Submodule.span K (↑A : Set Z) → ∃ (d : NumberField.RingOfIntegers K), d ≠ (0 : NumberField.RingOfIntegers K) ∧ d • x ∈ A :=
  fun hx => GlobalTheory.TargetLemmaCollection.main hx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraBis
section
open FractionalIdeal nonZeroDivisors

namespace GlobalTheory.ClosingLemma

theorem main {Ω : Type} [Field Ω] (S : Type) [CommRing S] [IsDomain S] [IsDedekindDomain S]
    [Algebra S Ω] [IsFractionRing S Ω] (A : ValuationSubring Ω)
    (hS : ∀ s : S, algebraMap S Ω s ∈ A) {x : Ω} (hx : x ∈ A) :
    ∃ s t : S, A.valuation (algebraMap S Ω s) = 1 ∧ algebraMap S Ω s * x = algebraMap S Ω t := by
  by_contra hcon
  push_neg at hcon
  have hSle : ∀ c : S, A.valuation (algebraMap S Ω c) ≤ 1 := fun c => (A.valuation_le_one_iff _).2 (hS c)
  let M : Submodule S Ω :=
    { carrier := {z | A.valuation z < 1}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        exact Valuation.map_add_lt _ ha hb
      zero_mem' := by simp
      smul_mem' := by
        intro c z hz
        simp only [Set.mem_setOf_eq, Algebra.smul_def, map_mul] at hz ⊢
        calc A.valuation (algebraMap S Ω c) * A.valuation z ≤ 1 * A.valuation z := by
              gcongr; exact hSle c
          _ < 1 := by simpa using hz }
  let N : Submodule S Ω :=
    { carrier := {z | A.valuation z ≤ 1}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        exact (Valuation.map_add _ _ _).trans (max_le ha hb)
      zero_mem' := by simp
      smul_mem' := by
        intro c z hz
        simp only [Set.mem_setOf_eq, Algebra.smul_def, map_mul] at hz ⊢
        calc A.valuation (algebraMap S Ω c) * A.valuation z ≤ 1 * 1 := by
              gcongr; exact hSle c
          _ = 1 := one_mul 1 }
  let J : FractionalIdeal S⁰ Ω := 1 + spanSingleton S⁰ x
  have hJ1 : (1 : FractionalIdeal S⁰ Ω) ≤ J := by
    show (1 : FractionalIdeal S⁰ Ω) ≤ 1 + spanSingleton S⁰ x
    rw [← sup_eq_add]; exact le_sup_left
  have hJ0 : J ≠ 0 := by
    intro h
    rw [h] at hJ1
    exact one_ne_zero (le_antisymm hJ1 (zero_le _))
  have hJN : (J : Submodule S Ω) ≤ N := by
    simp only [J, coe_add, coe_one, coe_spanSingleton]
    refine sup_le ?_ ?_
    · intro z hz
      obtain ⟨c, rfl⟩ := Submodule.mem_one.1 hz
      exact hSle c
    · rw [Submodule.span_le]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact (A.valuation_le_one_iff _).2 hx
  have hinv : ((J⁻¹ : FractionalIdeal S⁰ Ω) : Submodule S Ω) ≤ M := by
    intro y hy
    have hy' := (mem_inv_iff hJ0).1 hy
    obtain ⟨s, hs⟩ := (mem_one_iff S⁰).1 (by simpa using hy' 1 (hJ1 (one_mem_one _)))
    have hxJ : x ∈ J := by
      show x ∈ (J : Submodule S Ω)
      simp only [J, coe_add, coe_one, coe_spanSingleton]
      exact Submodule.mem_sup_right (Submodule.subset_span rfl)
    obtain ⟨t, ht⟩ := (mem_one_iff S⁰).1 (hy' x hxJ)
    show A.valuation y < 1
    rw [← hs] at ht ⊢
    exact lt_of_le_of_ne (hSle s) (fun h => hcon s t h ht.symm)
  have hmul : ((J * J⁻¹ : FractionalIdeal S⁰ Ω) : Submodule S Ω) ≤ M := by
    rw [coe_mul, Submodule.mul_le]
    intro z hz y hy
    show A.valuation (z * y) < 1
    rw [map_mul]
    calc A.valuation z * A.valuation y ≤ 1 * A.valuation y := by gcongr; exact hJN hz
      _ < 1 := by rw [one_mul]; exact hinv hy
  rw [mul_inv_cancel₀ hJ0, coe_one] at hmul
  have := hmul (Submodule.one_le.1 le_rfl)
  exact absurd this (by show ¬ A.valuation 1 < 1; simp)

end GlobalTheory.ClosingLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraLast
section
namespace GlobalTheory.NonzeroSmulMembership

theorem exists_ne_zero_smul_mem {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)) (hL : Submodule.IsFullLattice E L)
    (x : Fin n → E) :
    ∃ (d : NumberField.RingOfIntegers E), d ≠ (0 : NumberField.RingOfIntegers E) ∧ d • x ∈ L := by
  have hx : x ∈ Submodule.span E (L : Set (Fin n → E)) := by
    rw [hL.span_eq_top]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 : (a * b) • y = b • a • y := by rw [mul_comm, mul_smul]
    rw [smul_add, h1, mul_smul]
    exact L.add_mem (L.smul_mem b hay) (L.smul_mem a hbz)
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := NumberField.RingOfIntegers E) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hq1 : algebraMap (NumberField.RingOfIntegers E) E q ≠ 0 := by
      intro h
      exact hq0 (IsFractionRing.injective (NumberField.RingOfIntegers E) E (by simpa using h))
    refine ⟨q * a, mul_ne_zero hq0 ha, ?_⟩
    have key : (q * a) • ((algebraMap (NumberField.RingOfIntegers E) E p /
        algebraMap (NumberField.RingOfIntegers E) E q) • y) = p • a • y := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      simp only [Algebra.smul_def, map_mul]
      field_simp
    rw [key]
    exact L.smul_mem p hay

end GlobalTheory.NonzeroSmulMembership
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraSide
section
namespace GlobalTheory.ClosingLemmaFourth

theorem main : ∀ {z : ℂ} {d : ℕ}, (0 : ℕ) < d → z ^ (2 : ℕ) = -(↑d : ℂ) →
    (starRingEnd ℂ : ℂ → ℂ) z = -z ∧ z ≠ (0 : ℂ) := by
  intro z d hd h
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him
  have hr : z.re = 0 := by
    have h2 : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · rw [h3] at hre
      nlinarith [sq_nonneg z.re]
  refine ⟨?_, ?_⟩
  · apply Complex.ext <;> simp [hr]
  · rintro rfl
    simp at hre
    linarith

end GlobalTheory.ClosingLemmaFourth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsFurtherExtra
section
namespace GlobalTheory.SpectralLemmaSecond

open Matrix

theorem main : (let d1 : {m k : Type} → [Fintype m] → [Fintype k] → Matrix m k ℂ → ℝ := @(fun {m k : Type} [Fintype m] [Fintype k] (M : Matrix m k ℂ) ↦ ∑ i : m, ∑ j : k, ‖M i j‖); ∀ {m k p : Type} [inst : Fintype m] [inst_1 : Fintype k] [inst_2 : Fintype p] (M : Matrix m k ℂ) (N : Matrix k p ℂ), d1 (M * N) ≤ d1 M * d1 N) := by
  intro d1 m k p _ _ _ M N
  simp only [d1]
  have hB : ∀ l : k, ∑ j : p, ‖N l j‖ ≤ ∑ l' : k, ∑ j : p, ‖N l' j‖ := fun l =>
    Finset.single_le_sum (f := fun l' => ∑ j : p, ‖N l' j‖)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.mem_univ l)
  calc ∑ i : m, ∑ j : p, ‖(M * N) i j‖
      ≤ ∑ i : m, ∑ j : p, ∑ l : k, ‖M i l‖ * ‖N l j‖ := by
        gcongr with i _ j _
        rw [Matrix.mul_apply]
        refine (norm_sum_le _ _).trans ?_
        gcongr with l _
        exact (norm_mul _ _).le
    _ = ∑ i : m, ∑ l : k, ‖M i l‖ * ∑ j : p, ‖N l j‖ := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [Finset.mul_sum]
    _ ≤ ∑ i : m, ∑ l : k, ‖M i l‖ * ∑ l' : k, ∑ j : p, ‖N l' j‖ := by
        gcongr with i _ l _
        exact hB l
    _ = (∑ i : m, ∑ l : k, ‖M i l‖) * ∑ l' : k, ∑ j : p, ‖N l' j‖ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_mul]

end GlobalTheory.SpectralLemmaSecond
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsFurtherLast
section
namespace GlobalTheory.ValuationExtensionExistence

theorem exists_extension {V R K : Type} [CommRing V] [CommRing R] [IsDomain R] [Field K]
    [IsAlgClosed K] [Algebra V R] [Algebra.IsIntegral V R] [FaithfulSMul V R] (ev : V →+* K) :
    ∃ ev₁ : R →+* K, ev₁.comp (algebraMap V R) = ev := by
  classical

  have : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := R) (RingHom.ker ev) ⊥ (by
    rw [(show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective V R))]
    exact bot_le)
  have := hQ
  have : Q.LiesOver (RingHom.ker ev) := ⟨hQp.symm⟩

  let : Algebra (V ⧸ RingHom.ker ev) K := (RingHom.kerLift ev).toAlgebra
  have : Module.IsTorsionFree (V ⧸ RingHom.ker ev) K :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (RingHom.kerLift_injective ev)
  have : Module.IsTorsionFree (V ⧸ RingHom.ker ev) (R ⧸ Q) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective _ _)
  have : Algebra.IsIntegral (V ⧸ RingHom.ker ev) (R ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver Q (RingHom.ker ev)
  have : Algebra.IsAlgebraic (V ⧸ RingHom.ker ev) (R ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let f : R ⧸ Q →ₐ[V ⧸ RingHom.ker ev] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨(f : R ⧸ Q →+* K).comp (Ideal.Quotient.mk Q), ?_⟩
  ext v
  have h := f.commutes (Ideal.Quotient.mk (RingHom.ker ev) v)
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver] at h
  exact h.trans (RingHom.kerLift_mk ev v)

theorem main : ∀ (V R K : Type) [inst : CommRing V] [IsDomain V] [IsLocalRing V]
    [inst_3 : CommRing R] [IsDomain R] [IsLocalRing R] [inst_6 : Field K] [IsAlgClosed K]
    (ρ : V →+* R), Function.Injective (⇑ρ : V → R) → RingHom.Finite ρ →
      IsLocalHom ρ ∧ ∀ (ev : V →+* K), ∃ (ev₁ : R →+* K), RingHom.comp ev₁ ρ = ev := by
  intro V R K _ _ _ _ _ _ _ _ ρ hinj hfin
  have hint : ρ.IsIntegral := hfin.to_isIntegral
  refine ⟨?_, fun ev => ?_⟩
  · refine ((IsLocalRing.local_hom_tfae ρ).out 5 1).mp ?_
    exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' ρ hint _)
  · let := ρ.toAlgebra
    have : Algebra.IsIntegral V R := ⟨hint⟩
    have : FaithfulSMul V R := (faithfulSMul_iff_algebraMap_injective V R).2 hinj
    exact exists_extension ev

end GlobalTheory.ValuationExtensionExistence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsFurtherTail
section
namespace GlobalTheory.IntegralNormAtMostOne

theorem norm_le_one_of_isIntegral {l : ℕ} [hl : Fact (Nat.Prime l)] {y : ℂ_[l]}
    (hy : IsIntegral ℤ y) : ‖y‖ ≤ (1 : ℝ) := by
  obtain ⟨p, hp, hpy⟩ := hy
  by_contra hcon
  have h1 : 1 < ‖y‖ := not_le.mp hcon
  have h0 : 0 < ‖y‖ := lt_trans one_pos h1
  rw [← Polynomial.aeval_def, Polynomial.aeval_eq_sum_range, Finset.sum_range_succ,
    hp.coeff_natDegree, one_smul] at hpy
  have heq : y ^ p.natDegree = - ∑ i ∈ Finset.range p.natDegree, p.coeff i • y ^ i :=
    eq_neg_of_add_eq_zero_right hpy
  have hlt : ∀ (s : Finset ℕ), (∀ i ∈ s, i < p.natDegree) →
      ‖∑ i ∈ s, p.coeff i • y ^ i‖ < ‖y‖ ^ p.natDegree := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro _; simpa using pow_pos h0 _
    | insert a s ha ih =>
      intro hs
      rw [Finset.sum_insert ha]
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
      · rw [zsmul_eq_mul, norm_mul, norm_pow]
        have hc : ‖((p.coeff a : ℤ) : ℂ_[l])‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one _ _
        calc ‖((p.coeff a : ℤ) : ℂ_[l])‖ * ‖y‖ ^ a ≤ 1 * ‖y‖ ^ a :=
              mul_le_mul_of_nonneg_right hc (pow_nonneg h0.le _)
          _ = ‖y‖ ^ a := one_mul _
          _ < ‖y‖ ^ p.natDegree := pow_lt_pow_right₀ h1 (hs a (Finset.mem_insert_self _ _))
      · exact ih fun i hi => hs i (Finset.mem_insert_of_mem hi)
  have := hlt (Finset.range p.natDegree) fun i hi => Finset.mem_range.mp hi
  rw [← norm_neg, ← heq, norm_pow] at this
  exact lt_irrefl _ this

end GlobalTheory.IntegralNormAtMostOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsMoreFurther
section
namespace GlobalTheory.TargetEquivalence

open Finset

theorem main {R α β : Type} [AddCommMonoid R] [Fintype α] [Fintype β]
    (f : α → β → α → β → R) :
    ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ c : α, ∑ e : β, ∑ b : β, ∑ a : α, f a b c e := by
  calc ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e
      = ∑ a : α, ∑ c : α, ∑ b : β, ∑ e : β, f a b c e := by
        refine Finset.sum_congr rfl fun a _ => ?_
        exact Finset.sum_comm
    _ = ∑ c : α, ∑ a : α, ∑ b : β, ∑ e : β, f a b c e := Finset.sum_comm
    _ = ∑ c : α, ∑ a : α, ∑ e : β, ∑ b : β, f a b c e := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
        exact Finset.sum_comm
    _ = ∑ c : α, ∑ e : β, ∑ a : α, ∑ b : β, f a b c e := by
        refine Finset.sum_congr rfl fun c _ => ?_
        exact Finset.sum_comm
    _ = ∑ c : α, ∑ e : β, ∑ b : β, ∑ a : α, f a b c e := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
        exact Finset.sum_comm

theorem target : ∀ {R α β : Type} [inst : AddCommMonoid R] [inst_1 : Fintype α] [inst_2 : Fintype β] (f : α → β → α → β → R), ∑ a : α, ∑ b : β, ∑ c : α, ∑ e : β, f a b c e = ∑ c : α, ∑ e : β, ∑ b : β, ∑ a : α, f a b c e :=
  fun f => main f

end GlobalTheory.TargetEquivalence
end

