module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanInfEq
section
namespace GlobalTheory.SpanInfEq

open NumberField

theorem exists_smul_mem {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V]
    [Module K V] [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
    (L : Submodule (RingOfIntegers K) V) (hL : Submodule.IsFullLattice K L) (v : V) :
    ∃ d : RingOfIntegers K, d ≠ 0 ∧ d • v ∈ L := by
  have hv : v ∈ Submodule.span K (L : Set V) := by rw [hL.span_eq_top]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem _ h₁
    · rw [mul_smul]; exact L.smul_mem _ h₂
  | smul c x _ hx =>
    obtain ⟨d, hd, h⟩ := hx
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := RingOfIntegers K) c
    refine ⟨b * d, mul_ne_zero (nonZeroDivisors.ne_zero hb) hd, ?_⟩
    have hb' : algebraMap (RingOfIntegers K) K b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have : (b * d) • ((algebraMap (RingOfIntegers K) K a / algebraMap (RingOfIntegers K) K b) • x)
        = a • (d • x) := by
      rw [← algebraMap_smul K (b * d), ← algebraMap_smul K d, ← algebraMap_smul K a, smul_smul,
        smul_smul, map_mul]
      congr 1
      field_simp
    rw [this]
    exact L.smul_mem _ h

theorem span_inf_eq {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V]
    [Module K V] [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
    (L : Submodule (RingOfIntegers K) V) (hL : Submodule.IsFullLattice K L) (T : Submodule K V) :
    Submodule.span K (↑(L ⊓ Submodule.restrictScalars (RingOfIntegers K) T) : Set V) = T := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact (Submodule.mem_inf.mp hx).2
  · intro v hv
    obtain ⟨d, hd, h⟩ := exists_smul_mem L hL v
    have hd' : algebraMap (RingOfIntegers K) K d ≠ 0 := by
      intro h0
      exact hd ((map_eq_zero_iff _ (IsFractionRing.injective (RingOfIntegers K) K)).mp h0)
    have hdT : d • v ∈ Submodule.restrictScalars (RingOfIntegers K) T := by
      rw [← algebraMap_smul K d v]
      exact T.smul_mem _ hv
    have hmem : d • v ∈ L ⊓ Submodule.restrictScalars (RingOfIntegers K) T :=
      Submodule.mem_inf.mpr ⟨h, hdT⟩
    have : v = (algebraMap (RingOfIntegers K) K d)⁻¹ • (d • v) := by
      rw [← algebraMap_smul K d v, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem main : ∀ {K : Type} [inst : Field K] [NumberField K] {V : Type} [inst_2 : AddCommGroup V]
    [inst_3 : Module K V] [inst_4 : Module (NumberField.RingOfIntegers K) V]
    [inst_5 : IsScalarTower (NumberField.RingOfIntegers K) K V]
    (L : Submodule (NumberField.RingOfIntegers K) V), Submodule.IsFullLattice K L →
    ∀ (T : Submodule K V),
    Submodule.span K (↑(L ⊓ Submodule.restrictScalars (NumberField.RingOfIntegers K) T) : Set V) = T :=
  fun L hL T => span_inf_eq L hL T

end GlobalTheory.SpanInfEq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqIntervalIntegralLeMulIntervalIntegralSq
section
open MeasureTheory

namespace GlobalTheory

theorem sq_intervalIntegral_le_mul_intervalIntegral_sq (g : ℝ → ℝ) (s : ℝ) (hs : 0 < s)
    (hg : ContinuousOn g (Set.Icc 0 s)) :
    (∫ t in (0 : ℝ)..s, g t) ^ 2 ≤ s * ∫ t in (0 : ℝ)..s, g t ^ 2 := by
  have hIcc : Set.uIcc (0 : ℝ) s = Set.Icc 0 s := Set.uIcc_of_le hs.le
  have hg1 : IntervalIntegrable g volume 0 s := (hg.mono hIcc.subset).intervalIntegrable
  have hg2 : IntervalIntegrable (fun t => g t ^ 2) volume 0 s :=
    ((hg.pow 2).mono hIcc.subset).intervalIntegrable
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (∫ t in (0 : ℝ)..s, g t) / s := ⟨_, rfl⟩
  have hcs : c * s = ∫ t in (0 : ℝ)..s, g t := by rw [hc]; exact div_mul_cancel₀ _ hs.ne'
  have h0 : 0 ≤ ∫ t in (0 : ℝ)..s, (g t - c) ^ 2 :=
    intervalIntegral.integral_nonneg hs.le (fun t _ => sq_nonneg _)
  have hexp : (fun t => (g t - c) ^ 2) = fun t => (g t ^ 2 - (2 * c) * g t) + c ^ 2 := by
    funext t; ring
  rw [hexp, intervalIntegral.integral_add (hg2.sub (hg1.const_mul (2 * c))) intervalIntegrable_const,
    intervalIntegral.integral_sub hg2 (hg1.const_mul (2 * c)), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at h0
  simp only [sub_zero, smul_eq_mul] at h0
  have hsq : s * c ^ 2 = c * ∫ t in (0 : ℝ)..s, g t := by rw [← hcs]; ring
  have h1 : c * (∫ t in (0 : ℝ)..s, g t) ≤ ∫ t in (0 : ℝ)..s, g t ^ 2 := by linarith
  have h2 : (∫ t in (0 : ℝ)..s, g t) ^ 2 = s * (c * ∫ t in (0 : ℝ)..s, g t) := by
    rw [← hcs]; ring
  rw [h2]
  exact mul_le_mul_of_nonneg_left h1 hs.le

theorem sobolev_endpoint_one_variable : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (φ φ' : ℝ → H) (s : ℝ), 0 < s → (∀ t ∈ Set.Icc 0 s, HasDerivAt φ (φ' t) t) → ContinuousOn φ' (Set.Icc 0 s) → ‖φ 0‖ ^ 2 ≤ 2 / s * (∫ t in (0 : ℝ)..s, ‖φ t‖ ^ 2) + 2 * s * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2 := by
  intro H _ _ _ φ φ' s hs hd hc
  have hIcc : Set.uIcc (0 : ℝ) s = Set.Icc 0 s := Set.uIcc_of_le hs.le
  have hφc : ContinuousOn φ (Set.Icc 0 s) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hn' : ContinuousOn (fun t => ‖φ' t‖) (Set.Icc 0 s) := hc.norm
  have hn'i : IntervalIntegrable (fun t => ‖φ' t‖) volume 0 s :=
    (hn'.mono hIcc.subset).intervalIntegrable
  have hA : IntervalIntegrable (fun t => ‖φ t‖ ^ 2) volume 0 s :=
    ((hφc.norm.pow 2).mono hIcc.subset).intervalIntegrable
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) s,
      ‖φ 0‖ ^ 2 ≤ 2 * ‖φ t‖ ^ 2 + 2 * (∫ y in (0 : ℝ)..s, ‖φ' y‖) ^ 2 := by
    intro t ht
    have hsub : Set.uIcc 0 t ⊆ Set.Icc 0 s := by
      rw [Set.uIcc_of_le ht.1]; exact Set.Icc_subset_Icc le_rfl ht.2
    have hint : IntervalIntegrable φ' volume 0 t := (hc.mono hsub).intervalIntegrable
    have hftc : ∫ y in (0 : ℝ)..t, φ' y = φ t - φ 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hd x (hsub hx)) hint
    have h1 : ‖φ 0‖ ≤ ‖φ t‖ + ‖∫ y in (0 : ℝ)..t, φ' y‖ := by
      rw [hftc]
      have := norm_sub_le (φ t) (φ t - φ 0)
      rwa [sub_sub_cancel] at this
    have h2 : ‖∫ y in (0 : ℝ)..t, φ' y‖ ≤ ∫ y in (0 : ℝ)..t, ‖φ' y‖ :=
      intervalIntegral.norm_integral_le_integral_norm ht.1
    have h3 : ∫ y in (0 : ℝ)..t, ‖φ' y‖ ≤ ∫ y in (0 : ℝ)..s, ‖φ' y‖ :=
      intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (Filter.Eventually.of_forall fun y => norm_nonneg _) hn'i
    have h4 : ‖φ 0‖ ≤ ‖φ t‖ + ∫ y in (0 : ℝ)..s, ‖φ' y‖ := by linarith
    nlinarith [norm_nonneg (φ 0), mul_nonneg (norm_nonneg (φ 0)) (sub_nonneg.2 h4),
      sq_nonneg (‖φ t‖ - ∫ y in (0 : ℝ)..s, ‖φ' y‖),
      sq_nonneg (‖φ t‖ + (∫ y in (0 : ℝ)..s, ‖φ' y‖) - ‖φ 0‖)]
  have hmono : ∫ _ in (0 : ℝ)..s, ‖φ 0‖ ^ 2 ≤
      ∫ t in (0 : ℝ)..s, (2 * ‖φ t‖ ^ 2 + 2 * (∫ y in (0 : ℝ)..s, ‖φ' y‖) ^ 2) :=
    intervalIntegral.integral_mono_on hs.le intervalIntegrable_const
      ((hA.const_mul 2).add intervalIntegrable_const) hpt
  rw [intervalIntegral.integral_const,
    intervalIntegral.integral_add (hA.const_mul 2) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hmono
  simp only [sub_zero, smul_eq_mul] at hmono
  have hCS : (∫ y in (0 : ℝ)..s, ‖φ' y‖) ^ 2 ≤ s * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2 :=
    sq_intervalIntegral_le_mul_intervalIntegral_sq (fun t => ‖φ' t‖) s hs hn'
  have key : ‖φ 0‖ ^ 2 * s ≤
      2 * (∫ t in (0 : ℝ)..s, ‖φ t‖ ^ 2) + 2 * s ^ 2 * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hCS hs.le]
  calc ‖φ 0‖ ^ 2 = ‖φ 0‖ ^ 2 * s / s := by field_simp
    _ ≤ (2 * (∫ t in (0 : ℝ)..s, ‖φ t‖ ^ 2) + 2 * s ^ 2 * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2) / s := by
      gcongr
    _ = 2 / s * (∫ t in (0 : ℝ)..s, ‖φ t‖ ^ 2) + 2 * s * ∫ t in (0 : ℝ)..s, ‖φ' t‖ ^ 2 := by
      field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SqSumEqSumSqAddTwoMulSumLt
section
open Matrix Finset Real

namespace GlobalTheory


open Matrix Finset Real in
theorem _root_.GlobalTheory.sq_sum_eq_sum_sq_add_two_mul_sum_lt (a : ℕ) (j : Fin a → ℤ) :
    (∑ i, j i) ^ 2 = ∑ i, j i ^ 2 + 2 * ∑ i, ∑ k, if i < k then j i * j k else 0 := by
  have h : ∀ i k : Fin a, j i * j k = (if i < k then j i * j k else 0) +
      (if k < i then j k * j i else 0) + (if i = k then j i ^ 2 else 0) := by
    intro i k
    rcases lt_trichotomy i k with hik | hik | hik
    · simp [hik, hik.ne, not_lt.mpr hik.le]
    · subst hik; simp [sq]
    · simp [hik, hik.ne', not_lt.mpr hik.le, mul_comm]
  calc (∑ i, j i) ^ 2 = ∑ i, ∑ k, j i * j k := by rw [sq, Finset.sum_mul_sum]
    _ = ∑ i, ∑ k, ((if i < k then j i * j k else 0) + (if k < i then j k * j i else 0) +
          (if i = k then j i ^ 2 else 0)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => h i k
    _ = _ := by
        simp only [Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun i k => if k < i then j k * j i else 0)]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
        ring


open Matrix Finset Real in
theorem _root_.GlobalTheory.dim_unipotent_radical_identities :
    ∀ (a : ℕ) (j : Fin a → ℤ) (n : ℤ), let J := ∑ i, j i; let n₀ := n - 2 * J; let dimN := 4 * (∑ i, ∑ k, if i < k then j i * j k else 0) + 2 * J * n₀ + ∑ i, j i ^ 2; dimN = 2 * J ^ 2 - ∑ i, j i ^ 2 + 2 * J * n₀ ∧ n ^ 2 = n₀ ^ 2 + 2 * ∑ i, j i ^ 2 + 2 * dimN ∧ dimN ≤ 2 * J * n := by
  intro a j n
  dsimp only
  have key := _root_.GlobalTheory.sq_sum_eq_sum_sq_add_two_mul_sum_lt a j
  have hQ : 0 ≤ ∑ i, j i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (j i)
  generalize (∑ i, ∑ k, if i < k then j i * j k else 0) = S at key ⊢
  generalize (∑ i, j i ^ 2) = Q at key hQ ⊢
  generalize (∑ i, j i) = J at key ⊢
  refine ⟨by linear_combination (-2) * key, by linear_combination 4 * key, ?_⟩
  nlinarith [key, sq_nonneg J, hQ]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StarProjectionInfOrthogonalEqOfMemOrthogonal
section
open Finset
open scoped InnerProductSpace

namespace GlobalTheory

theorem starProjection_inf_orthogonal_eq_sub {n : ℕ}
    (A A' : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (h : A' ≤ A) (y : EuclideanSpace ℂ (Fin n))
    (hy : y ∈ A) : (A ⊓ A'ᗮ).starProjection y = y - A'.starProjection y := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact Submodule.mem_inf.2
      ⟨A.sub_mem hy (h (A'.starProjection_apply_mem y)), A'.sub_starProjection_mem_orthogonal y⟩
  · intro w hw
    rw [sub_sub_cancel]
    exact Submodule.inner_right_of_mem_orthogonal (A'.starProjection_apply_mem y)
      (Submodule.mem_inf.1 hw).2

theorem starProjection_inf_orthogonal_eq_of_mem_orthogonal {n : ℕ}
    (C C' : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (h : C' ≤ C) (v : EuclideanSpace ℂ (Fin n))
    (hv : v ∈ C'ᗮ) : (C ⊓ C'ᗮ).starProjection v = C.starProjection v := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · refine Submodule.mem_inf.2 ⟨C.starProjection_apply_mem v, ?_⟩
    rw [Submodule.mem_orthogonal]
    intro z hz
    rw [← Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.2 (h hz)]
    exact Submodule.inner_right_of_mem_orthogonal hz hv
  · intro w hw
    exact C.starProjection_inner_eq_zero v w (Submodule.mem_inf.1 hw).1

theorem infDist_le_norm_block_mul (n : ℕ)
    (A A' B B' C C' : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (D T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hD : ∀ x, ‖D x‖ = ‖x‖) (hA : A' ≤ A) (hC : C' ≤ C)
    (hB : ∀ x ∈ B, ∀ z ∈ C', ⟪z, D x⟫_ℂ = 0) (hB' : ∀ x ∈ B', ∀ z ∈ C, ⟪z, D x⟫_ℂ = 0)
    (hdim : Module.finrank ℂ C + Module.finrank ℂ B' = n)
    (hT : ∀ y ∈ A, T y ∈ B) (hT' : ∀ y ∈ A', T y ∈ B') (y : EuclideanSpace ℂ (Fin n))
    (hy : y ∈ A) :
    Metric.infDist (T y) (B' : Set (EuclideanSpace ℂ (Fin n))) ≤
      ‖(C ⊓ C'ᗮ).starProjection ∘L (D ∘L T) ∘L (A ⊓ A'ᗮ).starProjection‖ * ‖y‖ := by
  have hmap : B'.map (D : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) = Cᗮ := by
    have hinj : Function.Injective (D : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := by
      intro a b hab
      have h0 : ‖D (a - b)‖ = 0 := by
        rw [map_sub]
        simp only [ContinuousLinearMap.coe_coe] at hab
        rw [hab, sub_self, norm_zero]
      rwa [hD, norm_eq_zero, sub_eq_zero] at h0
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨x, hx, rfl⟩
      rw [Submodule.mem_orthogonal]
      intro z hz
      exact hB' x hx z hz
    · rw [← (Submodule.equivMapOfInjective _ hinj B').finrank_eq]
      symm
      apply Submodule.finrank_add_finrank_orthogonal'
      rw [finrank_euclideanSpace_fin]
      exact hdim
  have hy1 : (A ⊓ A'ᗮ).starProjection y = y - A'.starProjection y :=
    starProjection_inf_orthogonal_eq_sub A A' hA y hy
  have hy1A : (A ⊓ A'ᗮ).starProjection y ∈ A := by
    rw [hy1]
    exact A.sub_mem hy (hA (A'.starProjection_apply_mem y))
  set w := D (T ((A ⊓ A'ᗮ).starProjection y)) with hw_def
  have hw : w ∈ C'ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    exact hB _ (hT _ hy1A) z hz
  obtain ⟨b, hb, hbw⟩ : ∃ b ∈ B', D b = Cᗮ.starProjection w := by
    have hmem : Cᗮ.starProjection w ∈
        B'.map (D : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := by
      rw [hmap]
      exact Cᗮ.starProjection_apply_mem w
    obtain ⟨b, hb, hbw⟩ := hmem
    exact ⟨b, hb, hbw⟩
  have hmemB' : T (A'.starProjection y) + b ∈ B' :=
    B'.add_mem (hT' _ (A'.starProjection_apply_mem y)) hb
  calc Metric.infDist (T y) (B' : Set (EuclideanSpace ℂ (Fin n)))
      ≤ dist (T y) (T (A'.starProjection y) + b) := Metric.infDist_le_dist_of_mem hmemB'
    _ = ‖T ((A ⊓ A'ᗮ).starProjection y) - b‖ := by
      rw [dist_eq_norm, hy1, map_sub]
      congr 1
      abel
    _ = ‖w - Cᗮ.starProjection w‖ := by
      rw [← hD, map_sub, hbw]
    _ = ‖C.starProjection w‖ := by
      rw [Submodule.starProjection_orthogonal_val, sub_sub_cancel]
    _ = ‖(C ⊓ C'ᗮ).starProjection w‖ := by
      rw [starProjection_inf_orthogonal_eq_of_mem_orthogonal C C' hC w hw]
    _ = ‖((C ⊓ C'ᗮ).starProjection ∘L (D ∘L T) ∘L (A ⊓ A'ᗮ).starProjection) y‖ := rfl
    _ ≤ _ := ContinuousLinearMap.le_opNorm _ _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumFibreTwoIndexEncardBound
section
open scoped ENNReal Classical

namespace GlobalTheory

theorem sum_fibre_two_index_bound : ∀ (α Θ : Type) (S : Finset α) (xf yf : α → ℕ) (Φ : α → Θ) (Tr : ℕ → ℕ → Set Θ) (f : α → ℝ) (B₁ B₂ : ℕ → ℝ) (R₁ R₂ : Finset ℕ), (∀ a ∈ S, 0 ≤ f a) → (∀ a ∈ S, xf a ∈ R₁ ∧ yf a ∈ R₂ ∧ Φ a ∈ Tr (xf a) (yf a)) → (∀ a ∈ S, ∑ b ∈ S.filter (fun b => Φ b = Φ a ∧ xf b = xf a ∧ yf b = yf a), f b ≤ B₁ (xf a) * B₂ (yf a)) → ENNReal.ofReal (∑ a ∈ S, f a) ≤ ∑ x ∈ R₁, ∑ y ∈ R₂, (((Tr x y).encard : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (B₁ x * B₂ y) := by
  intro α Θ S xf yf Φ Tr f B₁ B₂ R₁ R₂ hf hR hB
  rw [ENNReal.ofReal_sum_of_nonneg hf]
  have h1 : ∑ a ∈ S, ENNReal.ofReal (f a) = ∑ x ∈ R₁, ∑ y ∈ R₂,
      ∑ a ∈ (S.filter (fun a => xf a = x)).filter (fun a => yf a = y), ENNReal.ofReal (f a) := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := xf) (t := R₁) (fun a ha => (hR a ha).1)]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← Finset.sum_fiberwise_of_maps_to (g := yf) (t := R₂)
      (fun a ha => (hR a (Finset.mem_filter.1 ha).1).2.1)]
  rw [h1]
  refine Finset.sum_le_sum (fun x _ => Finset.sum_le_sum (fun y _ => ?_))
  have hmem : ∀ a ∈ (S.filter (fun a => xf a = x)).filter (fun a => yf a = y),
      a ∈ S ∧ xf a = x ∧ yf a = y := by
    intro a ha
    simp only [Finset.mem_filter] at ha
    exact ⟨ha.1.1, ha.1.2, ha.2⟩
  generalize hS' : (S.filter (fun a => xf a = x)).filter (fun a => yf a = y) = S' at hmem ⊢
  rw [← Finset.sum_fiberwise_of_maps_to (g := Φ) (t := S'.image Φ)
    (fun a ha => Finset.mem_image_of_mem Φ ha)]
  have hfib : ∀ t ∈ S'.image Φ, ∑ a ∈ S'.filter (fun a => Φ a = t), ENNReal.ofReal (f a)
      ≤ ENNReal.ofReal (B₁ x * B₂ y) := by
    intro t ht
    obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨ha₀S, hx₀, hy₀⟩ := hmem a₀ ha₀
    have hsub : S'.filter (fun a => Φ a = Φ a₀)
        = S.filter (fun b => Φ b = Φ a₀ ∧ xf b = xf a₀ ∧ yf b = yf a₀) := by
      subst hS'
      ext b
      simp only [Finset.mem_filter]
      rw [hx₀, hy₀]
      tauto
    rw [hsub, ← ENNReal.ofReal_sum_of_nonneg (fun b hb => hf b (Finset.mem_filter.1 hb).1)]
    exact (ENNReal.ofReal_le_ofReal (hB a₀ ha₀S)).trans_eq (by rw [hx₀, hy₀])
  calc ∑ t ∈ S'.image Φ, ∑ a ∈ S'.filter (fun a => Φ a = t), ENNReal.ofReal (f a)
      ≤ ∑ t ∈ S'.image Φ, ENNReal.ofReal (B₁ x * B₂ y) := Finset.sum_le_sum hfib
    _ = ((S'.image Φ).card : ℝ≥0∞) * ENNReal.ofReal (B₁ x * B₂ y) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (((Tr x y).encard : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal (B₁ x * B₂ y) := by
      gcongr
      have hsubT : ((S'.image Φ : Finset Θ) : Set Θ) ⊆ Tr x y := by
        intro t ht
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 ht)
        obtain ⟨haS, hxa, hya⟩ := hmem a ha
        have h := (hR a haS).2.2
        rw [hxa, hya] at h
        exact h
      have hc := Set.encard_le_encard hsubT
      rw [Set.encard_coe_eq_coe_finsetCard] at hc
      rw [← ENat.toENNReal_coe]
      exact ENat.toENNReal_le.2 hc

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPairsWeightMulClassLeMulSum
section
open scoped Classical

namespace GlobalTheory

theorem sum_pairs_weight_mul_class_le_mul_sum (α β : Type) (S : Finset (α × α)) (cls : α → β)
    (w : α → ℝ) (om : β → ℝ) (T₁ T₂ : Finset β) (hw : ∀ a, 0 ≤ w a) (hom : ∀ b, 0 ≤ om b)
    (hT : ∀ p ∈ S, cls p.1 ∈ T₁ ∧ cls p.2 ∈ T₂)
    (hinj : ∀ p ∈ S, ∀ q ∈ S, p.1 = q.1 → cls p.2 = cls q.2 → p = q)
    (hsum : ∀ b, ∑ a ∈ (S.image Prod.fst).filter (fun a => cls a = b), w a ≤ 1) :
    ∑ p ∈ S, w p.1 * (om (cls p.1) * om (cls p.2)) ≤ (∑ b ∈ T₁, om b) * ∑ b ∈ T₂, om b := by

  have key : ∀ b ∈ T₁ ×ˢ T₂,
      ∑ p ∈ S.filter (fun p => (cls p.1, cls p.2) = b), w p.1 * (om (cls p.1) * om (cls p.2))
        ≤ om b.1 * om b.2 := by
    intro b _
    set F := S.filter (fun p => (cls p.1, cls p.2) = b) with hF
    have h1 : ∑ p ∈ F, w p.1 * (om (cls p.1) * om (cls p.2))
        = (∑ p ∈ F, w p.1) * (om b.1 * om b.2) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro p hp
      have e := (Finset.mem_filter.1 hp).2
      rw [← e]
    have h2 : ∑ p ∈ F, w p.1 = ∑ a ∈ F.image Prod.fst, w a := by
      rw [Finset.sum_image]
      intro p hp q hq hpq
      have ep := (Finset.mem_filter.1 hp).2
      have eq := (Finset.mem_filter.1 hq).2
      have hc : cls p.2 = cls q.2 := by
        have := congrArg Prod.snd (ep.trans eq.symm)
        simpa using this
      exact hinj p (Finset.mem_filter.1 hp).1 q (Finset.mem_filter.1 hq).1 hpq hc
    have h3 : F.image Prod.fst ⊆ (S.image Prod.fst).filter (fun a => cls a = b.1) := by
      intro a ha
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ha
      have hp' := Finset.mem_filter.1 hp
      refine Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hp'.1, ?_⟩
      have := congrArg Prod.fst hp'.2
      simpa using this
    have h4 : ∑ p ∈ F, w p.1 ≤ 1 := by
      rw [h2]
      exact (Finset.sum_le_sum_of_subset_of_nonneg h3 (fun a _ _ => hw a)).trans (hsum b.1)
    rw [h1]
    have hnn : 0 ≤ om b.1 * om b.2 := mul_nonneg (hom _) (hom _)
    calc (∑ p ∈ F, w p.1) * (om b.1 * om b.2) ≤ 1 * (om b.1 * om b.2) :=
          mul_le_mul_of_nonneg_right h4 hnn
      _ = om b.1 * om b.2 := one_mul _
  calc ∑ p ∈ S, w p.1 * (om (cls p.1) * om (cls p.2))
      = ∑ b ∈ T₁ ×ˢ T₂, ∑ p ∈ S.filter (fun p => (cls p.1, cls p.2) = b),
          w p.1 * (om (cls p.1) * om (cls p.2)) := by
        symm
        exact Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_product.2 (hT p hp)) _
    _ ≤ ∑ b ∈ T₁ ×ˢ T₂, om b.1 * om b.2 := Finset.sum_le_sum key
    _ = (∑ b ∈ T₁, om b) * ∑ b ∈ T₂, om b := by
      rw [Finset.sum_product, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumProdOfLocalChoicesBijection
section
open scoped Classical

namespace GlobalTheory

theorem prod_sum_of_local_choices {ι Q R : Type} {O : ι → Type} [CommSemiring R] [TopologicalSpace R] [∀ p, Nonempty (O p)]
    (s : Finset ι) (Φ : Q → ∀ p, O p) (Tq : Set Q) (U : ∀ p, Set (O p))
    (hU : ∀ p ∈ s, (U p).Finite)
    (hinj : ∀ c ∈ Tq, ∀ c' ∈ Tq, (∀ p ∈ s, Φ c p = Φ c' p) → c = c')
    (hmem : ∀ c ∈ Tq, ∀ p ∈ s, Φ c p ∈ U p)
    (hsurj : ∀ x : ∀ p, O p, (∀ p ∈ s, x p ∈ U p) → ∃ c ∈ Tq, ∀ p ∈ s, Φ c p = x p)
    (g : ∀ p, O p → R) :
    Tq.Finite ∧ (∑' c : Q, if c ∈ Tq then ∏ p ∈ s, g p (Φ c p) else 0)
      = ∏ p ∈ s, ∑' o : O p, if o ∈ U p then g p o else 0 := by
  have hT : Tq.Finite := by
    let e : Q → ∀ p : s, O p := fun c p => Φ c p
    have hfin : (Set.pi Set.univ (fun p : s => U p)).Finite :=
      Set.Finite.pi (fun p => hU p p.2)
    refine Set.Finite.of_finite_image (f := e) (hfin.subset ?_) ?_
    · rintro _ ⟨c, hc, rfl⟩ p _
      exact hmem c hc p p.2
    · intro c hc c' hc' h
      exact hinj c hc c' hc' (fun p hp => congrFun h ⟨p, hp⟩)
  refine ⟨hT, ?_⟩
  let t : ∀ p, Finset (O p) := fun p => if h : p ∈ s then (hU p h).toFinset else ∅
  have ht : ∀ p ∈ s, ∀ o, o ∈ t p ↔ o ∈ U p := by
    intro p hp o; simp [t, hp]
  rw [tsum_eq_sum (s := hT.toFinset) (fun c hc => by
    rw [Set.Finite.mem_toFinset] at hc; simp [hc])]
  have hR : ∀ p ∈ s, (∑' o : O p, if o ∈ U p then g p o else 0) = ∑ o ∈ t p, g p o := by
    intro p hp
    rw [tsum_eq_sum (s := t p) (fun o ho => by rw [ht p hp] at ho; simp [ho])]
    refine Finset.sum_congr rfl (fun o ho => ?_)
    rw [ht p hp] at ho; simp [ho]
  rw [Finset.prod_congr rfl hR, Finset.prod_sum]
  have hL : (∑ c ∈ hT.toFinset, if c ∈ Tq then ∏ p ∈ s, g p (Φ c p) else 0)
      = ∑ c ∈ hT.toFinset, ∏ p ∈ s, g p (Φ c p) :=
    Finset.sum_congr rfl (fun c hc => by rw [Set.Finite.mem_toFinset] at hc; simp [hc])
  rw [hL]
  refine Finset.sum_bij (fun c _ => fun p _ => Φ c p) ?_ ?_ ?_ ?_
  · intro c hc
    rw [Set.Finite.mem_toFinset] at hc
    rw [Finset.mem_pi]
    intro p hp
    exact (ht p hp _).2 (hmem c hc p hp)
  · intro c hc c' hc' h
    rw [Set.Finite.mem_toFinset] at hc hc'
    exact hinj c hc c' hc' (fun p hp => congrFun (congrFun h p) hp)
  · intro x hx
    rw [Finset.mem_pi] at hx
    let y : ∀ p, O p := fun p => if h : p ∈ s then x p h else Classical.arbitrary (O p)
    obtain ⟨c, hc, hcy⟩ := hsurj y (fun p hp => by
      simp only [y, dif_pos hp]; exact (ht p hp _).1 (hx p hp))
    refine ⟨c, (Set.Finite.mem_toFinset hT).2 hc, ?_⟩
    funext p hp
    rw [hcy p hp]; simp [y, hp]
  · intro c _
    exact (Finset.prod_attach s (fun p => g p (Φ c p))).symm

end GlobalTheory
end

