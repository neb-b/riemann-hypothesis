module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientSmulSupLeIntermediate
section
open Pointwise

namespace GlobalTheory

theorem length_quotient_tower_of_le {R : Type} [CommRing R] {X : Type} [AddCommGroup X] [Module R X]
    (Y W : Submodule R X) (hYW : Y ≤ W) :
    Module.length R (X ⧸ Y) =
      Module.length R (W ⧸ Y.comap W.subtype) + Module.length R (X ⧸ W) := by
  have hf : Function.Injective ((Y.comap W.subtype).mapQ Y W.subtype le_rfl) := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ]
    simp
  refine Module.length_eq_add_of_exact ((Y.comap W.subtype).mapQ Y W.subtype le_rfl)
    (Submodule.factor hYW) hf (Submodule.factor_surjective hYW) ?_
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H x =>
    constructor
    · intro h
      have hx : x ∈ W := by
        simpa [Submodule.Quotient.mk_eq_zero] using h
      exact ⟨Submodule.Quotient.mk ⟨x, hx⟩, rfl⟩
    · rintro ⟨w, hw⟩
      rw [← hw]
      induction w using Submodule.Quotient.induction_on with
      | H z => simp [Submodule.Quotient.mk_eq_zero]

theorem length_quotient_smul_sup_le : ∀ (O A : Type) [CommRing O] [AddCommGroup A] [Module O A]
    (Z B B' : Submodule O A) (a : O), B ≤ B' →
    Module.length O (↥Z ⧸ (Z.map (a • (LinearMap.id : A →ₗ[O] A)) ⊔ B).comap Z.subtype) ≤
      Module.length O ((↥Z ⧸ B'.comap Z.subtype) ⧸ LinearMap.range (a • (LinearMap.id :
        (↥Z ⧸ B'.comap Z.subtype) →ₗ[O] (↥Z ⧸ B'.comap Z.subtype)))) +
      Module.length O (↥(Z ⊓ B') ⧸ B.comap (Z ⊓ B').subtype) := by
  intro O A _ _ _ Z B B' a hBB'
  set N : Submodule O Z := (Z.map (a • (LinearMap.id : A →ₗ[O] A)) ⊔ B).comap Z.subtype with hN
  set C : Submodule O Z := B'.comap Z.subtype with hC
  set K : Submodule O Z := N ⊔ C with hK
  rw [length_quotient_tower_of_le N K le_sup_left, add_comm]
  refine add_le_add ?_ ?_
  ·
    let f : (↥Z ⧸ C) →ₗ[O] (↥Z ⧸ K) := Submodule.factor (le_sup_right : C ≤ K)
    have hf : LinearMap.range (a • (LinearMap.id : (↥Z ⧸ C) →ₗ[O] (↥Z ⧸ C))) ≤ LinearMap.ker f := by
      rintro y ⟨q, rfl⟩
      induction q using Submodule.Quotient.induction_on with
      | H z =>
        rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, map_smul]
        change a • (Submodule.Quotient.mk z : ↥Z ⧸ K) = 0
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        refine Submodule.mem_sup_left ?_
        show ((a • z : Z) : A) ∈ Z.map (a • (LinearMap.id : A →ₗ[O] A)) ⊔ B
        exact Submodule.mem_sup_left ⟨z, z.2, by simp⟩
    refine Module.length_le_of_surjective (Submodule.liftQ _ f hf) ?_
    intro w
    induction w using Submodule.Quotient.induction_on with
    | H z =>
      exact ⟨Submodule.Quotient.mk (Submodule.Quotient.mk z), rfl⟩
  ·
    let ι : ↥(Z ⊓ B') →ₗ[O] K :=
      LinearMap.codRestrict K (LinearMap.codRestrict Z (Z ⊓ B').subtype (fun x => x.2.1))
        (fun x => Submodule.mem_sup_right (show _ ∈ C from x.2.2))
    let φ : ↥(Z ⊓ B') →ₗ[O] (↥K ⧸ N.comap K.subtype) := (N.comap K.subtype).mkQ ∘ₗ ι
    have hφ : B.comap (Z ⊓ B').subtype ≤ LinearMap.ker φ := by
      intro x hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      show ((x : A)) ∈ Z.map (a • (LinearMap.id : A →ₗ[O] A)) ⊔ B
      exact Submodule.mem_sup_right hx
    refine Module.length_le_of_surjective (Submodule.liftQ _ φ hφ) ?_
    intro w
    induction w using Submodule.Quotient.induction_on with
    | H k =>
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp k.2
      refine ⟨Submodule.Quotient.mk ⟨(z : A), z.2, hz⟩, ?_⟩
      rw [Submodule.liftQ_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.eq]
      have : ((ι ⟨(z : A), z.2, hz⟩ - k : K) : Z) = -y := by
        ext
        simp only [ι, ← hyz, Submodule.coe_sub, Submodule.coe_neg, Submodule.coe_add]
        change (z : A) - ((y : A) + (z : A)) = -(y : A)
        abel
      show ((ι ⟨(z : A), z.2, hz⟩ - k : K) : Z) ∈ N
      rw [this]
      exact N.neg_mem hy

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientSpanPowLeMulLength
section
open Pointwise

namespace GlobalTheory

theorem length_quotient_span_pow_le (O : Type) [CommRing O] (p : O) (n : ℕ) :
    Module.length O (O ⧸ Ideal.span {p ^ n}) ≤ (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {p}) := by
  induction n with
  | zero =>
    rw [pow_zero, Ideal.span_singleton_one]
    haveI : Subsingleton (O ⧸ (⊤ : Ideal O)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    rw [Module.length_eq_zero]
    exact bot_le
  | succ n ih =>
    set S : Submodule O O := Ideal.span {p ^ (n + 1)} with hS
    set T : Submodule O O := Ideal.span {p ^ n} with hT
    have hST : S ≤ T := Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow p n.le_succ)
    let v : O ⧸ S := S.mkQ (p ^ n)
    have hker : (Ideal.span {p} : Submodule O O) ≤ LinearMap.ker (LinearMap.toSpanSingleton O (O ⧸ S) v) := by
      intro x hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      simp only [v, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, smul_eq_mul]
      rw [Submodule.Quotient.mk_eq_zero, hS, Ideal.mem_span_singleton']
      exact ⟨c, by ring⟩
    let ψ : (O ⧸ (Ideal.span {p} : Submodule O O)) →ₗ[O] O ⧸ S :=
      (Ideal.span {p} : Submodule O O).liftQ (LinearMap.toSpanSingleton O (O ⧸ S) v) hker
    let N : Submodule O (O ⧸ S) := LinearMap.range ψ
    have hN : N = T.map S.mkQ := by
      simp only [N, ψ, Submodule.range_liftQ, hT, Ideal.span, Submodule.map_span, Set.image_singleton]
      rw [← LinearMap.span_singleton_eq_range]
    have h1 := Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N)
    have hle : Module.length O N ≤ Module.length O (O ⧸ Ideal.span {p}) :=
      Module.length_le_of_surjective ψ.rangeRestrict ψ.surjective_rangeRestrict
    have heq : Module.length O ((O ⧸ S) ⧸ N) = Module.length O (O ⧸ Ideal.span {p ^ n}) := by
      rw [hN]
      exact (Submodule.quotientQuotientEquivQuotient S T hST).length_eq
    change Module.length O (O ⧸ S) ≤ _
    rw [h1, heq]
    calc Module.length O N + Module.length O (O ⧸ Ideal.span {p ^ n})
        ≤ Module.length O (O ⧸ Ideal.span {p}) + (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {p}) :=
          add_le_add hle ih
      _ = ((n + 1 : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {p}) := by
          push_cast; ring

theorem main : ∀ (O : Type) [CommRing O] (p : O) (n : ℕ),
    Module.length O (O ⧸ Ideal.span {p ^ n}) ≤ (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {p}) :=
  fun O _ p n => length_quotient_span_pow_le O p n

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearIndependentJointEigenvectors
section
namespace GlobalTheory.JointEigenvectorsIndependentSatakeParameters

theorem linearIndependent_jointEigenvectors {J V : Type} [AddCommGroup V] [Module ℂ V]
    (T : J → V →ₗ[ℂ] V) (S : Set (J → ℂ)) (v : S → V)
    (hv : ∀ χ : S, v χ ≠ 0)
    (hT : ∀ (χ : S) (j : J), T j (v χ) = (χ : J → ℂ) j • v χ) :
    LinearIndependent ℂ v := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro g _ i hi
    simp at hi
  | insert a s ha ih =>
    intro g hg
    rw [Finset.sum_insert ha] at hg
    have e1 : ∑ i ∈ s, g i • v i = -(g a • v a) := eq_neg_of_add_eq_zero_right hg
    have hs : ∀ i ∈ s, g i = 0 := by
      intro i hi
      have hne : (i : J → ℂ) ≠ a := fun h => ha (Subtype.ext h ▸ hi)
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
      have e2 : ∑ i ∈ s, (g i * (i : J → ℂ) j) • v i = -((g a * (a : J → ℂ) j) • v a) := by
        have := congrArg (T j) e1
        set_option synthInstance.maxHeartbeats 100000 in
          simpa [map_sum, map_smul, hT, smul_smul] using this
      have e3 : ∑ i ∈ s, ((a : J → ℂ) j * g i) • v i = -(((a : J → ℂ) j * g a) • v a) := by
        have := congrArg (fun x => (a : J → ℂ) j • x) e1
        simpa [Finset.smul_sum, smul_smul] using this
      have h2 : ∑ i ∈ s, (g i * ((i : J → ℂ) j - (a : J → ℂ) j)) • v i = 0 := by
        calc ∑ i ∈ s, (g i * ((i : J → ℂ) j - (a : J → ℂ) j)) • v i
            = ∑ i ∈ s, (g i * (i : J → ℂ) j) • v i - ∑ i ∈ s, ((a : J → ℂ) j * g i) • v i := by
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [← sub_smul]
              congr 1
              ring
          _ = 0 := by rw [e2, e3, mul_comm ((a : J → ℂ) j) (g a)]; exact sub_self _
      have := ih (fun i => g i * ((i : J → ℂ) j - (a : J → ℂ) j)) h2 i hi
      exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hj)
    have hsum : ∑ i ∈ s, g i • v i = 0 := Finset.sum_eq_zero fun i hi => by rw [hs i hi, zero_smul]
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · rw [hsum, add_zero] at hg
      exact (smul_eq_zero.mp hg).resolve_right (hv _)
    · exact hs i hi

end GlobalTheory.JointEigenvectorsIndependentSatakeParameters
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormAevalSubLe
section
namespace GlobalTheory.NormAevalSubBound

theorem norm_aeval_sub_le {k : Type} [inst : NormedField k] [NormOneClass k] [IsUltrametricDist k]
    {J : Type} {x y : J → k} {δ : ℝ} (hδ : (0 : ℝ) ≤ δ) (hx : ∀ (j : J), ‖x j‖ ≤ (1 : ℝ))
    (hy : ∀ (j : J), ‖y j‖ ≤ (1 : ℝ)) (hxy : ∀ (j : J), ‖x j - y j‖ ≤ δ) (P : MvPolynomial J ℤ) :
    ‖(MvPolynomial.aeval x : MvPolynomial J ℤ → k) P‖ ≤ (1 : ℝ) ∧
    ‖(MvPolynomial.aeval y : MvPolynomial J ℤ → k) P‖ ≤ (1 : ℝ) ∧
    ‖(MvPolynomial.aeval x : MvPolynomial J ℤ → k) P -
      (MvPolynomial.aeval y : MvPolynomial J ℤ → k) P‖ ≤ δ := by
  have hadd : ∀ (a b : k) (r : ℝ), ‖a‖ ≤ r → ‖b‖ ≤ r → ‖a + b‖ ≤ r := fun a b r ha hb =>
    (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h : ‖(a : k)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one k a
    refine ⟨?_, ?_, ?_⟩
    · simpa using h
    · simpa using h
    · simpa using hδ
  | add p q hp hq =>
    obtain ⟨p1, p2, p3⟩ := hp
    obtain ⟨q1, q2, q3⟩ := hq
    simp only [map_add (f := _)]
    refine ⟨hadd _ _ _ p1 q1, hadd _ _ _ p2 q2, ?_⟩
    rw [add_sub_add_comm]
    exact hadd _ _ _ p3 q3
  | mul_X p j hp =>
    obtain ⟨p1, p2, p3⟩ := hp
    simp only [map_mul, MvPolynomial.aeval_X]
    refine ⟨?_, ?_, ?_⟩
    · rw [norm_mul]; exact mul_le_one₀ p1 (norm_nonneg _) (hx j)
    · rw [norm_mul]; exact mul_le_one₀ p2 (norm_nonneg _) (hy j)
    · have e : MvPolynomial.aeval x p * x j - MvPolynomial.aeval y p * y j =
          MvPolynomial.aeval x p * (x j - y j) +
            (MvPolynomial.aeval x p - MvPolynomial.aeval y p) * y j := by ring
      rw [e]
      refine hadd _ _ _ ?_ ?_
      · rw [norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) p1).trans (hxy j)
      · rw [norm_mul]
        exact (mul_le_of_le_one_right (norm_nonneg _) (hy j)).trans p3

end GlobalTheory.NormAevalSubBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLeOfRecurrenceGrowth
section
open Finset

namespace GlobalTheory

theorem norm_le_of_recurrence_growth : ∀ (β : Multiset ℂ) (a : ℕ → ℂ) (C B : ℝ) (m : ℕ), 0 < B → a 0 = 1 → (∀ n, 1 ≤ n → ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * β.esymm k * a (n - k) = 0) → (∀ n, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ m * B ^ n) → ∀ b ∈ β, ‖b‖ ≤ B := by
  intro β a C B m hB ha0 hrec hgrow b hb
  by_contra hlt
  push_neg at hlt
  have hb0 : b ≠ 0 := by
    intro h; rw [h, norm_zero] at hlt; linarith
  set X : ℂ := b⁻¹ with hX
  have hXn : ‖X‖ = ‖b‖⁻¹ := norm_inv b
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb0
  set r : ℝ := B * ‖X‖ with hr
  have hrpos : 0 < r := by rw [hr, hXn]; positivity
  have hr1 : r < 1 := by
    rw [hr, hXn, ← div_eq_mul_inv, div_lt_one hbpos]; exact hlt
  have hes : ∀ k, Multiset.card β < k → β.esymm k = 0 := by
    intro k hk
    simp [Multiset.esymm, Multiset.powersetCard_eq_empty _ hk]
  set d := Multiset.card β with hd
  set p : ℕ → ℂ := fun k => (-1 : ℂ) ^ k * β.esymm k * X ^ k with hp
  have hpz : ∀ k ∉ Finset.range (d + 1), p k = 0 := by
    intro k hk
    simp only [Finset.mem_range, not_lt] at hk
    simp [hp, hes k (by omega)]
  have hpsum : ∑ k ∈ Finset.range (d + 1), p k = 0 := by
    have h1 := congrArg (Polynomial.eval b) (Multiset.prod_X_sub_X_eq_sum_esymm β)
    rw [Polynomial.eval_multiset_prod, Polynomial.eval_finsetSum] at h1
    have hz : (Multiset.map (Polynomial.eval b)
        (Multiset.map (fun t => Polynomial.X - Polynomial.C t) β)).prod = 0 := by
      apply Multiset.prod_eq_zero
      rw [Multiset.map_map]
      exact Multiset.mem_map.mpr ⟨b, hb, by simp⟩
    rw [hz] at h1
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one,
      Polynomial.eval_C, Polynomial.eval_X] at h1
    have h2 : ∑ k ∈ Finset.range (d + 1), p k
        = X ^ d * ∑ j ∈ Finset.range (d + 1), (-1 : ℂ) ^ j * (β.esymm j * b ^ (d - j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hkd : k ≤ d := by rw [Finset.mem_range] at hk; omega
      have hXb : X ^ (d - k) * b ^ (d - k) = 1 := by
        rw [← mul_pow, hX, inv_mul_cancel₀ hb0, one_pow]
      have : X ^ d = X ^ k * X ^ (d - k) := by rw [← pow_add, Nat.add_sub_cancel' hkd]
      simp only [hp]
      rw [this]
      linear_combination (-1 : ℂ) ^ k * β.esymm k * X ^ k * hXb.symm
    rw [h2, ← h1, mul_zero]
  have hpsumm : Summable (fun k => ‖p k‖) :=
    summable_of_ne_finset_zero (s := Finset.range (d + 1)) (fun k hk => by simp [hpz k hk])
  have hptsum : ∑' k, p k = 0 := by
    rw [tsum_eq_sum (s := Finset.range (d + 1)) hpz, hpsum]
  set q : ℕ → ℂ := fun n => a n * X ^ n with hq
  have hgeo : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ m * r ^ n) := by
    have h0 : Summable (fun n : ℕ => (n : ℝ) ^ m * r ^ n) :=
      summable_pow_mul_geometric_of_norm_lt_one m (by rw [Real.norm_eq_abs, abs_of_pos hrpos]; exact hr1)
    have h1 := (summable_nat_add_iff 1).mpr h0
    have h2 := h1.mul_left r⁻¹
    refine h2.congr (fun n => ?_)
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
  have hqsumm : Summable (fun n => ‖q n‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hgeo.mul_left C)
    simp only [hq, norm_mul, norm_pow]
    calc ‖a n‖ * ‖X‖ ^ n ≤ C * ((n : ℝ) + 1) ^ m * B ^ n * ‖X‖ ^ n :=
          mul_le_mul_of_nonneg_right (hgrow n) (by positivity)
      _ = C * (((n : ℝ) + 1) ^ m * r ^ n) := by rw [hr, mul_pow]; ring
  have hcauchy := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hpsumm hqsumm
  rw [hptsum, zero_mul] at hcauchy
  have hterm : ∀ n, ∑ k ∈ Finset.range (n + 1), p k * q (n - k)
      = X ^ n * ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * β.esymm k * a (n - k) := by
    intro n
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := by rw [Finset.mem_range] at hk; omega
    have : X ^ n = X ^ k * X ^ (n - k) := by rw [← pow_add, Nat.add_sub_cancel' hkn]
    simp only [hp, hq]
    rw [this]; ring
  have hone : ∑' n, ∑ k ∈ Finset.range (n + 1), p k * q (n - k) = 1 := by
    rw [tsum_eq_single 0]
    · simp [hp, hq, ha0, Multiset.esymm, Multiset.powersetCard_zero_left]
    · intro n hn
      rw [hterm n, hrec n (Nat.one_le_iff_ne_zero.mpr hn), mul_zero]
  rw [hone] at hcauchy
  exact zero_ne_one hcauchy

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormSumLt
section
namespace GlobalTheory.NormSumLt

universe u_1

theorem norm_sum_lt {K : Type u_1} [NormedField K] [IsUltrametricDist K] (s : Finset ℕ) (f : ℕ → K)
    {r : ℝ} (hr : (0 : ℝ) < r) (h : ∀ i ∈ s, ‖f i‖ < r) : ‖∑ i ∈ s, f i‖ < r := by
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have h1 : ‖f a‖ < r := h a (Finset.mem_insert_self a s)
    have h2 : ‖∑ i ∈ s, f i‖ < r := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h1 h2)

theorem main : ∀ {K : Type u_1} [inst : NormedField K] [IsUltrametricDist K] (s : Finset ℕ) (f : ℕ → K) {r : ℝ}, (0 : ℝ) < r → (∀ i ∈ s, ‖f i‖ < r) → ‖∑ i ∈ s, f i‖ < r :=
  by
  intro K _ _ s f r hr h
  exact norm_sum_lt s f hr h

end GlobalTheory.NormSumLt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormTensorProductMapLeft
section
open scoped TensorProduct

namespace GlobalTheory

theorem norm_tensorProduct_map_left {R B L : Type} [Field R] [CommRing B] [Algebra R B] [Field L]
    [Algebra R L] [FiniteDimensional R L] (f : B →ₐ[R] B) (w : B ⊗[R] L) :
    Algebra.norm B (Algebra.TensorProduct.map f (AlgHom.id R L) w) = f (Algebra.norm B w) := by
  classical
  let e := Module.finBasis R L
  let b := Algebra.TensorProduct.basis B e
  let σ := Algebra.TensorProduct.map f (AlgHom.id R L)
  have hrepr : ∀ z : B ⊗[R] L, ∀ i, b.repr (σ z) i = f (b.repr z i) := by
    intro z i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [σ, b, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
        smul_eq_mul, map_mul, AlgHom.commutes]
    | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  have hb : ∀ j, σ (b j) = b j := by
    intro j
    simp [σ, b, Algebra.TensorProduct.basis_apply]
  have hmat : Algebra.leftMulMatrix b (σ w) = (Algebra.leftMulMatrix b w).map f := by
    ext i j
    rw [Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
      ← hb j, ← map_mul, hb j, hrepr]
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b, hmat]
  exact (AlgHom.map_det f _).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NumberFieldEmbMemAlgebraicClosure
section
namespace GlobalTheory

open IntermediateField

theorem numberField_emb_mem_algebraicClosure {LL : Type} [Field LL] [NumberField LL]
    (e : LL →+* ℂ) (z : LL) : e z ∈ algebraicClosure ℚ ℂ := by
  rw [mem_algebraicClosure_iff]
  have hz : IsAlgebraic ℚ z := Algebra.IsAlgebraic.isAlgebraic z
  simpa using hz.algHom e.toRatAlgHom

theorem padic_emb_extends_algebraicClosure (p : ℕ) [Fact p.Prime] (LL : Type) [Field LL]
    [NumberField LL] (e : LL →+* ℂ) (i : LL →+* ℂ_[p]) :
    ∃ lam : (algebraicClosure ℚ ℂ) →+* ℂ_[p],
      ∀ (z : LL) (hz : e z ∈ algebraicClosure ℚ ℂ), i z = lam ⟨e z, hz⟩ := by
  let e' : LL →+* algebraicClosure ℚ ℂ :=
    (e.codRestrict (algebraicClosure ℚ ℂ).toSubring
      (fun z => numberField_emb_mem_algebraicClosure e z))
  letI : Algebra LL (algebraicClosure ℚ ℂ) := e'.toAlgebra
  letI : Algebra LL ℂ_[p] := i.toAlgebra
  haveI : IsScalarTower ℚ LL (algebraicClosure ℚ ℂ) :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      (RingHom.congr_fun (Subsingleton.elim ((algebraMap LL (algebraicClosure ℚ ℂ)).comp
        (algebraMap ℚ LL)) (algebraMap ℚ (algebraicClosure ℚ ℂ))) x).symm)
  haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  haveI : Algebra.IsAlgebraic LL (algebraicClosure ℚ ℂ) :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) LL
  let lamA : algebraicClosure ℚ ℂ →ₐ[LL] ℂ_[p] := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨lamA.toRingHom, fun z hz => ?_⟩
  have h1 : (⟨e z, hz⟩ : algebraicClosure ℚ ℂ) = algebraMap LL (algebraicClosure ℚ ℂ) z := rfl
  rw [h1]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ProdFinEqProdCastLE
section
namespace GlobalTheory.ProdFinCastLE

theorem prod_fin_eq_prod_castLE {a b : ℕ} {M : Type} [CommMonoid M] (h : a ≤ b) (f : Fin b → M)
    (hf : ∀ r : Fin b, a ≤ (r : ℕ) → f r = 1) :
    ∏ r : Fin b, f r = ∏ r : Fin a, f (Fin.castLE h r) := by
  symm
  rw [show (∏ r : Fin a, f (Fin.castLE h r)) =
      ∏ x ∈ Finset.univ.map ⟨Fin.castLE h, Fin.castLE_injective h⟩, f x by
    rw [Finset.prod_map]
    rfl]
  refine Finset.prod_subset (Finset.subset_univ _) fun x _ hx => hf x ?_
  by_contra hlt
  push Not at hlt
  exact hx (Finset.mem_map.2 ⟨⟨x, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)

end GlobalTheory.ProdFinCastLE
end

