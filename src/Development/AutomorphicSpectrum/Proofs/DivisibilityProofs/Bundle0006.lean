module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PScalarQuotient
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0011

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumMixedExpansion
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem rename_map_psumExpansion {σ : Type} (r k : ℕ) (e : Fin r → σ) (a : Fin r) :
    rename (Sum.map e e) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion r k a)) =
      ∑ j ∈ Finset.range k,
        (X (Sum.inl (e a)) : MvPolynomial (σ ⊕ σ) ℝ) ^ j * X (Sum.inr (e a)) ^ (k - 1 - j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [psumExpansion, map_sum, map_mul, map_pow, rename_X]

theorem isHomogeneous_rename_map_psumExpansion {σ : Type} (r k : ℕ) (e : Fin r → σ) (a : Fin r) :
    (rename (Sum.map e e) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion r k a))).IsHomogeneous
      (k - 1) := by
  rw [rename_map_psumExpansion]
  refine IsHomogeneous.sum _ _ _ fun j hj => ?_
  have hj' : j + (k - 1 - j) = k - 1 := by
    have := Finset.mem_range.mp hj
    omega
  have h := ((isHomogeneous_X ℝ (Sum.inl (e a) : σ ⊕ σ)).pow j).mul
    ((isHomogeneous_X ℝ (Sum.inr (e a) : σ ⊕ σ)).pow (k - 1 - j))
  simpa [hj'] using h

theorem mixDiff_sum_pow {σ : Type} [Fintype σ] (r k : ℕ) (e : Fin r → σ) :
    mixDiff (∑ a, X (e a) ^ k : MvPolynomial σ ℝ) =
      ∑ a, (X (Sum.inl (e a)) - X (Sum.inr (e a))) *
        rename (Sum.map e e) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion r k a)) := by
  unfold mixDiff
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_pow, rename_X, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [rename_map_psumExpansion, mul_comm, (Commute.all _ _).geom_sum₂_mul]

theorem isMixExpansion_psum_mul : ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (r k m : ℕ) (e : Fin r → σ) (G : MvPolynomial (σ ⊕ σ) ℝ), G.IsHomogeneous m → IsMixExpansion (k - 1 + m) (mixDiff (∑ a, X (e a) ^ k) * G) (fun i => (∑ a ∈ Finset.univ.filter (fun a => e a = i), rename (Sum.map e e) (MvPolynomial.map (Int.castRingHom ℝ) (psumExpansion r k a))) * G) := by
  intro σ _ _ r k m e G hG
  refine ⟨?_, fun i => ?_⟩
  · rw [mixDiff_sum_pow, ← Finset.sum_fiberwise Finset.univ e, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul, ← mul_assoc, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [(Finset.mem_filter.mp ha).2]
  · exact (IsHomogeneous.sum _ _ _ fun a _ => isHomogeneous_rename_map_psumExpansion r k e a).mul hG

end GlobalTheory.CompanionTheory.Ar.Num
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.SumPrimeLogDivLe
section
namespace GlobalTheory.CompanionTheory.Ar.Small

theorem mertens_first_log_four :
    ∀ x : ℝ, 1 ≤ x →
      ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime, Real.log p / p ≤ Real.log x + Real.log 4 := by
  intro B hB
  set N := ⌊B⌋₊ with hN
  set P := (Finset.Iic N).filter Nat.Prime with hP
  have hN2 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hB)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNB : (N : ℝ) ≤ B := Nat.floor_le (by linarith)
  have hpos : ∀ p ∈ P, (1 : ℝ) ≤ p := fun p hp => by
    exact_mod_cast (Finset.mem_filter.1 hp).2.one_lt.le

  have hle : ∏ p ∈ P, p ^ (N / p) ≤ N ^ N :=
    (Nat.le_of_dvd (Nat.factorial_pos _) (GroundTheory.Heights₂.Heights.Model.prod_pow_div_dvd_factorial N)).trans
      (Nat.factorial_le_pow N)
  have hlog : ∑ p ∈ P, ((N / p : ℕ) : ℝ) * Real.log p ≤ N * Real.log N := by
    have hprod : (0 : ℝ) < ∏ p ∈ P, ((p : ℝ) ^ (N / p)) :=
      Finset.prod_pos fun p hp => pow_pos (by linarith [hpos p hp]) _
    have h := Real.log_le_log hprod
      (show ∏ p ∈ P, ((p : ℝ) ^ (N / p)) ≤ (N : ℝ) ^ N by exact_mod_cast hle)
    rw [Real.log_prod (fun p hp => (pow_pos (by linarith [hpos p hp]) _).ne'),
      Real.log_pow] at h
    simpa [Real.log_pow] using h

  have hfloor : ∀ p ∈ P, ((N : ℝ) / p - 1) * Real.log p ≤ ((N / p : ℕ) : ℝ) * Real.log p :=
    fun p hp => mul_le_mul_of_nonneg_right
      (by rw [← Nat.floor_div_eq_div (K := ℝ)]; exact (Nat.sub_one_lt_floor _).le)
      (Real.log_nonneg (hpos p hp))

  have htheta : ∑ p ∈ P, Real.log p ≤ Real.log 4 * N := by
    have h := Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) hNpos.le
    have hset : P = (Finset.Ioc 0 ⌊(N : ℝ)⌋₊).filter Nat.Prime := by
      rw [Nat.floor_natCast, hP]
      ext p
      simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨h2.pos, h1⟩, h2⟩
      · rintro ⟨⟨-, h1⟩, h2⟩; exact ⟨h1, h2⟩
    rw [hset]; exact h
  have key : (N : ℝ) * ∑ p ∈ P, Real.log p / p - ∑ p ∈ P, Real.log p ≤ N * Real.log N := by
    calc (N : ℝ) * ∑ p ∈ P, Real.log p / p - ∑ p ∈ P, Real.log p
        = ∑ p ∈ P, ((N : ℝ) / p - 1) * Real.log p := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun p _ => ?_
          ring
      _ ≤ ∑ p ∈ P, ((N / p : ℕ) : ℝ) * Real.log p := Finset.sum_le_sum hfloor
      _ ≤ N * Real.log N := hlog
  have hS : ∑ p ∈ P, Real.log p / p ≤ Real.log N + Real.log 4 := by
    have : (N : ℝ) * ∑ p ∈ P, Real.log p / p ≤ N * (Real.log N + Real.log 4) := by
      rw [mul_add]; linarith
    exact le_of_mul_le_mul_left this hNpos
  have hlogNB : Real.log N ≤ Real.log B := Real.log_le_log hNpos hNB
  linarith

end GlobalTheory.CompanionTheory.Ar.Small
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.UniformizerDivisorCycleNumber
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.ConsPoly

theorem length_classList {K σ : Type} (cls : σ → K → ℤ) {H : MvPolynomial σ ℝ} {m : ℕ}
    (hH : H.IsHomogeneous m) {μ : σ →₀ ℕ} (hμ : μ ∈ H.support) :
    (classList cls μ).length = m := by
  have h := hH (mem_support_iff.mp hμ)
  rw [← h]
  simp [classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset,
    Finsupp.weight_apply, Finsupp.sum]

theorem cycList_const {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P : Ideal (MRing ι O)} (l : List (K → ℤ))
    (hM : IsModelOver P l.length) (u : Oˣ) (e : ℕ) :
    cycList (divCycle P (C ((u : O) * ϖ ^ e))) l =
      (e : ℤ) * intNumL (FractionRing O) (genFib P) l := by
  haveI : P.IsPrime := hM.multiProj.isPrime
  have hC : ∀ a : O, a ≠ 0 → (C a : MRing ι O) ∉ P := by
    intro a ha hmem
    apply ha
    have ha' : a ∈ P.comap (C : O →+* MRing ι O) := Ideal.mem_comap.2 hmem
    rw [hM.noTorsion] at ha'
    exact Ideal.mem_bot.1 ha'
  have hfin := ScalarQuotient.divCycle_support_finite P (C ϖ)
  have key : cycEval (fun W => vNumL W l) (divCycle P (C ϖ)) =
      intNumL (FractionRing O) (genFib P) l :=
    ConservationOfNumber.full O ϖ hϖ K ι P l.length hM l.get
  unfold cycList
  rw [ScalarQuotient.divCycle_const P hC hϖ.ne_zero u e, ← key]
  unfold cycEval
  show ∑ᶠ W, ((e : ℤ) * divCycle P (C ϖ) W) * vNumL W l =
    (e : ℤ) * ∑ᶠ W, divCycle P (C ϖ) W * vNumL W l
  rw [mul_finsum]
  · exact finsum_congr fun W => by ring
  all_goals exact hfin.subset (Function.support_mul_subset_left _ _)

end GlobalTheory.CompanionTheory.Ar.Num.ConsPoly


open GlobalTheory.CompanionTheory.Ar.Num.ConsPoly in
theorem GlobalTheory.CompanionTheory.Ar.Num.cycNum_divCycle_const : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (u : Oˣ) (e : ℕ) (σ : Type) (cls : σ → K → ℤ) (H : MvPolynomial σ ℝ) (m : ℕ), H.IsHomogeneous m → ∀ Q : List (K → ℤ), m + Q.length = d → cycNum (divCycle P (C ((u : O) * ϖ ^ e))) cls H Q = (e : ℝ) * genNum (FractionRing O) (genFib P) cls H Q := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hM u e σ cls H m hH Q hd
  unfold cycNum genNum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hlen : (classList cls μ ++ Q).length = d := by
    rw [List.length_append, GlobalTheory.CompanionTheory.Ar.Num.ConsPoly.length_classList cls hH hμ, hd]
  have hM' : IsModelOver P (classList cls μ ++ Q).length := by
    rw [hlen]
    exact hM
  rw [GlobalTheory.CompanionTheory.Ar.Num.ConsPoly.cycList_const hϖ _ hM' u e]
  push_cast
  ring
end

