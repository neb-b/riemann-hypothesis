module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Bundle0002

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PrimeWeightEqZeroOfLt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open Finset

noncomputable section

namespace Elem

def primeWeight (B : ℝ) (i : ℕ) : ℝ := if i.Prime ∧ B < i then Real.log i else 0

theorem primeWeight_nonneg (B : ℝ) (i : ℕ) : 0 ≤ primeWeight B i := by
  unfold primeWeight
  split_ifs
  · exact Real.log_natCast_nonneg i
  · exact le_rfl

theorem sum_primeWeight_le (B : ℝ) (K : ℕ) :
    ∑ i ∈ range (K + 1), primeWeight B i ≤ K * Real.log 4 := by
  have hθ := ChebyshevThetaBound.intersectionNumber_baseChange (K : ℝ) (Nat.cast_nonneg K)
  rw [Nat.floor_natCast] at hθ
  refine le_trans ?_ hθ
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro i _
  unfold primeWeight
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd h1.1 h2
  · exact Real.log_natCast_nonneg i
  · exact le_rfl

theorem primeWeight_eq_zero_of_lt (B : ℝ) (hB : 0 ≤ B) {i : ℕ} (hi : i < ⌊B⌋₊ + 1) :
    primeWeight B i = 0 := by
  unfold primeWeight
  rw [if_neg]
  rintro ⟨_, h⟩
  have : (i : ℝ) ≤ B := by
    have := Nat.le_floor_iff hB |>.mp (Nat.lt_succ_iff.mp hi)
    exact this
  linarith

theorem abel_step (B : ℝ) (hB : 0 < B) (j : ℕ) :
    (∑ i ∈ range (⌊B⌋₊ + 1 + j), primeWeight B i / (i : ℝ) ^ 2) -
        (∑ i ∈ range (⌊B⌋₊ + 1 + j), primeWeight B i) / ((⌊B⌋₊ + 1 + j : ℕ) : ℝ) ^ 2 ≤
      2 * Real.log 4 * (1 / ((⌊B⌋₊ + 1 : ℕ) : ℝ) - 1 / ((⌊B⌋₊ + 1 + j : ℕ) : ℝ)) := by
  set M := ⌊B⌋₊ + 1 with hM
  induction j with
  | zero =>
    have h0 : ∀ i ∈ range (M + 0), primeWeight B i = 0 := fun i hi =>
      primeWeight_eq_zero_of_lt B hB.le (by have := Finset.mem_range.mp hi; omega)
    rw [Finset.sum_eq_zero (fun i hi => by rw [h0 i hi, zero_div]),
      Finset.sum_eq_zero h0]
    simp
  | succ j ih =>
    set K := M + j with hK
    have hK1 : (1 : ℝ) ≤ K := by
      have : 1 ≤ K := by omega
      exact_mod_cast this
    have hKpos : (0 : ℝ) < K := by linarith
    rw [show M + (j + 1) = K + 1 by omega] at *
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    set S := ∑ i ∈ range K, primeWeight B i / (i : ℝ) ^ 2
    set G := ∑ i ∈ range K, primeWeight B i
    set g := primeWeight B K
    have hG1 : G + g ≤ K * Real.log 4 := by
      have := sum_primeWeight_le B K
      rw [Finset.sum_range_succ] at this
      exact this
    have hG1nn : 0 ≤ G + g := by
      have : 0 ≤ ∑ i ∈ range (K + 1), primeWeight B i :=
        Finset.sum_nonneg (fun i _ => primeWeight_nonneg B i)
      rw [Finset.sum_range_succ] at this
      exact this
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    push_cast at ih ⊢

    have hdiff : (S + g / (K : ℝ) ^ 2 - (G + g) / ((K : ℝ) + 1) ^ 2) -
        (S - G / (K : ℝ) ^ 2) = (G + g) * (1 / (K : ℝ) ^ 2 - 1 / ((K : ℝ) + 1) ^ 2) := by
      field_simp
      ring
    have hnn : 0 ≤ 1 / (K : ℝ) ^ 2 - 1 / ((K : ℝ) + 1) ^ 2 := by
      rw [sub_nonneg]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    have hstep : (G + g) * (1 / (K : ℝ) ^ 2 - 1 / ((K : ℝ) + 1) ^ 2) ≤
        2 * Real.log 4 * (1 / (K : ℝ) - 1 / ((K : ℝ) + 1)) := by
      calc (G + g) * (1 / (K : ℝ) ^ 2 - 1 / ((K : ℝ) + 1) ^ 2)
          ≤ (K * Real.log 4) * (1 / (K : ℝ) ^ 2 - 1 / ((K : ℝ) + 1) ^ 2) :=
            mul_le_mul_of_nonneg_right hG1 hnn
        _ = Real.log 4 * ((2 * K + 1) / (K * ((K : ℝ) + 1) ^ 2)) := by
            field_simp
            ring
        _ ≤ Real.log 4 * (2 * (1 / (K : ℝ) - 1 / ((K : ℝ) + 1))) := by
            apply mul_le_mul_of_nonneg_left _ hlog4
            rw [show (2 : ℝ) * (1 / (K : ℝ) - 1 / ((K : ℝ) + 1)) = 2 / (K * ((K : ℝ) + 1)) by
              field_simp; ring]
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith
        _ = 2 * Real.log 4 * (1 / (K : ℝ) - 1 / ((K : ℝ) + 1)) := by ring
    have ih' : S - G / (K : ℝ) ^ 2 ≤ 2 * Real.log 4 * (1 / ((M : ℕ) : ℝ) - 1 / (K : ℝ)) := by
      simpa using ih
    have : S + g / (K : ℝ) ^ 2 - (G + g) / ((K : ℝ) + 1) ^ 2 ≤
        2 * Real.log 4 * (1 / ((M : ℕ) : ℝ) - 1 / ((K : ℝ) + 1)) := by
      linarith
    simpa using this

theorem prime_partial_le (B : ℝ) (hB : 0 < B) (K : ℕ) :
    ∑ i ∈ range K, primeWeight B i / (i : ℝ) ^ 2 ≤ 2 * Real.log 4 / B := by
  set M := ⌊B⌋₊ + 1 with hM
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hMB : B < (M : ℝ) := by
    rw [hM]; push_cast; exact Nat.lt_floor_add_one B
  have hMpos : (0 : ℝ) < M := lt_trans hB hMB
  have hfinal : 2 * Real.log 4 / (M : ℝ) ≤ 2 * Real.log 4 / B :=
    div_le_div_of_nonneg_left (by positivity) hB hMB.le
  rcases lt_or_ge K M with hK | hK
  · rw [Finset.sum_eq_zero]
    · positivity
    · intro i hi
      rw [primeWeight_eq_zero_of_lt B hB.le (lt_trans (Finset.mem_range.mp hi) hK), zero_div]
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hK
    have hW := abel_step B hB j
    rw [← hM] at hW
    set K := M + j
    have hKpos : (0 : ℝ) < (K : ℝ) := by
      have : (M : ℝ) ≤ K := by exact_mod_cast (Nat.le_add_right M j)
      linarith
    have hG : ∑ i ∈ range K, primeWeight B i ≤ K * Real.log 4 := by
      calc ∑ i ∈ range K, primeWeight B i ≤ ∑ i ∈ range (K + 1), primeWeight B i :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
              (fun i _ _ => primeWeight_nonneg B i)
        _ ≤ K * Real.log 4 := sum_primeWeight_le B K
    have hGK : (∑ i ∈ range K, primeWeight B i) / (K : ℝ) ^ 2 ≤ Real.log 4 / K := by
      rw [div_le_div_iff₀ (by positivity) hKpos]
      nlinarith
    have h1 : 0 ≤ Real.log 4 / K := by positivity
    calc ∑ i ∈ range K, primeWeight B i / (i : ℝ) ^ 2
        ≤ 2 * Real.log 4 * (1 / (M : ℝ) - 1 / (K : ℝ)) + Real.log 4 / K := by linarith
      _ = 2 * Real.log 4 / (M : ℝ) - Real.log 4 / K := by ring
      _ ≤ 2 * Real.log 4 / (M : ℝ) := by linarith
      _ ≤ 2 * Real.log 4 / B := hfinal

end Elem


namespace Elem

end Elem


end

end RestTerms

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

def IsBlockAlternating (f N : ℕ) (P : RootRing f N) : Prop :=
  ∀ w : Fin f → Equiv.Perm (Fin N), blockPermute f N w P = blockSign f N w • P

def IsBlockSymmetric (f N : ℕ) (P : RootRing f N) : Prop :=
  ∀ w : Fin f → Equiv.Perm (Fin N), blockPermute f N w P = P

theorem isBlockAlternating_blockVandermonde (f N : ℕ) :
    IsBlockAlternating f N (blockVandermonde f N) :=
  fun w => Flag.blockPermute_blockVandermonde f N w

theorem isBlockAlternating_antisymmetrize (f N : ℕ) (H : RootRing f N) :
    IsBlockAlternating f N (antisymmetrize f N H) :=
  fun w => Flag.blockPermute_antisymmetrize f N w H

def FlagCoeffBlockPermute.Statement : Prop :=
  ∀ (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) (P : RootRing f N) (α : Fin f × Fin N →₀ ℕ),
    AddMonoidAlgebra.coeff (blockPermute f N w P) α =
      AddMonoidAlgebra.coeff P (Finsupp.equivFunOnFinite.symm fun p : Fin f × Fin N => α (p.1, w p.1 p.2))

def FlagAltCoeffInjective.Statement : Prop :=
  ∀ (f N : ℕ) (P : RootRing f N) (α : Fin f × Fin N →₀ ℕ),
    IsBlockAlternating f N P → AddMonoidAlgebra.coeff P α ≠ 0 → ∀ τ : Fin f, Function.Injective fun i : Fin N => α (τ, i)

def FlagInjSumBound.Statement : Prop :=
  ∀ (N : ℕ) (g : Fin N → ℕ), Function.Injective g →
    N * (N - 1) / 2 ≤ ∑ i, g i ∧ (∑ i, g i = N * (N - 1) / 2 → ∀ i, g i < N)

def FlagStaircaseOrbit.Statement : Prop :=
  ∀ (f N : ℕ) (α β : Fin f × Fin N →₀ ℕ), (∀ τ i, α (τ, i) < N) → (∀ τ i, β (τ, i) < N) →
    (∀ τ, Function.Injective fun i : Fin N => α (τ, i)) →
    (∀ τ, Function.Injective fun i : Fin N => β (τ, i)) →
    ∃ w : Fin f → Equiv.Perm (Fin N), ∀ τ i, α (τ, w τ i) = β (τ, i)

def FlagVandermondeHomogeneous.Statement : Prop :=
  ∀ f N : ℕ, (blockVandermonde f N).IsHomogeneous (topDegree f N)

def FlagAltTopDegree.Statement : Prop :=
  ∀ (f N : ℕ) (P : RootRing f N), IsBlockAlternating f N P → P.IsHomogeneous (topDegree f N) →
    ∃ e : ℚ, P = C e * blockVandermonde f N

def FlagIntegralPermute.Statement : Prop :=
  ∀ (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) (H : RootRing f N),
    flagIntegral f N (blockPermute f N w H) = blockSign f N w * flagIntegral f N H

def FlagIntegralAntisymmetrize.Statement : Prop :=
  ∀ (f N : ℕ) (H : RootRing f N),
    flagIntegral f N (antisymmetrize f N H) = (N.factorial : ℚ) ^ f * flagIntegral f N H

def FlagIntegralVandermondePos.Statement : Prop :=
  ∀ f N : ℕ, 0 < flagIntegral f N (blockVandermonde f N)

def FlagAntisymHomogeneous.Statement : Prop :=
  ∀ (f N : ℕ) (H : RootRing f N) (d : ℕ), H.IsHomogeneous d → (antisymmetrize f N H).IsHomogeneous d

def FlagHomogeneousComponentMul.Statement : Prop :=
  ∀ (σ : Type) (P G : MvPolynomial σ ℚ) (k n : ℕ), P.IsHomogeneous k →
    homogeneousComponent n (P * G) = if k ≤ n then P * homogeneousComponent (n - k) G else 0

def FlagIntegralTopComponent.Statement : Prop :=
  ∀ (f N : ℕ) (Φ : RootRing f N),
    flagIntegral f N Φ = flagIntegral f N (homogeneousComponent (topDegree f N) Φ)

def FlagIntegralVandermondeMul.Statement : Prop :=
  ∀ (f N : ℕ) (R : RootRing f N),
    flagIntegral f N (blockVandermonde f N * R) = constantCoeff R * flagIntegral f N (blockVandermonde f N)

def FlagIntegralViaQuotient.Statement : Prop :=
  ∀ (f N : ℕ) (H R : RootRing f N), antisymmetrize f N H = blockVandermonde f N * R →
    flagIntegral f N H =
      flagIntegral f N (blockVandermonde f N) / (N.factorial : ℚ) ^ f * constantCoeff R

def FlagIntegralTopDegree.Statement : Prop :=
  ∀ (f N : ℕ) (H : RootRing f N), H.IsHomogeneous (topDegree f N) →
    algebraMap ℚ (FractionRing (RootRing f N)) (flagIntegral f N H) =
      algebraMap ℚ (FractionRing (RootRing f N))
          (flagIntegral f N (blockVandermonde f N) / (N.factorial : ℚ) ^ f) *
        dividedDifference f N H

def FlagSymmetricMulAntisym.Statement : Prop :=
  ∀ (f N : ℕ) (P H : RootRing f N), IsBlockSymmetric f N P →
    antisymmetrize f N (P * H) = P * antisymmetrize f N H

def FlagPowerSumSymmetric.Statement : Prop :=
  ∀ (f N k : ℕ) (τ : Fin f), IsBlockSymmetric f N (blockPowerSum f N k τ)

def FlagSwapDivisible.Statement : Prop :=
  ∀ (σ : Type) [DecidableEq σ] (P : MvPolynomial σ ℚ) (a b : σ), a ≠ b →
    rename (Equiv.swap a b) P = -P → (X a - X b : MvPolynomial σ ℚ) ∣ P

def FlagDiffPrime.Statement : Prop :=
  ∀ (σ : Type) [DecidableEq σ] (a b : σ), a ≠ b → Prime (X a - X b : MvPolynomial σ ℚ)

def FlagDiffNotDvd.Statement : Prop :=
  ∀ (σ : Type) [DecidableEq σ] (a b c d : σ), a ≠ b → c ≠ d → ¬ (a = c ∧ b = d) →
    ¬ (a = d ∧ b = c) → ¬ (X a - X b : MvPolynomial σ ℚ) ∣ (X c - X d)

def FlagProdPrimesDvd.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (ι : Type) (s : Finset ι) (p : ι → R) (x : R),
    (∀ i ∈ s, Prime (p i)) → (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ p i ∣ p j) → (∀ i ∈ s, p i ∣ x) →
      (∏ i ∈ s, p i) ∣ x

def FlagVandermondeDvd.Statement : Prop :=
  ∀ (f N : ℕ) (P : RootRing f N), IsBlockAlternating f N P → blockVandermonde f N ∣ P

def FlagDividedDifferencePoly.Statement : Prop :=
  ∀ (f N : ℕ) (H : RootRing f N), ∃ R : RootRing f N,
    antisymmetrize f N H = blockVandermonde f N * R ∧ IsBlockSymmetric f N R

def FlagQuotientHomogeneous.Statement : Prop :=
  ∀ (σ : Type) (A R : MvPolynomial σ ℚ) (m k : ℕ), A ≠ 0 → A.IsHomogeneous m →
    (A * R).IsHomogeneous (m + k) → R.IsHomogeneous k

def FlagRestrictSymmetric.Statement : Prop :=
  ∀ (f N : ℕ) (τ : Fin f) (R : RootRing f N), IsBlockSymmetric f N R →
    (restrictToBlock f N τ R).IsSymmetric

def FlagRestrictPowerSum.Statement : Prop :=
  ∀ (f N k : ℕ) (τ σ : Fin f), 1 ≤ k →
    restrictToBlock f N τ (blockPowerSum f N k σ) = if σ = τ then psum (Fin N) ℚ k else 0

def FlagRestrictConstantCoeff.Statement : Prop :=
  ∀ (f N : ℕ) (τ : Fin f) (R : RootRing f N),
    constantCoeff (restrictToBlock f N τ R) = constantCoeff R

def FlagRestrictHomogeneous.Statement : Prop :=
  ∀ (f N : ℕ) (τ : Fin f) (R : RootRing f N) (k : ℕ), R.IsHomogeneous k →
    (restrictToBlock f N τ R).IsHomogeneous k

def FlagRestrictDecomposition.Statement : Prop :=
  ∀ (f N : ℕ) (τ : Fin f) (R : ℕ → Fin f → RootRing f N),
    restrictToBlock f N τ (∑ l ∈ Finset.Icc 1 N, ∑ σ : Fin f, blockPowerSum f N l σ * R l σ) =
      ∑ l ∈ Finset.Icc 1 N, psum (Fin N) ℚ l * restrictToBlock f N τ (R l τ)

def FlagPowerSumPreimage.Statement : Prop :=
  ∀ (N : ℕ) (T : ℕ → MvPolynomial (Fin N) ℚ), (∀ l, (T l).IsSymmetric) →
    ∃ S : MvPolynomial (Fin N) ℚ,
      powerSumHom N S = ∑ l ∈ Finset.Icc 1 N, psum (Fin N) ℚ l * T l ∧
      ∀ (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N),
        AddMonoidAlgebra.coeff S (Finsupp.single (⟨k - 1, by omega⟩ : Fin N) 1) = constantCoeff (T k)

def FlagAntisymDecomposition.Statement : Prop :=
  ∀ (f N : ℕ) (F G : RootRing f N) (Q R : ℕ → Fin f → RootRing f N),
    IsPowerSumDecomposition f N F Q →
    (∀ l σ, antisymmetrize f N (G * Q l σ) = blockVandermonde f N * R l σ) →
    antisymmetrize f N (G * F) =
      blockVandermonde f N * ∑ l ∈ Finset.Icc 1 N, ∑ σ : Fin f, blockPowerSum f N l σ * R l σ

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

