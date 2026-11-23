module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinS2LimitFormula
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.WeierstrassNumeratorDenominator
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.TaylorWp
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CoeffPowEqZeroOfCc

@[expose] public section

noncomputable section
open scoped BigOperators
open Formalism.L2.Th1.CM (cW)
open PowerSeries

namespace Formalism.L2.Th1.F

namespace Universal

def IsU (a : ∀ (K : Type) [Field K] [CharZero K], K → K → K) : Prop :=
  ∃ p : MvPolynomial (Fin 2) ℚ, ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K),
    a K g2 g3 = MvPolynomial.aeval ![g2, g3] p

theorem IsU.congr {a b : ∀ (K : Type) [Field K] [CharZero K], K → K → K} (h : IsU a)
    (hab : ∀ (K : Type) [Field K] [CharZero K] (g2 g3 : K), b K g2 g3 = a K g2 g3) : IsU b := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, fun K _ _ g2 g3 => by rw [hab, hp]⟩

theorem isU_const (q : ℚ) : IsU (fun K [Field K] [CharZero K] _ _ => (q : K)) :=
  ⟨MvPolynomial.C q, fun K _ _ g2 g3 => by rw [MvPolynomial.aeval_C, eq_ratCast]⟩

theorem universal_g2 : IsU (fun K [Field K] [CharZero K] g2 _ => g2) :=
  ⟨MvPolynomial.X 0, fun K _ _ g2 g3 => by simp⟩

theorem universal_g3 : IsU (fun K [Field K] [CharZero K] _ g3 => g3) :=
  ⟨MvPolynomial.X 1, fun K _ _ g2 g3 => by simp⟩

theorem IsU.add {a b : ∀ (K : Type) [Field K] [CharZero K], K → K → K} (ha : IsU a) (hb : IsU b) :
    IsU (fun K [Field K] [CharZero K] g2 g3 => a K g2 g3 + b K g2 g3) := by
  obtain ⟨p, hp⟩ := ha
  obtain ⟨q, hq⟩ := hb
  exact ⟨p + q, fun K _ _ g2 g3 => by
    show a K g2 g3 + b K g2 g3 = _
    rw [map_add (f := _), hp, hq]⟩

theorem IsU.mul {a b : ∀ (K : Type) [Field K] [CharZero K], K → K → K} (ha : IsU a) (hb : IsU b) :
    IsU (fun K [Field K] [CharZero K] g2 g3 => a K g2 g3 * b K g2 g3) := by
  obtain ⟨p, hp⟩ := ha
  obtain ⟨q, hq⟩ := hb
  exact ⟨p * q, fun K _ _ g2 g3 => by
    show a K g2 g3 * b K g2 g3 = _
    rw [map_mul, hp, hq]⟩

theorem IsU.sum {ι : Type} (s : Finset ι) (a : ι → ∀ (K : Type) [Field K] [CharZero K], K → K → K)
    (h : ∀ i ∈ s, IsU (a i)) :
    IsU (fun K [Field K] [CharZero K] g2 g3 => ∑ i ∈ s, a i K g2 g3) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (isU_const 0).congr fun K _ _ g2 g3 => by simp
  | insert i s hi ih =>
    refine ((h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))).congr fun K _ _ g2 g3 => ?_
    rw [Finset.sum_insert hi]

theorem isU_cW (k : ℕ) : IsU (fun K [Field K] [CharZero K] g2 g3 => cW g2 g3 k) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases h2 : k = 2
    · refine (universal_g2.mul (isU_const (1 / 20))).congr fun K _ _ g2 g3 => ?_
      rw [POf.cW_eq, if_pos h2]
      push_cast
      ring
    by_cases h3 : k = 3
    · refine (universal_g3.mul (isU_const (1 / 28))).congr fun K _ _ g2 g3 => ?_
      rw [POf.cW_eq, if_neg h2, if_pos h3]
      push_cast
      ring
    by_cases h4 : 4 ≤ k
    · refine ((isU_const (3 / ((2 * (k : ℚ) + 1) * ((k : ℚ) - 3)))).mul
        (IsU.sum Finset.univ (fun (m : Fin (k - 3)) K [Field K] [CharZero K] g2 g3 =>
          cW g2 g3 (m.val + 2) * cW g2 g3 (k - (m.val + 2)))
          fun m _ => (ih (m.val + 2) (by omega)).mul (ih (k - (m.val + 2)) (by omega)))).congr
        fun K _ _ g2 g3 => ?_
      rw [POf.cW_eq, if_neg h2, if_neg h3, if_pos h4]
      push_cast
      rfl
    · refine (isU_const 0).congr fun K _ _ g2 g3 => ?_
      rw [POf.cW_eq, if_neg h2, if_neg h3, if_neg h4]
      simp

theorem isU_pOf (n : ℕ) : IsU (fun K [Field K] [CharZero K] g2 g3 => coeff n (pOf g2 g3)) := by
  by_cases hn : Even n
  · exact (isU_cW (n / 2 + 1)).congr fun K _ _ g2 g3 => by rw [POf.coeff_pOf, if_pos hn]
  · exact (isU_const 0).congr fun K _ _ g2 g3 => by rw [POf.coeff_pOf, if_neg hn]; simp

variable {K : Type} [Field K] [CharZero K]

end Universal

end Formalism.L2.Th1.F
