module

public import Mathlib
public import Formalism.QuotientMetricDivisors.Bundle0002
public import Formalism.TranslateCocycles.StatementHC
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0003

@[expose] public section

open Module NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl lw PlOver IsConjAt)
open Formalism.CG (HCdeg HCDplus HCDminus)

noncomputable section

namespace Formalism.AtG

namespace ValuationJets

open Formalism.DivisionValues.ValuationRepresentative Formalism.DivisionValues.PlaceSumConjugation

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem val_int (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (hx : x ≠ 0) :
    w.valuation K (x : K) = WithZero.exp (-(vw w (x : K))) := by
  have h1 : (x : K) = algebraMap (𝓞 K) K x := rfl
  rw [h1, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg _ hx]
  congr 1
  rw [neg_inj]
  symm
  unfold vw
  rw [← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K w (by simpa using hx)]

theorem val_eq (w : HeightOneSpectrum (𝓞 K)) (a : K) (ha : a ≠ 0) :
    w.valuation K a = WithZero.exp (-(vw w a)) := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) a
  have hx0 : algebraMap (𝓞 K) K x ≠ 0 := (div_ne_zero_iff.mp ha).1
  have hy0 : algebraMap (𝓞 K) K y ≠ 0 := (div_ne_zero_iff.mp ha).2
  have hx : x ≠ 0 := fun h => hx0 (by rw [h, map_zero])
  have hy1 : y ≠ 0 := fun h => hy0 (by rw [h, map_zero])
  have vx := val_int w x hx
  have vy := val_int w y hy1
  rw [show ((x : K)) = algebraMap (𝓞 K) K x from rfl] at vx
  rw [show ((y : K)) = algebraMap (𝓞 K) K y from rfl] at vy
  have hmul : vw w (algebraMap (𝓞 K) K x) =
      vw w (algebraMap (𝓞 K) K x / algebraMap (𝓞 K) K y) + vw w (algebraMap (𝓞 K) K y) := by
    rw [← vw_mul w _ _ ha hy0, div_mul_cancel₀ _ hy0]
  rw [map_div₀, vx, vy, ← WithZero.exp_sub]
  congr 1
  linarith

theorem vw_add (w : HeightOneSpectrum (𝓞 K)) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a + b ≠ 0) :
    min (vw w a) (vw w b) ≤ vw w (a + b) := by
  have h1 := (w.valuation K).map_add a b
  rw [val_eq w a ha, val_eq w b hb, val_eq w _ hab] at h1
  rcases le_max_iff.mp h1 with h | h
  · have h2 := WithZero.exp_le_exp.mp h
    exact le_trans (min_le_left _ _) (by linarith)
  · have h2 := WithZero.exp_le_exp.mp h
    exact le_trans (min_le_right _ _) (by linarith)


end ValuationJets

open ValuationJets Formalism.DivisionValues.ValuationRepresentative Formalism.DivisionValues.PlaceSumConjugation

end Formalism.AtG
