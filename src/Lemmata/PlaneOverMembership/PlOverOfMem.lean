module

public import Mathlib
public import Formalism.LocalToGlobal.ExponentGrids.ScaledCoordinatesValuationLemma
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0003
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0002
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Formalism.PairingDivisors.PairingDivisorProofs.Height
public import Formalism.PairingDivisors.PairingDivisorProofs.SumValuationNat
public import Formalism.PairingDivisors.PairingDivisorProofs.ValAdd
public import Formalism.TowerValuationBounds.TowerValuationProofs.SumAdditiveCharacterEqZero
public import Formalism.SizeWindowBrackets.Bundle0004
public import Formalism.QuotientMetricDivisors.Bundle0004
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0004
public import Formalism.SizeWindowBrackets.Bundle0003
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtGram
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle0004
public import Formalism.SizeWindowBrackets.Bundle0001
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Fintype.BigOperators
public import Formalism.QuotientMetricDivisors.Bundle0001
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermodZ
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle0001
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.FinSup
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle0002
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle0003
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneq
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PolygonSlopeSum
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNSlopes
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Bundle0005
public import Formalism.HarderNarasimhan.DegSupermodZ
public import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
public import Formalism.LatticeSlopes.LatticeSlopesProofs.Bundle0001
public import Formalism.LatticeSlopes.LatticeSlopesProofs.Bundle0002
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PlaceSplit
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.GramBlock
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtImage
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Rerealize
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.QuotRealize
public import Formalism.HarderNarasimhan.StatementPl
public import Formalism.CorankShare.StatementFR
public import Formalism.CorankShare.CorankShareProofs.Bundle0001
public import Formalism.HarderNarasimhan.Bundle0001

@[expose] public section

namespace Bl.PlaneOverMembership

open NumberField IsDedekindDomain

private theorem plOver_of_mem {K : Type} [Field K] [NumberField K] {g : ℕ} (hg : 0 < g)
    (w : HeightOneSpectrum (𝓞 K)) (h : (g : 𝓞 K) ∈ w.asIdeal) : Formalism.DivisionValues.PlOver g w := by
  classical
  have hc : ((g : 𝓞 K) : K) = (g : K) := by simp
  have hg0 : (g : 𝓞 K) ≠ 0 := by exact_mod_cast hg.ne'
  have hJ : (Ideal.span {(g : 𝓞 K)} : Ideal (𝓞 K)) ≠ 0 := by
    rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  have hm : Associates.mk (Ideal.span {(g : 𝓞 K)}) ≠ 0 := by rwa [ne_eq, Associates.mk_eq_zero]
  have h1 : 1 ≤ (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {(g : 𝓞 K)})).factors := by
    rw [← Associates.prime_pow_dvd_iff_le hm w.associates_irreducible, pow_one,
      Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact h
  unfold Formalism.DivisionValues.PlOver Formalism.DivisionValues.vw
  rw [← hc, ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K _ hJ]
  exact_mod_cast h1

theorem goal1 :
  Formalism.AtG.FinitePlaceLiesOverPrime := by
  intro K _ _
  refine ⟨fun w => Ideal.absNorm (Ideal.under ℤ w.asIdeal), fun w => ?_⟩
  have : NeZero w.asIdeal := ⟨w.ne_bot⟩
  have hp : (Ideal.absNorm (Ideal.under ℤ w.asIdeal)).Prime := Nat.absNorm_under_prime w.asIdeal
  exact ⟨hp, plOver_of_mem hp.pos w (Int.absNorm_under_mem w.asIdeal)⟩

end Bl.PlaneOverMembership
