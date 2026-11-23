module

public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.PrimePairSizeCondition
public import Development.AutomorphicArithmetic.PrimeDiscriminants.Bundle0001
public import Development.AutomorphicArithmetic.WeightCongruences.Bundle0001
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005
public import Formalism.FrobeniusOrbits.HostThickExists
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0001
public import Development.AutomorphicArithmetic.FrobeniusLocalisation.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097

@[expose] public section

open UpperTheory.HF

open NumberField IsDedekindDomain Formalism.HC Formalism.L2.Host GlobalTheory.Mem.Chr GlobalTheory
open scoped Pointwise

private theorem exists_place {L : Type} [Field L] [NumberField L] {p : ℕ} (hs : SplitsC L p) :
    ∃ v : HeightOneSpectrum (𝓞 L), ((p : ℕ) : 𝓞 L) ∈ v.asIdeal := by
  unfold SplitsC at hs
  exact Set.nonempty_of_ncard_ne_zero (hs ▸ Module.finrank_pos.ne')

private theorem pow_sub_one_mem {L : Type} [Field L] [NumberField L] {p : ℕ} (v : HeightOneSpectrum (𝓞 L))
    (hN : Ideal.absNorm v.asIdeal = p) {x : 𝓞 L} {m : ℕ} (hm : m ≠ 0) (hx : x ^ m = 1) :
    x ^ (p - 1) - 1 ∈ v.asIdeal := by
  have := v.isMaximal
  let := Ideal.Quotient.field v.asIdeal
  have : Finite (𝓞 L ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  let := Fintype.ofFinite (𝓞 L ⧸ v.asIdeal)
  have hc : Fintype.card (𝓞 L ⧸ v.asIdeal) = p := by
    rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have h0 : Ideal.Quotient.mk v.asIdeal x ≠ 0 := by
    intro h
    have h1 := congrArg (Ideal.Quotient.mk v.asIdeal) hx
    rw [map_pow, h, zero_pow hm, map_one] at h1
    exact zero_ne_one h1
  rw [← Ideal.Quotient.eq, map_pow, map_one, ← hc]
  exact FiniteField.pow_card_sub_one_eq_one _ h0
