module

public import Formalism.ThetaLogCoordinates.SandwichModelDomains.SandwichModelProofs.Bundle0001
public import Formalism.ThetaLogCoordinates.SandwichModelDomains.SandwichModelProofs.SwappedHighestWeightNeZero
public import Formalism.ThetaLogCoordinates.SandwichModelDomains.SandwichModelProofs.Bundle0002

@[expose] public section

namespace Formalism.InvariantFactorPaths.INST.Top

theorem spreadTop : SpreadTop := spread_top_holds
theorem spreadSquare : SpreadSquare := spread_square_holds
theorem rowGlOne : RowGlOne := gl_one_first_line_action
theorem rowGlDiv : RowGlDiv := gl_first_line_divided_powers
theorem swpWt : SwpWt := swap_weight_compat
theorem swpPol : SwpPol := swap_polynomial_compat
theorem swpInt : SwpInt := swpInt_statement
theorem coreQp : CoreQp := coreQp_of rowGlOne rowGlDiv swpWt swpPol swpInt
theorem descentZ : DescentZ := descent_over_integers
theorem ascentDomain : AscentDomain := ascent_domain_holds
theorem unitsOfLocal : UnitsOfLocal := by
  intro p hp O _ _ hpu c hc
  by_contra hcu
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hcop : IsCoprime (p : ℤ) c := by
    first
    | exact (Irreducible.coprime_iff_not_dvd hpz.irreducible).2 hc
    | exact (Prime.coprime_iff_not_dvd hpz).2 hc
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : (u : O) * (p : O) + (v : O) * (c : O) = 1 := by
    have := congrArg (fun z : ℤ => (z : O)) huv
    push_cast at this
    exact this
  have hmp : (p : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hpu
  have hmc : (c : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hcu
  have h1m : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [← h1]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hmp) (Ideal.mul_mem_left _ _ hmc)
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h1m)
theorem sandwichZp : SandwichZp := by
  intro p hp r n hn ν hν l hL x hx
  have hS : Spread (Padic p) r n ν l := by
    rcases hL with h | ⟨rfl, h⟩
    · exact spreadTop _ r n ν l h
    · exact spreadSquare _ _ ν l h
  exact coreQp p r n hn ν hν l hS x hx
theorem sandwichZ : SandwichZ := by
  intro p hp r n hn ν hν l hL f hf
  exact descentZ p r n hn ν hν (sExp p r l) (sandwichZp p r n hn ν hν l hL) f hf
theorem sandwichDomain : SandwichDomain := sandwichDomain_of sandwichZ ascentDomain
theorem sandwichLocal : SandwichLocal := by
  intro p hp r n hn ν hν l hL O _ _ _ hpu
  exact sandwichDomain p r n hn ν hν l hL O (unitsOfLocal p O hpu)

end Formalism.InvariantFactorPaths.INST.Top
