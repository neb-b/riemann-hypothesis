module

public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

namespace FamilyRepresentationConstants

variable {D : D7}

abbrev RFam (D : D7) : Type := ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))

abbrev RhoFam (D : D7) : Type := ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))

theorem placesOver_finite (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have hp' : ((p : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have hI : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hp'
  refine (Ideal.finite_factors hI).subset ?_
  intro v hv
  show v.asIdeal ∣ Ideal.span {((p : ℕ) : 𝓞 E)}
  rw [Ideal.dvd_span_singleton]
  exact hv

def CG (constantFirstHub : ℝ) (Q : MvPolynomial (Fin 3) ℕ) : ℝ :=
  max (max constantFirstHub ((∑ m ∈ Q.support, Q.coeff m : ℕ) : ℝ)) (max (Q.totalDegree : ℝ) 1)

end FamilyRepresentationConstants

end Formalism.MainNotions.N

end
