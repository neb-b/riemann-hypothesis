module

public import Mathlib
public import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
public import Formalism.LocalRingCardinality.Bundle0004
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0018
public import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfDepthValuations
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HalfDepthValuations

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.MainNotions.DIV.Cons

variable {D : D7}



section Rec

variable {L : SizeData₂ D} {P : ParameterChoice' D L}

end Rec

theorem bar_eq_barE (Q : Par D) (a : 𝓞 D.host.E) : Q.H.bar a = barE D a := by
  apply IsFractionRing.injective (𝓞 D.host.E) D.host.E
  exact Q.H.bar_eq a

end GlobalTheory.IndefiniteRowSideFullHecke.HalfDepthValuations
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.HalfLevelCoefficients
section
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HalfLevelCoefficients

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

structure IsHalf (D : D7) (Mb : Ideal (𝓞 D.host.E)) : Prop where
  fromK : Mb = Ideal.span {a | a ∈ Mb ∧ a ∈ Algebra.adjoin ℤ {w0E D}}
  prod : Mb * Mb.map (bH D) = Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)}
  coprime : Mb ⊔ Mb.map (bH D) = ⊤

theorem three_le_g (D : D7) (k : Fin 2) : 3 ≤ D.host.g k := by
  have := (D.host.g_prime k).two_le
  have := g_ne_two D k
  omega

def levelAt (D : D7) (Mb : Ideal (𝓞 D.host.E)) (h : IsHalf D Mb) : Level (hostOfRecord D) where
  M := D.host.g 0 * D.host.g 1
  three_le := by
    have := three_le_g D 0
    have := three_le_g D 1
    nlinarith
  odd := ((D.host.g_prime 0).odd_of_ne_two (g_ne_two D 0)).mul ((D.host.g_prime 1).odd_of_ne_two (g_ne_two D 1))
  Mb := Mb
  fromK := h.fromK
  prod := h.prod
  coprime := h.coprime
  A := 1
  A_pos := Nat.one_pos


def PrimesOver (D : D7) (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) : Prop :=
  ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal

def halfOf (D : D7) (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K)) : Ideal (𝓞 D.host.E) :=
  ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

end GlobalTheory.IndefiniteRowSideFullHecke.HalfLevelCoefficients
end
end

