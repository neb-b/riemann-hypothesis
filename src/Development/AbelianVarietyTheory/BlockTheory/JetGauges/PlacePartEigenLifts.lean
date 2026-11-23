module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003
public import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PlacePartEigenLifts

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.TB

section Types

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}
variable (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F))

end Types

section Parts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

def chartVal (C : IntegralChartA3 Xo c T io y) (k : ℕ) {n : ℕ} (f : Germ.PS T.Fr n (chD C.ch))
    (P : MvPolynomial (LtN Dw n) T.Fr) : T.Fr :=
  letI := io.toAlgebra
  nabValN C.ch.B T.Fr C.ch.h H.w0 k f (fun ℓ => ℓ.2.2) (fun ℓ => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) P

end Parts

end GlobalTheory.IndefiniteRowSideFullHecke.PlacePartEigenLifts
