module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0021

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Set Matrix MeasureTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.ArInt
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt IsPeriodMap cov per stdLat transl IsFactor IsMetric)
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Points (PtsOver)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm (IsRegVar BottChern ArChow hermMat eval₂ bas relCot dRel IsRelAcyclic IsGenSmooth)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (om0)
open scoped ContDiff Real CategoryTheory.Obj ComplexOrder

namespace GlobalTheory.TorsionForm

variable {k : Type} [CommRing k] {S : Scheme.{0}} {p : S ⟶ Sp k} {σ : k →+* ℂ} {A : Over S}
  {g D : ℕ}

section Global

variable {D' r : ℕ}



end Global

end GlobalTheory.TorsionForm

namespace GlobalTheory.Published

open GlobalTheory.TorsionForm MvPolynomial

def AmpleVanishing : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A →
    ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → IsRelAcyclic A.hom A.hom L

end GlobalTheory.Published
