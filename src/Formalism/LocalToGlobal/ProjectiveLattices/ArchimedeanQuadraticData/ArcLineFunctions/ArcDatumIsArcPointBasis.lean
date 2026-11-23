module

public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QatOfBridge
public import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj.QAt

open CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct

variable {D : D7} {T : Core D}

structure ArcDatumAt (T : Core D) (j : ℕ) (K₁ : Type) [Field K₁] [Algebra T.Q.c.F K₁]
    [Algebra T.Q.c.F (ArcS (T.Q.Dw j) K₁)] where

  Wp : ValuationSubring ℂ
  Y : Model (T.Q.Xo j) T.Q.c (T.Q.c.V Wp).subtype
  a : ArcIn (T.Q.Dw j) T.Q.l (RingHom.id T.Q.c.F) K₁ (algebraMap T.Q.c.F K₁)
  χ : Sp (PowerSeries K₁) ⟶ Y.X

  chiOver : χ ≫ Y.s = spMap ((PowerSeries.C (R := K₁)).comp
    ((algebraMap T.Q.c.F K₁).comp (T.Q.c.V Wp).subtype))
  W : ArcWit Y (a.restrict (T.Q.c.V Wp).subtype) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := K₁))
    PowerSeries.X χ
  e : ∀ τ, Fin ((T.Q.Dw j).mult τ) →
    ReciprocityTheory.ChartRestriction.G.Out.GtPt (a.restrict (T.Q.c.V Wp).subtype).D₀ (epsR K₁)
  yF : FrPt (T.Q.Xo j) T.Q.c (ArcS (T.Q.Dw j) K₁)

  th : (a.restrict (T.Q.c.V Wp).subtype).D₀.P.L.Sec
  arcDatum_isArc_point_basis : IsArcPointPowerSeries Y (a.restrict (T.Q.c.V Wp).subtype) χ W e yF
  isArc3 : IsArcPt3At Y (a.restrict (T.Q.c.V Wp).subtype) χ W yF th
  μ : ArcLt (T.Q.Dw j) →₀ ℕ
  jj : ℤ

end Formalism.L2.Pj.QAt
