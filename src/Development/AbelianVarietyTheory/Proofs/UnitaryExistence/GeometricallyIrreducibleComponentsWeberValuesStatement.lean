module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0110
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0028

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricallyIrreducible_components_weberValues : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, Formalism.L2.Pj.InR D j → ∀ (l' : Level Q.H) (Xo' : Moduli (Q.Dw j) l') (c' : Coeff l') (n : ℕ), 0 < n → l'.M' ∣ n → (WeberIn Q.H c'.F n ∨ CurveOver Q.H c'.F n) → FnAlgClosed (Xo := Xo') (c := c') := by
  first | exact @GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_weberIn | exact GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_weberIn | (intros; apply GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_weberIn <;> assumption)
