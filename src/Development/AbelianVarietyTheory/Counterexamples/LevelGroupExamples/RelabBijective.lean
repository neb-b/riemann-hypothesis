module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.UnFree

@[expose] public section

noncomputable section

namespace GlobalTheory.UnifDataTest

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem relab_conj (c : Coeff l) (σ : c.F →+* ℂ) (τ : E →+* ℂ) :
    relab c σ (conjEmb τ) = conjEmb (relab c σ τ) := by
  ext a
  have h1 : embF c (conjEmb τ) a = embF c τ (IsCMField.complexConj E a) :=
    Subtype.ext (IsCMField.complexEmbedding_complexConj E τ a).symm
  show σ (embF c (conjEmb τ) a) = starRingEnd ℂ (relab c σ τ a)
  rw [h1]
  exact IsCMField.complexEmbedding_complexConj E (relab c σ τ) a

end GlobalTheory.UnifDataTest
