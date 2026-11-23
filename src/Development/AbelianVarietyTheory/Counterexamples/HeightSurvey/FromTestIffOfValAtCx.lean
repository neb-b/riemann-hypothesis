module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0014
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.Bundle0001

@[expose] public section

noncomputable section

namespace GlobalTheory.SupLawProbe

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

abbrev FT {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : Prop :=
  FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y

theorem evR_map (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)) (f : Rul Xo c)
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {K₁ K₂ : Type} [CommRing K₁] [Algebra c.F K₁] [CommRing K₂] [Algebra c.F K₂] (φ : K₁ →ₐ[c.F] K₂)
    (y₁ : FrPt Xo c K₁) (hT1 : FT y₁) (y₂ : FrPt Xo c K₂) (hm : FrMap φ y₁ y₂) :
    evR Xo c f y₂ = φ (evR Xo c f y₁) := by
  have hT2 : FT y₂ := by
    obtain ⟨p, ψ, y', hy'⟩ := hT1
    exact ⟨p, φ.comp ψ, y', frMap_trans (Xo := Xo) (c := c) _ _ _ ψ φ y' y₁ y₂ hy' hm⟩
  unfold evR evalAt
  rw [dite_eq_left hT2, dite_eq_left hT1]
  exact hWD f hf K₂ _ _ _ _ _ _ y₂ hT2.choose_spec.choose_spec.choose_spec
    (frMap_trans (Xo := Xo) (c := c) _ _ _ _ φ _ y₁ y₂ hT1.choose_spec.choose_spec.choose_spec hm)

variable {h : GenFrEx Xo c} {fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ}
  {yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))}

section Conj

variable (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
  (σ : c.F →+* ℂ) (cj : FrPt Xo c (CAt σ) → FrPt Xo c (CAt ((starRingEnd ℂ).comp σ)))
  (hcj : ∀ y, FrMap (SupNormExample.conjAt σ) y (cj y))
  (htr : ∀ y i, |fn _ (cj y) i| = |fn σ y i|) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c}
  (hS : f ∈ sec Xo c a n)




end Conj

end GlobalTheory.SupLawProbe
