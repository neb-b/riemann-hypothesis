module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0003

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def ltEquiv (Dw : Datum H) (n : ℕ) : LtN Dw n ≃ (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) × Fin n where
  toFun ℓ := (⟨ℓ.1, ℓ.2.1⟩, ℓ.2.2)
  invFun p := ⟨p.1.1, p.1.2, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def encP {Dw : Datum H} {n : ℕ} {K : Type} [CommRing K] (P : MvPolynomial (LtN Dw n) K) :
    MvPolynomial ((Σ τ : E →+* ℂ, Fin (Dw.mult τ)) × Fin n) K :=
  MvPolynomial.rename (ltEquiv Dw n) P

def PsiCoverSt (H : Host E) : Prop :=
  ∀ τ : E →+* ℂ, InPsi H τ ∨ InPsi H (ComplexEmbedding.conjugate τ)

end Formalism.MainNotions.ModuliIntegralCharts.H1
