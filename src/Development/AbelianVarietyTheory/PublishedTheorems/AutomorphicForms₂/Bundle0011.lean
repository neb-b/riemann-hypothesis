module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ChernWeilNumbers
section
noncomputable section

namespace GlobalTheory.Published

open AlgebraicGeometry CategoryTheory MvPolynomial GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

def ChernWeilNumbers : Prop :=
  ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0)
    (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (gr : Root m → Y.Dv),
    Refines E E' φ f → IsGraded E' gr →
      ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H →
        ∀ R : MvPolynomial (ι × ℕ) ℝ, HasChernIntegral E ⊤ H R (Y.interPoly gr (chernRoots m R * fibrePoint m))

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.GoodTopChernForm
section
noncomputable section

namespace GlobalTheory.Published

open AlgebraicGeometry CategoryTheory MvPolynomial GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

def GoodTopChernForm : Prop :=
  ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (m : ℕ) (E : Fr (ratOf X) (fun _ : Unit => m) 0)
    (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ),
    IsMetricOn E O H → IsGood E O H → IsMetricOn E ⊤ H₀ →
      ∀ t : ℝ, HasChernIntegral E ⊤ H₀ (MvPolynomial.X ((), X.dim)) t →
        HasChernIntegral E O H (MvPolynomial.X ((), X.dim)) t

end GlobalTheory.Published

end
end

