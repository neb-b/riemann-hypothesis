module

public import Mathlib

@[expose] public section

open Polynomial

namespace PositivityTheory.AutomorphicGaloisHodgeTate.Div

def IsSSMat {Γ K ι : Type} [Group Γ] [Field K] [Fintype ι] [DecidableEq ι]
    (ρ : Γ →* GL ι K) : Prop :=
  ∀ W : Submodule K (ι → K), (∀ g : Γ, ∀ v ∈ W, (ρ g : Matrix ι ι K).mulVec v ∈ W) →
    ∃ W' : Submodule K (ι → K), IsCompl W W' ∧
      ∀ g : Γ, ∀ v ∈ W', (ρ g : Matrix ι ι K).mulVec v ∈ W'

def InLieZar {Γ K K' ι : Type} [Group Γ] [Field K] [Field K'] [Algebra K K']
    [Fintype ι] [DecidableEq ι] (ρ : Γ →* GL ι K) (X : Matrix ι ι K') : Prop :=
  ∀ f : MvPolynomial (ι × ι) K,
    (∀ g : Γ, MvPolynomial.eval (fun p : ι × ι => (ρ g : Matrix ι ι K) p.1 p.2) f = 0) →
      ∑ p : ι × ι, algebraMap K K'
          (MvPolynomial.eval (fun q : ι × ι => (1 : Matrix ι ι K) q.1 q.2)
            (MvPolynomial.pderiv p f)) * X p.1 p.2 = 0

end PositivityTheory.AutomorphicGaloisHodgeTate.Div
