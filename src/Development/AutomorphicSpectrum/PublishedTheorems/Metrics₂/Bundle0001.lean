module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelong
section
namespace GlobalTheory.CompanionTheory.Ar.Pub

def PoincareLelong : Prop :=
  ReciprocityTheory.ChartRestriction.G.Geo.ArithmeticPoincareLelongFormula

end GlobalTheory.CompanionTheory.Ar.Pub
end

-- bundled from Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelongInv
section
namespace GlobalTheory.CompanionTheory.Hypotheses₂

open ReciprocityTheory.ChartRestriction.G.Geo

def PoincareLelongInv : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A B : HermLine ι) (s : MRing ι),
    IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
    (∀ j, IsConjInvariantH (L j)) → IsConjInvariantH A → IsConjInvariantH B →
    B.a = 0 → IsSectionOn P A s →
    ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot L)) (logNorm A s) =
      (∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W),
          (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) (fun z => Real.log (B.h z))) -
        ptsIntegral P (Fin.cons (fun z => Real.log (A.h z)) (pot L)) (fun z => Real.log (B.h z))

end GlobalTheory.CompanionTheory.Hypotheses₂
end

