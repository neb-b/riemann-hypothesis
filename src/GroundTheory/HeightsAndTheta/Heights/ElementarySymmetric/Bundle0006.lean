module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwinEqCech
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0014

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PGradedCech
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Swarm

theorem GradedCech.proof : GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.GradedCech.Statement :=
  GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.GradedCech.proof

end GroundTheory.Heights₂.Heights.Swarm
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StRestrLenEuler
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def RestrLenEuler.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (qq : Ideal (Poly k N)), (∀ f ∈ qq, ∀ d : ℕ, homogeneousComponent d f ∈ qq) →
    primeOf (S := k) x ≤ qq → ∀ (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ),
      ∀ᶠ c : ℤ in atTop,
        restrLen qq (((twistSys k x 0).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c)) =
          pieceChar k qq 0 L n c

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StSubsetDiffConst
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

def subsetDiff (n : ℕ) (f : (Fin (n + 1) → ℕ) → ℤ → ℚ) (m : ℕ) (c : ℤ) : ℚ :=
  ∑ T : Finset (Fin n), (-1 : ℚ) ^ (n - T.card) *
    f (Fin.snoc (α := fun _ => ℕ) (fun i => if i ∈ T then 1 else 0) m) c

def SubsetDiffConst.Statement : Prop :=
  ∀ (n : ℕ) (f : (Fin (n + 1) → ℕ) → ℤ → ℚ), IsNumPolyLT (n + 1) (n + 1) f →
    (∀ (m m' : ℕ) (c c' : ℤ), subsetDiff n f m c = subsetDiff n f m' c') ∧
      (IsNumPolyLT (n + 1) n f → ∀ (m : ℕ) (c : ℤ), subsetDiff n f m c = 0)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

