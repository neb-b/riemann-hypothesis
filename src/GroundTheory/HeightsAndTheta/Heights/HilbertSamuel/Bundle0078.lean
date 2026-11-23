module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0068
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0070
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0069
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecondVeroneseParts

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullFormsGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def PullFormsGeneric.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d →
      aeval (fun j => aeval y (L j)) F = 0 → F = 0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullGradedAlgebraic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def PullGradedAlgebraic.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (d₀ : K → ℕ),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ k, 1 ≤ e k) → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e) →
    (∀ (d : K → ℕ) (g : MvPolynomial (Σ k, ι k) ℚ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d → (∀ k, d₀ k ≤ d k) →
      ∃ a : Fin (D + 1) → MvPolynomial (Σ k, ι k) ℚ, (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (a j) (d - e)) ∧
        aeval y g = ∑ j, aeval y (a j) * aeval y (L j)) →
    ∀ p q : Σ k, ι k, p.1 = q.1 → IsAlgebraic (pullField y L) (y p / y q)

namespace ProjLine

end ProjLine

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullSectionIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def PullSectionIntegral.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (q : ℕ),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
      ∀ τ : ℕ, ∀ s ∈ chartLatNm y (fun k => ((q * e k : ℕ) : ℤ)) τ, ∀ j : Fin (D + 1), aeval y (L j) ≠ 0 →
        s / aeval y (L j) ^ (q * τ) ∈
          integralClosure (Algebra.adjoin ℚ (Set.range fun i => aeval y (L i) / aeval y (L j))) Ω

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionNormSqExtension
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionNormSqExtension.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (m N : ℕ) (v : Fin N → Ω),
    IsSmoothHerm A → IsConjInvariantH A →
    (∀ j, v j ∈ chartLat y A.a m) → KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v →
    ∃ S : ((Σ k, ι k) → ℂ) → ℝ,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S {x | ∀ k, ∃ i, x ⟨k, i⟩ ≠ 0} ∧
      (∀ x : (Σ k, ι k) → ℂ, (∀ k, ∃ i, x ⟨k, i⟩ ≠ 0) → 0 < S x) ∧
      (∀ (c : K → ℂ) (x : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → S (fun p => c p.1 * x p) = S x) ∧
      (∀ x : (Σ k, ι k) → ℂ, S (fun p => (starRingEnd ℂ) (x p)) = S x) ∧
      (∀ x ∈ mcPts (mCoordIdeal y), S x = ∑ j, secNormAt y A m (v j) x ^ 2) ∧
      ∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ w : (Σ k, addIdx ι N k) → ℂ,
        IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal (addBlock y v)) z w →
        leviForm (fun z' : (Σ k, addIdx ι N k) → ℂ =>
            Real.log (∑ j, ‖z' ⟨none, j⟩‖ ^ 2) / 2 - Real.log (S (basePart₂ z')) / 2) z w =
          (m : ℝ) * leviForm (fun x => Real.log (A.h x)) (basePart₂ z) (basePart₂ w)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockHorizDiv
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def TwoBlockHorizDiv.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (B : Matrix (Ix κ) (Ix κ) ℚ) (c : κ)
    (l : Ix κ → ℤ),
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j →
    ∀ W : Ideal (MRing (FinTwoTypeFamily κ)), IsHorizontal W →
      (W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockNum l) ↔
          W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockDen c)) ∧
        (W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockNum l) →
          multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockNum l}) W =
            multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c}) W)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockModuleCycle
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def TwoBlockModuleCycle.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (c : κ) (l : Ix κ → ℤ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j →
    ∀ e : Fin D → Fin 2 → ℤ,
      ∑ᶠ W ∈ topComps (twoBlockMInner x (matAct B x) l) D,
          ((multAt (twoBlockMInner x (matAct B x) l) W : ℝ) - multAt (twoBlockMOuter x (matAct B x) c) W) *
            Real.log (charOf W) * (geoNum D W e : ℝ) =
        twoBlockVert x (matAct B x) c l e

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockModuleFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def TwoBlockModuleFinite.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (c : κ) (l : Ix κ → ℤ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j →
    IsMultiHomogIdeal (twoBlockMOuter x (matAct B x) c) ∧ IsMultiHomogIdeal (twoBlockMInner x (matAct B x) l) ∧
      twoBlockMInner x (matAct B x) l ≤ twoBlockMOuter x (matAct B x) c ∧
      (∃ N : ℕ, 0 < N ∧ ∀ f ∈ twoBlockMOuter x (matAct B x) c,
        (N : MRing (FinTwoTypeFamily κ)) * f ∈ twoBlockMInner x (matAct B x) l) ∧
      ∀ W : Ideal (MRing (FinTwoTypeFamily κ)), W.IsPrime → twoBlockMInner x (matAct B x) l ≤ W → ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W →
        ringKrullDim (MRing (FinTwoTypeFamily κ) ⧸ W) ≤ ((D + Fintype.card (Fin 2) : ℕ) : WithBot ℕ∞)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockPieceIndex
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def TwoBlockPieceIndex.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (c : κ) (l : Ix κ → ℤ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j →
    ∀ a b : ℕ, twoBlockStep x (matAct B x) a b =
      Real.log (modPieceCard (twoBlockMOuter x (matAct B x) c) (twoBlockMInner x (matAct B x) l) ![a + 1, b + 1])

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsVeroneseGraph
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace Veronese

def forms (D : ℕ) : Ix (Idx D) → MRing (GlobalTheory (Fin (D + 1))) :=
  fun q => X ⟨(), q.2.1.1⟩ * X ⟨(), q.2.1.2⟩

end Veronese

def VeroneseGraphImage.Statement : Prop :=
  ∀ D : ℕ, imageZ (inrV (ι := GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D)))
      (graphIdeal ⊥ (Veronese.forms D)) = coordIdeal ℤ (Veronese.x D)

def VeroneseGraphDeg.Statement : Prop :=
  ∀ D : ℕ, 1 ≤ D →
    ∃ (G : GenFibre (inrV (ι := GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D))) (graphIdeal ⊥ (Veronese.forms D)))
      (J : IFamily G.Φ (fibreIdx (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D))) (Sum.inr : Unit → Unit ⊕ Unit))),
      IsFieldIntersection J ∧ J (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) 0 Fin.elim0 = 1

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

