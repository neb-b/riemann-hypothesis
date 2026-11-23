module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0031

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.GeneratedCechTieSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver GeneratedV)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2 (IsGenerated baseDeg pnPt isModelWithBase_pnPt)

def GeneratedCechTie.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (β : K → ℤ),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → IsGenerated S y β → GeneratedV S (mIdealOver S y) β

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSnapperQuotIsoX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w v'

theorem SnapperQuotIso.proof : SnapperQuotIso.Statement.{u, v, w, v'} := by
  intro k _ Ω _ _ N x E _ _ _ _ E' _ _ _ _ F₁ F₂ G₁ G₂ e
  unfold eulerCharQuot
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  exact (Cech.equivH e.equiv e.comm i).finrank_eq

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StInterNumCut
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w


open Classical in
def InterNumCut.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (pp : Ideal (Poly k N)) (L : Fin n → LineBundle k x) (Lc : LineBundle k x) (s : Ω),
      IsSubvar x pp (n + 1) → s ∈ Lc.secs → (∃ I, s ∉ (Lc.twist (idealSys x pp)).sub I) →
      interNum pp (Fin.snoc (α := fun _ => SubSystem k x Ω) (fun i => (L i).toSubSystem)
          Lc.toSubSystem) =
        ∑ᶠ qq : Ideal (Poly k N),
          if h : qq ∈ (pp ⊔ zeroIdeal Lc.toSubSystem s).minimalPrimes ∧ IsSubvar x qq n then
            haveI : qq.IsPrime := h.1.1.1
            ((cutMult (pp ⊔ zeroIdeal Lc.toSubSystem s) qq).toNat : ℤ) *
              interNum qq (fun i => (L i).toSubSystem)
          else 0

end

end GroundTheory.Heights₂.Heights.Kleiman
end

