module

public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpNZCut
public import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle0005
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.FramesTurn
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0005
public import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates

@[expose] public section

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.BetaCut
section
open MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.S.Pv.BetaCut

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

def coefM {k r : ℕ} {H Wp Wq : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (v v' : H) (ξ : Wp) (ξ' : Wq)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Wq →L[ℂ] Wp :=
  (innerSL ℂ ξ').smulRight (⟪v, σ g v'⟫_ℂ • ξ)

def CoefInCC : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (h : ℝ) (m : ℕ) (A : ℝ),
    IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ → GapAtLeast ε lam h → ReciprocityTheory.ChartRestriction.DS.thrStar ε + m < h → A ≤ m →
    ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ v' ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
      (ξ : Wp) (ξ' : Wq), Formalism.FourierDecayAlt.B.InCC (k := k) (r := r) A 5 (coefM σ v v' ξ ξ')

def BetaInfCoefNZ : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq)
    (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (h : ℝ),
    IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ → GapAtLeast ε lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h →
    ∀ (v v' : H) (l : H → Wp) (l' : H → Wq) (ξ : Wp) (ξ' : Wq),
      v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ → v' ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ →
      Formalism.FourierDecayAlt.ThreeDimData.be D.z Formalism.QuantumDeterminants.cStd D.π σ D.μW D.μN v v = (innerSL ℂ (l v)).smulRight (l v) →
      Formalism.FourierDecayAlt.ThreeDimData.be D.z' Formalism.QuantumDeterminants.cStd D.π' σ D.μW' D.μN v' v' = (innerSL ℂ (l' v')).smulRight (l' v') →
      ⟪l v, ξ⟫_ℂ ≠ 0 → ⟪ξ', l' v'⟫_ℂ ≠ 0 →
      Formalism.FourierDecayAlt.B.betaInf D (coefM σ v v' ξ ξ') (coefM σ v v' ξ ξ') ≠ 0

end Formalism.MainNotions.S.Pv.BetaCut
end
end

-- bundled from Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.FramesSh
section
set_option linter.unusedVariables false

noncomputable section

namespace Formalism.MainNotions.S.Pv.Frames

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.MainNotions.S.Bridge Formalism.BasicNotions

variable {k r : ℕ}

theorem orbSqO_le_turn (L : LocBessel k r) (ka : ℝ) (hka : 0 < ka) (hc : L.c = ((2 * ka : ℝ) : ℂ))
    (f : Mx k r → (L.Wq →L[ℂ] L.Wp)) (p : Point ℂ (r + 1)) :
    orbSqO L f p ≤ orbSq (turnL L ka) (turnF L ka f) (turnPt p) := by
  unfold orbSqO orbSq
  refine iSup_le fun g => iSup_le fun μR => iSup_le fun ν => iSup_le fun hg => ?_
  rw [← OrbInt_turn L ka hc f g ν]
  exact le_iSup_of_le (tTi k r * g * tT k r) (le_iSup_of_le (μR.map (cA k r))
    (le_iSup_of_le (ν.map (thP k r)) (le_iSup_of_le
      ⟨isPtRep_turn L ka hg.1, isRelStab_turn L ka hc hg.2.1, isRootMeas_turn L ka hka hc hg.2.2.1,
        isOrbQuot_turn L ka hg.2.2.2⟩ le_rfl)))

section OneRec

variable (D : D7)

end OneRec

end Formalism.MainNotions.S.Pv.Frames

end
end

