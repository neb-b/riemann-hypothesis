module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0296
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0290
public import CompanionTheory.AutomorphicTheory.CompactTopologicalForms.JacobiFieldSquareIntegrable
public import CompanionTheory.AutomorphicTheory.DiscreteGroupWaves.NFTopFormCpt

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP.CompactFormNormalFormDomination

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

theorem blockGrowthBound_apx_cutF (hA : P5.ThmPActualCpt) {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (nn χ : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (Y : Finset ℝ) (K N : ℕ) (Cb : ℝ) (hCb : KB.InDDplus2 P p.l0 p.T.base Cb p.Θ) (hχ : C6.IsCut0 χ)
    (hF : B.CkOn ⊤ (B.GV P.k P.r) F) (hnn : ∀ y, 0 < nn y) :
    ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn (apx (D.cutF p.T.base χ F ε) n) Y K N := fun _ hε n =>
  block_growth_bound_of_compact_coefCpt hA p nn _ Y K N Cb hCb (cptCoef_apx P p.T.base hχ hF hε n) hnn



end

end Formalism.FourierDecayAlt.P.CutBP.CompactFormNormalFormDomination

namespace Formalism.FourierDecayAlt.P.CutBPEq.CompactFormNormalFormDomination

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBP.CompactFormNormalFormDomination MeasureTheory
open scoped ENNReal

noncomputable section


end

end Formalism.FourierDecayAlt.P.CutBPEq.CompactFormNormalFormDomination
