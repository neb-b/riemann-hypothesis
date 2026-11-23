module

public import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemOfToL2MemIrreducible
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.FinitePartOfMeet
section
namespace PositivityTheory.jumpWindows

theorem finite_part_of_meet : Meet → CuspidalIrreducibleSubrep :=
  GlobalTheory.CompanionTheory.FinitePart.g14_of_meet

end PositivityTheory.jumpWindows
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.PsiDeterminantFlag
section
open GlobalTheory.CuspRep

namespace PositivityTheory.jumpWindows

theorem mean_convergence_of : Smo → GlobalTheory.Published.CuspidalMultiplicityOne := by
  intro h E _ _ _ a π π' e
  refine congrArg CuspSub.V (h E a π π' ?_)
  filter_upwards [_root_.GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep CuspFormAutomorphicBounds.automorphicFormsFiniteGL E a π] with w hw
  obtain ⟨B, hB⟩ := hw
  exact ⟨B, hB, e ▸ (show (CG.mk π).HasSat w B from hB)⟩

end PositivityTheory.jumpWindows
end

