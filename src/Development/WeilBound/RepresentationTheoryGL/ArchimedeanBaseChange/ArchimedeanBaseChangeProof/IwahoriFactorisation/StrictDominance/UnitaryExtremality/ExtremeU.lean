module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0488
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryCharacterFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0474
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitarySwapReduction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryInverseReduction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0210
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0473
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0135
public import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0289

@[expose] public section

noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun

namespace PositivityTheory.SphericalProduct

theorem extremeU : ExtremeU := by
  intro L _ _ _ ϖ σ q n V _ _ ρ α hU hA hI hS
  obtain ⟨y, hy, hy1⟩ := _root_.GlobalTheory.CompanionTheory.JacSph.jacNeU L ϖ σ q n V ρ α hU hA hI hS
  obtain ⟨y', ξ, hy', heig, h1⟩ := _root_.GlobalTheory.CompanionTheory.EigTorus.eigU_complete L ϖ σ q n V ρ hU hA y hy hy1
  obtain ⟨lam, hlam0, hne, hlam⟩ := _root_.GlobalTheory.CompanionTheory.EqForm.eqFormU L ϖ σ q n V ρ hU hA ξ y' hy' heig h1
  obtain ⟨β, hβ⟩ := _root_.GlobalTheory.CompanionTheory.TorusChar.charU L ϖ σ q n V ρ hU ξ y' hy' heig h1
  obtain ⟨hW, f, hf, hfe⟩ := _root_.GlobalTheory.CompanionTheory.FrobRec.frobU L ϖ σ q n V ρ α hU hA hI hS β lam hlam0 hne
    (fun t ht v => by rw [← hβ t ht]; exact hlam t ht v)
  exact _root_.GlobalTheory.CompanionTheory.ChamberInd.chamberU _root_.GlobalTheory.CompanionTheory.SwapRoot.swapStepU _root_.GlobalTheory.CompanionTheory.InvStep.invStepU L ϖ σ q n hU V ρ hA hI hS.1 α β hW f hf hfe

end PositivityTheory.SphericalProduct

end
