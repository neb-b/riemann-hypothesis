module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraEstimateForRegularity
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionFactsHold
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0299
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0217
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0324
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelUniqueness
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0228
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.AsmKerOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveSolutionExistence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelExistence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0327

@[expose] public section

namespace PositivityTheory.RgBcC

theorem wave_existence_speed_multiplicity : WaveEx ∧ WaveSpeed ∧ KerEx ∧ MultAlg := by
  have hL : LgFacts := _root_.GlobalTheory.CompanionTheory.LengthGL.lgFacts
  have hU : Unimod := _root_.GlobalTheory.CompanionTheory.GLUnimod.unimod
  have hS : SobG := _root_.GlobalTheory.CompanionTheory.SobGL.sobG
  have hR : RCalc := _root_.GlobalTheory.CompanionTheory.RCalc.rcalc
  have hKU : KerUniq := _root_.GlobalTheory.CompanionTheory.KerUniq.main
  have hA : AlgEst := _root_.GlobalTheory.CompanionTheory.SkewWords.algEst
  have hsp : WaveSpeed := _root_.GlobalTheory.CompanionTheory.WaveSpd.asmSpeed hL hU hR
  have hcpt : WaveCpt := Fc.asmCpt hL hU hR hS
  have hex : WaveEx := _root_.GlobalTheory.CompanionTheory.WaveAll.asmEx hL hR hsp hcpt
  have hk1 : KerOne := Fc.asmKerOne hL hU hR hS hA hsp
  exact ⟨hex, hsp, _root_.GlobalTheory.CompanionTheory.WaveKer.asmKerEx hL hR hsp hex hKU hk1,
    GlobalTheory.CompanionTheory.WaveMult.asmMult_main hL hU hR hsp hex hKU hk1⟩

end PositivityTheory.RgBcC
