module

public import Mathlib
public import Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjArchOfInfEmbArchPi
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0406
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SingleMulSingle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0689
public import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitarySiegelDomainExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0762
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0626

@[expose] public section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.SiegelRed

theorem siegelCore : SiegelCore := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW
  obtain ⟨K₁, h₁, c₁, i₁, g₁⟩ := GlobalTheory.CompanionTheory.SiegelArch.exists_kInf F E σ h n J hJ r X Y hW
  obtain ⟨K₂, h₂, c₂, i₂, g₂⟩ := _root_.GlobalTheory.CompanionTheory.KFin.exists_compact_iwasawa_good F E σ h n J hJ r X Y hW
  obtain ⟨K, hK, hI, hG⟩ := GlobalTheory.CompanionTheory.SiegelAssemble.exists_compact_iwasawa F E σ h n J hJ r X Y hW K₁ K₂ h₁ h₂ c₁ c₂
    i₁ i₂ g₁ g₂
  obtain ⟨Ω, c, hΩ, hΩP, hc, hcov⟩ := _root_.GlobalTheory.CompanionTheory.RedCov.cov_main F E σ h n J hJ r X Y hW K hK hI hG
  exact ⟨K, Ω, c, hK, hΩ, hΩP, hc, hI, hG, hcov,
    GlobalTheory.CompanionTheory.SiegelConj.conj_compact F E σ h n J hJ r X Y hW Ω c hΩ hΩP hc,
    GlobalTheory.T.cusp_form_siegel_bound F E σ h n J hJ r X Y hW K Ω c hK hΩ hΩP hc,
    _root_.GlobalTheory.CompanionTheory.RapidDecay.rapid_decrease F E σ h n J hJ r X Y hW K Ω c hK hΩ hΩP hc⟩

theorem siegelSetUnitary : GlobalTheory.Published.SiegelSetUnitary :=
  siegel_of_core siegelCore

end GlobalTheory.CompanionTheory.SiegelRed
