module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0081
public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Formalism.SharpRestriction.InertJacobiLevels.HostFam
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
public import Development.AbelianVarietyTheory.Definitions.Foundations.AuxiliaryFrameNormalizedSpaces
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleRanksRankComplement
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0031
public import Formalism.LocalRingCardinality.Bundle0001
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
public import Formalism.LocalRingCardinality.DataHost
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.NonemptyFieldAxiomsCyclicPow
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
public import Development.AutomorphicArithmetic.WeightCongruences.Bundle0001

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.PreXModel

open Formalism.BasicNotions NumberField IsDedekindDomain

theorem embLL_tauLL (B : Base) (τ : Tau B.R) : B.embLL.comp (B.tauLL τ) = B.host.emb τ := by
  unfold Base.tauLL Host.emb
  rw [← RingHom.comp_assoc, B.embE_φ₀]

end GlobalTheory.Mem.PreXModel

end
