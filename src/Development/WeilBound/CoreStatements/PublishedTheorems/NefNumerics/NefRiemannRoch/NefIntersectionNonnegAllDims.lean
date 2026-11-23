module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1150
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.AmplePlusNefInductionStatement
public import Development.WeilBound.CoreStatements.PublishedTheorems.NefNumerics.NefRiemannRoch.Bundle0002

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

theorem GlobalTheory.kleiman_interNum_nonneg : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ d : ℕ, (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ P : Fin d → LB X, (∀ i, IsNef k (P i)) → 0 ≤ interNum k E P) := by
  intro k _ _ X _ hproj d
  have amp : ∀ n : ℕ, ∀ (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (strHom k (X := Y)) →
      topologicalKrullDim Y ≤ (n : ℕ) → ∀ A N : LB Y, IsAmpleLB A → IsNef k N → IsAmpleLB (tens A N) := by
    intro n
    induction n with
    | zero =>
      intro Y _ hpY hdim A N hA hN
      haveI := isNoetherian_of_isProjOver hpY
      have hT : (tens A N).IsLB := isLB_tens hA.isLB hN.isLB
      refine isAmpleLB_of_subsingleton_coh_one Y _ hT (fun F hF => ⟨1, le_rfl, ?_⟩)
      haveI : SheafOfModules.IsQuasicoherent F := hF.isQuasicoherent
      haveI : SheafOfModules.IsQuasicoherent (twist F (lbPow (tens A N) 1)) :=
        isQuasicoherent_twist (isLB_lbPow hT 1)
      exact hA.subsingleton_coh_of_dim_lt _ (lt_of_le_of_lt hdim (by norm_num))
    | succ n ihn => exact isAmpleLB_tens_of_isNef_succ k n ihn
  exact KleimanDim.interNum_nonneg_of_ample_tens_nef k d (amp d) X hproj
