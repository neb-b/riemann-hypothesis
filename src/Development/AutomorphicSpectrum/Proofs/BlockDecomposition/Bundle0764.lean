module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitary
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0320
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0059
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0583
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0593
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0592
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0578
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0763
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0709
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0034

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cocompactness
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU PositivityTheory.Rg.Mass

namespace GlobalTheory.CompanionTheory.MassCocompact

theorem coCpt : CoCpt := by
  intro F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hCM hJ hA _ _ hμ h𝓕 _ _
  have hW : GlobalTheory.SiegelSet.IsWittFrame σ J (0 : Matrix (Fin 2) (Fin 0) E) 0 :=
    ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _, fun z _ _ hz => hA z hz⟩
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.SiegelSet.Model.compact_quotient GlobalTheory.CompanionTheory.SiegelRed.siegelSetUnitary hCM hJ hW
  refine ⟨⟨C, hC, fun h => ?_⟩, ?_, ?_⟩
  · obtain ⟨γ, hγ, c, hc, e⟩ := hcov h
    exact ⟨⟨γ, hγ⟩, c, hc, e⟩
  · exact (GlobalTheory.SiegelWeilConvCompare.measure_fundamentalDomain_pos F E σ 2 J μ hμ 𝓕 h𝓕).ne'
  · exact (((GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup F E σ hCM 2 J hJ).2 μ hμ).2 𝓕 h𝓕).ne

end GlobalTheory.CompanionTheory.MassCocompact

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModularStab
section
noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.QKAvg

theorem modular_stab (D : D7) (B W : HSp D) (t : ℕ) (d : HypDec B W t) [LocallyCompactSpace (GlobalTheory.RegSW.stab d)]
    (q : GlobalTheory.RegSW.stab d) :
    Measure.modularCharacterFun q = GlobalTheory.RegSW.absDet d q ^ (W.rank + t) := by
  haveI : LocallyCompactSpace (radN d) := (_root_.GlobalTheory.CompanionTheory.QKAvg.isClosed_radN D B W t d).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace (levM d) := (_root_.GlobalTheory.CompanionTheory.QKAvg.isClosed_levM D B W t d).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (GlobalTheory.RegSW.stab d) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨νN, h1, h2, h3⟩ := GlobalTheory.T.exists_haar_unipotent_radical_conj_scaling D B W t d
  obtain ⟨νM, h4, h5⟩ := _root_.GlobalTheory.CompanionTheory.QKAvg.exists_levM_haar D B W t d
  exact _root_.GlobalTheory.CompanionTheory.ModChar.modularCharacterFun_semidirect (GlobalTheory.RegSW.stab d) (radN d) (levM d) (_root_.GlobalTheory.CompanionTheory.QKAvg.isClosed_radN D B W t d) (_root_.GlobalTheory.CompanionTheory.QKAvg.isClosed_levM D B W t d)
    (exists_radN_mul_levM d) (_root_.GlobalTheory.CompanionTheory.QKAvg.radN_disj_levM D B W t d)
    νN νM h1 h2 h4 h5 ((powMonoidHom (W.rank + t) : ℝ≥0 →* ℝ≥0).comp (GlobalTheory.RegSW.absDet d))
    (fun n hn => by simp [_root_.GlobalTheory.CompanionTheory.QKAvg.absDet_radN D B W t d n hn]) (fun m hm => by simpa using h3 m hm) q

theorem qk : PositivityTheory.Rg.Rsw.L.QK := by
  intro D t B W d l hl νK hνK s hs hlaw g
  obtain ⟨hIw, hK⟩ := GlobalTheory.RegSch.FirstTermCompare.hasIw_of_good d hl
  haveI : LocallyCompactSpace (GlobalTheory.RegSW.stab d) :=
    (GlobalTheory.RegSW.isClosed_stab d).isClosedEmbedding_subtypeVal.locallyCompactSpace
  let μ : Measure (GA D B) := Measure.haar
  haveI : μ.IsMulRightInvariant := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D B μ inferInstance
  refine _root_.GlobalTheory.CompanionTheory.QKAvg.lintegral_mul_right_of_modular_law (GA D B) μ (GlobalTheory.RegSW.stab d) l.K (GlobalTheory.RegSW.isClosed_stab d) hK
    (fun g => ?_) ((powMonoidHom (W.rank + t) : ℝ≥0 →* ℝ≥0).comp (GlobalTheory.RegSW.absDet d))
    (show Continuous fun q => GlobalTheory.RegSW.absDet d q ^ (W.rank + t) from (GlobalTheory.RegSW.continuous_absDet d).pow _)
    (fun q => ?_) νK hνK s hs (fun q h => ?_) g
  · obtain ⟨q, k, hk, e⟩ := hIw g
    exact ⟨q, q.2, k, hk, e⟩
  · simpa using modular_stab D B W t d q
  · simpa using hlaw q h

end GlobalTheory.CompanionTheory.QKAvg
end
end

