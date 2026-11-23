module

public import Formalism.PeriodIntegrals.Bundle0026
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HasseJacobsonPowers.SfrMulMemJHfr
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0036
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bundle0002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.LocIdx
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.Bundle0004

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HasseJidPow
section
theorem hasse_jid_power : PI.HasseJidPow := PI.HJP.hasseJidPow_of hasse_presentation
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MassDataKppVol
section
theorem kpp_volume_at_instance : ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X)) (A : Formalism.L2.SG.TypedSets.AnIn),
    Formalism.L2.SG.TypedSets.KppVolAt X hb hK FdN FdN' u u' X0 L A :=
  PI.MassDataKppVolLemmas.massDataKppVol_of PI.MassDataKppVolLemmas.global_index_every_setting PI.MassDataKppVolLemmas.locIdxAll
    PI.MassDataKppVolLemmas.locPosAll (PI.MassDataKppVolLemmas.idxProdAll_of PI.MassDataKppVolLemmas.single_component_surjective)
end

