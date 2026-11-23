module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.LocalMassTypeOfParts
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.KUnip1Of
public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.Assembly

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LocMassTyp
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain

theorem locMassTyp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) {r : ℕ} (g : ℕ) (P P' : Frame E n r) (Λ : Set (Fin n → E)) : Formalism.L2.SG.LocVol.TypLocAt σ J ψ v g P P' Λ :=
  PI.LocMassTypW.local_mass_type_of_parts PI.LocMassTypR.right_invariant_compact
    (PI.LocMassTypW.kUnip1_of PI.LocMassTypS.split_reduction) σ J ψ v g P P' Λ
end

-- bundled from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MassDataLevelS
section
theorem level_s_at_instance : ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X)) (A : Formalism.L2.SG.TypedSets.AnIn), Formalism.L2.SG.TypedSets.InLevelSAt X hb hK FdN FdN' u u' X0 L A :=
  MassDataLevelSSteps.inLevelSAt_holds
end

