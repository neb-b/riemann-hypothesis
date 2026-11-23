module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle0001
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0020
public import Formalism.PeriodIntegrals.Bundle0019
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Formalism.PeriodIntegrals.Bundle0009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.StepBruhat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.LintegralMulAvgComm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.Bruhat
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.Bundle0003

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.BridgeKHolds
section
noncomputable section

open Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets
open Matrix

namespace MassDataMassesW.NBr

theorem incAf_finHA {D : Formalism.BasicNotions.D7} (X : HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
    (x : X.B.I.Gf) :
    Formalism.L2.SG.Sub.incAf X.B.I.cm.sig X.B.I.J (finHA X hb x) =
      Formalism.UG.bc (Formalism.L2.SG.AdBridge.prF X.B.I)
        (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) X.B.I.cm.sig X.B.I.J
          (Formalism.L2.SG.AdBridge.toHA X.B.I hb (1, x))) := rfl

theorem bridgeK_holds : BridgeK := by
  intro D X hb x
  have hbr' : X.B.I.fmat x = _ := (hb.choose_spec (1, x)).2
  have hK : x ∈ X.B.I.Kset ↔
      Formalism.L2.SG.AdBridge.toHA X.B.I hb (1, x) ∈ Formalism.L2.SG.AdBridge.KfHA X.B.I := by
    refine Iff.trans ?_ (adelic_compact_finite_places X.B.I (Formalism.L2.SG.AdBridge.toHA X.B.I hb (1, x)))
    show (∀ y, y ∈ X.B.I.Lf ↔ X.B.I.fmat x *ᵥ y ∈ X.B.I.Lf) ↔ _
    rw [hbr']
    rfl
  refine hK.trans ?_
  simp only [KX, Formalism.L2.SG.Sub.Kf, Subgroup.mem_iInf, Subgroup.mem_comap, MonoidHom.comp_apply,
    incAf_finHA]
  rfl

end MassDataMassesW.NBr
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.IsHermNDOfSetting
section
noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets
open scoped TensorProduct

namespace MassDataMassesW

theorem isCMExt_of_cmData {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) : IsCMExt F E hc.sig :=
  ⟨hc.totReal, hc.cmUnram.1, hc.deg2, fun τ x => hc.cmUnram.2.1 τ x⟩

theorem isHermND_of_setting {D : D7} (X : HidaSetting D) : IsHermND X.B.I.cm.sig X.B.I.J :=
  ⟨fun i j => congrFun (congrFun X.B.I.J_herm i) j, X.B.I.J_det⟩

theorem discHF_setting {D : D7} (X : HidaSetting D) : DiscreteTopology (HFinIn (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
  ((PI.VolSemiDirect.W.discHA_of PI.VolSemiDirect.W.Lc.tensor_adele_topology_holds) X.B.I.F X.B.I.E X.B.I.cm.sig
    (isCMExt_of_cmData X.B.I.cm) X.B.I.n X.B.I.J (isHermND_of_setting X)).2

theorem fdExistsH_holds : FDExistsH := by
  intro D X u
  haveI : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  haveI i1 : SecondCountableTopology (HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J) := inferInstance
  haveI i2 := discHF_setting X
  haveI i3 : SecondCountableTopology (Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  let f : ratOf (K := Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) →
      HFinIn (AF X.B.I.F) X.B.I.cm.sig X.B.I.J := fun x =>
    ⟨((x : Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J),
      Subgroup.mem_comap.1 x.2⟩
  have hf : Continuous f :=
    ((continuous_subtype_val.comp continuous_subtype_val :
      Continuous fun x : ratOf (K := Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) =>
        ((x : Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J))).subtype_mk _
  have hinj : Function.Injective f := by
    intro x y hxy
    have e := congrArg Subtype.val hxy
    exact Subtype.ext (Subtype.ext e)
  haveI : DiscreteTopology (ratOf (K := Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) :=
    DiscreteTopology.of_continuous_injective hf hinj
  obtain ⟨𝓕, -, h𝓕⟩ := PI.VolSemiDirect.W.exists_fd (G := Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))
    (ratOf (K := Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)))
  exact ⟨𝓕, h𝓕 _⟩

end MassDataMassesW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.MassDataMassesOf
section
open Formalism.L2.SG.TypedSets

namespace MassDataMassesW

theorem massDataMasses_of (hM : MassAll) (hN : NVolAll) :
    ∀ {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I)
      (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf) (u u' : D.what₂.Word)
      (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E) (L : Formalism.L2.SG.TypedSets.LocIn (Formalism.L2.SG.TypedSets.TypX X))
      (A : Formalism.L2.SG.TypedSets.AnIn), Formalism.L2.SG.TypedSets.InMassesAt X hb hK FdN FdN' u u' X0 L A := by
  intro D X hb hK FdN FdN' u u' X0 L A hX
  obtain ⟨hT, hL, hF, hF'⟩ := hX
  exact ⟨hM X hb u hT, hN X hb hK u FdN hT hL hF, hM X hb u' hT, hN X hb hK u' FdN' hT hL hF'⟩

end MassDataMassesW
end

