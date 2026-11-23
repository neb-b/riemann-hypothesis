module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NilpotentVolumeOne.LinearIndependentFrameWithNormal
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.StepGramH

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.StepFrameStd
section
noncomputable section

namespace MassDataVolumesW

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub

def StepFrameStd : Prop := ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word),
  ∃ T : X.B.I.F, (frameOf X u).IsStd X.B.I.cm.sig X.B.I.J T

theorem stepGramH_of (h : StepFrameStd) : StepGramH := by
  unfold StepGramH
  intro D X u hT1
  obtain ⟨T, hT⟩ := h X u
  exact PI.VolNzeroOne.W.det_gram_tupH_ne_zero X.B.I.cm.sig X.B.I.J (frameOf X u) T hT hT1

end MassDataVolumesW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.StepSize
section
noncomputable section

namespace MassDataVolumesW

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem stepCM : StepCM := by
  intro D X
  exact ⟨X.B.I.cm.totReal, X.B.I.cm.cmUnram.1, X.B.I.cm.deg2, fun τ x => X.B.I.cm.cmUnram.2.1 τ x⟩

theorem stepHerm : StepHerm := by
  intro D X
  exact ⟨fun i j => congrFun (congrFun X.B.I.J_herm i) j, X.B.I.J_det⟩

end MassDataVolumesW
end
end

