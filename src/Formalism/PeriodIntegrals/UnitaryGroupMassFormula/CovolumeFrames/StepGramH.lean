module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst

@[expose] public section

noncomputable section

namespace MassDataVolumesW

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.L2.SG.Volumes Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub

def StepCM : Prop := ∀ {D : D7} (X : HidaSetting D), IsCMExt X.B.I.F X.B.I.E X.B.I.cm.sig

def StepHerm : Prop := ∀ {D : D7} (X : HidaSetting D), IsHermND X.B.I.cm.sig X.B.I.J

def StepGramH : Prop := ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word),
  (∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u)) j i) =
    gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u)) i j) →
  (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u))).det ≠ 0

end MassDataVolumesW
