module

public import Development.WeilBound.ThetaLifts.TowerModels.TowerCodimensionTwoOf
public import Development.WeilBound.ThetaLifts.TowerModels.Bundle0005
public import Development.WeilBound.ThetaLifts.TowerModels.PlaneSkew
public import Development.WeilBound.ThetaLifts.TowerModels.Bundle0006
public import Development.WeilBound.ThetaLifts.TowerModels.Bundle0003
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.Bundle0003
public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

noncomputable section

namespace PositivityTheory.ThKG.Tow

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem planeEx : PlaneEx := ⟨planeHerm, planeSkew⟩

end PositivityTheory.ThKG.Tow

end
