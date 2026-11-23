module

public import Development.WeilBound.ThetaLifts.LeviDeterminants.Bundle0009

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical

namespace PositivityTheory.ThKF0

theorem thetaBasic : GlobalTheory.ThK.ThetaBasic := thetaBasic_of weil_rep_rapid_decay_height

end PositivityTheory.ThKF0
