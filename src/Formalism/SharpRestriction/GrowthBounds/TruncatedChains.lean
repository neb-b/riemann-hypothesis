module

public import Formalism.SharpRestriction.GrowthBounds.Bundle0003
public import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.Bundle0002
public import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.ProjectorFactorMemWeightSpace
public import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.Bundle0003
public import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.CnNODrop

@[expose] public section

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

theorem restYB (D : Formalism.BasicNotions.D7) : RestYB :=
  restYB_of (ybat_base D restKill restPair (restPair'_of restPair)) ybat_symm

theorem raising_operators_kill_image (D : Formalism.BasicNotions.D7) : SimpleRaisingKillsExtremalProjector :=
  raising_kill_of_interface restConn restComm (restYB D) restKill

theorem extremal_projector_statement (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.adm5 D := sizes_bound_of_log_estimates D (raising_operators_kill_image D)

end Formalism.MainNotions.G.ExtremalProjector
