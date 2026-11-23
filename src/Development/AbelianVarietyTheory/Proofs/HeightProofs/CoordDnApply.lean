module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace GlobalTheory.DualPairCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}
section Gen
variable {R : Type} [CommRing R] {a b : ℕ}

end Gen

open GlobalTheory.IndefiniteRowSideFullHecke

instance topRing (D : D7) : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) _

end GlobalTheory.DualPairCompare

end
