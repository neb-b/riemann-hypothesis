module

public import Formalism.WachLatticeTwists.CharacterSplitJumps.Statement

@[expose] public section

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JT

open Formalism.NG

theorem mem_annih {O Cw Cs P : Type*} [CommRing O] [AddCommGroup Cw] [Module O Cw]
    [AddCommGroup Cs] [Module O Cs] [AddCommGroup P] [Module O P] (pr : Cw →ₗ[O] Cs →ₗ[O] P)
    (U : Submodule O Cs) (x : Cw) : x ∈ annih pr U ↔ ∀ t ∈ U, pr x t = 0 := by
  simp only [annih, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]

end Formalism.RepresentationBoundsCohomology.JT
