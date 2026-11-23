module

public import Formalism.WachLatticeTwists.CharacterSplitJumps.Statement
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs

@[expose] public section

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.JT
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsCycOn)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology

def lcH1 {O Γ M : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [AddCommGroup M] [Module O M]
    (ρ : Representation O Γ M) : Submodule O (H1z ρ) :=
  Submodule.map (Submodule.mkQ _)
    { carrier := {c : coZ1s ρ | IsLocallyConstant (c : Γ → M)}
      add_mem' := fun {_ _} ha hb => IsLocallyConstant.add ha hb
      zero_mem' := IsLocallyConstant.const 0
      smul_mem' := fun c _ hx => IsLocallyConstant.comp hx (fun m => c • m) }

end Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology
