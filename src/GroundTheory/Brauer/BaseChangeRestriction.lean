module

public import Mathlib
public import GroundTheory.Brauer.SkolemNoether
public import GroundTheory.Brauer.IsBrauerEquivalentIffNonemptyAlgEquiv
public import GroundTheory.Brauer.TensorSimple
public import GroundTheory.Brauer.BaseChangeCSA
public import GroundTheory.Brauer.DoubleCentralizer
public import GroundTheory.Brauer.Degree
public import GroundTheory.ProfiniteCohomology.Bundle0006
public import GroundTheory.ProfiniteCohomology.GaloisCohomology.UnitsInflationCochainsFHomApply
public import GroundTheory.ProfiniteCohomology.GaloisCohomology.IsZeroGroupCohomologyQuotientToInvariantsGalAdd
public import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Brauer

open CategoryTheory groupCohomology GroundTheory.ProfCoh

universe u

section Cocycles

variable {k : Type u} [CommRing k] {H : Type u} [Group H] [TopologicalSpace H]
  [IsTopologicalGroup H] {B : Rep.{u} k H} [IsDiscreteRep B]

end Cocycles

section Topology

variable {K Ks : Type u} [Field K] [Field Ks] [Algebra K Ks]

end Topology

section Main

variable {K Ks : Type u} [Field K] [Field Ks] [Algebra K Ks] [IsSepClosure K Ks]

instance isSepClosure_intermediateField (E : IntermediateField K Ks) : IsSepClosure E Ks :=
  ⟨IsSepClosure.sep_closed K, Algebra.isSeparable_tower_top_of_isSeparable K E Ks⟩

variable (E : IntermediateField K Ks)

end Main

end GroundTheory.Brauer
