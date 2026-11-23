module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.Descend

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.RgEis

variable {E R : Type} [Field E] [CommRing R]

namespace Ad

variable (A : Ad E R)

variable [TopologicalSpace R]

end Ad


open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

def eSF {F : Type} [Field F] [NumberField F] (S : Finset (Pl F)) : AF F :=
  LinearMap.inl F (Ainf F) (Af F) 1 + LinearMap.inr F (Ainf F) (Af F) (∑ v ∈ S, singleFin v 1)

end PositivityTheory.RgEis
