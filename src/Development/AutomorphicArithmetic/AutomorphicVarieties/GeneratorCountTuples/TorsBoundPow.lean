module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK

@[expose] public section

noncomputable section

open NumberField

namespace UpperTheory.V.K

abbrev HGL (L : Type) [Field L] [NumberField L] (N m : ℕ) : Type :=
  groupHomology (Rep.trivial ℤ (GL (Fin N) (𝓞 L)) ℤ) m

abbrev torsHGL (L : Type) [Field L] [NumberField L] (N m : ℕ) : AddSubgroup (HGL L N m) :=
  AddCommGroup.torsion (HGL L N m)

end UpperTheory.V.K

end
