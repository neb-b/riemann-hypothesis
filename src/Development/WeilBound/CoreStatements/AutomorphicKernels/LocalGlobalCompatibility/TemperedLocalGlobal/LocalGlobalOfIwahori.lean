module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.GalOfCusp GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst

namespace LocalGlobalAboveLAlt

section Defs

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

inductive Sub : Subgroup ↥(Weil h) → Prop
  | top : Sub ⊤
  | step {U V : Subgroup ↥(Weil h)} : Sub V → U ≤ V → ⁅V, V⁆ ≤ U → U.relIndex V ≠ 0 →
      IsOpen {s : ↥(Ine (F := E) A) | ineIncl h s ∈ U} → Sub U

def Triv (y : WD h) (g : ↥(Weil h)) : Prop := y.charPol g = (X - 1) ^ y.lpDim

def Rel (x y : WD h) : Prop :=
  x.lpDim = y.lpDim ∧ (x.mono0 ↔ y.mono0) ∧ ∀ U : Subgroup ↥(Weil h), Sub U → (∀ g ∈ ⁅U, U⁆, Triv y g) →
    ∀ g ∈ U, x.charPol g = y.charPol g

end Defs

end LocalGlobalAboveLAlt
