module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ArithmeticPointClassicality
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.TaylorWilesObstructionBound

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV GlobalTheory.GalOfCusp

namespace UpperTheory.V.W

def LocCFTAll : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω), Pa.LocCFT s

def PhiAll : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev),
    Alg.PhiCond V.frame.Γ l ∧ Alg.PhiCond V.frame.G₀ l ∧ ∀ v, Alg.PhiCond (V.frame.Gv v) l

end UpperTheory.V.W
