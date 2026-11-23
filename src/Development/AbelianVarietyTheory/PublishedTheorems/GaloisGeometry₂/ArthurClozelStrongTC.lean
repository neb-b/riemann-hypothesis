module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open UpperTheory.V.Published

namespace GlobalTheory.Published

def ArthurClozelStrongTC : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Algebra K M]
    [IsGalois K M], (Module.finrank K M).Prime → ∀ (a : ℕ), 1 ≤ a → ∀ π : CuspSub K a,
    (∀ η : HChar K, IsNormChar M η → ¬ SelfTw (CG.mk π).HasSat η) → ∃ P : CuspSub M a, GalCut.IsLift π P

end GlobalTheory.Published

end
