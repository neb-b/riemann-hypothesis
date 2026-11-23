module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.CrystallineInputs.OfInputs
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.Bundle0001

@[expose] public section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.GalCut GlobalTheory.RoadU

namespace UpperTheory.Gal.ToralGalois

structure Inq : Prop extends UpperTheory.Gal.Int.Inp.Inp where
  chl : ∀ (K M : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Algebra K M]
    [IsGalois K M], (Module.finrank K M).Prime → ∀ (a : ℕ), 1 ≤ a → ∀ (π : CuspSub K a) (P : CuspSub M a), IsLift π P → CharLift π P

end UpperTheory.Gal.ToralGalois
