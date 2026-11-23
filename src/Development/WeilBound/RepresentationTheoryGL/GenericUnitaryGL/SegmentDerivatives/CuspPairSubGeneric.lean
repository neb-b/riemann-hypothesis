module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspStdSubGeneric
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace GlobalTheory.BZSeg

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def NuPair : Prop :=
  ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ω : Representation ℂ (GL (Fin N) k) V), IsSmooth ω →
    ω.IsIrreducible → ¬ IsGeneric ω → ∃ (α β β' : IrrGL (k := k)) (hd : ∑ a, (![α, β] a).1 = N)
      (hd' : ∑ a, (![β', α.nu 1] a).1 = N), 0 < α.1 ∧ 0 < β.1 ∧ β'.1 = β.1 ∧ 1 ≤ Zc.jm ![α, β] hd ω ∧
        1 ≤ Zc.jm ![β', α.nu 1] hd' ω

end GlobalTheory.BZSeg

end
