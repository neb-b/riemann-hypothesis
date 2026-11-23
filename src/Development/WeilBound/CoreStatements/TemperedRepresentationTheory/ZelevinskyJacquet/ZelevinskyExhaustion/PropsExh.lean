module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace Zc

def JacquetSubLeft (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : Prop :=
  ∀ x : IrrGL (k := k), 0 < x.1 → ∃ (y : Fin 2 → IrrGL (k := k)) (hd : ∑ a, (y a).1 = x.1), (y 0).IsCusp ∧
    ∃ f : x.rep.IntertwiningMap (prodIrr y hd), Function.Injective f

end Zc

end
