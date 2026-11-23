module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0593

@[expose] public section

open GlobalTheory.BZMir.Leib

namespace PositivityTheory.rg.gu.hered2

theorem whitHeredity_all :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      WhitHeredity k :=
  fun k _ _ _ _ => GlobalTheory.CompanionTheory.Rodier.whitHeredity k

end PositivityTheory.rg.gu.hered2
