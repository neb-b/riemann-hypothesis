module

public import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.EssSquareIntegrableSegmentsOfLit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0616
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.GKLocal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0353

@[expose] public section

noncomputable section

namespace PositivityTheory.PfEss

theorem lSocleGL_of_orderFree (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hO : Zc.LOrderFree k) : Zc.LSocleGL k :=
  _root_.GlobalTheory.CompanionTheory.LSocle.lSocleGL PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top (_root_.GlobalTheory.CompanionTheory.GKLocalProof.gkLocal PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top) hO

theorem essSquareIntegrableSegments_main2 (hE : GlobalTheory.Published.LanglandsExhaustionGL)
    (hF : GlobalTheory.Published.StandardFunctorsFiniteLength)
    (hO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], Zc.LOrderFree k)
    (hL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], Zc.LSegExists k)
    (hJ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], Zc.LSegJacquet k) : GlobalTheory.Published.EssSquareIntegrableSegments :=
  essSquareIntegrableSegments_main hE hF (fun k _ _ _ _ _ => lSocleGL_of_orderFree k (hO k)) hL hJ

end PositivityTheory.PfEss

end
