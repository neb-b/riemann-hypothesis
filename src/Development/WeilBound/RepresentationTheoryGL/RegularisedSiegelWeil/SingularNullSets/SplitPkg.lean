module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LJPos

structure SplitPkg (D : D7) (v : Pl D) where
  π : Fv D.host.F v ⊗[D.host.F] D.host.E ≃ₐ[Fv D.host.F v] Fv D.host.F v × Fv D.host.F v
  swap : ∀ y, π (sigR (Fv D.host.F v) D.sp.cm.sig y) = (π y).swap
  int : ∀ y, y ∈ intLoc D.host.F D.host.E v ↔
    (π y).1 ∈ v.adicCompletionIntegers D.host.F ∧ (π y).2 ∈ v.adicCompletionIntegers D.host.F

def PlaceEx : Prop := ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ χ, IsHeckeChar D χ →
  ∀ r : ℕ, ResEta D χ r → ∀ S : Finset (Pl D), ∃ v ∉ S, ∃ P : SplitPkg D v,
    (∀ a : Fv D.host.F v, (∀ b ∈ v.adicCompletionIntegers D.host.F, psiV D.host.F ψ v (a * b) = 1) ↔
      a ∈ v.adicCompletionIntegers D.host.F) ∧
    (∀ u : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ, (P.π u).1 ∈ v.adicCompletionIntegers D.host.F →
      (P.π (u⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ)).1 ∈ v.adicCompletionIntegers D.host.F → (P.π u).2 = 1 →
      χ (ideleAt D.host.F D.host.E v u) = 1) ∧
    ∀ u : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ, (P.π u).1 = (P.π u).2 → χ (ideleAt D.host.F D.host.E v u) = 1

end PositivityTheory.Rg.Rsw.L.LJPos

end
