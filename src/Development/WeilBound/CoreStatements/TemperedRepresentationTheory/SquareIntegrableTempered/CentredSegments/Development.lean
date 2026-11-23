module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorJacquetEigenLeft
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorJacquetEigenRight
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0583
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0356
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0611
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0345
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0362
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0347
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0359
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0353
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0381
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0364
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0374
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0357
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0355
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0386
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TemperedProducts.CentredSegSqInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002

@[expose] public section

noncomputable section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace Zls.FreeSingleHomotopyEquivDiscreteChains

theorem sspectral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.Published.StandardFunctorsFiniteLength → Zls.MaxExpStrict π → Zls.HeckeSpectral π := by
  exact GlobalTheory.T.hecke_spectral_of_strict_exponent

theorem ssqint : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → IsAdmissible π → Zls.UnitaryCentral π → Zls.HeckeSpectral π → IsSqIntCoeff π := by
  exact _root_.GlobalTheory.CompanionTheory.SqIntHecke.isSqIntCoeff_of_heckeSpectral

theorem casselmanSuffSq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hF : GlobalTheory.Published.StandardFunctorsFiniteLength) : Zls.CasselmanSuffSq k := by
  intro N V _ _ π _ hs hi hu he
  exact ssqint k N V π hs hi (hA k N V π hs hi) hu (sspectral k N V π hs hi hA hF he)

theorem sseglink : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zls.CasselmanSuffSq k → GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.LSegJacquet k → Zz.CentredSegSqInt k := by
  exact _root_.GlobalTheory.CompanionTheory.SegLink.centredSegSqInt

theorem centredSegSqInt (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hF : GlobalTheory.Published.StandardFunctorsFiniteLength) (hJ : Zc.LSegJacquet k) :
    Zz.CentredSegSqInt k :=
  sseglink k (casselmanSuffSq k hA hF) hA hJ

end Zls.FreeSingleHomotopyEquivDiscreteChains

end
