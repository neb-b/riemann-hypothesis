module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr
open GlobalTheory.SW hiding Level
open GlobalTheory.Ker
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate ComplexOrder Classical ENNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.VacuumCharacterDeterminant

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev Fam (D : D7) (m n : ℕ) : Type := D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ

def realOf (θ : InfFam D) {m n : ℕ} (z : Fam D m n) : Mx D m n := ∑ τ, lineAt θ τ (z τ) 1

section Forms

variable (S T : HSp D)

def hAt (τ : D.what₂.Tau) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) : ℂ :=
  Matrix.trace ((gramAt D S τ)⁻¹ * yᴴ * gramAt D T τ * x)

def efR (x y : Fam D T.rank S.rank) : ℝ :=
  -∑ τ, 2 * (tauE D τ D.host.xi0 * hAt S T τ (x τ) (y τ)).re

def cxJ (s : Fam D T.rank T.rank) (x : Fam D T.rank S.rank) : Fam D T.rank S.rank :=
  fun τ => cplxO 1 (s τ) (x τ)

def hermH (s : Fam D T.rank T.rank) (x y : Fam D T.rank S.rank) : ℂ :=
  (efR S T (cxJ S T s x) y : ℂ) + Complex.I * (efR S T x y : ℂ)

end Forms

section Moved

variable (θ : InfFam D) (S T : HSp D)

def movS (sT : Fam D T.rank T.rank) (g : GA D T) : Fam D T.rank T.rank :=
  fun τ => compAt θ τ (mt T g) * sT τ * compAt θ τ (mt T g⁻¹)

def frameFn (sT : Fam D T.rank T.rank) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (f : WO S T → ℂ)
    (g : GA D T) (z : Fam D T.rank S.rank) : ℂ :=
  Complex.exp (Real.pi * hermH S T (movS θ T sT g) z z / 2) * om (1, g) f (realOf θ z)

end Moved

section Canon

variable (S T : HSp D) (s : Fam D T.rank T.rank) (BS : Fam D S.rank S.rank) (BT : Fam D T.rank T.rank)
  (Γ : Set (Matrix (Fin T.rank) (Fin S.rank) D.host.E))

end Canon

section Chars

def detPos {r : ℕ} (s k : Matrix (Fin r) (Fin r) ℂ) : ℂ :=
  (k * ((1 / 2 : ℂ) • (1 + s)) + (1 / 2 : ℂ) • (1 - s)).det

def detNeg {r : ℕ} (s k : Matrix (Fin r) (Fin r) ℂ) : ℂ := detPos (-s) k

def vacChar (θ : InfFam D) (T : HSp D) (sT : Fam D T.rank T.rank) (n : ℕ) (a : D.what₂.Tau → ℤ) (k : GA D T) : ℂ :=
  ∏ τ, detPos (sT τ) (compAt θ τ (mt T k)) ^ (a τ + ((n / 2 : ℕ) : ℤ)) *
    detNeg (sT τ) (compAt θ τ (mt T k)) ^ (a τ - ((n / 2 : ℕ) : ℤ))

end Chars

end GlobalTheory.IndefiniteRowSideFullHecke.VacuumCharacterDeterminant

end
