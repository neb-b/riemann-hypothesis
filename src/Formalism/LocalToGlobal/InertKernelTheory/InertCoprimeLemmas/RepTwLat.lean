module

public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0014
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepFrob
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts

@[expose] public section

noncomputable section

open scoped Matrix

namespace Formalism.L2.KerInert.RepTwLat

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.KerInert.RepFrame
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

section Defs

variable (D : D7)

def IntAtP (p : ℕ) (e : D.host.E) : Prop :=
  ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) * e ∈ (algebraMap (𝓞 D.host.E) D.host.E).range

def hStd {N : ℕ} (x y : Fin N → D.host.E) : D.host.E := ∑ k, D.host.conj (x k) * y k

def SelfDualP (p : ℕ) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Prop :=
  (∀ x ∈ L, ∀ y ∈ L, IntAtP D p (hStd D x y)) ∧
  ∀ y : Fin N → D.host.E, (∀ x ∈ L, IntAtP D p (hStd D x y)) → ∃ s : ℕ, Nat.Coprime s p ∧ (s : D.host.E) • y ∈ L

def locSpan (R : Type*) {K : Type*} [CommRing R] [Field K] [Algebra R K] (ρ : D.host.E →+* K) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Submodule R (Fin N → K) :=
  Submodule.span R ((fun x : Fin N → D.host.E => fun k => ρ (x k)) '' (L : Set (Fin N → D.host.E)))

end Defs

section Ties

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
  (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
  (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
  (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

end Ties

section Glob

variable (D : D7) {p : ℕ} {N N' : ℕ}

end Glob

section Loc

variable (D : D7) {p : ℕ} {N N' : ℕ}

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]

end Loc

section Main

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (hfin : ∀ j c, (X.Lv.lev j c).FinClasses) (D : D7)
  (M : ∀ j, X.Lt j → ∀ v : X.Pl, Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) (X.G.P.Qq v))
  (large₂ : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj j).m + 1) → D.host.E))
  (Lg' : ∀ j, X.Lt j → X.Lt (j + 1) → Submodule (𝓞 D.host.E) (Fin ((X.Pj (j + 1)).m + 1) → D.host.E))

end Main

end Formalism.L2.KerInert.RepTwLat

set_option pp.fullNames true
