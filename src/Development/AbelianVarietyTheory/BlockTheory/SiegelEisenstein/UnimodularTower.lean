module

public import Mathlib
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnfoldingConstantsPos
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChainOnto
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnimodularTower

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev Fn (D : D7) (u : D.what₂.Word) (i : ℕ) : Type := Formalism.MainNotions.product_first_zeroth_parts.Fn D u i

abbrev Fm (D : D7) (u : D.what₂.Word) (i : ℕ) : Submodule ℂ (Fn D u i) := (D.fm u).Fi i

abbrev Ram (D : D7) (u : D.what₂.Word) (i : ℕ) : Submodule ℂ (Fn D u i) := Formalism.MainNotions.product_first_zeroth_parts.MramI D u i

abbrev Eps (D : D7) (u : D.what₂.Word) : Type := ∀ v : (D.mem u).A.vT, ((D.mem u).A.Fv v)ˣ

def colPar (D : D7) (u : D.what₂.Word) (j : ℕ) : D.what₂.Tau → SPar :=
  (TPar.ofWord D u (Ptw D).eta (Ptw D).eta_half).Xpar j

def dcos {V : HSp D} (R : Subgroup (GA D V)) (b : GA D V) (K : Subgroup (GA D V)) : Set (GA D V) :=
  {h | ∃ r ∈ R, ∃ x ∈ GinfC V, ∃ κ ∈ K, h = r * x * b * κ}

structure RowOn (V : HSp D) where
  par : D.what₂.Tau → SPar
  M : DSModel V par
  Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)
  β : GL (Fin V.rank) (Lev.EAf D)
  L : LevDat D.host.E ℂ V.rank
  ν : Measure (GA D V)
  fd : Set (GA D V)

abbrev RowOn.st {V : HSp D} (r : RowOn V) : PiLocalization₂ D := ⟨V, r.par, r.M, r.Λ, r.β, r.L, r.ν, r.fd⟩

structure ColOn (c : Com D) (u : D.what₂.Word) (X : HSp D) (j : ℕ) where
  M : DSModel X (colPar D u j)
  K : Subgroup (GA D X)
  a : Fm D u j →ₗ[ℂ] MultT c.θ M (K : Set (GA D X)) (fun _ => 1)

variable {c : Com D} {u : D.what₂.Word}

structure ColStep {X X' : HSp D} {j : ℕ} (A : ColOn c u X j) (A' : ColOn c u X' (j + 1)) where
  om : Om X X'
  f : WO X X' → ℂ
  it : PolF D X'.rank X.rank →ₗ[ℂ] SmT A.M →ₗ[ℂ] SmT A'.M

section ColStep

variable {X X' : HSp D} {j : ℕ} {A : ColOn c u X j} {A' : ColOn c u X' (j + 1)}

end ColStep

structure Node (c : Com D) (u : D.what₂.Word) (ρ j : ℕ) where
  B : BesLev D ρ
  row : RowOn B.V
  col : ColOn c u B.A j
  b : GA D B.V

structure Dbl {σ j : ℕ} (N : Node c u (σ + 1) j) (N' : Node c u σ (j + 1 + 1)) where
  J : JacLev D (σ + 1)
  row : RowOn J.W
  col : ColOn c u J.W₀ (j + 1)
  b : GA D J.W
  s₁ : StepBF c.ψ N.B J
  s₂ : StepFB c.ψ J N'.B
  l : Link N.B N'.B.L N'.B.ζ
  vL : VolM D N'.B.L.rank J.W₀.rank
  p₁ : ChainOnto.Step c N.row.st row.st
  p₂ : ChainOnto.Step c row.st N'.row.st
  k₁ : ColStep N.col col
  k₂ : ColStep col N'.col
  ε : Eps D u

section Dbl

variable {σ j : ℕ} {N : Node c u (σ + 1) j} {N' : Node c u σ (j + 1 + 1)}

end Dbl

structure Fin2 {j : ℕ} (N : Node c u 0 j) {T : HSp D} (top : RowOn T) where
  t : Last c.ψ T N.B
  row : RowOn t.J.W
  col₁ : ColOn c u t.J.W (j + 1)
  X : HSp D
  L : HSp D
  o : OrthDec X T L
  col₂ : ColOn c u X (j + 1 + 1)
  p₁ : ChainOnto.Step c N.row.st row.st
  p₂ : ChainOnto.Step c row.st top.st
  k₁ : ColStep N.col col₁
  k₂ : ColStep col₁ col₂
  ε : Eps D u
  ι : (D.mem u).P.Mt ≃ₗ[ℂ] top.st.CC c
  br : SmT col₂.M →ₗ[ℂ] SmT top.M →ₗ[ℂ] ℂ

section Fin2

variable {j : ℕ} {N : Node c u 0 j} {T : HSp D} {top : RowOn T}

end Fin2

end GlobalTheory.IndefiniteRowSideFullHecke.UnimodularTower

end
