module

public import Formalism.LocalToGlobal.NumberFieldFamilies.Bundle0002
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0004
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0005

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.MainNotions.Inhab

variable {D : D7}

structure ChrIn (D : D7) where
  chr : D.what₂.Tup → ℕ → chrA D
  chr_exp : ∀ μ (j : Fin D.R.m) τ, HasInfExp D (chr μ (j.1 + 1)).1 τ (-(D.hc τ).e j)
  chr_res : ∀ μ j, 1 ≤ j → j ≤ D.R.m → ResEta D (chr μ j).1 0
  eta : chrA D
  eta_exp : ∀ τ, HasInfExp D eta.1 τ (1 / 2)
  eta_res : ResEta D eta.1 1
  eta_unr : UnramEverywhere D eta.1

abbrev lowY (D : D7) (t j i : ℕ) : HSp D := lowC ((towC D t).Ys j) i

structure Free {ψ : AddChar (AF D.host.F) ℂ} (_Om : WeilC ψ) : Type 1 where
  petF : HSp D → ℝ
  petF_pos : ∀ V, 0 < petF V
  fact : ∀ V W, Set (schC ψ V W)
  conjS : ∀ V W, schC ψ V W → schC ψ V W
  conjS_add : ∀ V W Φ Φ', conjS V W (Φ + Φ') = conjS V W Φ + conjS V W Φ'
  conjS_smul : ∀ V W (c : ℂ) Φ, conjS V W (c • Φ) = star c • conjS V W Φ
  conjS_conjS : ∀ V W Φ, conjS V W (conjS V W Φ) = Φ
  conjS_fact : ∀ V W, ∀ Φ ∈ fact V W, conjS V W Φ ∈ fact V W
  conjS_kfin : ∀ V W, ∀ Φ ∈ kfinC ψ V W, conjS V W Φ ∈ kfinC ψ V W

  PosE : ∀ (A B : HSp D), (A.V →ₗ[D.host.E] B.V) → Type
  FJd : ∀ (A B : HSp D), (A.V →ₗ[D.host.E] B.V) → Type
  [fjAdd : ∀ A B ι, AddCommGroup (FJd A B ι)]
  [fjMod : ∀ A B ι, Module ℂ (FJd A B ι)]
  BE : ∀ (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V), PosE A B ι → FJd A B ι → afC D A → cuspC D B → ℂ
  BE_right : ∀ A B ι p s φ, IsLinearMap ℂ (BE A B ι p s φ)
  BE_add : ∀ A B ι p s φ φ' F, BE A B ι p s (φ + φ') F = BE A B ι p s φ F + BE A B ι p s φ' F
  BE_smul : ∀ A B ι p s (c : ℂ) φ F, BE A B ι p s (c • φ) F = star c * BE A B ι p s φ F
  pos1 : D.what₂.Word → {d : BesDat (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) // (d.y : GA D (D.sp.Y 0)) = 1}
  posSym : D.what₂.Word → {d : BesDat (D.sp.X 0) (D.sp.Y 0) (D.sp.iXY 0) // (d.y : GA D (D.sp.Y 0)) = 1}

  f1 : ∀ u, Matrix (Fin (D.sp.Y 0).rank) (Fin (pos1 u).1.ρ) D.host.E
  free_flag_dual : ∀ u, IsDualFlag (pos1 u).1 (f1 u)
  colAF : ∀ (u : D.what₂.Word) (_μ : D.what₂.Tup) (j : ℕ), D.what₂.Mu u →ₗ[ℂ] cuspC D (D.sp.X j)
  PhiX : ∀ (_u : D.what₂.Word) (_μ : D.what₂.Tup) (j : ℕ), schC ψ (D.sp.X j) (D.sp.X (j + 1))
  rowAF : ∀ (μ : D.what₂.Tup) (j : ℕ), D.what₂.Mult μ j →ₗ[ℂ] cuspC D (D.sp.Y j)
  PhiY : ∀ (_μ : D.what₂.Tup) (j : ℕ), schC ψ (D.sp.Y (j + 1)) (D.sp.Y j)
  PhiYLow : ∀ (_μ : D.what₂.Tup) (j i : ℕ), schC ψ (D.sp.Y (j + 1)) (lowY D D.R.t j i)
  PhiYupLow : ∀ (_μ : D.what₂.Tup) (j i : ℕ), schC ψ (D.sp.Y j) (lowY D D.R.t (j + 1) i)
  mY : D.what₂.Tup → ℕ → ℝ
  mY_pos : ∀ μ j, 0 < mY μ j
  adelicDataRowMeasureScale_trivialTuple : ∀ j, mY D.what₂.mu0 j = 1
  mY_zero : ∀ μ, mY μ 0 = 1

attribute [instance] Free.fjAdd Free.fjMod

variable {ψ : AddChar (AF D.host.F) ℂ}

section Ties

variable (G : FormGaps D) (P : PerGaps ψ) (hE : ExpU D) (Om : WeilC ψ) (c : ChrIn D) (f : Free Om)

end Ties

end Formalism.L2.Fam.ThC

end
