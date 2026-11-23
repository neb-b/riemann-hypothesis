module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HeckeCharacterFamilyConductor
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.AdelEqZeroOfOffDom

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop

namespace GlobalTheory.CovTop.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Cover

variable {T : Core D} {j : ℕ} {Y : Deep T j} {e e' : ℕ} {o o' : ℝ}

theorem chi_eq_one (h : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) (k) (la) (γ)
    (hγ : γ ∈ ((Y.U σ).X k).Γ) : ((Y.U σ).X k).χ la γ = 1 :=
  GlobalTheory.OneEmbeddingProbe.chi_eq_one _ (h.chiTriv σ hσ) k la γ hγ

end Cover

section Base

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (i : Fin D.R.m)

end Base

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
  (a : (E →+* ℂ) × ℕ → ℕ) (m : ℕ)

theorem exZ_shiftG (s : ℤ) : exZ Dw (shiftG Dw a (2 * m) s) = exOf Dw (laOf Dw a (2 * m) + s • hodgeWt Dw) m := by
  have h1 := exOf_add (laOf Dw a (2 * m)) (s • hodgeWt Dw) (m : ℤ) 0
  have h2 := exOf_weightOf (Dw := Dw) (fun x => (a x : ℤ)) m
  have h3 : laOf Dw a (2 * m) = weightOf Dw (fun x => (a x : ℤ)) m := by simp [laOf]
  rw [add_zero] at h1
  rw [h1, h3, h2]
  funext x
  rw [shiftG, exZ_add]
  simp only [wtZ, exOf, Pi.add_apply]
  push_cast
  rfl

end Weights

end GlobalTheory.CovTop.Model

end
