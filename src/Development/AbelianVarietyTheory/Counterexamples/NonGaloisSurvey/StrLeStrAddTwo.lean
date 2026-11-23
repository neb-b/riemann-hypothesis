module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0713
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0140
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0266

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.PtStringTest

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem aPl_last_pos (i : Fin D.R.m) (τ : D.what₂.Tau) : 0 < aPl D i (D.R.k + i) τ (D.R.k + i - 1) := by
  have hk : 1 ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    omega
  have hn : D.R.k + (i : ℕ) - 1 < D.R.k + (i : ℕ) := by omega
  have hlam : Formalism.L2.NTheta.lamAt (D.hc τ) (D.R.k + (i : ℕ) - 1) = -(D.hc τ).b i := by
    unfold Formalism.L2.NTheta.lamAt
    rw [dite_eq_right (by omega), dite_eq_left (by omega)]
    congr 2
    ext
    simp only
    omega
  have hc : ((D.R.k + (i : ℕ) - 1 : ℕ) : ℚ) + 1 = ((D.R.k + (i : ℕ) : ℕ) : ℚ) := by
    have : D.R.k + (i : ℕ) - 1 + 1 = D.R.k + (i : ℕ) := by omega
    exact_mod_cast this
  have hgap := (D.hc τ).gap_be i
  have h1 : (1 : ℚ) ≤ -(D.hc τ).b i + (D.hc τ).e i
      - (((D.R.k + (i : ℕ) : ℕ) : ℚ) - (((D.R.k + (i : ℕ) - 1 : ℕ) : ℚ) + 1)) - ((D.R.t : ℚ) + 1) / 2 := by
    linarith
  have h2 := Int.floor_pos.2 h1
  unfold aPl
  rw [if_pos hn, hlam]
  omega

end GlobalTheory.PtStringTest

end
