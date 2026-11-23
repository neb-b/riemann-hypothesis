module

public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.Bundle0001
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SigmaAlg
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.Bundle0002

@[expose] public section

noncomputable section

namespace Formalism.L2.KerInert

namespace JetsModel

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

theorem eisenstein_invariants_algebraic (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hcc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    g2 (lamOf D cc δ) ∈ Qbar ∧ g3 (lamOf D cc δ) ∈ Qbar := by
  have hδ0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.brcc_delta_ne D cc hcc δ hδ
  obtain ⟨⟨L, hL⟩, -⟩ := Formalism.L2.Th1.F2.lamOfLat D cc δ hcc.1 hδ0
  obtain ⟨hg2, hg3⟩ := Formalism.L2.KerInert.Sigma.invAlg' D cc δ hcc hδ L hL
  obtain ⟨e2, e3⟩ :=
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L (congrArg (fun A : AddSubgroup ℂ => (A : Set ℂ)) hL)
  rw [e2, e3]
  exact ⟨hg2, hg3⟩

theorem wModel_Δ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hcc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ)
    {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) : (wModel lam (lamOf D cc δ)).Δ = 1 := by
  obtain ⟨h2, h3⟩ := eisenstein_invariants_algebraic D cc δ hcc hδ
  set a2 : Qbar := ⟨g2 (lamOf D cc δ), h2⟩ with ha2
  set a3 : Qbar := ⟨g3 (lamOf D cc δ), h3⟩ with ha3
  have ea4 : lamC lam (-(g2 (lamOf D cc δ)) / 4) = lam (-a2 / 4) := by
    have : -(g2 (lamOf D cc δ)) / 4 = ((-a2 / 4 : Qbar) : ℂ) := by push_cast; rfl
    rw [this, Formalism.L2.KerInert.Sigma.lamC_coe]
  have ea6 : lamC lam (-(g3 (lamOf D cc δ)) / 4) = lam (-a3 / 4) := by
    have : -(g3 (lamOf D cc δ)) / 4 = ((-a3 / 4 : Qbar) : ℂ) := by push_cast; rfl
    rw [this, Formalism.L2.KerInert.Sigma.lamC_coe]
  have hd : a2 ^ 3 - 27 * a3 ^ 2 = 1 := by
    apply Subtype.ext
    have := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
    push_cast
    exact this
  have hw : wModel lam (lamOf D cc δ) = ⟨0, 0, 0, lam (-a2 / 4), lam (-a3 / 4)⟩ := by
    simp only [wModel, ea4, ea6]
  have key : lam (a2 ^ 3 - 27 * a3 ^ 2) = 1 := by rw [hd, map_one]
  rw [hw, ← key]
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, map_sub, map_mul, map_pow, map_div₀, map_neg, map_ofNat]
  ring


end JetsModel


end Formalism.L2.KerInert
