module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0630

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace PositivityTheory.Lit1

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_of_isLSeg {Δ : Segment k} {x y : IrrGL (k := k)} (hx : IsLSeg Δ x.rep) (hy : IsLSeg Δ y.rep) : x = y := by
  obtain ⟨n, a⟩ := x
  obtain ⟨m, b⟩ := y
  have hn : n = m := hx.deg_eq.symm.trans hy.deg_eq
  subst hn
  obtain ⟨e⟩ := hx.unique hy
  have hab : a = b := Quotient.out_equiv_out.mp ⟨e.symm⟩
  rw [hab]

variable {Lseg : Segment k → IrrGL (k := k)} {L : Multiset (Segment k) → IrrGL (k := k)} (h1 : ∀ Δ, IsLSeg Δ (Lseg Δ).rep)
  (h3 : ∀ (𝔪 : Multiset (Segment k)) (h : ℕ) (Δ : Fin h → Segment k), IsOrderedForm Δ 𝔪 →
    ∃ hd : ∑ a, (Lseg (Δ a)).1 = (L 𝔪).1, IsCosocle (L 𝔪).rep (prodIrr (fun a => Lseg (Δ a)) hd))



end

end PositivityTheory.Lit1

end
