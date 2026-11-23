module

public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.FinitePlaceArcs.FinAtOfStatement

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj.QAt

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FreeQuotientRank MvPolynomial

namespace FinKey

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

def detZ (Dw : Datum H) : MvPolynomial (ArcLt Dw) ℤ :=
  ∏ τ : E →+* ℂ, (Matrix.of fun i l : Fin (Dw.mult τ) => (X (⟨τ, i, l⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) ℤ)).det


open Classical in
def subA {K : Type} [Field K] (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (y x : ArcLt Dw) : K :=
  ∑ k : Fin (Dw.mult y.1), if x = ⟨y.1, y.2.1, k⟩ then A y.1 k y.2.2 else 0

theorem subA_sum {K : Type} [Field K] (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) K)
    (y : ArcLt Dw) :
    (∑ x : ArcLt Dw, C (subA A y x) * (X x : MvPolynomial (ArcLt Dw) K)) =
      ∑ k : Fin (Dw.mult y.1), C (A y.1 k y.2.2) * X ⟨y.1, y.2.1, k⟩ := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [subA, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single ⟨y.1, y.2.1, k⟩]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg hb, map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end FinKey

end Formalism.L2.Pj.QAt
