module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002

@[expose] public section

namespace GlobalTheory.FlagFlowCheck

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem c_pos (τ : X.Ψ) : 0 < X.c τ := by
  have h : τ.1 X.ξ0 ≠ 0 := (map_ne_zero_iff τ.1 τ.1.injective).2 X.ξ0_ne
  unfold Data.c
  positivity

theorem tt_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) {ξ : Fin r → E} (hξ : ξ ≠ 0) (τ : X.Ψ) :
    0 < X.tt ξ x τ := by
  have hv : Data.emb τ.1 ξ ≠ 0 := by
    intro h
    apply hξ
    funext a
    exact (map_eq_zero_iff τ.1 τ.1.injective).1 (congrFun h a)
  have := X.maj_pos hx τ hv
  have := c_pos X τ
  unfold Data.tt
  positivity

end GlobalTheory.FlagFlowCheck
