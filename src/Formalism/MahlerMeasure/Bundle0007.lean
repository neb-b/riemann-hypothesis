module

public import Formalism.MahlerMeasure.MahlerMeasureProofs.Bundle0004
public import Formalism.MahlerMeasure.Bundle0006
public import Formalism.MahlerMeasure.Bundle0005
public import Formalism.MahlerMeasure.MahlerMeasureProofs.GamDeg
public import Formalism.MahlerMeasure.MahlerMeasureProofs.GamLead
public import Formalism.MahlerMeasure.MahlerMeasureProofs.GamInt

@[expose] public section

-- bundled from Formalism.MahlerMeasure.CoarseLevelSlackInequalities
section
namespace Formalism.GM.Top
open Formalism.GM
theorem windowCountAP : WindowCountAP := window_count_progression
theorem discsDisjointAP : DiscsDisjointAP := root_discs_disjoint_progression
theorem windowMeanAP : WindowMeanAP := windowMeanAP_of windowCountAP discsDisjointAP
theorem windowFullAP : WindowFullAP := windowFullAP_of valuation_window_lower_bound windowMeanAP
end Formalism.GM.Top
end

-- bundled from Formalism.MahlerMeasure.GamLead
section
namespace Formalism.GM.Top
open Formalism.GM
theorem gamDeg : M.GamDeg := gamma_degree_bound
theorem gamLead : M.GamLead := gamma_leading_term
end Formalism.GM.Top
end

-- bundled from Formalism.MahlerMeasure.StatementTM
section
namespace Formalism.GM.M

open MvPolynomial Finset

def Letters.takeD {N : ℕ} (LL : Letters N) (k : ℕ) : Letters k where
  vec := fun i => if h : (i : ℕ) < N then LL.vec ⟨i, h⟩ else false
  deg := fun i => if h : (i : ℕ) < N then LL.deg ⟨i, h⟩ else 0


open Classical in
noncomputable def Letters.setTies {N : ℕ} (LL : Letters N) (T : TieData) (n : Fin T.t → ℕ) : Letters N where
  vec := LL.vec
  deg := fun a => if h : ∃ i, T.pos i + 1 = (a : ℕ) then n (Classical.choose h) else LL.deg a

def TieData.thrUpTo (T : TieData) (i : Fin T.t) : Fin T.q → WithTop ℤ :=
  fun k => if T.J k ≤ T.pos i + 1 then T.thr k else ⊤

noncomputable def TieData.phis (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : Letters N) (T : TieData) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  (List.finRange T.t).foldr (fun i acc => (T.phi p LL i) ∘ₗ acc) LinearMap.id

noncomputable def TieData.Ffull (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero N] (LL : Letters N) (T : TieData) (i : Fin T.t)
    (ρ : Fin r) (n : ℕ) (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) : MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  rename (fun x : Fin (T.pos i + 1 + 1) × Fin r =>
      (if h : (x.1 : ℕ) < N then (⟨x.1, h⟩ : Fin N) else ⟨0, Nat.pos_of_ne_zero (NeZero.ne N)⟩, x.2))
    (freeze p (LL.takeD (T.pos i + 1)) ρ n f)

noncomputable def TieData.YYsp (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero N] [NeZero r] (LL : Letters N) (T : TieData)
    (i : Fin T.t) (ρ : Fin r) (n : Fin T.t → ℕ) (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  Y p (LL.setTies T n) T.J T.thr ⊓
    Submodule.span ℚ_[p] {x | ∃ g ∈ gSpan p (LL.setTies T n) (T.pos i + 2) (T.Ffull p (LL.setTies T n) i ρ (n i) f),
      ∃ q ∈ MvPolynomial.supported ℚ_[p] {v : Fin N × Fin r | T.pos i + 2 ≤ (v.1 : ℕ)}, x = g * q}

def WeightSpaceDimMonotone : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r] (LL : Letters N) (T : TieData), T.Admissible LL →
    ∀ (ρ : Fin r), (ρ : ℕ) = r - 1 → 2 ≤ r → ∀ (i : Fin T.t) (n : Fin T.t → ℕ) (w : Fin r → ℤ)
      (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p]),
      f ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w → f ≠ 0 →
      ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i →
      ∀ n' : ℕ, n i ≤ n' →
        Module.finrank ℚ_[p] (T.YYsp p LL i ρ n f) ≤
          Module.finrank ℚ_[p] (T.YYsp p LL i ρ (Function.update n i n') f)

def MonoCount : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r] (LL : Letters N) (T : TieData), T.Admissible LL →
    ∀ (ρ : Fin r), (ρ : ℕ) = r - 1 → 2 ≤ r → ∀ (i : Fin T.t) (n : Fin T.t → ℕ),
      ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i →
      ∀ fw : (Fin r → ℤ) → MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p],
        (∀ w, fw w ∈ MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ∧
          (MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w ≠ ⊥ → fw w ≠ 0)) →
        ∑ᶠ w, Module.finrank ℚ_[p] (MMw p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ w) *
            Module.finrank ℚ_[p] (T.YYsp p LL i ρ n (fw w)) =
          Module.finrank ℚ_[p] (Y p (r := r) (LL.setTies T n) T.J T.thr)

end Formalism.GM.M
end

