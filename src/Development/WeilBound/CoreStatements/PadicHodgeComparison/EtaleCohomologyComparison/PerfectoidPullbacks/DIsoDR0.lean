module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.IsUnitWitt
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Pb

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

abbrev Lim (r : Res l K) (M : Model l K) (j : ℕ) : Type 1 := (Wc.HS l (B.schFn M.p) r.ρ j).lim

def LimCup (r : Res l K) (M : Model l K) {i j n : ℕ} (h : i + j = n) (x : Lim r M i) (y : Lim r M j) (z : Lim r M n) : Prop :=
  ∀ m, z.1 m = (CH.mulP (Wc.OA l (B.schFn M.p) r.ρ m)).cup h (x.1 m) (y.1 m)

def toD (r : Res l K) (M : Model l K) (j : ℕ) (x : Lim r M j) : r.iso.D M j := (1 : Wc.K₀ l r.k) ⊗ₜ[WittVector l r.k] x

end CrystallineSemistableComparison.Pb
