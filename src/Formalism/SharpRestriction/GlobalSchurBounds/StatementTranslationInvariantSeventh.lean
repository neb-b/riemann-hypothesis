module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.GL3r7

section A

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

def PhV {p : ℕ} [Fact p.Prime] (g : G1 p) {κ ι σ : Type*} [Fintype κ] [Fintype ι]
    (b : ι → κ → ℂ_[p] × ℂ_[p]) (w : ι → MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  ∑ k, g.phAt (g.lin (fun e => (b e k).1) w)

def sdL {p : ℕ} [Fact p.Prime] (g : G1 p) {κ ι ι' : Type*} [Fintype κ] [Fintype ι] [Fintype ι']
    (a : ι → κ → ℂ_[p] × ℂ_[p]) (a' : ι' → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries (ι ⊕ ι') ℂ_[p] :=
  g.PhOn (Sum.elim a a') - PhV g a (fun e => Xv (Sum.inl e)) - PhV g a' (fun e => Xv (Sum.inr e))

def sdR {p : ℕ} [Fact p.Prime] (g : G1 p) {κ ι ι' : Type*} [Fintype κ] [Fintype ι] [Fintype ι']
    (a : ι → κ → ℂ_[p] × ℂ_[p]) (a' : ι' → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries (ι ⊕ ι') ℂ_[p] :=
  ∑ f, ∑ f', g.be (g.mulBy (hP (a f) (a' f')).1 (Xv (Sum.inl f))) (Xv (Sum.inr f'))

def sdR' {p : ℕ} [Fact p.Prime] (g : G1 p) {κ ι ι' : Type*} [Fintype κ] [Fintype ι] [Fintype ι']
    (a : ι → κ → ℂ_[p] × ℂ_[p]) (a' : ι' → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries (ι ⊕ ι') ℂ_[p] :=
  ∑ f, ∑ f', g.be (Xv (Sum.inl f)) (g.mulBy (hP (a f) (a' f')).2 (Xv (Sum.inr f')))

end A

section C

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Classical

end C

section Z

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

end Z

end Formalism.MainNotions.GL3r7
