module

public import Mathlib
public import Formalism.LocalRingCardinality.DataKerI
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.KernelLattices.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.IntegralJetEntries
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IntegralJetEntries

def JetsIntegral {σ : Type} {l : ℕ} [Fact l.Prime] (F : MvPowerSeries σ ℂ_[l]) : Prop :=
  ∀ a : σ →₀ ℕ, ‖(a.prod fun _ n => (n.factorial : ℂ_[l])) * MvPowerSeries.coeff a F‖ ≤ 1

def IsRBasis (D : D7) {l : ℕ} [Fact l.Prime] (ρ : D.host.E → ℂ_[l]) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (g : Matrix (Fin N) (Fin N) ℂ_[l]) : Prop :=
  g.det ≠ 0 ∧
    Submodule.span 𝓞_ℂ_[l] (Set.range fun a : Fin N => fun k => g k a) =
      Submodule.span 𝓞_ℂ_[l] ((fun (x : Fin N → D.host.E) k => ρ (x k)) '' (L : Set (Fin N → D.host.E)))


end GlobalTheory.IndefiniteRowSideFullHecke.IntegralJetEntries
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.PolynomialIntegralityJets
section
open NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets

open Formalism.BasicNotions Formalism.MainNotions

def jetAt {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) (α : σ →₀ ℕ) : ℂ_[p] :=
  (α.prod fun _ n => (n.factorial : ℂ_[p])) * MvPowerSeries.coeff α F

def JetsIntegral {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ α, ‖jetAt F α‖ ≤ 1

end GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets
end
end

