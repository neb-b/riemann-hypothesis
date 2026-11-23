module

public import Formalism.LocalToGlobal.InertKernelTheory.StatementBe
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0002
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading

@[expose] public section

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
section
noncomputable section

namespace Formalism.L2.KerInert

open Formalism.MainNotions.GL3Theta Formalism.L2.G.Pend

def GenusOneModelExists : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ),
    Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc → Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], Nat.Coprime (Ideal.absNorm cc) p → 5 ≤ p → InertK D p →
    ∀ lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p],
      ∃ g : G1 p, g.lam = lam ∧ At D cc δ g ∧ ModelOverW g.lam g.abelian₂ g.C ∧ LTIso g

def GenusOneModelExistsLattice : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (NumberField.RingOfIntegers D.host.K)) (δ : ℂ),
    Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc → Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → InertK D p →
    ∀ lam : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ_[p],
      ∃ (cc' : Ideal (NumberField.RingOfIntegers D.host.K)) (δ' : ℂ) (g : G1 p),
        Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc' ∧ Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc' δ' ∧
        Formalism.MainNotions.TaylorLogMetric.lamOf D cc' δ' = Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ ∧
        g.lam = lam ∧ At D cc' δ' g ∧ ModelOverW g.lam g.abelian₂ g.C ∧ LTIso g

end Formalism.L2.KerInert
end
end

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.StatementAlgT
section
noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.L2.Ker

def AlgTAll : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : Formalism.MainNotions.TaylorLogMetric.IdE D → ℂ),
    Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc → Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → Formalism.MainNotions.TaylorLogMetric.IsChi D χ → B.AlgT χ

end Formalism.L2.KerInert
end
end

