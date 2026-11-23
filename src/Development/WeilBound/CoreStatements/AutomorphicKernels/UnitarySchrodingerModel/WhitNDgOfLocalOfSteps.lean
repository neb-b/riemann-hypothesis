module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.NDDefs

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

variable {D : D7} {n : ℕ}

def whitAt (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (μ : Measure (Mx D V.rank n)) (lam : Measure (hermA D n))
    (nb : hermA D n → G D n) (w : G D n) (H : G D n → ℝ≥0) (φ : Mx D V.rank n → ℂ) (β : HermE D n) (g : G D n) :
    ℂ → ℂ :=
  fun z => ∫ b, npow (H (w * nb b * g)) (z - s0 V n) * Jt ψ V μ φ b *
    ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D n n))) ∂lam

def HeightKInv : Prop :=
  ∀ (D : D7) (n : ℕ) (H : G D n → ℝ≥0), IsHeight H → ∀ x : G D n, ∀ k ∈ K D n, H (x * k) = H x

def FockKStable : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν Φ, Std D n V ψ χ θ μ ω H l s ν Φ → ∀ k ∈ K D n, (ω k Φ).1 ∈ fockA θ V n l s

end PositivityTheory.PfSWUS

end
