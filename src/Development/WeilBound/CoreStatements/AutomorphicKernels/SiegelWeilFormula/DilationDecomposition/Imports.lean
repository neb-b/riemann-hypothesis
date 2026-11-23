module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AuxiliaryPrimeFunction

@[expose] public section

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Kdil

variable {n : ℕ}

def sq {m : ℕ} (u : Fin m → Fin n → ℂ) : ℝ := ∑ a, ∑ j, ‖u a j‖ ^ 2

def fam (m : ℕ) (X : Fin n → ℝ) (z : ℂ) (u : Fin m → Fin n → ℂ) : ℂ :=
  Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) *
    Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖u a j‖ ^ 2 : ℝ) : ℂ))

def strip (X : Fin n → ℝ) : Set ℂ := {z | ∀ j, |z.im * X j| < Real.pi / 4}

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end PositivityTheory.SiegelWeilFormula.Kdil

end
