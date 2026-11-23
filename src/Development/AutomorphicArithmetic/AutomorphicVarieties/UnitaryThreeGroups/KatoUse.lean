module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteCohomology
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeneratorCountTuples.LemmaK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg

namespace UpperTheory.V.U3

structure CohInp : Prop where
  loc : Loc.LocalPublishedTheorems
  pt : GlobalTheory.Published.PoitouTateNormalised
  gf : GlobalFiniteness
  ge : GlobalEulerChar
  lemK : ∃ CK : ℝ, LemmaK CK

def PropGK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∃ c₅ A : ℕ,
    ∀ (e N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (p : ℕ), 1 ≤ e → p.Prime → ¬ p ∣ 30 * N * (discr K).natAbs →
    ∃ NN : ℤ, NN ≠ 0 ∧ Real.log |(NN : ℝ)| ≤ c₅ * Nat.totient H.index * ((N : ℝ) * (e + 1)) ^ A * Real.log p ∧
      ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω] (l : ℕ) [Fact l.Prime], l ≠ p →
        ∀ c : Coef l, (∃ ψ ∈ orb c H, GD Ω K l e ψ) →
          (∀ ψ ∈ orb c H, Vlen Ω c e ψ ≠ ⊤) ∧ ∑ ψ ∈ orb c H, Vn Ω c e ψ ≤ 2 * (padicValInt l NN : ℝ)

def CorGK : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∃ c₅ A : ℕ,
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra K Ω]
    (e N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (p p' : ℕ), p.Prime → p'.Prime → p ≠ p' →
    ¬ p ∣ 30 * N * (discr K).natAbs → ¬ p' ∣ 30 * N * (discr K).natAbs →
    ∀ (c : ∀ l : Nat.Primes, Coef l) (Ls : Finset Nat.Primes), (∀ l ∈ Ls, ∃ ψ ∈ orb (c l) H, GD Ω K l e ψ) →
      (∀ l ∈ Ls, ∀ ψ ∈ orb (c l) H, Vlen Ω (c l) e ψ ≠ ⊤) ∧
      ∑ l ∈ Ls, Real.log (l : ℕ) * ∑ ψ ∈ orb (c l) H, Vn Ω (c l) e ψ ≤
        2 * c₅ * (Nat.totient H.index) * ((N : ℝ) * (e + 1)) ^ A * (Real.log p + Real.log p')

end UpperTheory.V.U3

end
