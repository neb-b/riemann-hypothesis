module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.Bundle0001

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd
open UpperTheory.V.W (Plc Lp)

namespace UpperTheory.V.Z.Sym

structure UnrSplit (L : Type) [Field L] [NumberField L] [IsCMField L] (M : ℕ) : Prop where
  unr : ∀ w : Plc L, Algebra.IsUnramifiedAt (𝓞 (Lp L)) w.asIdeal
  split : ∀ w : Plc L, (M : 𝓞 L) ∈ w.asIdeal → IsSplitAt w

structure AdIn {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (M m : ℕ) (r : G L Ω →* GL (Fin 2) (Qbar l)) : Prop where
  cont : Continuous r
  aut : IsAutCsd ι r
  irr : IrrOpen r
  gap : 2 ≤ m
  unr : ∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → ∀ s ∈ Ine (F := L) A, r s = 1
  away : ∃ τ : Fin 2 → G L Ω →* (Qbar l)ˣ, (∀ i, Continuous (τ i)) ∧ TypeAway r τ
  above : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 →
    ∃ (b : ℤ) (k : ℕ) (κ : Fin 2 → ↥(Dec (F := L) A) →* (Qbar l)ˣ), 0 < k ∧ IsFlagOn r (Dec (F := L) A) κ ∧
      ∀ s : ↥(Dec (F := L) A), (s : G L Ω) ∈ Ine (F := L) A →
        κ 0 s ^ k = (cycBar L Ω l s ^ (b + m)) ^ k ∧ κ 1 s ^ k = (cycBar L Ω l s ^ b) ^ k

def TwEx : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra L Ω] (l : ℕ) [Fact l.Prime],
    l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω), Sd.IsCC c → ∀ M : ℕ, M ≠ 0 → l ∣ M → UnrSplit L M →
    ∀ (χ : G ℚ Ω →* (Qbar l)ˣ) (a : ℤ), IsOpen (χ.ker : Set (G ℚ Ω)) → χ c = (-1) ^ a →
    (∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → ∀ s ∈ Ine (F := L) A, χ (galEmb ℚ L Ω s) = 1) →
    ∃ κ : G L Ω →* (Qbar l)ˣ, Sd.IsAlgChar ι κ ∧
      (∀ s s' : G L Ω, galEmb ℚ L Ω s' = c * galEmb ℚ L Ω s * c⁻¹ → κ s * κ s' = cycBar L Ω l s ^ a * χ (galEmb ℚ L Ω s)) ∧
      (∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → ∀ s ∈ Ine (F := L) A, κ s = 1) ∧
      ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∃ (b : ℤ) (k : ℕ), 0 < k ∧
        ∀ s ∈ Ine (F := L) A, κ s ^ k = (cycBar L Ω l s ^ b) ^ k

end UpperTheory.V.Z.Sym

end
