module

public import Mathlib

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsNormForm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def normForm (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S] {n : ℕ}
    (η : Fin n → S) : MvPolynomial (Fin n) R := by
  classical
  exact (Matrix.of fun i j =>
    ∑ m, X m * C (Algebra.leftMulMatrix (Module.Free.chooseBasis R S) (η m) i j)).det

def NormFormEval.Statement : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S] (n : ℕ)
    (η : Fin n → S) (u : Fin n → R),
    eval u (normForm R S η) = Algebra.norm R (∑ m, u m • η m)

def NormFormEmbeddings.Statement : Prop :=
  ∀ (K L Ω : Type) [Field K] [Infinite K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (n : ℕ) (η : Fin n → L),
    map (algebraMap K Ω) (normForm K L η) = ∏ σ : L →ₐ[K] Ω, ∑ m, X m * C (σ (η m))

def LinearFormPrime.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (a : Fin n → F), a ≠ 0 →
    Prime (∑ m, X m * C (a m) : MvPolynomial (Fin n) F)

def MapDvdDescent.Statement : Prop :=
  ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (σ : Type) (f g : MvPolynomial σ K),
    map (algebraMap K Ω) f ∣ map (algebraMap K Ω) g → f ∣ g

def NormFormDvd.Statement : Prop :=
  ∀ (K L : Type) [Field K] [Infinite K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (n : ℕ) (η : Fin n → L) (t : Fin n → K) (P : MvPolynomial (Fin n) K),
    Algebra.adjoin K (Set.range η) = ⊤ → ∑ m, t m • η m = 1 →
      (∑ m, X m * C (η m)) ∣ map (algebraMap K L) P → normForm K L η ∣ P

def PrimeMapFractionRing.Statement : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (n : ℕ)
    (P : MvPolynomial (Fin n) O),
    Prime P → (∀ a : O, P ≠ C a) → Prime (map (algebraMap O K) P)

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsNormOfDividedForm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def NormOfDividedForm.Statement : Prop :=
  ∀ (O B : Type) [CommRing O] [IsDomain O] [CharZero O] [CommRing B] [IsDomain B] [Algebra O B]
    [Module.Free O B] [Module.Finite O B] (n : ℕ) (η : Fin n → B) (t : Fin n → O)
    (P : MvPolynomial (Fin n) O),
    Algebra.adjoin O (Set.range η) = ⊤ → ∑ m, t m • η m = 1 → Prime P →
      (∑ m, X m * C (η m)) ∣ map (algebraMap O B) P →
        ∀ u : Fin n → O,
          eval u P = eval t P * LinearMap.det (LinearMap.mulLeft O (∑ m, u m • η m))

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

