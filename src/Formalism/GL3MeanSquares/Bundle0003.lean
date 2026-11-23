module

public import Mathlib
public import Formalism.GL3MeanSquares.RationalMatrixPrimeOrderBound
public import Formalism.FormalGroupWitt.Statement

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.AffineFibreCountComparison
section
namespace Formalism.HermitianLattices.RamifiedLatticeOperators

open Finset Matrix ComplexConjugate

def Fubini_orbits : Prop :=
  ∀ (Γ P Q V : Type) [Group Γ] [MulAction Γ P] [MulAction Γ Q] [AddCommGroup V] [Module ℚ V]
    (pr : P → Q) (fib : Q → Finset P) (Ψ : P → V) (RP : Finset P) (RQ : Finset Q),
    (∀ (γ : Γ) (p : P), pr (γ • p) = γ • pr p) → (∀ p y, p ∈ fib y ↔ pr p = y) →
    (∀ (γ : Γ) (p : P), Ψ (γ • p) = Ψ p) →
    (∀ y : Q, Finite (MulAction.stabilizer Γ y)) →
    (∀ p : P, ∃! r, r ∈ RP ∧ r ∈ MulAction.orbit Γ p) →
    (∀ y : Q, ∃! r, r ∈ RQ ∧ r ∈ MulAction.orbit Γ y) →
    ∑ p ∈ RP, ((Nat.card (MulAction.stabilizer Γ p) : ℚ))⁻¹ • Ψ p =
      ∑ y ∈ RQ, ((Nat.card (MulAction.stabilizer Γ y) : ℚ))⁻¹ • ∑ p ∈ fib y, Ψ p

def Count_orbits : Prop :=
  ∀ (Γ A B V : Type) [Group Γ] [MulAction Γ A] [MulAction Γ B] [AddCommGroup V] [Module ℚ V]
    (up : A → Finset B) (down : B → Finset A) (G : A → B → V) (RA : Finset A) (RB : Finset B),
    (∀ a b, b ∈ up a ↔ a ∈ down b) → (∀ (γ : Γ) a b, b ∈ up a → γ • b ∈ up (γ • a)) →
    (∀ (γ : Γ) a b, b ∈ up a → G (γ • a) (γ • b) = G a b) →
    (∀ a : A, Finite (MulAction.stabilizer Γ a)) → (∀ b : B, Finite (MulAction.stabilizer Γ b)) →
    (∀ a : A, ∃! r, r ∈ RA ∧ r ∈ MulAction.orbit Γ a) →
    (∀ b : B, ∃! r, r ∈ RB ∧ r ∈ MulAction.orbit Γ b) →
    ∑ a ∈ RA, ((Nat.card (MulAction.stabilizer Γ a) : ℚ))⁻¹ • ∑ b ∈ up a, G a b =
      ∑ b ∈ RB, ((Nat.card (MulAction.stabilizer Γ b) : ℚ))⁻¹ • ∑ a ∈ down b, G a b

def LemmaB'_length : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R), Irreducible ϖ →
    ∀ (ι : Type) [Fintype ι] (deg : ι → ℕ),
      Module.length R ((ι → R) ⧸
        (Submodule.pi Set.univ (fun i => Ideal.span {ϖ ^ deg i}) : Submodule R (ι → R))) =
        ((∑ i, deg i : ℕ) : ℕ∞)

end Formalism.HermitianLattices.RamifiedLatticeOperators
end

-- bundled from Formalism.GL3MeanSquares.InvariantSeriesBidegreeOneOne
section
noncomputable section

namespace Formalism.HermitianLattices.IntegralLatticeDensity

open Finset



def SeSign : Prop :=
  ∀ (A : Type) [CommRing A] (q : ℕ) (ε η : A), Odd q → ε ^ q = η * ε → η * η = 1 →
    ∀ (n : ℕ) (ζ : ZMod n → A) (e : ZMod n) (L : ℕ),
      ∑ l ∈ range L, (-η) ^ l * (ε * ζ (e - 2 * (l : ZMod n))) ^ (q ^ l) =
        ε * ∑ l ∈ range L, (-1) ^ l * ζ (e - 2 * (l : ZMod n)) ^ (q ^ l)


def PowerCongruenceIffEqual : Prop :=
  ∀ (l d s s' : ℕ), 2 ≤ l → s < d → s' < d →
    ((l ^ d - 1 : ℕ) : ℤ) ∣ (l : ℤ) ^ s - (l : ℤ) ^ s' → s = s'

def cob {M Q : Type} [AddCommGroup M] [AddCommGroup Q] (φ : M → Q) (a b : M) : Q :=
  φ (a + b) - φ a - φ b

def NormAllAlpha : Prop :=
  ∀ (Z O M Q : Type) [CommRing Z] [CommRing O] [StarRing O] [Algebra Z O] [AddCommGroup M]
    [Module O M] [AddCommGroup Q] [Module Z Q] (φ : M → Q) (nm tr : O → Z),
    Function.Injective (algebraMap Z O) →
    (∀ α, algebraMap Z O (nm α) = star α * α) → (∀ α, algebraMap Z O (tr α) = star α + α) →
    (∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) →
    (∀ (z : Z) a b, cob φ a (algebraMap Z O z • b) = z • cob φ a b) →
    (∀ (α : O) a b, cob φ (α • a) b = cob φ a (star α • b)) →
    (∀ x : Q, x + x = 0 → x = 0) →
    ∀ (α α' : O) (u : M), φ ((2 : O) • u) = (4 : Z) • φ u →
      φ (α • u) = nm α • φ u → φ (α' • u) = nm α' • φ u →
      φ ((α + α') • u) = nm (α + α') • φ u

def UnitaryInvariance : Prop :=
  ∀ (Z O M Q : Type) [CommRing Z] [CommRing O] [StarRing O] [Algebra Z O] [AddCommGroup M]
    [Module O M] [AddCommGroup Q] [Module Z Q] (φ : M → Q) (nm : O → Z),
    Function.Injective (algebraMap Z O) →
    (∀ α, algebraMap Z O (nm α) = star α * α) →
    (∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) →
    (∀ (α : O) a b, cob φ (α • a) b = cob φ a (star α • b)) →
    (∀ (α : O) u, φ (α • u) = nm α • φ u) →
    ∀ (n : Type) [Fintype n] [DecidableEq n] (δ : Matrix n n O), δ.conjTranspose * δ = 1 →
      ∀ u : n → M, ∑ i, φ (∑ j, δ i j • u j) = ∑ j, φ (u j)

def HyperbolicSplit : Prop :=
  ∀ (Z O M Q : Type) [CommRing Z] [CommRing O] [StarRing O] [Algebra Z O] [AddCommGroup M]
    [Module O M] [AddCommGroup Q] [Module Z Q] (φ : M → Q) (nm : O → Z),
    Function.Injective (algebraMap Z O) →
    (∀ α, algebraMap Z O (nm α) = star α * α) →
    (∀ a a' b, cob φ (a + a') b = cob φ a b + cob φ a' b) →
    (∀ (α : O) a b, cob φ (α • a) b = cob φ a (star α • b)) →
    (∀ (α : O) u, φ (α • u) = nm α • φ u) →
    ∀ (n ι : Type) [Fintype n] [Fintype ι] [DecidableEq ι] (f f' : ι → n → O),
      (∀ e e', ∑ i, star (f e i) * f e' i = 0) → (∀ e e', ∑ i, star (f' e i) * f' e' i = 0) →
      (∀ e e', ∑ i, star (f e i) * f' e' i = if e = e' then 1 else 0) →
      ∀ t t' : ι → M,
        ∑ i, φ (∑ e, (f e i • t e + f' e i • t' e)) = ∑ e, cob φ (t e) (t' e)

def IntegerMeanLog : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (x : NumberField.RingOfIntegers K), x ≠ 0 →
    0 ≤ ∑ φ : K →+* ℂ, Real.log ‖φ (x : K)‖

def WeberRoot : Prop :=
  ∀ (x j : ℂ) (s : ℤ), (s = 16 ∨ s = -16) → IsIntegral ℤ j → (x - (s : ℂ)) ^ 3 = j * x →
    IsIntegral ℤ x ∧ x ≠ 0

end Formalism.HermitianLattices.IntegralLatticeDensity
end
end

-- bundled from Formalism.GL3MeanSquares.LegendreCoefficient
section
noncomputable section

namespace Formalism.HermitianLattices.ExpSeriesBivariate

open Finset

def expS {σ K : Type} [Field K] [Algebra ℚ K] (f : MvPowerSeries σ K) : MvPowerSeries σ K :=
  PowerSeries.subst f (PowerSeries.exp K)

def InLam {σ K : Type} [NormedField K] [Algebra ℚ K] (f : MvPowerSeries σ K) : Prop :=
  MvPowerSeries.constantCoeff f = 0 ∧ Formalism.G.IntegralMv (expS f)

def IntegralInverse : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (σ : Type) [Fintype σ] [DecidableEq σ]
    (T : σ → MvPowerSeries σ K) (J' : Matrix σ σ K),
    (∀ i, MvPowerSeries.constantCoeff (T i) = 0) → (∀ i, Formalism.G.IntegralMv (T i)) →
    (∀ i j, ‖J' i j‖ ≤ 1) →
    (Matrix.of fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (T i)) * J' = 1 →
    ∃ X' : σ → MvPowerSeries σ K, (∀ i, MvPowerSeries.constantCoeff (X' i) = 0) ∧
      (∀ i, Formalism.G.IntegralMv (X' i)) ∧ (∀ i, MvPowerSeries.subst X' (T i) = MvPowerSeries.X i) ∧
      ∀ i, MvPowerSeries.subst T (X' i) = MvPowerSeries.X i





end Formalism.HermitianLattices.ExpSeriesBivariate
end
end

