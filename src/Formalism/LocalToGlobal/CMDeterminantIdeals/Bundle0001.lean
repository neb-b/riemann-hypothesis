module

public import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CMDeterminantIdeals.StatementA
section
noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder

def DegAlg : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (L M : MLine K), L.Good → M.Good →
    (L.tensor M).Good ∧ (L.tensor M).deg = L.deg + M.deg ∧ L.dual.Good ∧ L.dual.deg = - L.deg ∧
      ∀ k : ℕ, (L.pow k).Good ∧ (L.pow k).deg = k * L.deg

def MemOfLoc : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (I : FractionalIdeal (𝓞 K)⁰ K) (x : K), I ≠ 0 →
    (∀ p : HeightOneSpectrum (𝓞 K), ∃ c : K, IsLocGen p c I ∧ p.valuation K x ≤ p.valuation K c) → x ∈ I

def HadamardPD : Prop :=
  ∀ (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ), A.PosDef → A.det.re ≤ ∏ i, (A i i).re

end Formalism.L2.LamCM
end
end

-- bundled from Formalism.LocalToGlobal.CMDeterminantIdeals.StatementC
section
noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder

def CoeffCauchy : Prop :=
  ∀ (V : Type) [Fintype V] (G : MvPolynomial V ℂ) (ρ : V → ℝ) (S : ℝ) (μ : V →₀ ℕ), (∀ v, 0 < ρ v) →
    (∀ z : V → ℂ, (∀ v, ‖z v‖ ≤ ρ v) → ‖MvPolynomial.eval z G‖ ≤ S) →
    ‖AddMonoidAlgebra.coeff G μ‖ * ∏ v, ρ v ^ μ v ≤ S

def LamEnd : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (NN : MLine K) (cf : K) (S : (K →+* ℂ) → ℝ) (B : ℝ),
    NN.Good → cf ≠ 0 → cf ∈ NN.I → (∀ σ, 0 < S σ) → 0 < B → (∀ σ, NN.len σ cf ≤ S σ * B) →
    - NN.deg - (Module.finrank ℚ K : ℝ) * Real.log B ≤ ∑ σ : K →+* ℂ, Real.log (S σ)

def pDeg (logOm : ℝ) : ℝ := (1 + |logOm|) / 2

def lineNN {K : Type} [Field K] [NumberField K] {g : ℕ} {V : Type} [Fintype V] (de : MLine K) (ℓ : Fin g → MLine K)
    (c : V → Fin g) (μ : V → ℕ) (n : ℕ) : MLine K :=
  (de.pow n).tensor (MLine.prodPow (fun v => ℓ (c v)) μ).dual

end Formalism.L2.LamCM
end
end

-- bundled from Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
section
noncomputable section

namespace Formalism.L2.LamCM

open IsLocalRing
open scoped ComplexOrder

abbrev FrVar {B : Type} (m : B → ℕ) : Type := Σ b : B, Fin (m b) × Fin (m b)

variable {B : Type} {m : B → ℕ}

def evalFr {R : Type} [CommRing R] (P : MvPolynomial (FrVar m) R) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R) : R :=
  MvPolynomial.eval (fun v : FrVar m => X v.1 v.2.2 v.2.1) P

def substFr {R : Type} [CommRing R] (U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R) (P : MvPolynomial (FrVar m) R) :
    MvPolynomial (FrVar m) R :=
  MvPolynomial.bind₁ (fun v : FrVar m => ∑ j, MvPolynomial.C (U v.1 j v.2.2) * MvPolynomial.X (⟨v.1, (v.2.1, j)⟩ : FrVar m)) P

def LemmaGCore : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    (B : Type) [Fintype B] (m : B → ℕ) (P : MvPolynomial (FrVar m) K),
    (Infinite (ResidueField R) ∨ P.totalDegree + ∑ b, m b < Nat.card (ResidueField R)) →
    (∀ X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) R, (∀ b, IsUnit (X b).det) →
      evalFr P (fun b => (X b).map (algebraMap R K)) ∈ Set.range (algebraMap R K)) →
    ∀ μ, AddMonoidAlgebra.coeff P μ ∈ Set.range (algebraMap R K)

def BigResExt : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V →
    Finite (ResidueField V) → ∀ N : ℕ,
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra V W),
      IsAdicComplete (maximalIdeal W) W ∧ Finite (ResidueField W) ∧ N < Nat.card (ResidueField W) ∧
      Function.Injective (algebraMap V W) ∧ IsLocalHom (algebraMap V W)

def LemmaG : Prop :=
  ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (B : Type) [Fintype B] (m : B → ℕ) (P : MvPolynomial (FrVar m) K),
    IsAdicComplete (maximalIdeal V) V → Finite (ResidueField V) →
    (∀ (W KW : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field KW] [Algebra W KW] [IsFractionRing W KW]
      [Algebra V W] (f : K →+* KW), IsAdicComplete (maximalIdeal W) W → Finite (ResidueField W) →
      IsLocalHom (algebraMap V W) → (∀ a : V, f (algebraMap V K a) = algebraMap W KW (algebraMap V W a)) →
      ∀ X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) W, (∀ b, IsUnit (X b).det) →
        evalFr (MvPolynomial.map f P) (fun b => (X b).map (algebraMap W KW)) ∈ Set.range (algebraMap W KW)) →
    ∀ μ, AddMonoidAlgebra.coeff P μ ∈ Set.range (algebraMap V K)

def SubstGauss : Prop :=
  ∀ (R K : Type) [CommRing R] [Field K] [Algebra R K] (B : Type) [Fintype B] (m : B → ℕ) (P : MvPolynomial (FrVar m) K)
    (U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) K) (c : ∀ b, Fin (m b) → K),
    (∀ μ, AddMonoidAlgebra.coeff P μ ∈ Set.range (algebraMap R K)) →
    (∀ b j k, c b j * U b j k ∈ Set.range (algebraMap R K)) →
    ∀ μ : FrVar m →₀ ℕ, AddMonoidAlgebra.coeff (substFr U P) μ * ∏ v : FrVar m, c v.1 v.2.2 ^ μ v ∈ Set.range (algebraMap R K)

def IsEquiv [DecidableEq B] (a : ∀ b, Fin (m b) → ℕ) (P : MvPolynomial (FrVar m) ℂ) : Prop :=
  ∀ (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℂ) (b : B) (t : Matrix (Fin (m b)) (Fin (m b)) ℂ),
    (∀ b', (X b').det ≠ 0) → t.det ≠ 0 → t.BlockTriangular id →
    evalFr P (Function.update X b (X b * t)) = ReciprocityTheory.MultiplicativeHeights.triChar (a b) t * evalFr P X

def ArchTie : Prop :=
  ∀ (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (a : ∀ b, Fin (m b) → ℕ) (P : MvPolynomial (FrVar m) ℂ)
    (Hm U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℂ) (nn : ∀ b, Fin (m b) → ℝ) (C La : ℝ) (r : ℕ),
    (∀ b, (Hm b).PosDef) → IsEquiv a P →
    (∀ X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℂ, (∀ b, (X b).conjTranspose * Hm b * X b = 1) → ‖evalFr P X‖ ≤ C) →
    (∀ b j, 0 < nn b j) → 0 ≤ La → (∀ b, m b ≤ r) →
    (∀ b j, ReciprocityTheory.MultiplicativeHeights.hq (Hm b) (U b j) ≤ (La * nn b j) ^ 2) →
    ∀ z : FrVar m → ℂ, (∀ v : FrVar m, ‖z v‖ * nn v.1 v.2.2 ≤ 1) →
      ‖MvPolynomial.eval z (substFr U P)‖ ≤ C * ((r : ℝ) * La) ^ (∑ b, ∑ i, a b i)

def SubstHomog : Prop :=
  ∀ (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (a : ∀ b, Fin (m b) → ℕ) (P : MvPolynomial (FrVar m) ℂ)
    (U : ∀ b, Matrix (Fin (m b)) (Fin (m b)) ℂ), IsEquiv a P →
    ∀ μ : FrVar m →₀ ℕ, AddMonoidAlgebra.coeff (substFr U P) μ ≠ 0 → ∑ v : FrVar m, μ v = ∑ b, ∑ i, a b i

end Formalism.L2.LamCM
end
end

-- bundled from Formalism.LocalToGlobal.CMDeterminantIdeals.StatementP
section
noncomputable section

namespace Formalism.L2.LamCM

open NumberField IsDedekindDomain
open scoped nonZeroDivisors

def IsBaseChangeLine {K K1 : Type} [Field K] [NumberField K] [Field K1] [NumberField K1] [Algebra K K1] (L : MLine K)
    (L1 : MLine K1) : Prop :=
  ((L1.I : Submodule (𝓞 K1) K1) = Submodule.span (𝓞 K1) (algebraMap K K1 '' {x | x ∈ L.I})) ∧
  ∀ σ : K1 →+* ℂ, L1.n σ = L.n (σ.comp (algebraMap K K1))

def NdegBaseChange : Prop :=
  ∀ (K K1 : Type) [Field K] [NumberField K] [Field K1] [NumberField K1] [Algebra K K1] (L : MLine K) (L1 : MLine K1),
    L.Good → IsBaseChangeLine L L1 → L1.Good ∧ L1.ndeg = L.ndeg

def LocGenBaseChange : Prop :=
  ∀ (K K1 : Type) [Field K] [NumberField K] [Field K1] [NumberField K1] [Algebra K K1] (L : MLine K) (L1 : MLine K1)
    (p : HeightOneSpectrum (𝓞 K)) (p1 : HeightOneSpectrum (𝓞 K1)) (c : K), L.I ≠ 0 → IsBaseChangeLine L L1 →
    (∀ a : 𝓞 K, a ∈ p.asIdeal ↔ (algebraMap (𝓞 K) (𝓞 K1) a) ∈ p1.asIdeal) → IsLocGen p c L.I →
    IsLocGen p1 (algebraMap K K1 c) L1.I

end Formalism.L2.LamCM
end
end

